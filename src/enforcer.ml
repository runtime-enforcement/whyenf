(*******************************************************************)
(*     This is part of WhyEnf, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  François Hublet (ETH Zurich)                                   *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Stdio
open Etc

module type EnforcerT = sig

  val exec: Formula.t -> in_channel -> int -> unit

end

module Make (CI: Checker_interface.Checker_interfaceT) = struct

  module Monitor = Monitor.Make (CI)
  module Plain = Out.Plain (CI)

  open Monitor
  open MFormula

  module Triple = struct

    type t = Db.t * Db.t * FObligations.t

    let join (sup1, cau1, fobligs1) (sup2, cau2, fobligs2) =
      (Set.union sup1 sup2, Set.union cau1 cau2, Set.union fobligs1 fobligs2)

    let equal (sup1, cau1, fobligs1) (sup2, cau2, fobligs2) =
      Set.equal sup1 sup2 && Set.equal cau1 cau2 && Set.equal fobligs1 fobligs2

    let sup (sup, _, _) = sup
    let cau (_, cau, _) = cau
    let fobligs (_, _, fobligs) = fobligs

    let empty = (Set.empty (module Db.Event), Set.empty (module Db.Event), Set.empty (module FObligation))
    let empty2 fobligs = (Set.empty (module Db.Event), Set.empty (module Db.Event), fobligs)

    let is_empty (sup, cau, fobligs) = Set.is_empty sup && Set.is_empty cau && Set.is_empty fobligs

    let update_db db (sup, cau, _) = Set.union (Set.diff db sup) cau

    let update_fobligs fobligs (_, _, fobligs') = Set.union fobligs fobligs'

    let to_lists (sup, cau, fobligs) =
      (Set.to_list sup, Set.to_list cau, fobligs)

    let to_string indent (sup, cau, fobligs) =
      "\nTriple:\n" ^
        Printf.sprintf "\n%ssup = %s" indent (Db.to_string sup) ^
          Printf.sprintf "\n%scau = %s" indent (Db.to_string cau) ^
            Printf.sprintf "\n%sfobligs = %s" indent (FObligations.to_string fobligs) ^ "]\n"

  end

  module EState = struct

    type t = { ms: MState.t
             ; tp: timepoint
             ; ts: timepoint
             ; db: Db.t
             ; r : Triple.t
             ; fobligs: FObligations.t
             ; nick: bool
             ; vars: string list
             }

    let to_string { ms
                  ; tp
                  ; ts
                  ; db
                  ; r
                  ; fobligs } =
      "\n<> EState <> \n" ^
        Printf.sprintf "ts = %d\n" ts ^
          Printf.sprintf "tp = %d\n" tp ^
            Printf.sprintf "db = %s\n" (Db.to_string db) ^
              Printf.sprintf "fobligs = %s\n" (FObligations.to_string fobligs) ^
                Printf.sprintf "%s" (MState.to_string "  " ms) ^
                  (Triple.to_string "  " r)

    let init ms mf = { ms;
                       tp = 0;
                       ts = 0;
                       db = Db.create [];
                       r = Triple.empty;
                       fobligs = Set.singleton (module FObligation)
                                   (FFormula (mf, -1), Base.Map.empty (module Base.String), POS);
                       nick = false;
                       vars = Set.elements (MFormula.fv mf) }

    let update r es =
      { es with db      = Triple.update_db es.db r;
                fobligs = Triple.update_fobligs es.fobligs r;
                r       = Triple.join es.r r }

    let add_sup sup es =
      update (Set.singleton (module Db.Event) sup,
              Set.empty (module Db.Event),
              Set.empty (module FObligation)) es

    let add_cau cau es =
      update (Set.empty (module Db.Event),
              Set.singleton (module Db.Event) cau,
              Set.empty (module FObligation)) es

    let add_foblig foblig es =
      update (Set.empty (module Db.Event),
              Set.empty (module Db.Event),
              Set.singleton (module FObligation) foblig) es

    let combine es' es = update es'.r es

    let fixpoint fn es =
      let rec loop r es =
        let es' = fn (update r es) in
        if not (Triple.equal es.r es'.r) then
          loop es.r es'
        else
          es'
      in loop Triple.empty es

    let mstep_state vars es =
      mstep Out.ENFORCE vars es.ts es.db true es.ms es.fobligs

    let exec_monitor mf es =
      let vars = Set.elements (MFormula.terms mf) in
      let (_, aexpl, _) = mstep_state vars { es with ms = { es.ms with mf } } in
      (*print_endline (Expl.to_string aexpl);*)
      aexpl

    let sat v mf es =
      CI.Expl.Proof.isS (Expl.Pdt.specialize v (exec_monitor mf es))

    let vio v mf es =
      sat v (MNeg mf) es

    let all_not_sat v x mf es =
      (*print_endline "all_not_sat.begin";
      print_endline (Etc.valuation_to_string v);
      print_endline (Monitor.CI.Expl.to_string (exec_monitor mf es));*)
      match Expl.Pdt.collect CI.Expl.Proof.isV v x (exec_monitor mf es) with
      | Setc.Finite s -> Set.elements s
      | _ -> failwith ("Infinite set of candidates for " ^ x ^ " in " ^ MFormula.to_string mf)

    let all_not_vio v x mf es =
      match Expl.Pdt.collect CI.Expl.Proof.isS v x (exec_monitor (MNeg mf) es) with
      | Setc.Finite s -> Set.elements s
      | _ -> failwith ("Infinite set of candidates for " ^ x ^ " in " ^ MFormula.to_string mf)

    let lr test1 test2 enf1 enf2 mf1 mf2 v es =
      let es =
        if not (test1 v mf1 es) then
          enf1 mf1 v es
        else
          es in
      if not (test2 v mf2 es) then
        enf2 mf2 v es
      else
        es

    let rec enfsat_and mf1 =
      lr sat sat enfsat enfsat mf1

    and enfsat_forall x mf v es =
      let enfs d = enfsat mf (Map.update v x ~f:(fun _ -> d)) es in
      (* print_endline (Etc.string_list_to_string (List.map ~f:to_string (List.map (all_not_sat v x mf es) ~f:enfs))); *)
      (* print_endline (to_string (List.fold_left (List.map (all_not_sat v x mf es) ~f:enfs) ~init:es ~f:combine )); *)
      List.fold_left (List.map (all_not_sat v x mf es) ~f:enfs) ~init:es ~f:combine

    and enfvio_or mf1 =
      lr vio vio enfvio enfvio mf1

    and enfvio_imp mf1 =
      lr sat vio enfsat enfvio mf1

    and enfvio_exists x mf v es =
      let enfs d = enfvio mf (Base.Map.update v x ~f:(fun _ -> d)) es in
      List.fold_left (List.map (all_not_vio v x mf es) ~f:enfs) ~init:es ~f:combine

    and enfvio_until i h mf1 mf2 =
      let test1 = if Interval.mem 0 i then vio else (fun _ _ _ -> true) in
      let enf2 mf2 v es = add_foblig (FUntil (es.ts, LR, i, mf1, mf2, h), v, NEG) es in
      lr test1 sat enfvio enf2 mf1 mf2

    and enfvio_eventually i h mf v es =
      let test1 = if Interval.mem 0 i then vio else (fun _ _ _ -> true) in
      let es = add_foblig (FEventually (es.ts, i, mf, h), v, NEG) es in
      enfvio mf v es

    and enfsat (mf: MFormula.t) v es =
      (*Stdio.printf "enfsat(mf=%s, op=%s, side=%s, v=%s, db=%s)\n" (MFormula.to_string mf)
        (MFormula.op_to_string mf) (MFormula.side_to_string mf) (Etc.valuation_to_string v) (Db.to_string es.db);
        Stdlib.flush_all ();*)
      match mf with
      | MTT -> es
      | MPredicate (r, trms) when Pred.Sig.equal_pred_kind (Pred.Sig.kind_of_pred r) Pred.Sig.Trace ->
         let new_cau = (r, List.map trms (fun trm -> Pred.Term.unconst (Pred.Sig.eval v trm))) in
         add_cau new_cau es
      | MNeg mf -> enfvio mf v es
      | MAnd (L, mf1, mf2, _) -> fixpoint (enfsat_and mf1 mf2 v) es
      | MAnd (R, mf1, mf2, _) -> fixpoint (enfsat_and mf2 mf1 v) es
      | MOr (L, mf1, mf2, _) -> enfsat mf1 v es
      | MOr (R, mf1, mf2, _) -> enfsat mf2 v es
      | MImp (L, mf1, mf2, _) -> enfvio mf1 v es
      | MImp (R, mf1, mf2, _) -> enfsat mf2 v es
      | MIff (side1, side2, mf1, mf2, bi) ->
         fixpoint (enfsat_and
                     (MImp (side1, mf1, mf2, empty_binop_info))
                     (MImp (side1, mf2, mf1, empty_binop_info)) v) es
      | MExists (x, tt, mf) -> enfsat mf (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
      | MForall (x, tt, mf) -> fixpoint (enfsat_forall x mf v) es
      | MENext (i, mf, h) -> add_foblig (FInterval (es.ts, i, mf, h), v, POS) es
      | MEEventually (i, mf, h) ->
         if Interval.equal i (Interval.singleton 0) && es.nick then
           enfsat mf v es
         else
           add_foblig (FEventually (es.ts, i, mf, h), v, POS) es
      | MEAlways (i, mf, h) ->
         add_foblig (FAlways (es.ts, i, mf, h), v, POS) (enfsat mf v es)
      | MSince (_, _, mf1, mf2, _, _) -> enfsat mf2 v es
      | MEUntil (R, i, mf1, mf2, h) ->
         if Interval.equal i (Interval.singleton 0) && es.nick then
           add_cau Db.Event._tp (enfsat mf2 v es)
         else if not (sat v mf1 es) then
           enfsat mf2 v es
         else
           add_foblig (FUntil (es.ts, LR, i, mf1, mf2, h), v, POS) (enfsat mf1 v es)
      | MEUntil (LR, i, mf1, mf2, h) ->
         if Interval.equal i (Interval.singleton 0) && es.nick then
           add_cau Db.Event._tp (enfsat mf2 v es)
         else
           add_foblig (FUntil (es.ts, LR, i, mf1, mf2, h), v, POS) (enfsat mf1 v es)
      | MAnd (LR, _, _, _) -> raise (Invalid_argument ("side for " ^
                                                         MFormula.op_to_string mf ^ " was not fixed"))
      | _ -> raise (Invalid_argument ("function enfsat is not defined for "
                                      ^ MFormula.op_to_string mf))
    and enfvio (mf: MFormula.t) v es =
      (*Stdio.printf "enfvio(mf=%s, op=%s, side=%s, v=%s, db=%s)\n" (MFormula.to_string mf)
        (MFormula.op_to_string mf) (MFormula.side_to_string mf) (Etc.valuation_to_string v) (Db.to_string es.db);
        Stdlib.flush_all ();*)
      match mf with
      | MFF -> es
      | MPredicate (r, trms) when Pred.Sig.equal_pred_kind (Pred.Sig.kind_of_pred r) Pred.Sig.Trace ->
         let new_sup = (r, List.map trms (fun trm -> match trm with
                                                     | Var x -> Map.find_exn v x
                                                     | Const c -> c)) in
         add_sup new_sup es
      | MNeg mf -> enfsat mf v es
      | MAnd (L, mf1, _, _) -> enfvio mf1 v es
      | MAnd (R, _, mf2, _) -> enfvio mf2 v es
      | MOr (L, mf1, mf2, _) -> fixpoint (enfvio_or mf1 mf2 v) es
      | MOr (R, mf1, mf2, _) -> fixpoint (enfvio_or mf2 mf1 v) es
      | MImp (L, mf1, mf2, _) -> fixpoint (enfvio_imp mf1 mf2 v) es
      | MImp (R, mf1, mf2, _) -> fixpoint (enfvio_imp mf2 mf1 v) es
      | MIff (L, _, mf1, mf2, _) -> fixpoint (enfvio_imp mf1 mf2 v) es
      | MIff (R, _, mf1, mf2, _) -> fixpoint (enfvio_imp mf2 mf1 v) es
      | MExists (x, tt, mf) -> fixpoint (enfvio_exists x mf v) es
      | MForall (x, tt, mf) -> enfvio mf (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
      | MENext (i, mf, h) -> add_foblig (FInterval (es.ts, i, mf, h), v, NEG) es
      | MEEventually (i, mf, h) -> enfvio_eventually i h mf v es
      | MEAlways (i, mf, h) ->
         if Interval.equal i (Interval.singleton 0) && es.nick then
           enfvio mf v es
         else
           add_foblig (FAlways (es.ts, i, mf, h), v, NEG) es
      | MSince (L, _, mf1, _, _, _) -> enfvio mf1 v es
      | MSince (R, i, mf1, mf2, _, _) ->
         let f' = MNeg (MAnd (R, mf1, mf, empty_binop_info)) in
         fixpoint (enfsat_and f' (MNeg mf2) v) es

      | MEUntil (L, _, mf1, _, _) -> enfvio mf1 v es
      | MEUntil (R, i, mf1, mf2, h) -> fixpoint (enfvio_until i h mf1 mf2 v) es
      | MAnd (LR, _, _, _)
        | MOr (LR, _, _, _)
        | MImp (LR, _, _, _)
        | MSince (LR, _, _, _, _, _)
        | MEUntil (LR, _, _, _, _) ->
         raise (Invalid_argument ("side for " ^ MFormula.op_to_string mf ^ " was not fixed"))
      | _ -> raise (Invalid_argument ("function enfvio is not defined for "
                                      ^ MFormula.op_to_string mf))

    let enf mf es =
      let es = { es with r = Triple.empty; fobligs = FObligations.empty } in
      let v = Map.empty (module String) in
      if not (sat v mf es) then
        enfsat mf (Map.empty (module String)) es
      else
        es

  end

  module Order = struct

    type t = ReOrd of Db.t * Db.t | PrOrd of Db.t | NoOrd

    let print ts = function
      | PrOrd c -> Stdio.printf "[Enforcer] @%d proactively commands:\nCause: \n%s\nOK.\n" ts (Db.to_string c)
      | ReOrd (c, s) when not (Db.is_empty c) && not (Db.is_empty s) ->
         Stdio.printf "[Enforcer] @%d reactively commands:\nCause:\n%s\nSuppress:\n%s\nOK.\n" ts (Db.to_string c) (Db.to_string s)
      | ReOrd (c, s) when not (Db.is_empty c) && Db.is_empty s ->
         Stdio.printf "[Enforcer] @%d reactively commands:\nCause:\n%s\nOK.\n" ts (Db.to_string c)
      | ReOrd (c, s) when Db.is_empty c && not (Db.is_empty s) ->
         Stdio.printf "[Enforcer] @%d reactively commands:\nSuppress:\n%s\nOK.\n" ts (Db.to_string s)
      | ReOrd (_, _) -> Stdio.printf "[Enforcer] @%d OK.\n" ts
      | NoOrd -> Stdio.printf "[Enforcer] @%d nothing to do proactively.\n" ts
  end

  let goal (es: EState.t) =
    let obligs = List.map (Set.elements es.fobligs) ~f:(FObligation.eval es.ts es.tp) in
    let mf = match obligs with
      | [] -> MFormula.MTT
      | init::rest -> List.fold_left rest ~init ~f:(fun mf mg -> MAnd (L, mf, mg, empty_binop_info)) in
    let vars = Set.elements (MFormula.terms mf) in
    match (mstep Out.ENFORCE vars es.ts es.db false { es.ms with mf } es.fobligs)
    with (_, _, ms) -> (*Stdio.printf "b\n"; Stdlib.flush_all (); *)ms.mf


  (* (NOT-SO-URGENT) TODO: other execution mode with automatic timestamps; Pdts everywhere *)
  let exec f inc b =
    let reactive_step new_db es =
      let mf = goal es in
      (*print_endline (MFormula.to_string mf);*)
      let vars = Set.elements (MFormula.fv mf) in
      let es = { es with ms      = { es.ms with tp_cur = es.tp };
                         r       = (Db.create [Db.Event._tp], Db.create [], FObligations.empty);
                         db      = Db.add_event new_db Db.Event._tp;
                         fobligs = FObligations.empty;
                         nick    = false } in
      let es = EState.enf mf es in
      Order.ReOrd (Triple.cau es.r, Triple.sup es.r), es
    in
    let proactive_step es =
      let mf = goal es in
      let vars = Set.elements (MFormula.fv mf) in
      let es' = { es with ms      = { es.ms with tp_cur = es.tp };
                          r       = (Db.create [], Db.create [], FObligations.empty);
                          db      = Db.create [];
                          fobligs = FObligations.empty;
                          nick    = true } in
      let es' = EState.enf mf es' in
      if Db.mem (Triple.cau es'.r) Db.Event._tp then
        Order.PrOrd (Db.remove (Triple.cau es'.r) Db.Event._tp), es'
      else
        Order.NoOrd, es
    in
    let rec process_db (pb: Other_parser.Parsebuf.t) (es: EState.t) =
      (*Stdio.printf "%d %d %d" pb.ts es.ts es.tp;
      Stdio.printf "------------\n";
      Stdio.printf "Before: \n";
      Stdio.printf "%s" (EState.to_string es);
      Stdlib.flush_all ();*)
      if Int.equal pb.ts (-1) && FObligations.accepts_empty es.fobligs then
        es
      else if not (Int.equal pb.ts es.ts) then
        match proactive_step { es with db = Db.create [] } with
        | PrOrd c as o, es' -> Other_parser.Stats.add_cau ~ins:true (Db.size c) pb.stats;
                               Order.print es.ts o;
                               process_db pb { es' with tp = es.tp + 1;
                                                        ts = es.ts + 1;
                                                        db = es.db }
        | NoOrd as o, es'   -> Order.print es.ts o;
                               process_db pb { es' with ts = es.ts + 1;
                                                        db = es.db }
      else if not (Db.is_tick pb.db) then
        match reactive_step pb.db es with
        | ReOrd (c, s) as o, es -> Other_parser.Stats.add_cau (Db.size c) pb.stats;
                                   Other_parser.Stats.add_sup (Db.size s) pb.stats;
                                   Order.print es.ts o;
                                   { es with tp = es.tp + 1 }
      else
        es
    in
    let rec step first pb_opt (es: EState.t) =
      let conclude (pb: Other_parser.Parsebuf.t) es =
        let _ = process_db { pb with ts = -1; db = Db.create [] } es
        in ()
      in
      match Other_parser.Trace.parse_from_channel inc pb_opt with
      | None -> ()
      | Some (more, pb) ->
         (*Stdio.printf "------------\n";
           Stdio.printf "Before: \n";
           Stdio.printf "%s" (EState.to_string es);
           Stdlib.flush_all ();*)
         let es = if first then { es with ts = pb.ts } else es in
         let es = process_db pb es in
         Stdlib.flush_all();
         (*Stdio.printf "------------\n";
           Stdio.printf "After: \n";
           Stdio.printf "%s" (EState.to_string es);
           Stdlib.flush_all ();*)
         if more then step false (Some(pb)) es else conclude pb es in
    let tf = try Typing.do_type f b with Invalid_argument s -> failwith s in
    let transparent =
      try Typing.is_transparent tf
      with Invalid_argument s -> print_endline s; false in
    let f = Tformula.to_formula tf in
    let mf = Monitor.MFormula.init tf in
    let ms = Monitor.MState.init mf in
    let es = EState.init ms mf in
    step true None es

end
