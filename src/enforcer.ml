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

  val exec: Formula.t -> in_channel -> Time.t -> unit

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
            Printf.sprintf "\n%sfobligs = [%s]\n" indent (FObligations.to_string fobligs)

  end

  module EState = struct

    type t = { ms: MState.t
             ; tp: timepoint
             ; ts: timepoint
             ; db: Db.t
             ; r : Triple.t
             ; fobligs: FObligations.t
             ; memo: Monitor.memo
             ; nick: bool
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
                                   (FFormula (mf, -1, Etc.empty_valuation), Base.Map.empty (module Base.String), POS);
                       memo = Hashtbl.create (module Int);
                       nick = false; }

    let update r es =
      if not (Triple.is_empty r) then
        Hashtbl.clear es.memo;
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

    let mstep_state es =
      let fvs = Set.elements (MFormula.fv es.ms.mf) in
      let lbls = MFormula.lbls fvs es.ms.mf in
      mstep Out.ENFORCE fvs lbls es.tp es.ts es.db true es.ms es.fobligs

    let exec_monitor mf es =
      let (_, aexpl, _) = mstep_state { es with ms = { es.ms with mf } } es.memo in
      aexpl

    let do_or (p1: CI.Expl.Proof.t) (p2: CI.Expl.Proof.t) : CI.Expl.Proof.t = match p1, p2 with
      | S sp1, S sp2 -> (S (CI.Expl.Proof.make_sorl sp1))
      | S sp1, V _ -> S (CI.Expl.Proof.make_sorl sp1)
      | V _ , S sp2 -> S (CI.Expl.Proof.make_sorr sp2)
      | V vp1, V vp2 -> V (CI.Expl.Proof.make_vor vp1 vp2)

    let do_and (p1: CI.Expl.Proof.t) (p2: CI.Expl.Proof.t) : CI.Expl.Proof.t = match p1, p2 with
      | S sp1, S sp2 -> S (CI.Expl.Proof.make_sand sp1 sp2)
      | S _ , V vp2 -> V (CI.Expl.Proof.make_vandr vp2)
      | V vp1, S _ -> V (CI.Expl.Proof.make_vandl vp1)
      | V vp1, V vp2 -> V (CI.Expl.Proof.make_vandl vp1)

    let rec do_ors tp : CI.Expl.Proof.t list -> CI.Expl.Proof.t = function
      | [] -> S (CI.Expl.Proof.make_stt tp)
      | h::t -> do_or h (do_ors tp t)

    let rec do_ands tp : CI.Expl.Proof.t list -> CI.Expl.Proof.t = function
      | [] -> V (CI.Expl.Proof.make_vff tp)
      | h::t -> do_and h (do_ands tp t)
      
    let specialize mf es =
      let fvs = Set.elements (MFormula.fv mf) in
      let lbls = MFormula.lbls fvs mf in
      Expl.Pdt.specialize (do_ors es.tp) (do_ands es.tp)

    let sat v mf es =
      (*print_endline "--sat";
      print_endline ("sat.mf=" ^ MFormula.to_string mf);
      print_endline ("sat.expl=" ^ CI.Expl.to_string (exec_monitor mf es));
      print_endline ("sat.v=" ^ Etc.valuation_to_string v);
      print_endline ("sat.proof=" ^ CI.Expl.Proof.to_string "" (specialize mf es v (exec_monitor mf es)));*)
      CI.Expl.Proof.isS (specialize mf es v (exec_monitor mf es))

    let vio x mf es =
      sat x (MFormula.make (MNeg mf)) es
    
    let all_not_sat v x mf es =
      (*print_endline "--all_not_sat";
      print_endline ("all_not_sat.mf=" ^ MFormula.to_string mf);
      print_endline ("all_not_sat.x=" ^ x);
      print_endline ("all_not_sat.v=" ^ Etc.valuation_to_string v);
      print_endline ("all_not_sat.proof="^ CI.Expl.to_string (exec_monitor mf es));
      print_endline ("all_not_sat.collected(" ^ x  ^ ")=" ^ Setc.to_string (Expl.Pdt.collect CI.Expl.Proof.isV (Setc.inter_list (module Dom)) (Setc.union_list (module Dom)) v x (exec_monitor mf es)));*)
      match Expl.Pdt.collect CI.Expl.Proof.isV (Setc.inter_list (module Dom)) (Setc.union_list (module Dom)) v x (exec_monitor mf es) with
      | Setc.Finite s -> Set.elements s
      | _ -> failwith ("Infinite set of candidates for " ^ x ^ " in " ^ MFormula.to_string mf)

    let all_not_vio v x mf es =
      match Expl.Pdt.collect CI.Expl.Proof.isS (Setc.union_list (module Dom)) (Setc.inter_list (module Dom)) v x (exec_monitor (MFormula.make (MNeg mf)) es) with
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
      List.fold_left (List.map (all_not_sat v x mf es) ~f:enfs) ~init:es ~f:combine

    and enfvio_or mf1 =
      lr vio vio enfvio enfvio mf1

    and enfvio_imp mf1 =
      lr sat vio enfsat enfvio mf1

    and enfvio_exists x mf v es =
      let enfs d = enfvio mf (Base.Map.update v x ~f:(fun _ -> d)) es in
      List.fold_left (List.map (all_not_vio v x mf es) ~f:enfs) ~init:es ~f:combine

    and enfvio_until i (h, vv) mf1 mf2 =
      let test1 = if Interval.has_zero i then vio else (fun _ _ _ -> true) in
      let enf2 mf2 v es = add_foblig (FUntil (Time.of_timestamp es.ts, LR, i, mf1, mf2, h, vv), v, NEG) es in
      lr test1 sat enfvio enf2 mf1 mf2

    and enfvio_eventually i (h, vv) mf v es =
      let test1 = if Interval.has_zero i then vio else (fun _ _ _ -> true) in
      let es = add_foblig (FEventually (Time.of_timestamp es.ts, i, mf, h, vv), v, NEG) es in
      enfvio mf v es

    and enfsat (mformula: MFormula.t) v es =
      (*print_endline "--enfsat";
      print_endline ("mformula=" ^ MFormula.to_string mformula);
      print_endline ("v=" ^ Etc.valuation_to_string v);*)
      match mformula.mf with
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
                     (MFormula.make (MImp (side1, mf1, mf2, empty_binop_info)))
                     (MFormula.make (MImp (side1, mf2, mf1, empty_binop_info))) v) es
      | MExists (x, tt, b, _, _, mf) -> enfsat mf (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
      | MForall (x, tt, b, _, _, mf) -> fixpoint (enfsat_forall x mf v) es
      | MENext (i, mf, vv) -> add_foblig (FInterval (Time.of_timestamp es.ts, i, mf, mformula.hash, vv), v, POS) es
      | MEEventually (i, mf, vv) ->
         if Interval.is_zero i && es.nick then
           enfsat mf v es
         else
           add_foblig (FEventually (Time.of_timestamp es.ts, i, mf, mformula.hash, vv), v, POS) es
      | MEAlways (i, mf, vv) ->
         add_foblig (FAlways (Time.of_timestamp es.ts, i, mf, mformula.hash, vv), v, POS) (enfsat mf v es)
      | MSince (_, _, mf1, mf2, _, _) -> enfsat mf2 v es
      | MEUntil (R, i, mf1, mf2, vv) ->
         if Interval.is_zero i && es.nick then
           add_cau Db.Event._tp (enfsat mf2 v es)
         else if not (sat v mf1 es) then
           enfsat mf2 v es
         else
           add_foblig (FUntil (Time.of_timestamp es.ts, LR, i, mf1, mf2, mformula.hash, vv), v, POS) (enfsat mf1 v es)
      | MEUntil (LR, i, mf1, mf2, vv) ->
         if Interval.is_zero i && es.nick then
           add_cau Db.Event._tp (enfsat mf2 v es)
         else
           add_foblig (FUntil (Time.of_timestamp es.ts, LR, i, mf1, mf2, mformula.hash, vv), v, POS) (enfsat mf1 v es)
      | MAnd (LR, _, _, _) -> raise (Invalid_argument ("side for " ^
                                                         MFormula.op_to_string mformula ^ " was not fixed"))
      | _ -> raise (Invalid_argument ("function enfsat is not defined for "
                                      ^ MFormula.op_to_string mformula))
    and enfvio (mformula: MFormula.t) v es =
      match mformula.mf with
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
      | MExists (x, tt, b, _, _, mf) -> fixpoint (enfvio_exists x mf v) es
      | MForall (x, tt, b, _, _, mf) -> enfvio mf (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
      | MENext (i, mf, vv) -> add_foblig (FInterval (Time.of_timestamp es.ts, i, mf, mformula.hash, vv), v, NEG) es
      | MEEventually (i, mf, vv) -> enfvio_eventually i (mformula.hash, vv) mf v es
      | MEAlways (i, mf, vv) ->
         if Interval.is_zero i && es.nick then
           enfvio mf v es
         else
           add_foblig (FAlways (Time.of_timestamp es.ts, i, mf, mformula.hash, vv), v, NEG) es
      | MSince (L, _, mf1, _, _, _) -> enfvio mf1 v es
      | MSince (R, i, mf1, mf2, _, _) ->
         let f' = MFormula.make (MNeg (MFormula.make (MAnd (R, mf1, mformula, empty_binop_info)))) in
         fixpoint (enfsat_and f' (MFormula.make (MNeg mf2)) v) es

      | MEUntil (L, _, mf1, _, _) -> enfvio mf1 v es
      | MEUntil (R, i, mf1, mf2, vv) -> fixpoint (enfvio_until i (mformula.hash, vv) mf1 mf2 v) es
      | MAnd (LR, _, _, _)
        | MOr (LR, _, _, _)
        | MImp (LR, _, _, _)
        | MSince (LR, _, _, _, _, _)
        | MEUntil (LR, _, _, _, _) ->
         raise (Invalid_argument ("side for " ^ MFormula.op_to_string mformula ^ " was not fixed"))
      | _ -> raise (Invalid_argument ("function enfvio is not defined for "
                                      ^ MFormula.op_to_string mformula))

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
    let obligs = List.map (Set.elements es.fobligs) ~f:(FObligation.eval (Time.of_timestamp es.ts) es.tp) in
    let mf = match obligs with
      | [] -> MFormula.make (MFormula.MTT)
      | init::rest -> List.fold_left rest ~init ~f:(fun mf mg -> MFormula.make (MAnd (L, mf, mg, empty_binop_info))) in
    (*print_endline ("<-- " ^ MFormula.to_string mf);*)
    match (EState.mstep_state { es with ms = { es.ms with mf } }) es.memo
    with (_, _, ms) -> (*print_endline ("--> " ^ MFormula.to_string ms.mf) ; *)ms.mf


  (* (NOT-SO-URGENT) TODO: other execution mode with automatic timestamps; Pdts everywhere *)
  let exec f inc b =
    let reactive_step new_db (es: EState.t) =
      Hashtbl.clear es.memo;
      (*print_endline ("-- reactive_step tp=" ^ string_of_int es.tp);*)
      let mf = goal es in
      (*print_endline ("goal="^  MFormula.to_string mf);*)
      let es = { es with ms      = { es.ms with tp_cur = es.tp };
                         r       = (Db.create [Db.Event._tp], Db.create [], FObligations.empty);
                         db      = Db.add_event new_db Db.Event._tp;
                         fobligs = FObligations.empty;
                         nick    = false } in
      Hashtbl.clear es.memo;
      (*print_endline ("before: " ^ EState.to_string es);*)
      let es = EState.enf mf es in
      (*print_endline ("after: " ^ EState.to_string es);*)
      Order.ReOrd (Triple.cau es.r, Triple.sup es.r), es
    in
    let proactive_step (es: EState.t) =
      Hashtbl.clear es.memo;
      (*print_endline ("-- proactive_step ts=" ^ string_of_int es.ts);
      print_endline ("before: " ^ EState.to_string es);*)
      let mf = goal es in
      let es' = { es with ms      = { es.ms with tp_cur = es.tp };
                          r       = (Db.create [], Db.create [], FObligations.empty);
                          db      = Db.create [];
                          fobligs = FObligations.empty;
                          nick    = true } in
      Hashtbl.clear es.memo;
      let es' = EState.enf mf es' in
      (*print_endline ("after: " ^ EState.to_string es');*)
      if Db.mem (Triple.cau es'.r) Db.Event._tp then
        Order.PrOrd (Db.remove (Triple.cau es'.r) Db.Event._tp), es'
      else
        Order.NoOrd, es
    in
    let rec process_db (pb: Other_parser.Parsebuf.t) (es: EState.t) =
      (*print_endline ("--process_db " ^ string_of_int !Monitor.meval_c);*)
      Monitor.meval_c := 0;
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
        | ReOrd (c, s) as o, es' -> Other_parser.Stats.add_cau (Db.size c) pb.stats;
                                    Other_parser.Stats.add_sup (Db.size s) pb.stats;
                                    Order.print es.ts o;
                                    if pb.check then
                                      es
                                    else
                                      { es' with tp = es'.tp + 1 }
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
         let es = if first then { es with ts = pb.ts } else es in
         let es = process_db pb es in
         Stdlib.flush_all();
         if more then step false (Some(pb)) es else conclude pb es in
    let tf = try Typing.do_type f b with Invalid_argument s -> failwith s in
    let transparent =
      try Typing.is_transparent tf
      with Invalid_argument s -> print_endline s; false in
    let f = Tformula.to_formula tf in
    let fvs = Set.elements (Formula.fv f) in
    let lbls = Formula.lbls fvs f in
    let mf = Monitor.MFormula.init lbls tf in
    let ms = Monitor.MState.init mf in
    let es = EState.init ms mf in
    step true None es

end
