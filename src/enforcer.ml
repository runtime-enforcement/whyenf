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

  val exec: Formula.t -> in_channel -> Time.Span.s -> unit

end

module Make (CI: Checker_interface.Checker_interfaceT) = struct

  module Monitor = Monitor.Make (CI)
  module Plain = Out.Plain (CI)

  open Monitor
  open MFormula

  module Triple = struct

    type t = Db.t * Db.t * FObligations.t

    let join (sup1, cau1, fobligs1) (sup2, cau2, fobligs2) =
      (Db.union sup1 sup2, Db.union cau1 cau2, Set.union fobligs1 fobligs2)

    let equal (sup1, cau1, fobligs1) (sup2, cau2, fobligs2) =
      Db.equal sup1 sup2 && Db.equal cau1 cau2 && Set.equal fobligs1 fobligs2

    let db_equal (sup1, cau1, _) (sup2, cau2, _) =
      Db.equal sup1 sup2 && Db.equal cau1 cau2

    let sup (sup, _, _) = sup
    let cau (_, cau, _) = cau
    let fobligs (_, _, fobligs) = fobligs

    let empty = (Db.empty, Db.empty, Set.empty (module FObligation))
    let empty2 fobligs = (Db.empty, Db.empty, fobligs)

    let is_empty (sup, cau, fobligs) = Db.is_empty sup && Db.is_empty cau && Set.is_empty fobligs

    let update_db db (sup, cau, _) = Db.union (Db.diff db sup) cau

    let update_fobligs fobligs (_, _, fobligs') = Set.union fobligs fobligs'

    let update_memo (_, cau, fobligs) memo =
      let memo = Set.fold (Set.map (module String) ~f:Db.Event.name (Db.events cau))
                   ~init:memo ~f:Memo.add_event in
      let memo = Set.fold (Set.map (module Int) ~f:FObligation.h fobligs)
                   ~init:memo ~f:Memo.add_obligation in
      memo

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
             ; memo: Monitor.res Monitor.Memo.t
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
                       memo = Memo.empty;
                       nick = false; }

    let update r es =
      let memo = Triple.update_memo r es.memo in
      { es with db      = Triple.update_db es.db r;
                fobligs = Triple.update_fobligs es.fobligs r;
                r       = Triple.join es.r r;
                memo }

    let add_sup sup es =
      update (Db.singleton sup, Db.empty, Set.empty (module FObligation)) es

    let add_cau cau es =
      update (Db.empty, Db.singleton cau, Set.empty (module FObligation)) es

    let add_foblig foblig es =
      (*print_endline ("add_foblig: " ^ FObligation.to_string foblig);*)
      update (Db.empty, Db.empty, Set.singleton (module FObligation) foblig) es

    let combine es' es = update es'.r es

    let fixpoint fn es =
      let rec loop r es =
        let es' = fn (update r es) in
        if not (Triple.db_equal es.r es'.r) then
          loop es.r es'
        else
          es'
      in loop Triple.empty es

    let mstep_state es =
      mstep Out.ENFORCE es.tp es.ts es.db true es.ms es.fobligs

    let exec_monitor mf es =
      let memo, (_, aexpl, _) = mstep_state { es with ms = { es.ms with mf } } es.memo in
      { es with memo }, aexpl

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

    let do_ors tp : CI.Expl.Proof.t list -> CI.Expl.Proof.t = function
      | [] -> V (CI.Expl.Proof.make_vff tp)
      | h::t -> List.fold_left ~init:h ~f:do_or t

    let rec do_ands tp : CI.Expl.Proof.t list -> CI.Expl.Proof.t = function
      | [] -> S (CI.Expl.Proof.make_stt tp)
      | h::t -> List.fold_left ~init:h ~f:do_and t
      
    let specialize es =
      Expl.Pdt.specialize (do_ors es.tp) (do_ands es.tp)

    let sat v mf es =
      (*print_endline "--sat";
      print_endline ("sat.mf=" ^ MFormula.to_string mf);
      print_endline ("sat.expl=" ^ CI.Expl.to_string (exec_monitor mf es));
      print_endline ("sat.v=" ^ Etc.valuation_to_string v);
      print_endline ("sat.proof=" ^ CI.Expl.Proof.to_string "" (specialize mf es v (exec_monitor mf es)));*)
      let es, p = exec_monitor mf es in
      (*print_endline (Printf.sprintf "sat(%s)=%s"
                       (CI.Expl.to_string  p)
                       (CI.Expl.Proof.to_string "" (specialize es v p)));*)
      es, CI.Expl.Proof.isS (specialize es v p)

    let vio x mf es =
      sat x (MFormula.map_mf mf Formula.Filter._true (fun mf -> MNeg mf)) es
    
    let all_not_sat v x mf es =
      (*print_endline "--all_not_sat";*)
      (*print_endline ("all_not_sat.mf=" ^ MFormula.to_string mf);
      print_endline ("all_not_sat.x=" ^ x);
      print_endline ("all_not_sat.v=" ^ Etc.valuation_to_string v);
      print_endline ("all_not_sat.proof="^ CI.Expl.to_string (snd(exec_monitor mf es)));*)
      (*print_endline ("all_not_sat.collected(" ^ x  ^ ")=" ^ Setc.to_string (Expl.Pdt.collect CI.Expl.Proof.isV (Setc.inter_list (module Dom)) (Setc.union_list (module Dom)) v x (snd (exec_monitor mf es))));*)
      let es, p = exec_monitor mf es in
      match Expl.Pdt.collect
              CI.Expl.Proof.isV
              (Setc.inter_list (module Dom))
              (Setc.union_list (module Dom))
              v x p with
      | Setc.Finite s -> es, Set.elements s
      | _ -> failwith ("Infinite set of candidates for " ^ x ^ " in " ^ MFormula.to_string mf)

    let all_not_vio v x mf es =
      let es, p = exec_monitor (MFormula.map_mf mf mf.filter (fun mf -> MNeg mf)) es in
      match Expl.Pdt.collect
              CI.Expl.Proof.isS
              (Setc.union_list (module Dom))
              (Setc.inter_list (module Dom))
              v x p with
      | Setc.Finite s -> es, Set.elements s
      | _ -> failwith ("Infinite set of candidates for " ^ x ^ " in " ^ MFormula.to_string mf)

    let can_skip es mformula =
      not (Formula.Filter.eval es.db mformula.filter)

    let testenf test enf v es mf =
      (*print_endline "-- testenf";
      print_endline ("filters=" ^ Formula.Filter.to_string mf.filter);*)
      if not (can_skip es mf) then
        (let es, b = test v mf es in
         if not b then
           enf mf v es
         else
           es)
      else
        es
      
    let lr test1 test2 enf1 enf2 mf1 mf2 v es =
      let es = testenf test1 enf1 v es mf1 in
      testenf test2 enf2 v es mf2

    let default_ts ts es =
      Option.value ts ~default:(Time.of_int es.ts)

    let rec enfsat_andl v mfs es =
      List.fold_left mfs ~init:es ~f:(testenf sat enfsat v)

    and enfsat_andr v mfs es =
      List.fold_right mfs ~init:es ~f:(fun mf es -> testenf sat enfsat v es mf)

    and enfsat_forall x mf v es =
      let enfs es d = enfsat mf (Map.update v x ~f:(fun _ -> d)) es in
      let es, ds = all_not_sat v x mf es in
      List.fold ds ~init:es ~f:enfs

    and enfvio_orl v mfs es =
      List.fold_left mfs ~init:es ~f:(testenf vio enfvio v)

    and enfvio_orr v mfs es =
      List.fold_right mfs ~init:es ~f:(fun mf es -> testenf vio enfvio v es mf)

    and enfvio_imp mf1 =
      lr sat vio enfsat enfvio mf1

    and enfvio_exists x mf v es =
      let enfs es d = enfvio mf (Base.Map.update v x ~f:(fun _ -> d)) es in
      let es, ds = all_not_vio v x mf es in
      List.fold ds ~init:es ~f:enfs

    and enfvio_until i ts (h, vv) mf1 mf2 =
      let test1 = if Interval.has_zero i then vio else (fun _ _ es -> es, true) in
      let enf2 mf2 v es = add_foblig (FUntil (default_ts ts es, R, i, mf1, mf2, h, vv), v, NEG) es in
      lr test1 sat enfvio enf2 mf1 mf2

    and enfvio_eventually i ts (h, vv) mf v es =
      let test1 = if Interval.has_zero i then vio else (fun _ _ es -> es, true) in
      let es = add_foblig (FEventually (default_ts ts es, i, mf, h, vv), v, NEG) es in
      enfvio mf v es

    and enfsat (mformula: MFormula.t) v es : t =
      (*print_endline "--enfsat";
      print_endline ("mformula=" ^ MFormula.to_string mformula);*)
      (*print_endline ("v=" ^ Etc.valuation_to_string v);
      print_endline ("es=" ^ to_string es);*)
      (*print_endline ("filter=" ^ Formula.Filter.to_string mformula.filter);*)
      match mformula.mf with
      | _ when can_skip es mformula ->
         (*print_endline (Printf.sprintf "Skipping %s as there are no %s in %s"
                          (MFormula.to_string mformula)
                          (Formula.Filter.to_string mformula.filter)
                          (Db.to_string es.db));*)
         es
      | MTT -> es
      | MPredicate (r, trms) when Pred.Sig.equal_pred_kind (Pred.Sig.kind_of_pred r) Pred.Sig.Trace ->
         let new_cau = (r, List.map trms (fun trm -> Pred.Term.unconst (Pred.Sig.eval v trm))) in
         add_cau new_cau es
      | MNeg mf -> enfvio mf v es
      | MAnd (L, mfs, _) -> fixpoint (enfsat_andl v mfs) es
      | MAnd (R, mfs, _) -> fixpoint (enfsat_andr v mfs) es
      | MOr (L, [mf1; _], _) -> enfsat mf1 v es
      | MOr (R, [_; mf2], _) -> enfsat mf2 v es
      | MImp (L, mf1, mf2, _) -> enfvio mf1 v es
      | MImp (R, mf1, mf2, _) -> enfsat mf2 v es
      | MIff (side1, side2, mf1, mf2, bi) ->
         fixpoint (enfsat_andl v
                     [MFormula.map2_mf mf1 mf2 Formula.Filter._true
                        (fun mf1 mf2 -> MImp (side1, mf1, mf2, empty_binop_info));
                      MFormula.map2_mf mf2 mf1 Formula.Filter._true
                        (fun mf2 mf1 -> MImp (side1, mf2, mf1, empty_binop_info))]) es
      | MExists (x, tt, b, mf) -> enfsat mf (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
      | MForall (x, tt, b, mf) -> fixpoint (enfsat_forall x mf v) es
      | MENext (i, ts, mf, vv) ->
         add_foblig (FInterval (default_ts ts es, i, mf, mformula.hash, vv), v, POS) es
      | MEEventually (i, ts, mf, vv) ->
         if Interval.diff_right_of (default_ts ts es) (Time.of_int (es.ts+1)) i && es.nick then
           enfsat mf v es
         else
           add_foblig (FEventually (default_ts ts es, i, mf, mformula.hash, vv), v, POS) es
      | MEAlways (i, ts, mf, vv) ->
         let es =
           let es, b = sat v mf es in
           if Interval.diff_is_in (default_ts ts es) (Time.of_int es.ts) i && not b then
             enfsat mf v es
           else
             es
         in if Interval.diff_right_of (default_ts ts es) (Time.of_int (es.ts+1)) i && es.nick then
              es
            else
              add_foblig (FAlways (default_ts ts es, i, mf, mformula.hash, vv), v, POS) es
      | MOnce (_, mf, _, _) -> enfsat mf v es
      | MSince (_, _, mf1, mf2, _, _) -> enfsat mf2 v es
      | MEUntil (R, i, ts, mf1, mf2, vv) ->
         if Interval.diff_right_of (default_ts ts es) (Time.of_int (es.ts+1)) i && es.nick then
           add_cau Db.Event._tp (enfsat mf2 v es)
         else (
           let es, b = sat v mf1 es in
           if not b then
             enfsat mf2 v es
           else
             add_foblig (FUntil (default_ts ts es, R, i, mf1, mf2, mformula.hash, vv), v, POS) es)
      | MEUntil (LR, i, ts, mf1, mf2, vv) ->
         if Interval.diff_right_of (default_ts ts es) (Time.of_int (es.ts+1)) i && es.nick then
           add_cau Db.Event._tp (enfsat mf2 v es)
         else
           add_foblig (FUntil (default_ts ts es, LR, i, mf1, mf2, mformula.hash, vv), v, POS)
             (enfsat mf1 v es)
      | MAnd (LR, _, _) ->
         raise (Invalid_argument ("side for " ^ MFormula.to_string mformula ^ " was not fixed"))
      | _ -> (*print_endline (MFormula.to_string mformula);
             print_endline (to_string es);*)
             raise (Invalid_argument ("function enfsat is not defined for "
                                      ^ MFormula.op_to_string mformula))
    and enfvio (mformula: MFormula.t) v es =
      (*print_endline "--enfvio";
      print_endline ("mformula=" ^ MFormula.to_string mformula);*)
        (*print_endline ("v=" ^ Etc.valuation_to_string v);
      print_endline ("es=" ^ to_string es);*)
      match mformula.mf with
      | _ when can_skip es mformula -> es
      | MFF -> es
      | MPredicate (r, trms) when Pred.Sig.equal_pred_kind (Pred.Sig.kind_of_pred r) Pred.Sig.Trace ->
         let new_sup = (r, List.map trms (fun trm -> match trm with
                                                     | Var x -> Map.find_exn v x
                                                     | Const c -> c)) in
         add_sup new_sup es
      | MNeg mf -> enfsat mf v es
      | MAnd (L, [mf1; _], _) -> enfvio mf1 v es
      | MAnd (R, [_; mf2], _) -> enfvio mf2 v es
      | MOr (L, mfs, _) -> fixpoint (enfvio_orl v mfs) es
      | MOr (R, mfs, _) -> fixpoint (enfvio_orr v mfs) es
      | MImp (L, mf1, mf2, _) -> fixpoint (enfvio_imp mf1 mf2 v) es
      | MImp (R, mf1, mf2, _) -> fixpoint (enfvio_imp mf2 mf1 v) es
      | MIff (L, _, mf1, mf2, _) -> fixpoint (enfvio_imp mf1 mf2 v) es
      | MIff (R, _, mf1, mf2, _) -> fixpoint (enfvio_imp mf2 mf1 v) es
      | MExists (x, tt, b, mf) -> fixpoint (enfvio_exists x mf v) es
      | MForall (x, tt, b, mf) -> enfvio mf (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
      | MENext (i, ts, mf, vv) ->
         add_foblig (FInterval (default_ts ts es, i, mf, mformula.hash, vv), v, NEG) es
      | MEEventually (i, ts, mf, vv) -> enfvio_eventually i ts (mformula.hash, vv) mf v es
      | MEAlways (i, ts, mf, vv) ->
         if Interval.diff_right_of (default_ts ts es) (Time.of_int (es.ts+1)) i && es.nick then
           enfvio mf v es
         else
           add_foblig (FAlways (default_ts ts es, i, mf, mformula.hash, vv), v, NEG) es
      | MSince (L, _, mf1, _, _, _) -> enfvio mf1 v es
      | MEUntil (L, _, ts, mf1, _, _) -> enfvio mf1 v es
      | MEUntil (R, i, ts, mf1, mf2, vv) ->
         let es, b1 = sat v mf1 es in
         let es, b2 = sat v mf2 es in
         let es =
           if Interval.diff_is_in (default_ts ts es) (Time.of_int es.ts) i && b2 then
             enfvio mf2 v es
           else
             es
         in
         if not (Interval.diff_right_of (default_ts ts es) (Time.of_int (es.ts+1)) i && es.nick)
            && b1 then
           add_foblig (FUntil (default_ts ts es, R, i, mf1, mf2, mformula.hash, vv), v, NEG) es
         else
           es
      | MAnd (LR, _, _)
        | MOr (LR, _, _)
        | MImp (LR, _, _, _)
        | MSince (LR, _, _, _, _, _)
        | MEUntil (LR, _, _, _, _, _) ->
         raise (Invalid_argument ("side for " ^ MFormula.to_string mformula ^ " was not fixed"))
      | _ -> raise (Invalid_argument ("function enfvio is not defined for "
                                      ^ MFormula.op_to_string mformula))

    let enf mf es =
      let es = { es with r = Triple.empty; fobligs = FObligations.empty } in
      let v = Map.empty (module String) in
      let es, b = sat v mf es in
      if not b then
        enfsat mf (Map.empty (module String)) es
      else
        es

  end

  module Order = struct

    type t = ReOrd of Db.t * Db.t | PrOrd of Db.t | NoOrd

    let print ts = function
      | PrOrd c -> Stdio.printf "[Enforcer] @%d proactively commands:\nCause: \n%s\nOK.\n" ts (Db.to_string c)
      | ReOrd (c, s) when not (Db.is_empty c) && not (Db.is_empty s) ->
         Stdio.printf "[Enforcer] @%d reactively commands:\nCause:\n%s\nSuppress:\n%s\nOK.\n" ts
           (Db.to_string c) (Db.to_string s)
      | ReOrd (c, s) when not (Db.is_empty c) && Db.is_empty s ->
         Stdio.printf "[Enforcer] @%d reactively commands:\nCause:\n%s\nOK.\n" ts (Db.to_string c)
      | ReOrd (c, s) when Db.is_empty c && not (Db.is_empty s) ->
         Stdio.printf "[Enforcer] @%d reactively commands:\nSuppress:\n%s\nOK.\n" ts (Db.to_string s)
      | ReOrd (_, _) -> Stdio.printf "[Enforcer] @%d OK.\n" ts
      | NoOrd -> Stdio.printf "[Enforcer] @%d nothing to do proactively.\n" ts
  end

  let goal (es: EState.t) =
    let obligs = List.map (Set.elements es.fobligs)
                   ~f:(fun f -> (*print_endline (FObligation.to_string f);
                                print_endline (MFormula.to_string (FObligation.eval (Time.of_int es.ts) es.tp f));*)
                                FObligation.eval (Time.of_int es.ts) es.tp f) in
    let mf = match obligs with
      | [] -> MFormula._tt
      | [mf] -> mf
      | mfs -> MFormula.mapn_mf mfs Formula.Filter._true (fun mfs -> MAnd (L, mfs, empty_binop_info))  in
    match (EState.mstep_state { es with ms = { es.ms with mf } }) es.memo
    with (memo, (_, _, ms)) -> (
      (*print_endline ("goal= " ^ MFormula.to_string ms.mf) ;*) { es with memo }, ms.mf)


  (* (NOT-SO-URGENT) TODO: other execution mode with automatic timestamps; Pdts everywhere *)
  let exec f inc (b: Time.Span.s) =
    let reactive_step new_db (es: EState.t) =
      (*Hashtbl.clear es.memo;*)
      (*print_endline ("-- reactive_step tp=" ^ string_of_int es.tp);*)
      (*let time_before = Unix.gettimeofday() in*)
      let es, mf = goal es in
      (*let time_after = Unix.gettimeofday() in
      print_endline ("Goal time: " ^ string_of_float (time_after -. time_before));*)
      (*print_endline ("goal="^  MFormula.to_string mf);*)
      let time_before = Unix.gettimeofday() in
      let es = { es with ms      = { es.ms with tp_cur = es.tp };
                         r       = (Db.singleton Db.Event._tp,
                                    Db.empty,
                                    FObligations.empty);
                         db      = Db.add_event new_db Db.Event._tp;
                         fobligs = FObligations.empty;
                         nick    = false;
                         memo    = Monitor.Memo.empty } in
      (*let time_after = Unix.gettimeofday() in*)
      (*print_endline ("Update es time: " ^ string_of_float (time_after -. time_before));*)
      (*let time_before = Unix.gettimeofday() in*)
      (*Hashtbl.clear es.memo;*)
      (*let time_after = Unix.gettimeofday() in
      print_endline ("Clear memo time: " ^ string_of_float (time_after -. time_before));*)
      (*print_endline ("before: " ^ EState.to_string es);*)
      (*let time_before = Unix.gettimeofday() in*)
      let es = EState.enf mf es in
      (*let time_after = Unix.gettimeofday() in
      print_endline ("Enf time: " ^ string_of_float (time_after -. time_before));*)
      (*print_endline ("after: " ^ EState.to_string es);*)
      Order.ReOrd (Triple.cau es.r, Triple.sup es.r), es
    in
    let proactive_step (es: EState.t) =
      (*Hashtbl.clear es.memo;*)
      (*print_endline ("-- proactive_step ts=" ^ string_of_int es.ts);*)

      (*print_endline "-- proactive_step";
      print_endline (EState.to_string es);*)
      let es, mf = goal es in
      (*print_endline ("goal="^  MFormula.to_string mf);*)
      let es' = { es with ms      = { es.ms with tp_cur = es.tp };
                          r       = Triple.empty;
                          db      = Db.create [];
                          fobligs = FObligations.empty;
                          nick    = true;
                          memo    = Monitor.Memo.empty } in
      (*Hashtbl.clear es.memo;*)
      (*print_endline ("before: " ^ EState.to_string es);*)
      let es' = EState.enf mf es' in
      (*print_endline ("after: " ^ EState.to_string es');*)
      if Db.mem (Triple.cau es'.r) Db.Event._tp then
        Order.PrOrd (Db.remove (Triple.cau es'.r) Db.Event._tp), es'
      else
        Order.NoOrd, es
    in
    let rec process_db (pb: Other_parser.Parsebuf.t) (es: EState.t) =
      (*let time_before = Unix.gettimeofday() in*)
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
    let mf = Monitor.MFormula.init tf in
    (*print_endline (Monitor.MFormula.to_string mf);*)
    let ms = Monitor.MState.init mf in
    let es = EState.init ms mf in
    step true None es

end

(* TODO[FH]: variable renaming --- order of vars in aggregations *)
(* dummy OK
   clean-logs OK
   logging-behavior OK
   finalized-height OK
   finalization-consistency OK
   replica-divergence OK
   block-validation-latency OK
   unauthorized-connections OK
   reboot-count OK

   OK = sanity checked (probably actually buggy)
*)
