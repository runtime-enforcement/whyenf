open Base
open Stdio

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm
module Valuation = ITerm.Valuation
open Etc
open Global

open Monitor
open Mformula

module Triple = struct

  type t = Db.t * Db.t * FObligations.t

  let join (sup1, cau1, fobligs1) (sup2, cau2, fobligs2) =
    (Db.union sup1 sup2, Db.union cau1 cau2, Set.union fobligs1 fobligs2)

  (*let equal (sup1, cau1, fobligs1) (sup2, cau2, fobligs2) =
    Db.equal sup1 sup2 && Db.equal cau1 cau2 && Set.equal fobligs1 fobligs2*)

  let db_equal (sup1, cau1, _) (sup2, cau2, _) =
    Db.equal sup1 sup2 && Db.equal cau1 cau2

  let sup (sup, _, _) = sup
  let cau (_, cau, _) = cau
  (*let fobligs (_, _, fobligs) = fobligs*)

  let empty = (Db.empty, Db.empty, Set.empty (module FObligation))
  (*let empty2 fobligs = (Db.empty, Db.empty, fobligs)*)

  (*let is_empty (sup, cau, fobligs) = Db.is_empty sup && Db.is_empty cau && Set.is_empty fobligs*)

  let update_db db (sup, cau, _) = Db.union (Db.diff db sup) cau

  let update_fobligs fobligs (_, _, fobligs') = Set.union fobligs fobligs'

  let update_memo (sup, cau, fobligs) memo =
    let memo = Set.fold (Set.map (module String) ~f:Db.Event.name (Db.events (Db.union sup cau)))
                 ~init:memo ~f:Memo.add_event in
    let memo = Set.fold (Set.map (module Int) ~f:FObligation.h fobligs)
                 ~init:memo ~f:Memo.add_obligation in
    memo

(*let to_lists (sup, cau, fobligs) =
  (Set.to_list sup, Set.to_list cau, fobligs)*)

let to_string indent (sup, cau, fobligs) =
  "\nTriple:\n" ^
  Printf.sprintf "\n%ssup = %s" indent (Db.to_string sup) ^
  Printf.sprintf "\n%scau = %s" indent (Db.to_string cau) ^
    Printf.sprintf "\n%sfobligs = [%s]\n" indent (FObligations.to_string fobligs)

end

let inc_ts ts = Time.(ts + !s_ref)

let labels_to_string ls =
  String.concat ~sep:", " (List.map ~f:(fun l -> Printf.sprintf "\"%s\"" l) ls)

module EState = struct

  type t = { ms: MState.t
           ; tp: timepoint
           ; ts: timestamp
           ; db: Db.t
           ; r : Triple.t
           ; fobligs: FObligations.t
           ; memo: Monitor.res Monitor.Memo.t
           ; nick: bool
           ; labels: string list
           }

  let to_string { ms
    ; tp
    ; ts
    ; db
    ; r
    ; fobligs } =
    "\n<> EState <> \n" ^
    Printf.sprintf "ts = %s\n" (Time.to_string ts) ^
    Printf.sprintf "tp = %d\n" tp ^
    Printf.sprintf "db = %s\n" (Db.to_string db) ^
    Printf.sprintf "fobligs = %s\n" (FObligations.to_string fobligs) ^
    Printf.sprintf "%s" (MState.to_string "  " ms) ^
    (Triple.to_string "  " r)

  let init ms mf = { ms;
                     tp = 0;
                     ts = Time.zero;
                     db = Db.create [];
                     r = Triple.empty;
                     fobligs = Set.singleton (module FObligation)
                                 (FFormula (IFormula.init mf, -1, Valuation.empty), Valuation.empty, POS);
                     memo = Memo.empty;
                     nick = false;
                     labels = [] }

  let update r es =
    let memo = Triple.update_memo r es.memo in
    { es with db      = Triple.update_db es.db r;
              fobligs = Triple.update_fobligs es.fobligs r;
              r       = Triple.join es.r r;
              memo }

  let add_sup sup es =
    if !Global.label then
      Stdio.printf "[Enforcer:Label] Suppress %s: %s\n"
        (Db.Event.to_string sup)
        (labels_to_string es.labels);
    update (Db.singleton sup, Db.empty, Set.empty (module FObligation)) es

  let add_cau cau es =
    if !Global.label then
      Stdio.printf "[Enforcer:Label] Cause %s: %s\n"
        (Db.Event.to_string cau)
        (labels_to_string es.labels);
    update (Db.empty, Db.singleton cau, Set.empty (module FObligation)) es

  let add_foblig foblig es =
    (*print_endline ("add_foblig: " ^ FObligation.to_string foblig);*)
    update (Db.empty, Db.empty, Set.singleton (module FObligation) foblig) es

  (*let combine es' es = update es'.r es*)

  let fixpoint fn es =
    let rec loop r es =
      let es' = fn (update r es) in
      if not (Triple.db_equal es.r es'.r) then
        loop es.r es'
      else
        es'
    in
    loop Triple.empty es

  let mstep_state es =
    mstep es.tp es.ts es.db true es.ms es.fobligs

  let exec_monitor mf es =
    let memo, (_, aexpl, _) = mstep_state { es with ms = { es.ms with mf } } es.memo in
    { es with memo }, aexpl

  let do_or = (||)
  let do_and = (&&)
  let do_ors = List.fold_left ~f:(||) ~init:false
  let do_ands = List.fold_left ~f:(&&) ~init:true

  let specialize lbls es = Expl.Pdt.specialize lbls do_ors do_ands

  let sat (v: ITerm.Valuation.t) mf es =
    (*print_endline "--sat";
      print_endline ("sat.mf=" ^ MFormula.to_string mf);
      print_endline ("sat.expl=" ^ Expl.to_string (exec_monitor mf es));
      print_endline ("sat.v=" ^ Etc.valuation_to_string v);
      print_endline ("sat.proof=" ^ E.Proof.to_string "" (specialize mf es v (exec_monitor mf es)));*)
    let es, p = exec_monitor mf es in
    (*print_endline (Printf.sprintf "sat(%s)=%s"
      (Expl.to_string  p)
      (E.Proof.to_string "" (specialize es v p)));*)
    es, specialize mf.lbls es v p

  let vio x mf es =
    sat x (IFormula.map_mf mf Filter.tt ~exquant:true (fun mf p -> MNeg (p mf))) es
  
  let all_not_sat v (x: int) mf es =
    (*print_endline "--all_not_sat";*)
    (*print_endline ("all_not_sat.mf=" ^ MFormula.to_string mf);*)
    (*print_endline ("all_not_sat.x=" ^ x);
      print_endline ("all_not_sat.v=" ^ Etc.valuation_to_string v);
      print_endline ("all_not_sat.proof="^ E.to_string (snd(exec_monitor mf es)));
      print_endline ("all_not_sat.collected(" ^ x  ^ ")=" ^ Setc.to_string (Expl.Pdt.collect E.Proof.isV (Setc.inter_list (module Dom)) (Setc.union_list (module Dom)) v x (snd (exec_monitor mf es))));*)
    let es, p = exec_monitor mf es in
    match Expl.Pdt.collect
            mf.lbls
            (fun b -> not b)
            (Setc.inter_list (module Dom))
            (Setc.union_list (module Dom))
            v x p with
    | Setc.Finite s -> es, Set.elements s
    | s -> Stdio.printf "Infinite set of candidates for %d in %s: from %s collected %s\n"
             x (IFormula.to_string mf) (Expl.to_string p) (Setc.to_string s);
           raise (Errors.EnforcementError "Internal error: Infinite set of candidates in all_not_sat")

  let all_not_vio v x mf es =
    (*let neg_mf = MFormula.map_mf mf mf.filter ~exquant:true (fun mf -> MNeg mf) in*)
    (*print_endline ("all_not_vio.x=" ^ x);
      print_endline ("all_not_vio.v=" ^ Etc.valuation_to_string v);
      print_endline ("all_not_vio.proof="^ E.to_string (snd(exec_monitor mf es)));
      print_endline ("all_not_vio.collected(" ^ x  ^ ")=" ^ Setc.to_string (Expl.Pdt.collect E.Proof.isV (Setc.union_list (module Dom)) (Setc.inter_list (module Dom)) v x (snd (exec_monitor neg_mf es))));*)
    let es, p = exec_monitor (*neg_*)mf es in
    match Expl.Pdt.collect
            mf.lbls
            (fun b -> b)
            (Setc.union_list (module Dom))
            (Setc.inter_list (module Dom))
            v x p with
    | Setc.Finite s -> es, Set.elements s
    | s -> Stdio.printf "Infinite set of candidates for %d in %s: from %s collected %s\n"
             x (IFormula.to_string mf) (Expl.to_string p) (Setc.to_string s);
           raise (Errors.EnforcementError "Internal error: Infinite set of candidates in all_not_vio")

  let rec filter_eval (db : Db.t) = function
    | Filter.An e -> (Db.mem_trace db e)
    | AllOf fis -> List.for_all fis ~f:(filter_eval db)
    | OneOf fis -> List.exists fis ~f:(filter_eval db)

  let can_skip es (mformula: IFormula.t) =
    !Global.filter && not (filter_eval es.db mformula.filter)

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
    Option.value ts ~default:es.ts

  let rec enfsat_andl v mfs es =
    List.fold_left mfs ~init:es ~f:(testenf sat enfsat v)

  and enfsat_andr v mfs es =
    List.fold_right mfs ~init:es ~f:(fun mf es -> testenf sat enfsat v es mf)

  and enfsat_forall x mf v es =
    let enfs es d = enfsat mf (Map.update v x ~f:(fun _ -> d)) es in
    let es, ds = all_not_sat v x mf es in
    (*print_endline ("--enfsat_forall.mf="^ (MFormula.value_to_string mf));
    print_endline ("--enfsat_forall.ds="^ (Dom.list_to_string ds));*)
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
    (*print_endline ("--enfvio_exists.mf="^ (MFormula.value_to_string mf));
    print_endline ("--enfvio_exists.ds="^ (Dom.list_to_string ds));*)
    List.fold ds ~init:es ~f:enfs

  (*and enfvio_until i ts (h, vv) mf1 mf2 =
    let test1 = if Interval.has_zero i then vio else (fun _ _ es -> es, true) in
    let enf2 mf2 v es = add_foblig (FUntil (default_ts ts es, R, i, mf1, mf2, h, vv), v, NEG) es in
    lr test1 sat enfvio enf2 mf1 mf2*)

  and enfvio_eventually i ts (h, vv) (mf: IFormula.t) v es =
    (*let test1 = if Interval.has_zero i then vio else (fun _ _ es -> es, true) in*)
    let es = add_foblig (FEventually (default_ts ts es, i, mf, h, vv), v, NEG) es in
    enfvio mf v es

  and enfsat (mformula: IFormula.t) v es : t =
    (*print_endline ("--enfsat");*)
    (*print_endline ("mformula=" ^ MFormula.value_to_string mformula);*)
    (*print_endline ("v=" ^ Etc.valuation_to_string v);*)
    (*print_endline ("db=" ^ Db.to_string (es.db));*)
      (*print_endline ("es=" ^ to_string es);*)
    (*print_endline ("filter=" ^ Filter.to_string mformula.filter);*)
    match mformula.mf with
    | _ when can_skip es mformula ->
      (*print_endline (Printf.sprintf "Skipping %s as there are no %s in %s"
         (MFormula.to_string mformula)
         (Filter.to_string mformula.filter)
         (Db.to_string es.db));*)
       es
    | MTT -> es
    | MPredicate (r, trms) when Sig.equal_pred_kind (Sig.kind_of_pred r) Sig.Trace ->
       let new_cau = (r, List.map trms ~f:(fun trm -> ITerm.unconst (Sig.eval mformula.lbls v trm))) in
       add_cau new_cau es
    | MNeg mf -> enfvio mf v es
    | MAnd (L, mfs, _) -> fixpoint (enfsat_andl v mfs) es
    | MAnd (R, mfs, _) -> fixpoint (enfsat_andr v mfs) es
    | MOr (L, mf1 :: _, _) -> enfsat mf1 v es
    | MOr (R, mfs, _) when not (List.is_empty mfs) -> enfsat (List.last_exn mfs) v es
    | MImp (L, mf1, _, _) -> enfvio mf1 v es
    | MImp (R, _, mf2, _) -> enfsat mf2 v es
    | MExists (x, tt, _, mf) -> enfsat mf (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
    | MForall (x, _, _, mf) -> fixpoint (enfsat_forall x mf v) es
    | MENext (i, ts, mf, vv) ->
       add_foblig (FInterval (default_ts ts es, i, mf, mformula.hash, vv), v, POS) es
    | MEEventually (i, ts, mf, vv) ->
       if Interval.diff_right_of (default_ts ts es) (inc_ts es.ts) i && es.nick then
         enfsat mf v es
       else
         add_foblig (FEventually (default_ts ts es, i, mf, mformula.hash, vv), v, POS) es
    | MEAlways (i, ts, mf, vv) ->
       let es =
         let es, b = if can_skip es mf then es, true else sat v mf es in
         if Interval.diff_is_in (default_ts ts es) es.ts i && not b then
           enfsat mf v es
         else
           es
       in if Interval.diff_right_of (default_ts ts es) (inc_ts es.ts) i && es.nick then
            es
          else
            add_foblig (FAlways (default_ts ts es, i, mf, mformula.hash, vv), v, POS) es
    | MOnce (_, mf, _) -> enfsat mf v es
    | MSince (_, _, _, mf2, _) -> enfsat mf2 v es
    | MEUntil (R, i, ts, mf1, mf2, vv) ->
       if Interval.diff_right_of (default_ts ts es) (inc_ts es.ts) i && es.nick then
         add_cau Db.Event._tp (enfsat mf2 v es)
       else (
         let es, b = if can_skip es mf1 then es, true else sat v mf1 es in
         if not b then
           enfsat mf2 v es
         else
           add_foblig (FUntil (default_ts ts es, R, i, mf1, mf2, mformula.hash, vv), v, POS) es)
    | MEUntil (LR, i, ts, mf1, mf2, vv) ->
       if Interval.diff_right_of (default_ts ts es) (inc_ts es.ts) i && es.nick then
         add_cau Db.Event._tp (enfsat mf2 v es)
       else
         add_foblig (FUntil (default_ts ts es, LR, i, mf1, mf2, mformula.hash, vv), v, POS)
           (enfsat mf1 v es)
    | MAnd (LR, _, _) ->
       raise (Errors.EnforcementError
                (Printf.sprintf "side for %s was not fixed" (IFormula.to_string mformula)))
    | MLabel (s, mf) ->
       let es' = enfsat mf v { es with labels = s :: es.labels } in
       { es' with labels =  es.labels }
    | _ -> raise (Errors.EnforcementError
                    (Printf.sprintf "function enfsat is not defined for %s"
                       (IFormula.op_to_string mformula)))
  and enfvio (mformula: IFormula.t) v es =
    (*print_endline "--enfvio";
      print_endline ("mformula=" ^ MFormula.value_to_string mformula);*)
    (*print_endline ("v=" ^ Etc.valuation_to_string v);*)
    (*print_endline ("es=" ^ to_string es);*)
    match mformula.mf with
    | _ when can_skip es mformula -> es
    | MFF -> es
    | MPredicate (r, trms) when Sig.equal_pred_kind (Sig.kind_of_pred r) Sig.Trace ->
       let new_sup = (r, List.map trms ~f:(fun trm -> ITerm.unconst (Sig.eval mformula.lbls v trm))) in
       add_sup new_sup es
    | MNeg mf -> enfsat mf v es
    | MAnd (L, mf1 :: _, _) -> enfvio mf1 v es
    | MAnd (R, mfs, _) when not (List.is_empty mfs) -> enfvio (List.last_exn mfs) v es
    | MOr (L, mfs, _) -> fixpoint (enfvio_orl v mfs) es
    | MOr (R, mfs, _) -> fixpoint (enfvio_orr v mfs) es
    | MImp (L, mf1, mf2, _) -> fixpoint (enfvio_imp mf1 mf2 v) es
    | MImp (R, mf1, mf2, _) -> fixpoint (enfvio_imp mf2 mf1 v) es
    | MExists (x, _, _, mf) -> fixpoint (enfvio_exists x mf v) es
    | MForall (x, tt, _, mf) -> enfvio mf (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
    | MENext (i, ts, mf, vv) ->
       add_foblig (FInterval (default_ts ts es, i, mf, mformula.hash, vv), v, NEG) es
    | MEEventually (i, ts, mf, vv) -> enfvio_eventually i ts (mformula.hash, vv) mf v es
    | MEAlways (i, ts, mf, vv) ->
       if Interval.diff_right_of (default_ts ts es) (inc_ts es.ts) i && es.nick then
         enfvio mf v es
       else
         add_foblig (FAlways (default_ts ts es, i, mf, mformula.hash, vv), v, NEG) es
    | MSince (L, _, mf1, _, _) -> enfvio mf1 v es
    | MEUntil (L, _, _, mf1, _, _) -> enfvio mf1 v es
    | MEUntil (R, i, ts, mf1, mf2, vv) ->
       let es, b1 = sat v mf1 es in
       let es, b2 = sat v mf2 es in
       let es =
         if Interval.diff_is_in (default_ts ts es) es.ts i && b2 then
           enfvio mf2 v es
         else
           es
       in
       if not (Interval.diff_right_of (default_ts ts es) (inc_ts es.ts) i && es.nick)
          && b1 then
         add_foblig (FUntil (default_ts ts es, R, i, mf1, mf2, mformula.hash, vv), v, NEG) es
       else
         es
    | MAnd (LR, _, _)
      | MOr (LR, _, _)
      | MImp (LR, _, _, _)
      | MSince (LR, _, _, _, _)
      | MEUntil (LR, _, _, _, _, _) ->
       raise (Errors.EnforcementError
                (Printf.sprintf "side for %s was not fixed" (IFormula.to_string mformula)))
    | MLabel (s, mf) ->
       let es' = enfvio mf v { es with labels = s :: es.labels } in
       { es' with labels = es.labels }
    | _ -> raise (Errors.EnforcementError
                    (Printf.sprintf "function enfvio is not defined for %s"
                       (IFormula.op_to_string mformula)))

  let enf mf es =
    let es = { es with r = Triple.empty; fobligs = FObligations.empty } in
    let es, b = sat ITerm.Valuation.empty mf es in
    if not b then
      enfsat mf ITerm.Valuation.empty es
    else
      es

end

module Order = struct

  type t = ReOrd of Db.t * Db.t | PrOrd of Db.t | NoOrd

  let print_json ts = function
    | PrOrd c ->
       Stdio.printf "{ \"ts\": %s, \"cause\": %s, \"proactive\": true }\n"
         (Time.to_epoch_string ts) (Db.to_json c)
    | ReOrd (c, s) when not (Db.is_empty c) && not (Db.is_empty s) ->
       Stdio.printf "{ \"ts\": %s, \"cause\": %s, \"suppress\": %s }\n"
         (Time.to_epoch_string ts) (Db.to_json c) (Db.to_json s)
    | ReOrd (c, s) when not (Db.is_empty c) && Db.is_empty s ->
       Stdio.printf "{ \"ts\": %s, \"cause\": %s }\n"
         (Time.to_epoch_string ts) (Db.to_json c)
    | ReOrd (c, s) when Db.is_empty c && not (Db.is_empty s) ->
       Stdio.printf "{ \"ts\": %s, \"suppress\": %s }\n"
         (Time.to_epoch_string ts) (Db.to_json s)
    | ReOrd (_, _) -> Stdio.printf "{ \"ts\": %s }\n" (Time.to_epoch_string ts)
    | NoOrd -> Stdio.printf "{ \"ts\": %s, \"proactive\": true }\n" (Time.to_epoch_string ts)

  let print_textual ts = function
    | PrOrd c -> Stdio.printf "[Enforcer] @%s proactively commands:\nCause: \n%s\nOK.\n"
                   (Time.to_epoch_string ts) (Db.to_string c)
    | ReOrd (c, s) when not (Db.is_empty c) && not (Db.is_empty s) ->
       Stdio.printf "[Enforcer] @%s reactively commands:\nCause:\n%s\nSuppress:\n%s\nOK.\n"
         (Time.to_epoch_string ts) (Db.to_string c) (Db.to_string s)
    | ReOrd (c, s) when not (Db.is_empty c) && Db.is_empty s ->
       Stdio.printf "[Enforcer] @%s reactively commands:\nCause:\n%s\nOK.\n"
         (Time.to_epoch_string ts) (Db.to_string c)
    | ReOrd (c, s) when Db.is_empty c && not (Db.is_empty s) ->
       Stdio.printf "[Enforcer] @%s reactively commands:\nSuppress:\n%s\nOK.\n"
         (Time.to_epoch_string ts) (Db.to_string s)
    | ReOrd (_, _) -> Stdio.printf "[Enforcer] @%s OK.\n" (Time.to_epoch_string ts)
    | NoOrd -> Stdio.printf "[Enforcer] @%s nothing to do proactively.\n" (Time.to_epoch_string ts)
  
  let print ts ord =
    if !json then print_json ts ord else print_textual ts ord
  
end

let goal (es: EState.t) : IFormula.t =
  (*print_endline ("state_goal=" ^ EState.to_string es);*)
  let obligs = List.map (Set.elements es.fobligs) ~f:(FObligation.eval es.ts es.tp) in
  match obligs with
    | [] -> IFormula._tt
    | [mf] -> mf
    | mfs -> IFormula.mapn_mf mfs Filter.tt
               (fun mfs p -> MAnd (L, List.map ~f:p mfs, IFormula.empty_nop_info (List.length mfs)))

let update_fobligs (es: EState.t) =
  let aux (es: EState.t) mf  = 
    let memo, (_, _, ms) = EState.mstep_state { es with ms = { es.ms with mf } } es.memo in
    { es with memo }, ms.mf in
  let es, fobligs_list =
    List.fold_map (Set.elements es.fobligs) ~init:es ~f:(FObligation.fold_map aux) in
  { es with fobligs = Set.of_list (module FObligation) fobligs_list }

let exec' (tf: Tformula.t) inc (b: Time.Span.s) =
  let reactive_step new_db (es: EState.t) =
    (*print_endline ("-- reactive_step tp=" ^ string_of_int es.tp);*)
    (*let time_before = Unix.gettimeofday() in*)
    let mf = goal es in
    (*let time_after = Unix.gettimeofday() in
      print_endline ("Goal time: " ^ string_of_float (time_after -. time_before));*)
    (*print_endline ("goal="^  MFormula.to_string mf);*)
    (*let time_before = Unix.gettimeofday() in*)
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
    (*print_endline ("BEFORE UPDATE: " ^ EState.to_string es);*)
    let es = update_fobligs es in
    (*print_endline ("AFTER UPDATE: " ^ EState.to_string es);*)
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
    let mf = goal es in
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
    let es' = update_fobligs es' in
    (*print_endline ("after: " ^ EState.to_string es');*)
    if Db.mem (Triple.cau es'.r) Db.Event._tp then
      Order.PrOrd (Db.remove (Triple.cau es'.r) Db.Event._tp), es'
    else
      Order.NoOrd, es
  in
  let rec process_db (pb: Other_parser.Parsebuf.t) (es: EState.t) =
    (*let time_before = Unix.gettimeofday() in*)
    if Int.equal pb.ts (-1) && FObligations.accepts_empty es.fobligs then
      es
    else if not (Time.equal (Time.of_int pb.ts) es.ts) then
      match proactive_step es with
      | PrOrd c as o, es' -> Other_parser.Stats.add_cau ~ins:true (Db.size c) pb.stats;
                             Order.print es.ts o;
                             process_db pb { es' with tp = es.tp + 1;
                                                      ts = inc_ts es.ts;
                                                      db = es.db }
      | NoOrd as o, es'   -> Order.print es.ts o;
                             process_db pb { es' with ts = inc_ts es.ts;
                                                      db = es.db }
      | _ -> raise (Invalid_argument "Reactive step did not return a proactive command")
    else if not (Db.is_tick pb.db) then
      match reactive_step pb.db es with
      | ReOrd (c, s) as o, es' -> Other_parser.Stats.add_cau (Db.size c) pb.stats;
                                  Other_parser.Stats.add_sup (Db.size s) pb.stats;
                                  Order.print es.ts o;
                                  if pb.check then
                                    es
                                  else
                                    { es' with tp = es'.tp + 1 }
      | _ -> raise (Invalid_argument "Reactive step did not return a reactive command")
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
       let es = if first then { es with ts = Time.of_int pb.ts } else es in
       let es = process_db pb es in
       Stdlib.flush_all();
       if more then step false (Some(pb)) es else conclude pb es in
  let mf = MFormula.init tf in
  (*print_endline (Monitor.MFormula.to_string mf);*)
  let ms = Monitor.MState.init mf in
  let es = EState.init ms mf in
  step true None es

let make_monitoring (tyf : Tyformula.t) : Tyformula.t =
  let open Tyformula in
  let xs = Set.elements (fv tyf) in
  Sig.add_pred "violation" xs Enftype.cau 0 Trace;
  let vars = List.map ~f:(fun x -> Tterm.make_dummy (Tterm.var x)) xs in
  let violation = make_dummy (Predicate ("violation", vars)) in
  let tyf = make_dummy (Imp (Side.R, tyf, violation)) in
  let tyf = List.fold_right xs ~init:tyf ~f:(fun x f -> make_dummy (forall x f)) in
  make_dummy (Always (Interval.full, tyf))

let compile (f: Formula.t) (b: Time.Span.s) : Tformula.t =
  let open Tyformula.MFOTL_Enforceability(Sig) in
  (* Applying alpha conversion to obtain unique variable names *)
  let f = Formula.convert_vars f in
  (* Typing terms: Formula.t -> Tyformula.t *)
  let tyf = Tyformula.of_formula' f in
  (* If monitoring, do f -> FORALL x_1, ..., x_k. f IMPLIES violation(x_1, ..., x_k) *)
  let tyf = if !monitoring then make_monitoring tyf else tyf in
  (* Typing formulae: Tyformula.t -> Tyformula.typed_t *)
  let typed_tyf = do_type tyf b in
  (* Checking monitorability: Tyformula.typed_t -> Tformula.t *)
  let tf = Tformula.of_formula' typed_tyf in
  (* Checking transparency *)
  let transparent = is_transparent typed_tyf in
  if (not transparent) then
    print_endline "This formula cannot be transparently enforced.";
  (*let tf = if !Global.simplify then Tformula.simplify tf else tf in*)
  (*print_endline ("unprimed: " ^ Tformula.to_string (Tformula.unprime tf));*)
  tf

let exec (f: Formula.t) =
  let tf = compile f !b_ref in
  exec' tf !inc_ref !b_ref

