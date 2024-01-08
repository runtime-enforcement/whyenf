(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
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
open Monitor
open MFormula
open FObligation

module Triple = struct

  type t = Db.t * Db.t * FObligation.t list

  let join (sup1, cau1, fobligs1) (sup2, cau2, fobligs2) =
    (Set.union sup1 sup2, Set.union cau1 cau2, fobligs1 @ fobligs2)

  let equal (sup1, cau1, fobligs1) (sup2, cau2, fobligs2) =
    Set.equal sup1 sup2 && Set.equal cau1 cau2 && (List.equal FObligation.equal fobligs1 fobligs2)

  let sup (sup, _, _) = sup
  let cau (_, cau, _) = cau
  let fobligs (_, _, fobligs) = fobligs

  let empty = (Set.empty (module Db.Event), Set.empty (module Db.Event), [])
  let empty2 fobligs = (Set.empty (module Db.Event), Set.empty (module Db.Event), fobligs)

  let is_empty (sup, cau, fobligs) = Set.is_empty sup && Set.is_empty cau && List.is_empty fobligs

  let update_db db (sup, cau, _) = Set.union (Set.diff db sup) cau
  let update_fobligs fobligs (_, _, fobligs') = fobligs @ fobligs'

  let to_lists (sup, cau, fobligs) =
    (Set.to_list sup, Set.to_list cau, fobligs)

end

module EState = struct

  type t = { ms: MState.t
           ; tp: timepoint
           ; ts: timepoint
           ; db: Db.t
           ; r : Triple.t
           ; fobligs: FObligation.t list }

  let init ms mf = { ms;
                     tp = 0;
                     ts = 0;
                     db = Db.create [];
                     r = Triple.empty;
                     fobligs = [(FFormula mf, Base.Map.empty (module Base.String), POS)] }

  let update r es =
    { es with db      = Triple.update_db es.db r;
              fobligs = [];
              r       = Triple.join es.r r }

  let add_sup sup es =
    update (Set.singleton (module Db.Event) sup, Set.empty (module Db.Event), []) es

  let add_cau cau es =
    update (Set.singleton (module Db.Event) cau, Set.empty (module Db.Event), []) es

  let add_foblig foblig es =
    { es with fobligs = foblig::es.fobligs }

  let combine es' es = update es'.r es

  let fixpoint fn es =
    let rec loop r es =
      let es' = fn (update r es) in
      if not (Triple.equal es.r es'.r) then
        loop es.r es
      else
        es
    in loop Triple.empty es

  let mstep_state vars es =
    mstep Out.Plain.ENFORCE vars es.ts es.db es.ms es.fobligs

  let exec_monitor v mf es =
    let vars = Set.elements (MFormula.fv mf) in
    let (tstp_expls, ms') = mstep_state vars { es with ms = { es.ms with mf } } in
    match tstp_expls with
    | []   -> failwith ("Monitor did not return a verdict on " ^ (MFormula.to_string mf))
    | ((ts, tp), _)::_ when not (Int.equal ts es.ts) || not (Int.equal tp es.tp) ->
       failwith ("Invalid tstp in proof: " ^ Int.to_string ts ^ " <> " ^ Int.to_string es.ts
                 ^ " or " ^ Int.to_string tp ^ " <> " ^ Int.to_string es.tp)
    | (_, expl)::_ -> (expl, ms'.mf)

  let sat v mf es =
    (* TODO: use mf' *)
    let (expl, mf') = exec_monitor v mf es in
    Expl.Proof.isS (Expl.Pdt.specialize v expl)

  let vio v mf es =
    sat v (MNeg mf) es

  let all_not_sat v x mf es =
    (* TODO: use mf' *)
    let (expl, mf') = exec_monitor v mf es in
    match Expl.Pdt.collect Expl.Proof.isV v x expl with
    | Setc.Finite s -> Set.elements s
    | _ -> failwith ("Infinite set of candidates for " ^ x ^ " in " ^ (MFormula.to_string mf))

  let all_not_vio v x mf es =
    (* TODO: use mf' *)
    let (expl, mf') = exec_monitor v mf es in
    match Expl.Pdt.collect Expl.Proof.isS v x expl with
    | Setc.Finite s -> Set.elements s
    | _ -> failwith ("Infinite set of candidates for " ^ x ^ " in " ^ (MFormula.to_string mf))

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
    let enfs d = enfsat mf (Base.Map.update v x ~f:(fun _ -> d)) es in
    List.fold_left (List.map (all_not_sat v x mf es) ~f:enfs) ~init:es ~f:combine

  and enfvio_or mf1 =
    lr vio vio enfvio enfvio mf1

  and enfvio_imp mf1 =
    lr sat vio enfsat enfvio mf1

  and enfvio_exists x mf v es =
    let enfs d = enfvio mf (Base.Map.update v x ~f:(fun _ -> d)) es in
    List.fold_left (List.map (all_not_vio v x mf es) ~f:enfs) ~init:es ~f:combine

  and enfvio_until i mf1 mf2 ui =
    let test1 = if Interval.mem 0 i then vio else (fun _ _ _ -> true) in
    let enf2 mf2 v es = add_foblig (FUntil (es.ts, LR, i, mf1, mf2, ui), v, NEG) es in
    lr test1 sat enfvio enf2 mf1 mf2

  and enfvio_eventually i mf ei v es =
    let test1 = if Interval.mem 0 i then vio else (fun _ _ _ -> true) in
    let es = add_foblig (FEventually (es.ts, i, mf, ei), v, NEG) es in
    enfvio mf v es

  and enfsat (mf: MFormula.t) v es = match mf with
    | MTT -> es
    | MPredicate (r, trms) ->
       let new_cau = (r, List.map trms (fun trm -> match trm with
                                             | Var x -> Map.find_exn v x
                                             | Const c -> c)) in
       add_cau new_cau es
    | MNeg mf -> enfvio mf v es
    | MAnd (L, mf1, mf2, _) -> fixpoint (enfsat_and mf1 mf2 v) es
    | MAnd (R, mf1, mf2, _) -> fixpoint (enfsat_and mf2 mf1 v) es
    | MAnd (LR, mf1, mf2, _) -> if MFormula.rank mf1 < MFormula.rank mf2 then
                                  fixpoint (enfsat_and mf1 mf2 v) es
                                else
                                  fixpoint (enfsat_and mf2 mf1 v) es
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
    | MNext (i, mf, bi, _) -> add_foblig (FFormula mf, v, POS) es
    | MEventually (i, mf, bi, ei) ->
       let (a, b) = Interval.boundaries i in
       if Int.equal a 0 && Int.equal b 0 then
         enfsat mf v es
       else
         add_foblig (FEventually (es.ts, i, mf, ei), v, POS) es
    | MAlways (i, mf, bi, ai) -> add_foblig (FAlways (es.ts, i, mf, ai), v, POS) (enfsat mf v es)
    | MSince (_, _, mf1, mf2, _, _) -> enfsat mf2 v es
    | MUntil (side, i, mf1, mf2, bi, ui) ->
       let (a, b) = Interval.boundaries i in
       if Int.equal a 0 && Int.equal b 0 then
         enfsat mf2 v es
       else
         add_foblig (FUntil (es.ts, side, i, mf1, mf2, ui), v, POS) (enfsat mf1 v es)
    | _ -> raise (Invalid_argument ("function enfsat is not defined for "
                                    ^ MFormula.op_to_string mf))
  and enfvio (mf: MFormula.t) v es = match mf with
    | MFF -> es
    | MPredicate (r, trms) ->
       let new_sup = (r, List.map trms (fun trm -> match trm with
                                                   | Var x -> Map.find_exn v x
                                                   | Const c -> c)) in
       add_sup new_sup es
    | MNeg mf -> enfsat mf v es
    | MAnd (L, mf1, _, _) -> enfvio mf1 v es
    | MAnd (R, _, mf2, _) -> enfvio mf2 v es
    | MAnd (LR, mf1, mf2, _) -> if MFormula.rank mf1 < MFormula.rank mf2 then
                                  enfvio mf1 v es
                                else
                                  enfvio mf2 v es
    | MOr (L, mf1, mf2, _) -> fixpoint (enfvio_or mf1 mf2 v) es
    | MOr (R, mf1, mf2, _) -> fixpoint (enfvio_or mf2 mf1 v) es
    | MOr (LR, mf1, mf2, _) -> if MFormula.rank mf1 < MFormula.rank mf2 then
                                 fixpoint (enfvio_or mf1 mf2 v) es
                               else
                                 fixpoint (enfvio_or mf2 mf1 v) es
    | MImp (L, mf1, mf2, _) -> fixpoint (enfvio_imp mf1 mf2 v) es
    | MImp (R, mf1, mf2, _) -> fixpoint (enfvio_imp mf2 mf1 v) es
    | MImp (LR, mf1, mf2, _) -> if MFormula.rank mf1 < MFormula.rank mf2 then
                                  fixpoint (enfvio_imp mf1 mf2 v) es
                                else
                                  fixpoint (enfvio_imp mf2 mf1 v) es
    | MIff (L, _, mf1, mf2, _) -> fixpoint (enfvio_imp mf1 mf2 v) es
    | MIff (R, _, mf1, mf2, _) -> fixpoint (enfvio_imp mf2 mf1 v) es
    | MExists (x, tt, mf) -> fixpoint (enfvio_exists x mf v) es
    | MForall (x, tt, mf) -> enfvio mf (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
    | MNext (i, mf, b, ti) -> add_foblig (FInterval (es.ts, i, mf), v, NEG) es
    | MEventually (i, mf, bi, ei) -> enfvio_eventually i mf ei v es
    | MAlways (i, mf, bi, ai) ->
       let (a, b) = Interval.boundaries i in
       if Int.equal a 0 && Int.equal b 0 then
         enfvio mf v es
       else
         add_foblig (FAlways (es.ts, i, mf, ai), v, NEG) es
    | MSince (L, _, mf1, _, _, _) -> enfvio mf1 v es
    | MSince (R, i, mf1, mf2, _, _) ->
       let f' = MNeg (MAnd (R, mf1, mf, empty_binop_info)) in
       fixpoint (enfsat_and f' (MNeg mf2) v) es
    | MSince (LR, i, mf1, mf2, _, _) -> if MFormula.rank mf1 < MFormula.rank mf2 then
                                          enfvio mf1 v es
                                        else
                                          let f' = MNeg (MAnd (LR, mf1, mf, empty_binop_info)) in
                                          fixpoint (enfsat_and f' (MNeg mf2) v) es
    | MUntil (L, _, mf1, _, _, _) -> enfvio mf1 v es
    | MUntil (R, i, mf1, mf2, bi, ui) -> fixpoint (enfvio_until i mf1 mf2 ui v) es
    | MUntil (LR, i, mf1, mf2, bi, ui) -> if MFormula.rank mf1 < MFormula.rank mf2 then
                                            enfvio mf1 v es
                                          else
                                            fixpoint (enfvio_until i mf1 mf2 ui v) es
    | _ -> raise (Invalid_argument ("function enfvio is not defined for "
                                    ^ MFormula.op_to_string mf))

  let enf mf es ts =
    enfsat mf (Map.empty (module String)) { es with r = Triple.empty; fobligs = [] }

end

let goal es ts tp =
  let obligs = List.map EState.(es.fobligs) (FObligation.eval ts tp) in
  match obligs with
  | [] -> MFormula.MTT
  | init::rest -> List.fold_left rest ~init ~f:(fun mf mg -> MAnd (LR, mf, mg, empty_binop_info))

let exec f inc =
  let rec step pb_opt es ts =
    match Other_parser.Trace.parse_from_channel inc pb_opt with
    | None -> ()
    | Some (more, pb) ->
       let mf = goal es ts es.EState.tp in
       let vars = Set.elements (MFormula.fv mf) in
       let es = { es with EState.ms = { es.EState.ms with ts_waiting = Queue.of_list [ts] } } in
       let es = EState.enf mf
                  (if Int.equal pb.ts ts then
                     EState.{ es with db = pb.db; tp = es.tp + 1; ts }
                   else
                     EState.{ es with db = Db.create []; tp = es.tp + 1; ts = ts + 1 })
                  es in
       let (tstp_expls, ms') = EState.mstep_state vars es in
       Out.Plain.expls tstp_expls None None None Out.Plain.ENFORCE;
       if more then step (Some(pb)) es ts in
  let tf = try Typing.do_type f with Invalid_argument s -> failwith s in
  let transparent =
    try Typing.is_transparent tf
    with Invalid_argument s -> print_endline s; false in
  let f = Tformula.to_formula tf in
  let mf = Monitor.MFormula.init f in
  let ms = Monitor.MState.init mf in
  step None (EState.init ms mf) 0

       (* (NOT REALLY) TODO: other execution mode with automatic timestamps *)

       (* TODO: additional proof rules;
           update state in *eval*, passing the es from the previous step;
           change to Pdt;
           correct the mistake with the ms called with the wrong mf in sat;
           add TP;
           update the loop;
           add one enforcement strategy *)
