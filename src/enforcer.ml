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
    Set.equal sup1 sup2 && Set.equal cau1 cau2 && (fobligs1 == fobligs2)

  let sup (sup, _, _) = sup
  let cau (_, cau, _) = cau
  let fobligs (_, _, fobligs) = fobligs

  let empty = (Set.empty (module Db.Event), Set.empty (module Db.Event), [])
  let empty2 fobligs = (Set.empty (module Db.Event), Set.empty (module Db.Event), fobligs)

  let is_empty (sup, cau, fobligs) = Set.is_empty sup && Set.is_empty cau && fobligs == []

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

  let init ms mf = { ms; tp = 0; ts = 0; db = Db.create []; r = Triple.empty;
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

  let expl v f es = 
    let vars = Set.elements (MFormula.fv f) in
    let (tstp_expls, ms') = mstep_state vars es in
    match tstp_expls with
    | []   -> failwith ("Monitor did not return a verdict on " ^ (MFormula.to_string f))
    | ((ts, tp), _)::_ when (ts <> es.ts) || (tp <> es.tp) ->
       failwith ("Invalid tstp in proof: " ^ string_of_int ts ^ " <> " ^ string_of_int es.ts
                 ^ " or " ^ string_of_int tp ^ " <> " ^ string_of_int es.tp)
    | (_, p)::_ -> p
       
  let sat v f es =
    let p = expl v f es in
    Expl.Proof.isS (Expl.Pdt.specialize v p)

  let vio v f es =
    sat v (MNeg f) es

  let all_not_sat v x f es =
    let p = expl v f es in
    match Expl.Pdt.collect Expl.Proof.isV v x p with
    | Setc.Finite s -> Set.elements s
    | _ -> failwith ("Infinite set of candidates for " ^ x ^ " in " ^ (MFormula.to_string f))
  
  let all_not_vio v x f es =
    let p = expl v f es in
    match Expl.Pdt.collect Expl.Proof.isS v x p with
    | Setc.Finite s -> Set.elements s
    | _ -> failwith ("Infinite set of candidates for " ^ x ^ " in " ^ (MFormula.to_string f))

  let lr test1 test2 enf1 enf2 f1 f2 v es =
    let es =
      if not (test1 v f1 es) then
        enf1 f1 v es
      else
        es in
    if not (test2 v f2 es) then
      enf2 f2 v es
    else
      es

  let rec enfsat_and f1 = 
    lr sat sat enfsat enfsat f1

  and enfsat_forall x f v es =
    let enfs d = enfsat f (Base.Map.update v x ~f:(fun _ -> d)) es in
    List.fold_left (List.map (all_not_sat v x f es) ~f:enfs) ~init:es ~f:combine

  and enfvio_or f1 = 
    lr vio vio enfvio enfvio f1

  and enfvio_imp f1 = 
    lr sat vio enfsat enfvio f1

  and enfvio_exists x f v es =
    let enfs d = enfvio f (Base.Map.update v x ~f:(fun _ -> d)) es in
    List.fold_left (List.map (all_not_vio v x f es) ~f:enfs) ~init:es ~f:combine

  and enfvio_until i f1 f2 bi ui =
    let test1 = if Interval.mem 0 i then vio else (fun _ _ _ -> true) in
    let enf2 f2 v es = add_foblig (FUntil (es.ts, LR, i, f1, f2, bi, ui), v, NEG) es in
    lr test1 sat enfvio enf2 f1 f2 

  and enfvio_eventually i f bi ei v es =
    let test1 = if Interval.mem 0 i then vio else (fun _ _ _ -> true) in
    let es = add_foblig (FEventually (es.ts, i, f, bi, ei), v, NEG) es in
    enfvio f v es

  and enfsat (f: MFormula.t) v es = match f with
    | MTT -> es
    | MPredicate (r, trms) ->
       let new_cau = (r, List.map trms (fun trm -> match trm with
                                             | Var x -> Map.find_exn v x
                                             | Const c -> c)) in
       add_cau new_cau es
    | MNeg f -> enfvio f v es
    | MAnd (L, f1, f2, bi) -> fixpoint (enfsat_and f1 f2 v) es
    | MAnd (R, f1, f2, bi) -> fixpoint (enfsat_and f2 f1 v) es
    | MAnd (LR, f1, f2, bi) -> if MFormula.rank f1 < MFormula.rank f2 then
                                 fixpoint (enfsat_and f1 f2 v) es
                               else
                                 fixpoint (enfsat_and f2 f1 v) es
    | MOr (L, f1, f2, bi) -> enfsat f1 v es
    | MOr (R, f1, f2, bi) -> enfsat f2 v es
    | MImp (L, f1, f2, bi) -> enfvio f1 v es
    | MImp (R, f1, f2, bi) -> enfsat f2 v es
    | MIff (side1, side2, f1, f2, bi) ->
       fixpoint (enfsat_and
                   (MImp (side1, f1, f2, empty_binop_info))
                   (MImp (side1, f2, f1, empty_binop_info)) v) es
    | MExists (x, tt, f) -> enfsat f (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
    | MForall (x, tt, f) -> fixpoint (enfsat_forall x f v) es
    | MNext (i, f, bi, ni) -> add_foblig (FFormula f, v, POS) es
    | MEventually (i, f, bi, ei) ->
       let (a, b) = Interval.boundaries i in
       if Int.equal a 0 && Int.equal b 0 then
         enfsat f v es
       else
         add_foblig (FEventually (es.ts, i, f, bi, ei), v, POS) es 
    | MAlways (i, f, bi, ai) -> add_foblig (FAlways (es.ts, i, f, bi, ai), v, POS) (enfsat f v es)
    | MSince (_, _, f1, f2, bi, si) -> enfsat f2 v es
    | MUntil (side, i, f1, f2, bi, ui) ->
       let (a, b) = Interval.boundaries i in
       if Int.equal a 0 && Int.equal b 0 then
         enfsat f2 v es
       else
         add_foblig (FUntil (es.ts, side, i, f1, f2, bi, ui), v, POS) (enfsat f1 v es)
    | _ -> raise (Invalid_argument ("function enfsat is not defined for "
                                    ^ MFormula.op_to_string f))
  and enfvio (f: MFormula.t) v es = match f with
    | MFF -> es
    | MPredicate (r, trms) ->
       let new_sup = (r, List.map trms (fun trm -> match trm with
                                                   | Var x -> Map.find_exn v x
                                                   | Const c -> c)) in
       add_sup new_sup es
    | MNeg f -> enfsat f v es
    | MAnd (L, f1, _, bi) -> enfvio f1 v es
    | MAnd (R, _, f2, bi) -> enfvio f2 v es
    | MAnd (LR, f1, f2, bi) -> if MFormula.rank f1 < MFormula.rank f2 then
                                 enfvio f1 v es
                               else
                                 enfvio f2 v es
    | MOr (L, f1, f2, bi) -> fixpoint (enfvio_or f1 f2 v) es
    | MOr (R, f1, f2, bi) -> fixpoint (enfvio_or f2 f1 v) es
    | MOr (LR, f1, f2, bi) -> if MFormula.rank f1 < MFormula.rank f2 then
                                fixpoint (enfvio_or f1 f2 v) es
                              else
                            fixpoint (enfvio_or f2 f1 v) es
    | MImp (L, f1, f2, bi) -> fixpoint (enfvio_imp f1 f2 v) es
    | MImp (R, f1, f2, bi) -> fixpoint (enfvio_imp f2 f1 v) es
    | MImp (LR, f1, f2, bi) -> if MFormula.rank f1 < MFormula.rank f2 then
                                 fixpoint (enfvio_imp f1 f2 v) es
                               else
                                 fixpoint (enfvio_imp f2 f1 v) es
    | MIff (L, _, f1, f2, bi) -> fixpoint (enfvio_imp f1 f2 v) es
    | MIff (R, _, f1, f2, bi) -> fixpoint (enfvio_imp f2 f1 v) es
    | MExists (x, tt, f) -> fixpoint (enfvio_exists x f v) es
    | MForall (x, tt, f) -> enfvio f (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
    | MNext (i, f, b, ti) -> add_foblig (FInterval (es.ts, i, f), v, NEG) es
    | MEventually (i, f, bi, ei) -> enfvio_eventually i f bi ei v es
    | MAlways (i, f, bi, ai) ->
       let (a, b) = Interval.boundaries i in
       if Int.equal a 0 && Int.equal b 0 then
         enfvio f v es
       else
         add_foblig (FAlways (es.ts, i, f, bi, ai), v, NEG) es
    | MSince (L, _, f1, _, bi, si) -> enfvio f1 v es
    | MSince (R, i, f1, f2, bi, si) ->
       let f' = MNeg (MAnd (R, f1, f, empty_binop_info)) in
       fixpoint (enfsat_and f' (MNeg f2) v) es
    | MSince (LR, i, f1, f2, bi, si) -> if MFormula.rank f1 < MFormula.rank f2 then
                                          enfvio f1 v es
                                        else
                                          let f' = MNeg (MAnd (LR, f1, f, empty_binop_info)) in
                                          fixpoint (enfsat_and f' (MNeg f2) v) es
    | MUntil (L, _, f1, _, bi, ui) -> enfvio f1 v es
    | MUntil (R, i, f1, f2, bi, ui) -> fixpoint (enfvio_until i f1 f2 bi ui v) es
    | MUntil (LR, i, f1, f2, bi, ui) -> if MFormula.rank f1 < MFormula.rank f2 then
                                         enfvio f1 v es
                                       else
                                         fixpoint (enfvio_until i f1 f2 bi ui v) es
    | _ -> raise (Invalid_argument ("function enfvio is not defined for "
                                    ^ MFormula.op_to_string f))

  let enf f es ts =
    enfsat f (Map.empty (module String)) { es with r = Triple.empty; fobligs = [] }

end

let goal es ts =
  let obligs = List.map EState.(es.fobligs) (FObligation.eval ts) in
  match obligs with
  | [] -> MFormula.MTT
  | init::rest -> List.fold_left rest ~init ~f:(fun f g -> MAnd (LR, f, g, empty_binop_info))
  
let exec f inc =
  let rec step pb_opt es ts =
    match Other_parser.Trace.parse_from_channel inc pb_opt with
    | None -> ()
    | Some (more, pb) ->
         let f = goal es ts in
         let vars = Set.elements (MFormula.fv f) in
         let es = EState.enf f
                    (if pb.ts == ts then
                       EState.{ es with db = pb.db; tp = es.tp + 1; ts }
                     else
                       EState.{ es with db = Db.create []; tp = es.tp + 1; ts = ts + 1 })
                    es in
         let (tstp_expls, ms') = EState.mstep_state vars es in
         Out.Plain.expls tstp_expls None None None Out.Plain.ENFORCE;
         if more then step (Some(pb)) es ts in
  let tf = try Typing.do_type f with Invalid_argument s -> failwith s in
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
