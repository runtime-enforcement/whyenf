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
open Fobligation

module Triple = struct

  type t = Db.t * Db.t * Fobligation.t list

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
           ; fobligs: Fobligation.t list }

  let init ms tf = { ms; tp = 0; ts = 0; db = Db.create []; r = Triple.empty;
                     fobligs = [(FFormula tf, Base.Map.empty (module Base.String), POS)] }

  let update r es =
    { es with db      = Triple.update_db es.db r;
              fobligs = Triple.update_fobligs es.fobligs r;
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
      let es  = update r es in
      let es' = fn es in
      if not (Triple.equal es.r es'.r) then
        loop es.r es
      else
        es
    in loop Triple.empty es

  let sat v f es = true

  let vio v f es =
    sat v (Tformula.neg f Pred.EnfType.Cau) es

  let all_not_sat v x f es = []
  let all_not_vio v x f es = []

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

  and enfvio_until i f1 =
    let test1 = if Interval.mem 0 i then vio else (fun _ _ _ -> true) in
    let enf2 f2 v es = add_foblig (FUntil (es.ts, LR, i, f1, f2), v, NEG) es in
    lr test1 sat enfvio enf2 f1

  and enfvio_eventually f v es =
    assert false

  and enfsat (f: Tformula.t) v es = match f.f with
    | TTT -> es
    | TPredicate (r, trms) ->
       let new_cau = (r, List.map trms (fun trm -> match trm with
                                             | Var x -> Map.find_exn v x
                                             | Const c -> c)) in
       add_cau new_cau es
    | TNeg f -> enfvio f v es
    | TAnd (L, f1, f2) -> fixpoint (enfsat_and f1 f2 v) es
    | TAnd (R, f1, f2) -> fixpoint (enfsat_and f2 f1 v) es
    | TAnd (LR, f1, f2) -> if Tformula.rank f1 < Tformula.rank f2 then
                             fixpoint (enfsat_and f1 f2 v) es
                           else
                             fixpoint (enfsat_and f2 f1 v) es
    | TOr (L, f1, f2) -> enfsat f1 v es
    | TOr (R, f1, f2) -> enfsat f2 v es
    | TImp (L, f1, f2) -> enfvio f1 v es
    | TImp (R, f1, f2) -> enfsat f2 v es
    | TIff (side1, side2, f1, f2) ->
       fixpoint (enfsat_and
                   { f = Tformula.TImp (side1, f1, f2); enftype = Pred.EnfType.Cau }
                   { f = Tformula.TImp (side1, f2, f1); enftype = Pred.EnfType.Cau }
                   v) es
    | TExists (x, tt, f) -> enfsat f (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
    | TForall (x, tt, f) -> fixpoint (enfsat_forall x f v) es
    | TNext (i, f) -> add_foblig (FFormula f, v, POS) es
    | TEventually (i, f) ->
       let (a, b) = Interval.boundaries i in
       if Int.equal a 0 && Int.equal b 0 then
         enfsat f v es
       else
         add_foblig (FEventually (es.ts, i, f), v, POS) es 
    | TAlways (i, f) -> add_foblig (FAlways (es.ts, i, f), v, POS) (enfsat f v es)
    | TSince (_, _, f1, f2) -> enfsat f2 v es
    | TUntil (side, i, f1, f2) ->
       let (a, b) = Interval.boundaries i in
       if Int.equal a 0 && Int.equal b 0 then
         enfsat f2 v es
       else
         add_foblig (FUntil (es.ts, side, i, f1, f2), v, POS) (enfsat f1 v es)
    | _ -> raise (Invalid_argument ("function enfsat is not defined for "
                                    ^ Tformula.op_to_string f))
  and enfvio (f: Tformula.t) v es = match f.f with
    | TFF -> es
    | TPredicate (r, trms) ->
       let new_sup = (r, List.map trms (fun trm -> match trm with
                                                   | Var x -> Map.find_exn v x
                                                   | Const c -> c)) in
       add_sup new_sup es
    | TNeg f -> enfsat f v es
    | TAnd (L, f1, _) -> enfvio f1 v es
    | TAnd (R, _, f2) -> enfvio f2 v es
    | TAnd (LR, f1, f2) -> if Tformula.rank f1 < Tformula.rank f2 then
                             enfvio f1 v es
                           else
                             enfvio f2 v es
    | TOr (L, f1, f2) -> fixpoint (enfvio_or f1 f2 v) es
    | TOr (R, f1, f2) -> fixpoint (enfvio_or f2 f1 v) es
    | TOr (LR, f1, f2) -> if Tformula.rank f1 < Tformula.rank f2 then
                            fixpoint (enfvio_or f1 f2 v) es
                          else
                            fixpoint (enfvio_or f2 f1 v) es
    | TImp (L, f1, f2) -> fixpoint (enfvio_imp f1 f2 v) es
    | TImp (R, f1, f2) -> fixpoint (enfvio_imp f2 f1 v) es
    | TImp (LR, f1, f2) -> if Tformula.rank f1 < Tformula.rank f2 then
                             fixpoint (enfvio_imp f1 f2 v) es
                           else
                             fixpoint (enfvio_imp f2 f1 v) es
    | TIff (L, _, f1, f2) -> fixpoint (enfvio_imp f1 f2 v) es
    | TIff (R, _, f1, f2) -> fixpoint (enfvio_imp f2 f1 v) es
    | TExists (x, tt, f) -> fixpoint (enfvio_exists x f v) es
    | TForall (x, tt, f) -> enfvio f (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) es
    | TNext (i, f) -> add_foblig (FInterval (es.ts, i, f), v, NEG) es
    | TEventually (i, f) -> fixpoint (enfvio_eventually f v) es
    | TAlways (i, f) ->
       let (a, b) = Interval.boundaries i in
       if Int.equal a 0 && Int.equal b 0 then
         enfvio f v es
       else
         add_foblig (FAlways (es.ts, i, f), v, NEG) es
    | TSince (L, _, f1, _) -> enfvio f1 v es
    | TSince (R, i, f1, f2) -> let f' = Tformula.neg (Tformula.conj R f1 f Cau) Pred.EnfType.Sup in
                               fixpoint (enfsat_and f' (Tformula.neg f2 Pred.EnfType.Sup) v) es
    | TSince (LR, i, f1, f2) -> if Tformula.rank f1 < Tformula.rank f2 then
                                  enfvio f1 v es
                                else
                                  let f' = Tformula.neg (Tformula.conj LR f1 f Cau) Pred.EnfType.Sup in
                                  fixpoint (enfsat_and f' (Tformula.neg f2 Pred.EnfType.Cau) v) es
    | TUntil (L, _, f1, _) -> enfvio f1 v es
    | TUntil (R, i, f1, f2) -> fixpoint (enfvio_until i f1 f2 v) es
    | TUntil (LR, i, f1, f2) -> if Tformula.rank f1 < Tformula.rank f2 then
                                  enfvio f1 v es
                                else
                                  fixpoint (enfvio_until i f1 f2 v) es
    | _ -> raise (Invalid_argument ("function enfvio is not defined for " ^ Tformula.op_to_string f))

  let enf f es ts =
    enfsat f (Map.empty (module String)) { es with r = Triple.empty; fobligs = [] }

end

let goal es ts =
  let obligs = List.map EState.(es.fobligs) (Fobligation.eval ts) in
  match obligs with
  | [] -> Tformula.ttrue
  | init::rest -> List.fold_left rest ~init ~f:(fun f g -> Tformula.conj LR f g Cau)
  
let exec f inc =
  let rec step pb_opt es ts =
    match Other_parser.Trace.parse_from_channel inc pb_opt with
    | None -> ()
    | Some (more, pb) ->
         let f = goal es ts in
         let vars = Set.elements (Tformula.fv f) in
         let es = EState.enf f
                    (if pb.ts == ts then
                       EState.{ es with db = pb.db; tp = es.tp + 1; ts }
                     else
                       EState.{ es with db = Db.create []; tp = es.tp + 1; ts = ts + 1 })
                    es in
         let (tstp_expls, ms') = mstep Out.Plain.ENFORCE vars es.ts es.db es.ms in
         if more then step (Some(pb)) es ts in
  let tf = try Typing.do_type f with Invalid_argument s -> failwith s in
  let mf = Monitor.MFormula.init f in
  let ms = Monitor.MState.init mf in
  step None (EState.init ms tf) 0

       (* TODO: other execution mode with automatic timestamps *)
       (* TODO: sat, etc.; additional proof rules; reconstruct state *)
