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

let (@@) (sup1, cau1, coms1) (sup2, cau2, coms2) =
  (sup1 @ sup2, cau1 @ cau2, coms1 @ coms2)

let empty3 = ([], [], [])

let fixpoint fn fobligs tsdbs =
  let (ts, db) = Queue.dequeue_exn tsdbs in
  let sup = ref [] in
  let cau = ref [] in
  let fobligs = ref fobligs in
  let stop = ref false in
  (while not !stop do
     let db' = List.fold !cau ~init:(Set.filter db ~f:(fun evt -> List.mem !sup evt ~equal:Db.Event.equal))
                 ~f:(fun db evt -> Set.add db evt) in
     Queue.enqueue tsdbs (ts, db');
     let (sup', cau', coms') = fn !fobligs tsdbs in
     if not (List.is_empty sup' && List.is_empty cau' && List.is_empty coms') then
       (sup := !sup @ sup';
        cau := !cau @ cau';
        fobligs := !fobligs @ coms')
     else stop := true;
   done);
  (!sup, !cau, !fobligs)

let sat v f fobligs tsdbs = true

let vio v f fobligs tsdbs =
  sat v (Tformula.neg f Pred.EnfType.Cau) fobligs tsdbs

let all_not_sat v x f fobligs tsdbs = []
let all_not_vio v x f fobligs tsdbs = []

let update_tsdbs tsdbs sup cau = assert false

let lr test1 test2 enf1 enf2 f1 f2 ts tp v fobligs tsdbs =
  let (sup, cau, com) =
    if not (test1 v f1 fobligs tsdbs) then
      enf1 f1 ts tp v fobligs tsdbs
    else
      empty3 in
  let tsdbs' = update_tsdbs tsdbs sup cau in
  let fobligs' = fobligs @ com in
  let (sup', cau', com') =
    if not (test2 v f2 fobligs' tsdbs') then
      enf2 f2 ts tp v fobligs' tsdbs'
    else
      empty3 in
  (sup, cau, com) @@ (sup', cau', com')

let rec enfsat_and f1 = 
  lr sat sat enfsat enfsat f1

and enfsat_forall x f ts tp v fobligs tsdbs =
  let enfs d = enfsat f ts tp (Base.Map.update v x ~f:(fun _ -> d)) fobligs tsdbs in
  List.fold_left (List.map (all_not_sat v x f fobligs tsdbs) ~f:enfs) ~init:empty3 ~f:(@@)

and enfvio_or f1 = 
  lr vio vio enfvio enfvio f1

and enfvio_imp f1 = 
  lr sat vio enfsat enfvio f1

and enfvio_exists x f ts tp v fobligs tsdbs =
  let aux d (fobligs, tsdbs, r) =
    let (sup, cau, com) = enfvio f ts tp (Base.Map.update v x ~f:(fun _ -> d)) fobligs tsdbs in
    let tsdbs' = update_tsdbs tsdbs sup cau in
    let fobligs' = fobligs @ com in
    (fobligs', tsdbs', r @@ (sup, cau, com)) in
  let (_, _, com) =
    List.fold_right (all_not_vio v x f fobligs tsdbs) ~init:(fobligs, tsdbs, empty3) ~f:aux in
  com

and enfvio_until i f1 =
  let test1 = if Interval.mem 0 i then vio else (fun _ _ _ _ -> true) in
  let enf2  = fun f2 ts _ v _ _ -> ([], [], [(FUntil (ts, LR, i, f1, f2), v, NEG)]) in
  lr test1 sat enfvio enf2 f1

and enfvio_eventually f ts tp v fobligs tsdbs =
  empty3

and enfsat (f: Tformula.t) ts tp v fobligs tsdbs = match f.f with
  | TTT -> empty3
  | TPredicate (r, trms) ->
     ([], [(r, List.map trms (fun trm -> match trm with
                                         | Var x -> Map.find_exn v x
                                         | Const c -> c))], [])
  | TNeg f -> enfvio f ts tp v fobligs tsdbs
  | TAnd (L, f1, f2) -> fixpoint (enfsat_and f1 f2 ts tp v) fobligs tsdbs
  | TAnd (R, f1, f2) -> fixpoint (enfsat_and f2 f1 ts tp v) fobligs tsdbs
  | TAnd (LR, f1, f2) -> if Tformula.rank f1 < Tformula.rank f2 then
                           fixpoint (enfsat_and f1 f2 ts tp v) fobligs tsdbs
                         else
                           fixpoint (enfsat_and f2 f1 ts tp v) fobligs tsdbs
  | TOr (L, f1, f2) -> enfsat f1 ts tp v fobligs tsdbs
  | TOr (R, f1, f2) -> enfsat f2 ts tp v fobligs tsdbs
  | TImp (L, f1, f2) -> enfvio f1 ts tp v fobligs tsdbs
  | TImp (R, f1, f2) -> enfsat f2 ts tp v fobligs tsdbs
  | TIff (side1, side2, f1, f2) ->
     fixpoint (enfsat_and
                 { f = Tformula.TImp (side1, f1, f2); enftype = Pred.EnfType.Cau }
                 { f = Tformula.TImp (side1, f2, f1); enftype = Pred.EnfType.Cau }
                 ts tp v) fobligs tsdbs
  | TExists (x, tt, f) -> enfsat f ts tp (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) fobligs tsdbs
  | TForall (x, tt, f) -> fixpoint (enfsat_forall x f ts tp v) fobligs tsdbs
  | TNext (i, f) -> ([], [], [(FFormula f, v, POS)])
  | TEventually (i, f) ->
     let (a, b) = Interval.boundaries i in
     if Int.equal a 0 && Int.equal b 0 then
       enfsat f ts tp v fobligs tsdbs
     else
       ([], [], [(FEventually (ts, i, f), v, POS)]) 
  | TAlways (i, f) -> (enfsat f ts tp v fobligs tsdbs) @@ ([], [], [(FAlways (ts, i, f), v, POS)])
  | TSince (_, _, f1, f2) -> enfsat f2 ts tp v fobligs tsdbs
  | TUntil (side, i, f1, f2) ->
     let (a, b) = Interval.boundaries i in
     if Int.equal a 0 && Int.equal b 0 then
       enfsat f2 ts tp v fobligs tsdbs
     else
       (enfsat f1 ts tp v fobligs tsdbs) @@ ([], [], [(FUntil (ts, side, i, f1, f2), v, POS)])
  | _ -> raise (Invalid_argument ("function enfsat is not defined for " ^ Tformula.op_to_string f))
and enfvio (f: Tformula.t) ts tp v fobligs tsdbs = match f.f with
  | TFF -> empty3
  | TPredicate (r, trms) ->
     ([(r, List.map trms (fun trm -> match trm with
                                     | Var x -> Map.find_exn v x
                                     | Const c -> c))], [], [])
  | TNeg f -> enfsat f ts tp v fobligs tsdbs
  | TAnd (L, f1, _) -> enfvio f1 ts tp v fobligs tsdbs
  | TAnd (R, _, f2) -> enfvio f2 ts tp v fobligs tsdbs
  | TAnd (LR, f1, f2) -> if Tformula.rank f1 < Tformula.rank f2 then
                           enfvio f1 ts tp v fobligs tsdbs
                         else
                           enfvio f2 ts tp v fobligs tsdbs
  | TOr (L, f1, f2) -> fixpoint (enfvio_or f1 f2 ts tp v) fobligs tsdbs
  | TOr (R, f1, f2) -> fixpoint (enfvio_or f2 f1 ts tp v) fobligs tsdbs
  | TOr (LR, f1, f2) -> if Tformula.rank f1 < Tformula.rank f2 then
                          fixpoint (enfvio_or f1 f2 ts tp v) fobligs tsdbs
                        else
                          fixpoint (enfvio_or f2 f1 ts tp v) fobligs tsdbs
  | TImp (L, f1, f2) -> fixpoint (enfvio_imp f1 f2 ts tp v) fobligs tsdbs
  | TImp (R, f1, f2) -> fixpoint (enfvio_imp f2 f1 ts tp v) fobligs tsdbs
  | TImp (LR, f1, f2) -> if Tformula.rank f1 < Tformula.rank f2 then
                           fixpoint (enfvio_imp f1 f2 ts tp v) fobligs tsdbs
                         else
                           fixpoint (enfvio_imp f2 f1 ts tp v) fobligs tsdbs
  | TIff (L, _, f1, f2) -> fixpoint (enfvio_imp f1 f2 ts tp v) fobligs tsdbs
  | TIff (R, _, f1, f2) -> fixpoint (enfvio_imp f2 f1 ts tp v) fobligs tsdbs
  | TExists (x, tt, f) -> fixpoint (enfvio_exists x f ts tp v) fobligs tsdbs
  | TForall (x, tt, f) -> enfvio f ts tp (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) fobligs tsdbs
  | TNext (i, f) -> ([], [], [(FInterval (ts, i, f), v, NEG)])
  | TEventually (i, f) -> fixpoint (enfvio_eventually f ts tp v) fobligs tsdbs
  | TAlways (i, f) ->
     let (a, b) = Interval.boundaries i in
     if Int.equal a 0 && Int.equal b 0 then
       enfvio f ts tp v fobligs tsdbs
     else
       ([], [], [(FAlways (ts, i, f), v, NEG)]) 
  | TSince (L, _, f1, _) -> enfvio f1 ts tp v fobligs tsdbs
  | TSince (R, i, f1, f2) -> let f' = Tformula.neg (Tformula.conj R f1 f Cau) Pred.EnfType.Sup in
                             fixpoint (enfsat_and f' (Tformula.neg f2 Pred.EnfType.Sup) ts tp v) fobligs tsdbs
  | TSince (LR, i, f1, f2) -> if Tformula.rank f1 < Tformula.rank f2 then
                                enfvio f1 ts tp v fobligs tsdbs
                              else
                                let f' = Tformula.neg (Tformula.conj LR f1 f Cau) Pred.EnfType.Sup in
                                fixpoint (enfsat_and f' (Tformula.neg f2 Pred.EnfType.Cau) ts tp v) fobligs tsdbs
  | TUntil (L, _, f1, _) -> enfvio f1 ts tp v fobligs tsdbs
  | TUntil (R, i, f1, f2) -> fixpoint (enfvio_until i f1 f2 ts tp v) fobligs tsdbs
  | TUntil (LR, i, f1, f2) -> if Tformula.rank f1 < Tformula.rank f2 then
                                enfvio f1 ts tp v fobligs tsdbs
                              else
                                fixpoint (enfvio_until i f1 f2 ts tp v) fobligs tsdbs
  | _ -> raise (Invalid_argument ("function enfvio is not defined for " ^ Tformula.op_to_string f))

let enf ts tp fobligs tsdbs =
  let obligs = List.map fobligs (Fobligation.eval ts) in
  let f = match obligs with
    | [] -> Tformula.ttrue
    | init::t -> List.fold_left t ~init ~f:(fun f g -> Tformula.conj LR f g Cau) in
  enfsat f ts tp (Map.empty (module String)) [] tsdbs

let estep vars ts db (ms: MState.t) fobligs =
  let (cau, sup, fobligs) = enf ts (MState.tp_cur ms) fobligs (MState.tsdbs ms) in
  let db = List.fold sup ~init:db ~f:(fun db' ev_sup ->
               Set.filter db' ~f:(fun ev -> Db.Event.equal ev ev_sup)) in
  let db = List.fold cau ~init:db ~f:(fun db' ev -> Set.add db' ev) in
  let (tstp_expls, ms') = Monitor.mstep Out.Plain.ENFORCE vars ts db ms in
  (cau, sup, fobligs, (tstp_expls, ms'))

let exec measure f inc =
  let vars = Set.elements (Formula.fv f) in
  let rec step pb_opt fobligs ms =
    match Other_parser.Trace.parse_from_channel inc pb_opt with
    | None -> ()
    | Some (more, pb) ->
       let (cau, sup, coms', (tstp_expls, ms')) = estep vars pb.ts pb.db ms [] in
       Out.Plain.enf_expls pb.ts (MState.tp_cur ms) (List.map tstp_expls ~f:snd) cau sup (coms' @ fobligs);
       if more then step (Some(pb)) fobligs ms' in
  let tf = try Typing.do_type f with Invalid_argument s -> failwith s in
  let mf = Monitor.MFormula.init f in
  let ms = Monitor.MState.init mf in
  step None [(FFormula tf, Map.empty (module String), POS)] ms

