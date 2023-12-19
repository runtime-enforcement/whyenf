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

let append (sup1, cau1, coms1) (sup2, cau2, coms2) =
  (sup1 @ sup2, cau1 @ cau2, coms1 @ coms2)

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

let sat f fobligs tsdbs = true

let enfsat_and f1 f2 v fobligs tsdbs =
  ([], [], [])

let enfsat_forall f v fobligs tsdbs =
  ([], [], [])

let enfvio_exists f v fobligs tsdbs =
  ([], [], [])

let enfvio_until f1 f2 v fobligs tsdbs =
  ([], [], [])

let rec enfsat (f: Formula.t) ts tp v fobligs tsdbs = match f with
  | TT -> ([], [], [])
  | Predicate (r, trms) ->
     ([], [(r, List.map trms (fun trm -> match trm with
                                         | Var x -> Map.find_exn v x
                                         | Const c -> c))], [])
  | Neg f -> enfvio f ts tp v fobligs tsdbs
  | And (_, f1, f2) -> fixpoint (enfsat_and f1 f2 v) fobligs tsdbs
  | Or (_, f1, f2) -> ([], [], [])
  | Imp (_, f1, f2) -> ([], [], [])
  | Iff (_, _, f1, f2) -> ([], [], [])
  | Exists (x, tt, f) -> enfsat f ts tp (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) fobligs tsdbs
  | Forall (x, tt, f) -> fixpoint (enfsat_forall f v) fobligs tsdbs
  | Next (i, f) -> ([], [], [(NextCau, (fun ts' -> f), v, POS)])
  | Once (i, f) -> ([], [], [])
  | Eventually (i, f) -> ([], [], [])
  | Historically (i, f) -> ([], [], [])
  | Always (i, f) -> ([], [], [])
  | Since (_, _, f1, f2) -> enfsat f2 ts tp v fobligs tsdbs
  | Until (side, i, f1, f2) ->
     let (a, b) = Interval.boundaries i in
     if Int.equal a 0 && Int.equal b 0 then
       enfsat f2 ts tp v fobligs tsdbs
     else
       let fn = fun ts' -> Formula.until side (Interval.sub i (ts' - ts)) f1 f2 in
       append (enfsat f1 ts tp v fobligs tsdbs) ([], [], [(UntilCau, fn, v, POS)])
  | _ -> raise (Invalid_argument ("function enfsat is not defined for " ^ Formula.op_to_string f))
and enfvio (f: Formula.t) ts tp v fobligs tsdbs = match f with
  | FF -> ([], [], [])
  | Predicate (r, trms) ->
     ([(r, List.map trms (fun trm -> match trm with
                                     | Var x -> Map.find_exn v x
                                     | Const c -> c))], [], [])
  | Neg f -> enfsat f ts tp v fobligs tsdbs
  | And (L, f1, _) -> enfvio f1 ts tp v fobligs tsdbs
  | And (R, _, f2) -> enfvio f2 ts tp v fobligs tsdbs
  | And (LR, f1, f2) -> if Formula.rank f1 < Formula.rank f2 then
                          enfvio f1 ts tp v fobligs tsdbs
                        else enfvio f2 ts tp v fobligs tsdbs
  | Or (_, f1, f2) -> ([], [], [])
  | Imp (_, f1, f2) -> ([], [], [])
  | Iff (_, _, f1, f2) -> ([], [], [])
  | Exists (x, tt, f) -> fixpoint (enfvio_exists f v) fobligs tsdbs
  | Forall (x, tt, f) -> enfvio f ts tp (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) fobligs tsdbs
  | Next (i, f) -> let fn = fun ts' -> if Interval.mem (ts' - ts) i then f else TT in
                   ([], [], [(NextSup, fn, v, NEG)])
  | Once (i, f) -> ([], [], [])
  | Eventually (i, f) -> ([], [], [])
  | Historically (i, f) -> ([], [], [])
  | Always (i, f) -> ([], [], [])
  | Since (L, _, f1, _) -> enfvio f1 ts tp v fobligs tsdbs
  | Since (R, i, f1, f2) -> let f' = Formula.neg (Formula.conj LR f1 (Formula.since R i f1 f2)) in
                            fixpoint (enfsat_and f' (Formula.neg f2) v) fobligs tsdbs
  | Since (LR, i, f1, f2) -> if Formula.rank f1 < Formula.rank f2 then
                               enfvio f1 ts tp v fobligs tsdbs
                             else (let f' = Formula.neg (Formula.conj LR f1 (Formula.since R i f1 f2)) in
                                   fixpoint (enfsat_and f' (Formula.neg f2) v) fobligs tsdbs)
  | Until (L, _, f1, _) -> enfvio f1 ts tp v fobligs tsdbs
  | Until (R, _, f1, f2) -> fixpoint (enfvio_until f1 f2 v) fobligs tsdbs
  | Until (LR, _, f1, f2) -> if Formula.rank f1 < Formula.rank f2 then
                               enfvio f1 ts tp v fobligs tsdbs
                             else fixpoint (enfvio_until f1 f2 v) fobligs tsdbs
  | _ -> raise (Invalid_argument ("function enfvio is not defined for " ^ Formula.op_to_string f))

let enf ts tp fobligs tsdbs =
  (* let f = List.fold fobligs ~init:Formula.TT *)
  (*           ~f:(fun (_, fn, *)
  enfsat Formula.TT ts tp (Map.empty (module String)) [] tsdbs

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
  let _ = try Typing.do_type f with Invalid_argument s -> failwith s in
  let mf = Monitor.MFormula.init f in
  let ms = Monitor.MState.init mf in
  step None [(Other, (fun _ -> f), Map.empty (module String), POS)] ms
