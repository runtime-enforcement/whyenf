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

type take_formula = timestamp -> Formula.t
type valuation = (string, Dom.t, String.comparator_witness) Map.t
type polarity = POS | NEG
type commitments = (take_formula * valuation * polarity) list

module EState = struct

  type t = { mf: MFormula.t
           ; tp_cur: timepoint
           ; tp_out: timepoint
           ; ts_waiting: timestamp Queue.t
           ; tsdbs: (timestamp * Db.t) Queue.t
           ; commitments: commitments }

  let init mf = { mf = mf
                ; tp_cur = 0
                ; tp_out = -1
                ; ts_waiting = Queue.create ()
                ; tsdbs = Queue.create ()
                ; commitments = [] }

  let to_string { mf
                ; tp_cur
                ; tp_out
                ; ts_waiting
                ; tsdbs
                ; commitments } =
    "\nEState: \n\n" ^
      Printf.sprintf "mf = %s\n" (MFormula.to_string mf) ^
        Printf.sprintf "tp_cur = %d\n" tp_cur ^
          Printf.sprintf "tp_out = %d\n" tp_out ^
            "\nts_waiting = [" ^ (String.concat ~sep:", "
                                    (Queue.to_list (Queue.map ts_waiting ~f:Int.to_string))) ^ "]\n" ^
              "\ntsdbs = [" ^ (String.concat ~sep:", "
                                 (Queue.to_list (Queue.map tsdbs ~f:(fun (ts, db) ->
                                                     Printf.sprintf "(%d):\n %s\n" ts (Db.to_string db))))) ^ "]\n"

end


(* module AD = struct *)

(*   type t = (Dom.t, Dom.comparator_witness) Set.t *)

(*   let init () = Set.empty (module Dom) *)

(*   let add ds ad = *)
(*     List.fold ds ~init:ad ~f:(fun ad trm -> Set.add ad trm) *)

(*   let ds_not_in pred trms ad v = *)
(*     let int_not_in ad = *)
(*       let intw_opt = Set.find ad ~f:(fun d -> match d with *)
(*                                               | Dom.Int _ -> true *)
(*                                               | _ -> false) in *)
(*       match intw_opt with *)
(*       | None -> Dom.tt_default TInt *)
(*       | Some(Int(v)) -> (let v' = ref (v + 1) in *)
(*                          (while Set.mem ad (Int !v') do *)
(*                             v' := !v' + 1 *)
(*                           done); Int(!v')) *)
(*       | _ -> raise (Invalid_argument "expected an Int element") in *)
(*     let str_not_in ad = *)
(*       let strw_opt = Set.find ad ~f:(fun d -> match d with *)
(*                                               | Dom.Str _ -> true *)
(*                                               | _ -> false) in *)
(*       match strw_opt with *)
(*       | None -> Dom.tt_default TStr *)
(*       | Some(Str(v)) -> (let v' = ref (v ^ "a") in *)
(*                          (while Set.mem ad (Str !v') do *)
(*                             v' := !v' ^ "a" *)
(*                           done); Str(!v')) *)
(*       | _ -> raise (Invalid_argument "expected an Str element") in *)
(*     let float_not_in ad = *)
(*       let floatw_opt = Set.find ad ~f:(fun trm -> match trm with *)
(*                                                   | Dom.Float _ -> true *)
(*                                                   | _ -> false) in *)
(*       match floatw_opt with *)
(*       | None -> Dom.tt_default TFloat *)
(*       | Some(Float(v)) -> (let v' = ref (v +. 1.0) in *)
(*                            (while Set.mem ad (Float !v') do *)
(*                               v' := !v' +. 1.0 *)
(*                             done); Float(!v')) *)
(*       | _ -> raise (Invalid_argument "expected a Float element") in *)
(*     List.fold (List.zip_exn (Pred.Sig.tconsts pred) trms) ~init:(ad, []) *)
(*       ~f:(fun (ad, ds) (tt, trm) -> match trm with *)
(*                                     | Pred.Term.Const d -> (Set.add ad d, ds @ [d]) *)
(*                                     | Var x -> (match Map.find v x with *)
(*                                                 | None -> (match tt with *)
(*                                                            | TInt _ -> let d = int_not_in ad in *)
(*                                                                        (Set.add ad d, ds @ [d]) *)
(*                                                            | TStr _ -> let d = str_not_in ad in *)
(*                                                                        (Set.add ad d, ds @ [d]) *)
(*                                                            | TFloat _ -> let d = float_not_in ad in *)
(*                                                                          (Set.add ad d, ds @ [d])) *)
(*                                                 | Some z -> (Set.add ad z, ds @ [z]))) *)

(* end *)

let append (sup1, cau1, coms1) (sup2, cau2, coms2) =
  (sup1 @ sup2, cau1 @ cau2, coms1 @ coms2)

let fixpoint fn coms tsdbs =
  let (ts, db) = Queue.dequeue_exn tsdbs in
  let sup = ref [] in
  let cau = ref [] in
  let coms = ref coms in
  let stop = ref false in
  (while not !stop do
     let db' = List.fold !cau ~init:(Set.filter db ~f:(fun evt -> List.mem !sup evt ~equal:Db.Event.equal))
                 ~f:(fun db evt -> Set.add db evt) in
     Queue.enqueue tsdbs (ts, db');
     let (sup', cau', coms') = fn !coms tsdbs in
     if not (List.is_empty sup' && List.is_empty cau' && List.is_empty coms') then
       (sup := !sup @ sup';
        cau := !cau @ cau';
        coms := !coms @ coms')
     else stop := true;
   done);
  (!sup, !cau, !coms)

let sat f coms tsdbs = true

let enfsat_and f1 f2 is_tp_last v coms tsdbs =
  ([], [], [])

let enfsat_forall f is_tp_last v coms tsdbs =
  ([], [], [])

let enfvio_exists f is_tp_last v coms tsdbs =
  ([], [], [])

let enfvio_until f1 f2 is_tp_last v coms tsdbs =
  ([], [], [])

let rec enfsat (f: Formula.t) ts tp is_tp_last v coms tsdbs = match f with
  | TT -> ([], [], [])
  | Predicate (r, trms) ->
     ([], [(r, List.map trms (fun trm -> match trm with
                                         | Var x -> Map.find_exn v x
                                         | Const c -> c))], [])
  | Neg f -> enfvio f ts tp is_tp_last v coms tsdbs
  | And (_, f1, f2) -> fixpoint (enfsat_and f1 f2 is_tp_last v) coms tsdbs
  | Or (_, f1, f2) -> ([], [], [])
  | Imp (_, f1, f2) -> ([], [], [])
  | Iff (_, _, f1, f2) -> ([], [], [])
  | Exists (x, tt, f) -> enfsat f ts tp is_tp_last (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) coms tsdbs
  | Forall (x, tt, f) -> fixpoint (enfsat_forall f is_tp_last v) coms tsdbs
  | Next (i, f) -> ([], [], [((fun ts' -> f), v, POS)])
  | Once (i, f) -> ([], [], [])
  | Eventually (i, f) -> ([], [], [])
  | Historically (i, f) -> ([], [], [])
  | Always (i, f) -> ([], [], [])
  | Since (_, _, f1, f2) -> enfsat f2 ts tp is_tp_last v coms tsdbs
  | Until (side, i, f1, f2) ->
     let (a, b) = Interval.boundaries i in
     if Int.equal a 0 && Int.equal b 0 then
       enfsat f2 ts tp is_tp_last v coms tsdbs
     else
       let fn = fun ts' -> Formula.until side (Interval.sub i (ts' - ts)) f1 f2 in
       append (enfsat f1 ts tp is_tp_last v coms tsdbs) ([], [], [(fn, v, POS)])
  | _ -> raise (Invalid_argument ("function enfsat is not defined for " ^ Formula.op_to_string f))
and enfvio (f: Formula.t) ts tp is_tp_last v coms tsdbs = match f with
  | FF -> ([], [], [])
  | Predicate (r, trms) ->
     ([(r, List.map trms (fun trm -> match trm with
                                     | Var x -> Map.find_exn v x
                                     | Const c -> c))], [], [])
  | Neg f -> enfsat f ts tp is_tp_last v coms tsdbs
  | And (L, f1, _) -> enfvio f1 ts tp is_tp_last v coms tsdbs
  | And (R, _, f2) -> enfvio f2 ts tp is_tp_last v coms tsdbs
  | And (LR, f1, f2) -> if Formula.rank f1 < Formula.rank f2 then
                          enfvio f1 ts tp is_tp_last v coms tsdbs
                        else enfvio f2 ts tp is_tp_last v coms tsdbs
  | Or (_, f1, f2) -> ([], [], [])
  | Imp (_, f1, f2) -> ([], [], [])
  | Iff (_, _, f1, f2) -> ([], [], [])
  | Exists (x, tt, f) -> fixpoint (enfvio_exists f is_tp_last v) coms tsdbs
  | Forall (x, tt, f) -> enfvio f ts tp is_tp_last (Map.add_exn v ~key:x ~data:(Dom.tt_default tt)) coms tsdbs
  | Next (i, f) -> let fn = fun ts' -> if Interval.mem (ts' - ts) i then f else TT in
                   ([], [], [(fn, v, NEG)])
  | Once (i, f) -> ([], [], [])
  | Eventually (i, f) -> ([], [], [])
  | Historically (i, f) -> ([], [], [])
  | Always (i, f) -> ([], [], [])
  | Since (L, _, f1, _) -> enfvio f1 ts tp is_tp_last v coms tsdbs
  | Since (R, i, f1, f2) -> let f' = Formula.neg (Formula.conj LR f1 (Formula.since R i f1 f2)) in
                            fixpoint (enfsat_and f' (Formula.neg f2) is_tp_last v) coms tsdbs
  | Since (LR, i, f1, f2) -> if Formula.rank f1 < Formula.rank f2 then
                               enfvio f1 ts tp is_tp_last v coms tsdbs
                             else (let f' = Formula.neg (Formula.conj LR f1 (Formula.since R i f1 f2)) in
                                   fixpoint (enfsat_and f' (Formula.neg f2) is_tp_last v) coms tsdbs)
  | Until (L, _, f1, _) -> enfvio f1 ts tp is_tp_last v coms tsdbs
  | Until (R, _, f1, f2) -> fixpoint (enfvio_until f1 f2 is_tp_last v) coms tsdbs
  | Until (LR, _, f1, f2) -> if Formula.rank f1 < Formula.rank f2 then
                               enfvio f1 ts tp is_tp_last v coms tsdbs
                             else fixpoint (enfvio_until f1 f2 is_tp_last v) coms tsdbs
  | _ -> raise (Invalid_argument ("function enfvio is not defined for " ^ Formula.op_to_string f))

let enf ts tp is_tp_last coms tsdbs =
  let f = Formula.TT in
  enfsat f ts tp is_tp_last (Map.empty (module String)) [] tsdbs

(* let estep ts db (es: EState.t) = *)
(*   Queue.enqueue es.tsdbs (ts, db); *)
(*   let (cau, sup, coms) = enf ts es.tp_cur true es.commitments es.tsdbs in *)
(*   Queue.enqueue es.ts_waiting ts; *)
(*   let tstps = List.zip_exn (List.take (Queue.to_list es.ts_waiting) (List.length expls)) *)
(*                 (List.range es.tp_cur (es.tp_cur + List.length expls)) in *)
(*   (List.zip_exn tstps expls, *)
(*    { es with *)
(*      mf = mf' *)
(*    ; tp_cur = es.tp_cur + 1 *)
(*    ; ts_waiting = queue_drop es.ts_waiting (List.length expls) }) *)

let exec measure f inc =
  (* let rec step pb_opt es = *)
  (*   let (more, pb) = Other_parser.Trace.parse_from_channel inc pb_opt in *)
  (*   let (tstp_expls, ms') = estep pb.ts pb.db es in *)
  (*   (\* Out.Plain.expls pb.ts tstp_expls None None None Out.Plain.ENFORCE; *\) *)
  (*   if more then step (Some(pb)) ms' in *)
  let f' = Typing.do_type f in
  ()
