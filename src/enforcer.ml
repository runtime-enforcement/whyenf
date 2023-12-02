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

type ts_to_formula = timestamp -> Formula.t

type polarity = POS | NEG

type commitments = (ts_to_formula * polarity) list

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

(* let enfsat (f: Formula.t) ts tp is_tp_last coms tsdbs = match f with *)
(*   | TT -> ([], [], []) *)
(*   | Predicate (r, trms) -> ([], [], []) *)
(*   | Neg f -> ([], [], []) *)
(*   | And (side, f1, f2) -> ([], [], []) *)
(*   | Or (side, f1, f2) -> ([], [], []) *)
(*   | Imp (side, f1, f2) -> ([], [], []) *)
(*   | Iff (side1, side2, f1, f2) -> ([], [], []) *)
(*   | Exists (x, f) -> ([], [], []) *)
(*   | Forall (x, f) -> ([], [], []) *)
(*   | Next (i, f) -> ([], [], []) *)
(*   | Once (i, f) -> ([], [], []) *)
(*   | Eventually (i, f) -> ([], [], []) *)
(*   | Historically (i, f) -> ([], [], []) *)
(*   | Always (i, f) -> ([], [], []) *)
(*   | Since (side, i, f1, f2) -> ([], [], []) *)
(*   | Until (side, i, f1, f2) -> ([], [], []) *)
(*   | _ -> raise (Invalid_argument ("function enfsat is not defined for " ^ Formula.op_to_string f)) *)


(* let enfvio (f: Formula.t) ts tp is_tp_last coms tsdbs = match f with *)
(*   | FF -> ([], [], []) *)
(*   | Predicate (r, trms) -> ([], [], []) *)
(*   | Neg f -> ([], [], []) *)
(*   | And (side, f1, f2) -> ([], [], []) *)
(*   | Or (side, f1, f2) -> ([], [], []) *)
(*   | Imp (side, f1, f2) -> ([], [], []) *)
(*   | Iff (side1, side2, f1, f2) -> ([], [], []) *)
(*   | Exists (x, f) -> ([], [], []) *)
(*   | Forall (x, f) -> ([], [], []) *)
(*   | Next (i, f) -> ([], [], []) *)
(*   | Once (i, f) -> ([], [], []) *)
(*   | Eventually (i, f) -> ([], [], []) *)
(*   | Historically (i, f) -> ([], [], []) *)
(*   | Always (i, f) -> ([], [], []) *)
(*   | Since (side, i, f1, f2) -> ([], [], []) *)
(*   | Until (side, i, f1, f2) -> ([], [], []) *)
(*   | _ -> raise (Invalid_argument ("function enfvio is not defined for " ^ Formula.op_to_string f)) *)

(* let enf ts tp is_tp_last coms tsdbs = *)

(* let estep vars ts db (es: EState.t) = *)
(*   let (expls, mf') = enf vars ts es.tp_cur db es.mf in *)
(*   Queue.enqueue es.ts_waiting ts; *)
(*   let tstps = List.zip_exn (List.take (Queue.to_list es.ts_waiting) (List.length expls)) *)
(*                 (List.range es.tp_cur (es.tp_cur + List.length expls)) in *)
(*   Queue.enqueue es.tsdbs (ts, db); *)
(*   (List.zip_exn tstps expls, *)
(*    { es with *)
(*      mf = mf' *)
(*    ; tp_cur = es.tp_cur + 1 *)
(*    ; ts_waiting = queue_drop es.ts_waiting (List.length expls) }) *)

let exec measure f inc =
  (* let rec step pb_opt ms = *)
  (*   let (more, pb) = Other_parser.Trace.parse_from_channel inc pb_opt in *)
  (*   let (tstp_expls, ms') = estep (Set.elements (Formula.fv f)) pb.ts pb.db ms in *)
  (*   Out.Plain.expls pb.ts tstp_expls None None None Out.Plain.ENFORCE; *)
  (*   if more then step (Some(pb)) ms' in *)
  let f' = Typing.do_type f in
  ()
