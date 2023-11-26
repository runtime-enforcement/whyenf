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

module EState = struct

  type t = { mf: MFormula.t
           ; tp_cur: timepoint
           ; tp_out: timepoint
           ; ts_waiting: timestamp Queue.t }

  let init mf = { mf = mf
                ; tp_cur = 0
                ; tp_out = -1
                ; ts_waiting = Queue.create () }

  let to_string { mf
                ; tp_cur
                ; tp_out
                ; ts_waiting } =
    "\nEState: \n\n" ^
      Printf.sprintf "mf = %s\n" (MFormula.to_string mf) ^
        Printf.sprintf "tp_cur = %d\n" tp_cur ^
          Printf.sprintf "tp_out = %d\n" tp_out ^
            "\nts_waiting = [" ^ (String.concat ~sep:", "
                                    (Queue.to_list (Queue.map ts_waiting ~f:Int.to_string))) ^ "]\n"

end

type ts_to_formula = timestamp -> Formula.t

type polarity = POS | NEG

type future_obligations = ts_to_formula * polarity

(* let eeval = () *)

(* let estep vars ts db (es: EState.t) = *)
(*   let (expls, mf') = eeval vars ts es.tp_cur db es.mf in *)
(*   Queue.enqueue es.ts_waiting ts; *)
(*   let tstps = List.zip_exn (List.take (Queue.to_list es.ts_waiting) (List.length expls)) *)
(*                 (List.range es.tp_cur (es.tp_cur + List.length expls)) in *)
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
