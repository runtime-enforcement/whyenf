(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl
open Util
open Expl
open Checker_interface
open Checker.Explanator2

type output =
  | Explanation of (timestamp * timepoint) * expl * bool option
  | ExplanationJSON of (timestamp * timepoint) * timepoint list * expl * bool option
  | ExplanationDebug of (timestamp * timepoint) * expl * bool * checker_proof * trace_t
  | Info of string

val input_event: in_channel -> out_channel -> event * in_channel
val output_event: out_channel -> string -> unit
val output_preamble: out_channel -> mode -> out_mode -> formula -> unit
val output_closing: out_channel -> out_mode -> unit
val print_ps: out_channel -> mode -> out_mode -> timestamp -> timepoint -> expl list -> timepoint list -> (bool * checker_proof * trace_t) list option -> bool -> unit
