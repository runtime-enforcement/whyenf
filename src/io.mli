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
  | Boolean of (timestamp * timepoint) * bool
  | BooleanCheck of (timestamp * timepoint) * bool * bool
  | Explanation of (timestamp * timepoint) * expl
  | ExplanationCheck of (timestamp * timepoint)  * expl * bool
  | ExplanationDebug of (timestamp * timepoint)  * expl * bool * checker_proof * checker_trace
  | Info of string

val input_event: in_channel -> out_channel -> event * in_channel
val output_event: out_channel -> string -> unit
val preamble: out_channel -> mode -> formula -> unit
val print_ps: out_channel -> mode -> timestamp -> timepoint -> expl list -> (bool * checker_proof * checker_trace) list option -> bool -> unit
