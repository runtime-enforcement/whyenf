(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util
open Expl
open Interval

type input_type =
  | Event of event
  | Noise of string

type input_channel =
  | Input of in_channel
  | InputMock of input_type list

type output_type =
  | Explanation of (timestamp * timepoint) * expl
  | Boolean of (timestamp * timepoint) * bool
  | Info of string

type output_channel =
  | Output of out_channel
  | OutputDebug of timepoint * out_channel
  | OutputMock of output_type list

type channel =
  | IC of input_channel
  | OC of output_channel

exception End_of_mock of output_channel

val input_event: input_channel -> output_channel -> event * input_channel
val output_event: output_channel -> string -> output_channel
val output_debug: int -> output_channel -> (unit -> string) -> output_channel

val channel_to_string: channel -> string
val output_explanation: output_channel -> (timestamp * timepoint) * expl -> output_channel
val output_boolean: output_channel -> (timestamp * timepoint) * bool -> output_channel
val output_check: output_channel -> (timestamp * timepoint) * bool -> output_channel
val output_interval: output_channel -> interval -> output_channel
