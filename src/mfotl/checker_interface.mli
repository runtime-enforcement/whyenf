(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Etc
open Checker.MFOTL_Explanator2

module Checker_trace : sig

  type t = ((string * event_data list) set * nat) list

  val to_string: t -> string

end

module Checker_pdt : sig

  type t = (event_data, (event_data sproof, event_data vproof) sum) pdt

  val to_string: string -> t -> string

end

val check: (timestamp * (string * Domain.t list, 'a) Base.Set.t) list -> Formula.t -> Expl.Proof.t Expl.Pdt.t list ->
           (bool * (event_data, (event_data sproof, event_data vproof) sum) pdt * Checker_trace.t) list

val false_paths: (timestamp * (string * Domain.t list, 'a) Base.Set.t) list -> Formula.t -> Expl.Proof.t Expl.Pdt.t list ->
                 (Domain.t, Domain.comparator_witness) Setc.t list list option list
