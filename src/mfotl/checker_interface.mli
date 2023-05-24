(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
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

  type t = (string * event_data list) trace

end

module Checker_pdt : sig

  type t = (event_data, (event_data sproof, event_data vproof) sum) pdt

  val to_string: string -> (event_data, (event_data sproof, event_data vproof) sum) Checker.MFOTL_Explanator2.pdt -> string

end

val check: (timestamp * (string * Domain.t list, 'a) Base.Set.t) list -> Formula.t -> Expl.Proof.t Expl.pdt list ->
           (bool * (event_data, (event_data sproof, event_data vproof) sum) pdt * (string * event_data list) trace) list
