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
open Checker.Whymon

module Checker_trace : sig

  type t = ((string * event_data list) set * nat) list

  val to_string: t -> string

end

module type Checker_interfaceT = sig

  module Expl : sig

    module Proof: Expl.ProofT
    type t = Proof.t Expl.Pdt.t

    val is_violated: t -> bool
    val is_satisfied: t -> bool
    val at: t -> int

    val to_string: t -> string
    val to_latex: Formula.t -> t -> string
    val to_light_string: t -> string

  end

  module Vis : sig

    val to_json: Formula.t -> Expl.t -> string

  end

  module Checker_pdt : sig

    type t = (event_data, (event_data sproof, event_data vproof) sum) pdt

    val to_string: string -> t -> string

  end

  val check: (timestamp * (string * Dom.t list, 'a) Base.Set.t) list -> Formula.t -> Expl.t list ->
             (bool * (event_data, (event_data sproof, event_data vproof) sum) pdt * Checker_trace.t) list

  val false_paths: (timestamp * (string * Dom.t list, 'a) Base.Set.t) list -> Formula.t -> Expl.t list ->
                   (Dom.t, Dom.comparator_witness) Setc.t list list option list

end

module Checker_interface : Checker_interfaceT
module LightChecker_interface : Checker_interfaceT
