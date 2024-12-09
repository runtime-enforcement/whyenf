(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

module StringVar : MFOTL_Base.V with type t = string

include module type of MFOTL.Make(Term.TrivialInfo)(StringVar)(Dom)(Term)

val init: Sformula.t -> t

val check_agg : Ctxt.t -> string -> Aggregation.op -> Term.t -> string list -> typed_t -> Ctxt.t * Dom.tt
val check_top : Ctxt.t -> string list -> string -> Term.t list -> string list -> typed_t -> Ctxt.t * Dom.tt list
