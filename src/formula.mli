open Base

module MyTerm = Term
open MFOTL_lib
module Ctxt : module type of Ctxt.Make(Dom)
module Term = MyTerm

module StringVar : Modules.V with type t = string

include module type of MFOTL.Make(Term.TrivialInfo)(StringVar)(Dom)(Term)

val init: Sformula.t -> t

val check_agg : Ctxt.t -> string -> Aggregation.op -> Term.t -> string list -> t -> Ctxt.t * Dom.tt
val check_top : Ctxt.t -> string list -> string -> Term.t list -> string list -> t -> Ctxt.t * Dom.tt list

val print_statistics : t -> unit
