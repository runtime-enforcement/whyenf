open Base

module Dom = MFOTL_lib.Dom

module StringVar : MFOTL_lib.Modules.V with type t = string

include module type of MFOTL_lib.MFOTL.Make(Term.TrivialInfo)(StringVar)(Dom)(Term)

val init: Sformula.t -> t

val check_agg : Ctxt.t -> string -> MFOTL_lib.Aggregation.op -> Term.t -> string list -> typed_t -> Ctxt.t * Dom.tt
val check_top : Ctxt.t -> string list -> string -> Term.t list -> string list -> typed_t -> Ctxt.t * Dom.tt list
