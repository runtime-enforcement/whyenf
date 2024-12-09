open Base

module TypedVar : MFOTL_Base.V with type t = string * Dom.tt

include module type of MFOTL_Term.Make(TypedVar)(Dom)(Term.NoOp)(Term.NoOp)(Term.TrivialInfo)

val convert_var : Ctxt.t -> Term.v -> v
val convert_vars : Ctxt.t -> Term.v list -> v list
val convert : Ctxt.t -> Term.t -> t
val convert_multiple : Ctxt.t -> Term.t list -> t list
val to_term : t -> Term.t
val to_terms : t list -> Term.t list
