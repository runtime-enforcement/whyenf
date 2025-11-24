open Base

module MyTerm = Term
open MFOTL_lib
module Ctxt : module type of Ctxt.Make(Dom)
module Term = MyTerm

type info_type = {
    enftype: Enftype.t;
    filter:  Filter.t;
    flag:    bool;
  } [@@deriving compare, sexp_of, hash]

module TypeInfo : Modules.I with type t = info_type

include module type of MFOTL.Make(TypeInfo)(Tterm.TypedVar)(Dom)(Tterm)

val of_formula : ?m:((string, Enftype.t, String.comparator_witness) Map.t) -> Tyformula.typed_t -> Ctxt.t -> Ctxt.t * t
val of_formula' : Tyformula.typed_t -> t
