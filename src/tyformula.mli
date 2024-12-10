open Base

module MyTerm = Term
open MFOTL_lib
module Ctxt : module type of Ctxt.Make(Dom)
module Term = MyTerm

include module type of MFOTL.Make(Term.TrivialInfo)(Tterm.TypedVar)(Dom)(Tterm)

val of_formula :  Formula.t -> ?let_types:(string, Ctxt.ttt list, String.comparator_witness) Map.t -> Ctxt.t -> Ctxt.t * t
val of_formula' : Formula.t -> t




















