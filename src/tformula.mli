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

include module type of Tyformula.MFOTL_Enforceability(Sig)

