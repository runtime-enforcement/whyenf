open Base

module MyTerm = Term
module Errs = Errors
open MFOTL_lib
module Ctxt = Ctxt.Make(Dom)
module Term = MyTerm

type info_type = {
    enftype: Enftype.t;
    filter:  Filter.t;
    flag:    bool;
  } [@@deriving compare, sexp_of, hash, equal]

module TypeInfo : Modules.I with type t = info_type = struct

  type t = info_type [@@deriving compare, sexp_of, hash, equal]

  let to_string l s info =
    if Enftype.is_only_observable info.enftype then
      s
    else
      Printf.sprintf (Etc.paren l 0 "%s : %s") s (Enftype.to_string info.enftype)

  let dummy = { enftype = Enftype.obs; filter = Filter.tt; flag = false }

end 

include MFOTL.Make(TypeInfo)(Tterm.TypedVar)(Dom)(Tterm)

include Tyformula.MFOTL_Enforceability(Sig)

