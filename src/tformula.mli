open Base

type info_type = {
    enftype: MFOTL_lib.Enftype.t;
    filter:  MFOTL_lib.Filter.t;
    flag:    bool;
  } [@@deriving compare, sexp_of, hash]

module TypeInfo : MFOTL_lib.Modules.I with type t = info_type

include module type of MFOTL_lib.MFOTL.Make(TypeInfo)(Tterm.TypedVar)(MFOTL_lib.Dom)(Tterm)

val of_formula :  Formula.typed_t ->  ?let_types:(string, MFOTL_lib.Enftype.t, Base.String.comparator_witness) Base.Map.t -> Ctxt.t -> Ctxt.t * t
val of_formula' : Formula.typed_t -> t
