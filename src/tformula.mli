(*******************************************************************)
(*     This is part of WhyEnf, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Base

type info_type = {
    enftype: Enftype.t;
    filter:  MFOTL.Filter.t;
    flag:    bool;
  } [@@deriving compare, sexp_of, hash]

module TypeInfo : MFOTL_Base.I with type t = info_type

include module type of MFOTL.Make(TypeInfo)(Tterm.TypedVar)(Dom)(Tterm)

val of_formula :  Formula.typed_t ->  ?let_types:(string, Enftype.t, Base.String.comparator_witness) Base.Map.t -> Ctxt.t -> Ctxt.t * t
val of_formula' : Formula.typed_t -> t
