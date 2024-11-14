(*******************************************************************)
(*     This is part of WhyEnf, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Base

open Formula

type core_t =
  | TTT
  | TFF
  | TEqConst of Term.t * Dom.t
  | TPredicate of string * Term.t list
  | TPredicate' of string * Term.t list * t
  | TLet' of string * string list * t * t
  | TAgg of string * Dom.tt * Aggregation.op * Term.t * string list * t
  | TTop of (string * Dom.tt) list * string * Term.t list * string list * t
  | TNeg of t
  | TAnd of Side.t * t list
  | TOr of Side.t * t list
  | TImp of Side.t * t * t
  | TIff of Side.t * Side.t * t * t
  | TExists of string * Dom.tt * bool * t
  | TForall of string * Dom.tt * bool * t
  | TPrev of Interval.t * t
  | TNext of Interval.t * t
  | TOnce of Interval.t * t
  | TEventually of Interval.t * bool * t
  | THistorically of Interval.t * t
  | TAlways of Interval.t * bool * t
  | TSince of Side.t * Interval.t * t * t
  | TUntil of Side.t * Interval.t * bool * t * t

and t = {
    f:       core_t;
    enftype: Enftype.t;
    filter:  Filter.filter
  }  [@@deriving compare, hash, sexp_of]

val ttrue  : t
val tfalse : t

val neg : t -> Enftype.t -> t
(*val fv : t -> (String.t, Base.String.comparator_witness) Base.Set.t*)
val conj : Side.t -> t -> t -> Enftype.t -> t

val op_to_string : t -> string

val of_formula :  Formula.t ->  ?let_types:(string, Enftype.t, Base.String.comparator_witness) Base.Map.t -> Ctxt.t -> Ctxt.t * t
val of_formula' : Formula.t -> t

val ac_simplify : t -> t

val to_formula : t -> Formula.t
val to_string : t -> string
