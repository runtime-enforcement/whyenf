open Base
open Pred

open Formula

type core_t =
  | TTT
  | TFF
  | TEqConst of string * Dom.t
  | TPredicate of string * Term.t list
  | TNeg of t
  | TAnd of Side.t * t * t
  | TOr of Side.t * t * t
  | TImp of Side.t * t * t
  | TIff of Side.t * Side.t * t * t
  | TExists of string * Dom.tt * t
  | TForall of string * Dom.tt * t
  | TPrev of Interval.t * t
  | TNext of Interval.t * t
  | TOnce of Interval.t * t
  | TEventually of Interval.t * bool * t
  | THistorically of Interval.t * t
  | TAlways of Interval.t * bool * t
  | TSince of Side.t * Interval.t * t * t
  | TUntil of Side.t * Interval.t * bool * t * t

and t = { f: core_t; enftype: EnfType.t }

val ttrue  : t
val tfalse : t

val neg : t -> EnfType.t -> t
(*val fv : t -> (String.t, Base.String.comparator_witness) Base.Set.t*)
val conj : Side.t -> t -> t -> EnfType.t -> t

val op_to_string : t -> string

val of_formula : Formula.t -> t
val to_formula : t -> Formula.t
val to_string : t -> string
