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
  | TExists of string * t
  | TForall of string * t
  | TPrev of Interval.t * t
  | TNext of Interval.t * t
  | TOnce of Interval.t * t
  | TEventually of Interval.t * t
  | THistorically of Interval.t * t
  | TAlways of Interval.t * t
  | TSince of Side.t * Interval.t * t * t
  | TUntil of Side.t * Interval.t * t * t

and t = { f: core_t; enftype: EnfType.t }

val of_formula : Formula.t -> t
val to_string : t -> string
