(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

type t =
  | TT
  | FF
  | EqConst of Term.t * Dom.t
  | Predicate of string * Term.t list
  | Predicate' of string * Term.t list * t
  | Let of string * Enftype.t option * string list * t * t
  | Let' of string * string list * t * t
  | Agg of string * Aggregation.op * Term.t * string list * t
  | Neg of t
  | And of Side.t * t * t
  | Or of Side.t * t * t
  | Imp of Side.t * t * t
  | Iff of Side.t * Side.t * t * t
  | Exists of string * t
  | Forall of string * t
  | Prev of Interval.t * t
  | Next of Interval.t * t
  | Once of Interval.t * t
  | Eventually of Interval.t * t
  | Historically of Interval.t * t
  | Always of Interval.t * t
  | Since of Side.t * Interval.t * t * t
  | Until of Side.t * Interval.t * t * t [@@deriving compare, sexp_of, hash]

val tt: t
val ff: t
val eqconst: Term.t -> Dom.t -> t
val agg: string -> Aggregation.op -> Term.t -> string list -> t -> t
val predicate: string -> Term.t list -> t
val flet: string -> Enftype.t option -> string list -> t -> t -> t
val neg: t -> t
val conj: Side.t -> t -> t -> t
val disj: Side.t -> t -> t -> t
val imp: Side.t -> t -> t -> t
val iff: Side.t -> Side.t -> t -> t -> t
val exists: string -> t -> t
val forall: string -> t -> t
val prev: Interval.t -> t -> t
val next: Interval.t -> t -> t
val once: Interval.t -> t -> t
val eventually: Interval.t -> t -> t
val historically: Interval.t -> t -> t
val always: Interval.t -> t -> t
val since: Side.t -> Interval.t -> t -> t -> t
val until: Side.t -> Interval.t -> t -> t -> t
val trigger: Side.t -> Interval.t -> t -> t -> t
val release: Side.t -> Interval.t -> t -> t -> t

val init: Sformula.t -> t

val fv: t -> (String.t, Base.String.comparator_witness) Base.Set.t
val list_fv: t -> String.t list
val terms: t -> (Term.t, Term.comparator_witness) Base.Set.t

val equal: t -> t -> bool

val op_to_string: t -> string
val to_string: t -> string

val solve_past_guarded: string -> bool -> t -> (string, Base.String.comparator_witness) Base.Set.t list
val is_past_guarded: string -> bool -> t -> bool

val check_agg: Ctxt.t -> string -> Aggregation.op -> Term.t -> string list -> t -> Ctxt.t

val convert_vars: t -> t
val convert_lets: t -> t
val unroll_let: t -> t

module Filter : sig

  type filter = An of string | AllOf of filter list | OneOf of filter list [@@deriving equal, compare, hash, sexp_of]

  val _true : filter
  val _false : filter

  val eval : Db.t -> filter -> bool

  val to_string : filter -> string

  val simplify : filter -> filter
  val present_filter : ?b:bool -> t -> filter

  val conj : filter -> filter -> filter
  val disj : filter -> filter -> filter
  
end
