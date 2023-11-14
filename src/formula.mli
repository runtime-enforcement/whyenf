(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Pred

type side = N | L | R | LR

type t =
  | TT
  | FF
  | EqConst of string * Dom.t
  | Predicate of string * Term.t list
  | Neg of t
  | And of side * t * t
  | Or of side * t * t
  | Imp of side * t * t
  | Iff of side * side * t * t
  | Exists of string * t
  | Forall of string * t
  | Prev of Interval.t * t
  | Next of Interval.t * t
  | Once of Interval.t * t
  | Eventually of Interval.t * t
  | Historically of Interval.t * t
  | Always of Interval.t * t
  | Since of side * Interval.t * t * t
  | Until of side * Interval.t * t * t

val tt: t
val ff: t
val eqconst: string -> Dom.t -> t
val predicate: string -> Term.t list -> t
val neg: t -> t
val conj: side -> t -> t -> t
val disj: side -> t -> t -> t
val imp: side -> t -> t -> t
val iff: side -> side -> t -> t -> t
val exists: string -> t -> t
val forall: string -> t -> t
val prev: Interval.t -> t -> t
val next: Interval.t -> t -> t
val once: Interval.t -> t -> t
val eventually: Interval.t -> t -> t
val historically: Interval.t -> t -> t
val always: Interval.t -> t -> t
val since: side -> Interval.t -> t -> t -> t
val until: side -> Interval.t -> t -> t -> t
val trigger: side -> Interval.t -> t -> t -> t
val release: side -> Interval.t -> t -> t -> t

val fv: t -> (String.t, Base.String.comparator_witness) Base.Set.t
val check_bindings: t -> bool

val hp: t -> int
val hf: t -> int
val height: t -> int

val subfs_bfs: t list -> t list
val subfs_dfs: t -> t list
val subfs_scope: t -> int -> (int * (int list * int list)) list
val preds: t -> t list
val pred_names: t -> (string, Base.String.comparator_witness) Base.Set.t

val op_to_string: t -> string
val to_string: t -> string
val to_json: t -> string
val to_latex: t -> string

val string_of_side: side -> string
val string_of_sides: side * side -> string
val side_of_string: string -> side
