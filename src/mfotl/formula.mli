(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Pred

type t =
  | TT
  | FF
  | Predicate of string * Term.t list
  | Neg of t
  | And of t * t
  | Or of t * t
  | Imp of t * t
  | Iff of t * t
  | Exists of Term.t * t
  | Forall of Term.t * t
  | Prev of Interval.t * t
  | Next of Interval.t * t
  | Once of Interval.t * t
  | Eventually of Interval.t * t
  | Historically of Interval.t * t
  | Always of Interval.t * t
  | Since of Interval.t * t * t
  | Until of Interval.t * t * t

val tt: t
val ff: t
val predicate: string -> Term.t list -> t
val neg: t -> t
val conj: t -> t -> t
val disj: t -> t -> t
val imp: t -> t -> t
val iff: t -> t -> t
val exists: string -> t -> t
val forall: string -> t -> t
val prev: Interval.t -> t -> t
val next: Interval.t -> t -> t
val once: Interval.t -> t -> t
val eventually: Interval.t -> t -> t
val historically: Interval.t -> t -> t
val always: Interval.t -> t -> t
val since: Interval.t -> t -> t -> t
val until: Interval.t -> t -> t -> t
val trigger: Interval.t -> t -> t -> t
val release: Interval.t -> t -> t -> t

val fv: t -> (Term.t, Term.comparator_witness) Base.Set.t

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
