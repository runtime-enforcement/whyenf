(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (ETH Zürich)                                   *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util.Interval
open Pred

type formula =
  | TT
  | FF
  | Predicate of string * (term list)
  | Neg of formula
  | Conj of formula * formula
  | Disj of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Exists of string * formula
  | Forall of string * formula
  | Prev of interval * formula
  | Next of interval * formula
  | Once of interval * formula
  | Historically of interval * formula
  | Eventually of interval * formula
  | Always of interval * formula
  | Since of interval * formula * formula
  | Until of interval * formula * formula

val tt: formula
val ff: formula
val predicate: string -> string list -> formula
val neg: formula -> formula
val conj: formula -> formula -> formula
val disj: formula -> formula -> formula
val imp: formula -> formula -> formula
val iff: formula -> formula -> formula
val exists: string -> formula -> formula
val forall: string -> formula -> formula
val prev: interval -> formula -> formula
val next: interval -> formula -> formula
val once: interval -> formula -> formula
val historically: interval -> formula -> formula
val eventually: interval -> formula -> formula
val always: interval -> formula -> formula
val since: interval -> formula -> formula -> formula
val until: interval -> formula -> formula -> formula
val trigger: interval -> formula -> formula -> formula
val release: interval -> formula -> formula -> formula

val hp: formula -> int
val hf: formula -> int
val height: formula -> int

val subfs_bfs: formula list -> formula list
val subfs_dfs: formula -> formula list
val preds: formula -> formula list

val f_to_string: (const -> string) -> formula -> string
val op_to_string: (const -> string) -> formula -> string
val f_to_json: (const -> string) -> formula -> string
