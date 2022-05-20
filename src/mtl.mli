(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (ETH Zürich)                                   *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util
open Expl
open Interval

type formula =
  | TT
  | FF
  | P of string
  | Neg of formula
  | Conj of formula * formula
  | Disj of formula * formula
  | Prev of interval * formula
  | Next of interval * formula
  | Since of interval * formula * formula
  | Until of interval * formula * formula

val tt: formula
val ff: formula
val p: string -> formula
(* propositional operators *)
val neg: formula -> formula
val conj: formula -> formula -> formula
val disj: formula -> formula -> formula
(* temporal operators *)
val prev: interval -> formula -> formula
val next: interval -> formula -> formula
val since: interval -> formula -> formula -> formula
val until: interval -> formula -> formula -> formula

val imp: formula -> formula -> formula
val iff: formula -> formula -> formula
val trigger: interval -> formula -> formula -> formula
val release: interval -> formula -> formula -> formula
val eventually: interval -> formula -> formula
val once: interval -> formula -> formula
val always: interval -> formula -> formula
val historically: interval -> formula -> formula

val atoms: formula -> string list

val hp: formula -> int
val hf: formula -> int
val height: formula -> int

val subfs_bfs: formula list -> formula list
val subfs_dfs: formula -> formula list

val formula_to_string: formula -> string
val op_to_string: formula -> string
val formula_to_json: formula -> string
