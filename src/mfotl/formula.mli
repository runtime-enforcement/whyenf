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

type 'd term = Var of string | Const of 'd

type 'd formula =
  | TT
  | FF
  | Pred of string * ('d term list)
  | Neg of 'd formula
  | Conj of 'd formula * 'd formula
  | Disj of 'd formula * 'd formula
  | Imp of 'd formula * 'd formula
  | Iff of 'd formula * 'd formula
  | Exists of string * 'd formula
  | Forall of string * 'd formula
  | Prev of interval * 'd formula
  | Next of interval * 'd formula
  | Once of interval * 'd formula
  | Historically of interval * 'd formula
  | Eventually of interval * 'd formula
  | Always of interval * 'd formula
  | Since of interval * 'd formula * 'd formula
  | Until of interval * 'd formula * 'd formula

val tt: 'd formula
val ff: 'd formula
val pred: string -> 'd term list -> 'd formula
val neg: 'd formula -> 'd formula
val conj: 'd formula -> 'd formula -> 'd formula
val disj: 'd formula -> 'd formula -> 'd formula
val imp: 'd formula -> 'd formula -> 'd formula
val iff: 'd formula -> 'd formula -> 'd formula
val exists: string -> 'd formula -> 'd formula
val forall: string -> 'd formula -> 'd formula
val prev: interval -> 'd formula -> 'd formula
val next: interval -> 'd formula -> 'd formula
val once: interval -> 'd formula -> 'd formula
val historically: interval -> 'd formula -> 'd formula
val eventually: interval -> 'd formula -> 'd formula
val always: interval -> 'd formula -> 'd formula
val since: interval -> 'd formula -> 'd formula -> 'd formula
val until: interval -> 'd formula -> 'd formula -> 'd formula
val trigger: interval -> 'd formula -> 'd formula -> 'd formula
val release: interval -> 'd formula -> 'd formula -> 'd formula

val hp: 'd formula -> int
val hf: 'd formula -> int
val height: 'd formula -> int

val subfs_bfs: 'd formula list -> 'd formula list
val subfs_dfs: 'd formula -> 'd formula list
val preds: 'd formula -> (string * 'd term list) list

val f_to_string: 'd formula -> string
val op_to_string: 'd formula -> string
val f_to_json: 'd formula -> string
