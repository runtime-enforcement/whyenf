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
open Hashcons

type formula_ =
  | TT
  | FF
  | P of string
  | Neg of formula
  | Conj of formula * formula
  | Disj of formula * formula
  | Impl of formula * formula
  | Iff of formula * formula
  | Prev of interval * formula
  | Next of interval * formula
  | Once of interval * formula
  | Historically of interval * formula
  | Always of interval * formula
  | Eventually of interval * formula
  | Since of interval * formula * formula
  | Until of interval * formula * formula
and formula = formula_ hash_consed

val hash: formula -> int
val value: formula -> formula_

val tt: formula
val ff: formula
val p: string -> formula
(* propositional operators *)
val neg: formula -> formula
val conj: formula -> formula -> formula
val disj: formula -> formula -> formula
val impl: formula -> formula -> formula
val iff: formula -> formula -> formula
(* temporal operators *)
val prev: interval -> formula -> formula
val next: interval -> formula -> formula
val once: interval -> formula -> formula
val historically: interval -> formula -> formula
val always: interval -> formula -> formula
val eventually: interval -> formula -> formula
val since: interval -> formula -> formula -> formula
val until: interval -> formula -> formula -> formula
val release: interval -> formula -> formula -> formula
val weak_until: interval -> formula -> formula -> formula
val trigger: interval -> formula -> formula -> formula

val atoms: formula -> string list

val hp: formula -> int
val hf: formula -> int
val height: formula -> int

val formula_to_string: formula -> string

val subfs: formula -> string list
