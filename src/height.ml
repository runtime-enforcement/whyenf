(*******************************************************************)
(*    This is part of Explanator2, it is distributed under the     *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl

(* height *)
let rec hp x = match x.node with
  | TT | FF | P _ -> 0
  | Neg f -> hp f
  | Conj (f1, f2) | Disj (f1, f2)
  | Impl (f1, f2) | Iff (f1, f2) -> max (hp f1) (hp f2)
  | Until (i, f1, f2) -> max (hp f1) (hp f2)
  | Next (i, f) | Always (i, f) | Eventually (i, f) -> hp f
  | Prev (i, f) | Once (i, f) | Historically (i, f) -> hp f + 1
  | Since (i, f1, f2) -> max (hp f1) (hp f2) + 1

(* future height *)
let rec hf x = match x.node with
  | TT | FF | P _ -> 0
  | Neg f -> hf f
  | Conj (f1, f2) | Disj (f1, f2)
  | Impl (f1, f2) | Iff (f1, f2) -> max (hf f1) (hf f2)
  | Since (i, f1, f2) -> max (hf f1) (hf f2)
  | Prev (i, f) | Once (i, f) | Historically (i, f) -> hf f
  | Next (i, f) | Always (i, f) | Eventually (i, f) -> hf f + 1
  | Until (i, f1, f2) -> max (hf f1) (hf f2) + 1

let height f = hp f + hf f
