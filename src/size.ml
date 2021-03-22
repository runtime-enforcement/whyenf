(*******************************************************************)
(*    This is part of Explanator2, it is distributed under the     *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

let rec s_size = function
  | STT i -> 1
  | SAtom (i, _) -> 1
  | SNeg expl -> 1 + v_size expl
  | SPrev expl -> 1 + s_size expl
  | SOnce (i, expl) -> 1 + s_size expl
  | SHistorically expls -> 1 + sum s_size expls
  | SNext expl -> 1 + s_size expl
  | SEventually (i, expl) -> 1 + s_size expl
  | SAlways expls -> 1 + sum s_size expls
  | SConj (sphi, spsi) -> 1 + s_size sphi + s_size spsi
  | SDisjL sphi -> 1 + s_size sphi
  | SDisjR spsi -> 1 + s_size spsi
  | SImplL vphi -> 1 + v_size vphi
  | SImplR spsi -> 1 + s_size spsi
  | SIffS (sphi, spsi) -> 1 + s_size sphi + s_size spsi
  | SIffV (vphi, vpsi) -> 1 + v_size vphi + v_size vpsi
  | SSince (spsi, sphis) -> 1 + s_size spsi + sum s_size sphis
  | SUntil (spsi, sphis) -> 1 + s_size spsi + sum s_size sphis
and v_size = function
  | VFF i -> 1
  | VAtom (i, _) -> 1
  | VNeg sphi -> 1 + s_size sphi
  | VDisj (vphi, vpsi) -> 1 + v_size vphi + v_size vpsi
  | VConjL vphi -> 1 + v_size vphi
  | VConjR vpsi -> 1 + v_size vpsi
  | VImpl (sphi, vpsi) -> 1 + s_size sphi + v_size vpsi
  | VIffL (sphi, vpsi) -> 1 + s_size sphi + v_size vpsi
  | VIffR (vphi, spsi) -> 1 + v_size vphi + s_size spsi
  | VPrev vphi -> 1 + v_size vphi
  | VPrev0 -> 1
  | VOnce expls -> 1 + sum v_size expls
  | VHistorically (i, expl) -> 1 + v_size expl
  | VNext vphi -> 1 + v_size vphi
  | VEventually expls -> 1 + sum v_size expls
  | VAlways (i, expl) -> 1 + v_size expl
  | VSince (vphi, vpsis) -> 1 + v_size vphi + sum v_size vpsis
  | VSincew vpsis-> 1 + sum v_size vpsis
  | VUntilw vpsis -> 1 + sum v_size vpsis
  | VUntil (vphi, vpsis) -> 1 + v_size vphi + sum v_size vpsis

let size = function
  | S s_p -> s_size s_p
  | V v_p -> v_size v_p

let size_le = mk_le size

let minsize a b = if size a <= size b then a else b
let minsize_list = function
  | [] -> failwith "empty list for minsize_list"
  | x::xs -> List.fold_left minsize x xs
