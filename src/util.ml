(*******************************************************************)
(*     This is part of Aerial, it is distributed under the         *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

type mode = NAIVE | COMPRESS_LOCAL | COMPRESS_GLOBAL

(* Sets are defined using a functional interface given a type *)
module SS = Set.Make(String)
type ts = int
type tp = int
(* (atomic propositions satisfied at that event * timestamp) *)
type trace = (SS.t * ts) list

(* Make the list [i, i+1, i+2, ..., j] *)
let rec ( -- ) i j =
  if i > j then [] else i :: (i + 1 -- j)

let paren h k x = if h>k then "("^^x^^")" else x

let sum mes = List.fold_left (fun a b -> a + mes b) 0

let mk_le f r s = f r <= f s

let prod_le p q r s = p r s && q r s

let min x y = if x < y then x else y

(* let minsize a b = if size a <= size b then a else b
 * let minsize_list = function
 *   | [] -> failwith "empty list for minsize_list"
 *   | x::xs -> List.fold_left minsize x xs *)
