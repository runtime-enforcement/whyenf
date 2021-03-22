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
type timestamp = int
type timepoint = int
type ts_asc_list = timestamp list
type ts_desc_list = timestamp list
type trace = (SS.t * timestamp) list

(* Make the list [i, i+1, i+2, ..., j] *)
let rec ( -- ) i j =
  if i > j then [] else i :: (i + 1 -- j)

let paren h k x = if h>k then "("^^x^^")" else x 

(* let minsize a b = if size a <= size b then a else b
 * let minsize_list = function
 *   | [] -> failwith "empty list for minsize_list"
 *   | x::xs -> List.fold_left minsize x xs *)
