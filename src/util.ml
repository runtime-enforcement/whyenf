(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
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

let min x y = if x < y then x else y

(* Make the list [i, i+1, i+2, ..., j] *)
let rec ( -- ) i j =
  if i > j then [] else i :: (i + 1 -- j)

let paren h k x = if h>k then "("^^x^^")" else x

let sum mes = List.fold_left (fun a b -> a + mes b) 0

let prod_le p q r s = p r s && q r s

let lex_le p q r s = p r s || (not (p s r) && q r s)

let mk_le f r s = f r <= f s

(*stolen from https://github.com/Octachron/ocaml/blob/posets_for_parmatch/typing/parmatch.ml#L1501*)
let get_mins le ps =
  let rec select_rec r = function
    | [] -> r
    | p::ps ->
      if List.exists (fun x -> le x p) r
      then select_rec r ps
      else select_rec (p :: List.filter (fun x -> not (le p x)) r) ps in
  List.rev (select_rec [] ps)
