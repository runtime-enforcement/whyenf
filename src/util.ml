(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

(* Sets are defined using a functional interface given a type *)
module SS = Set.Make(String)
type timestamp = int
type timepoint = int
(* (atomic propositions satisfied at that event * timestamp) *)
type event = SS.t * timestamp
type trace = event list

type mode = SAT | VIOL | ALL

let rec max_list = List.fold_left max 0
let rec min_list = List.fold_left min 0

(* Make the list [i, i+1, i+2, ..., j] *)
let rec ( -- ) i j =
  if i > j then [] else i :: (i + 1 -- j)

let last l = List.nth l (List.length l - 1)

let paren h k x = if h>k then "("^^x^^")" else x

let sum mes = List.fold_left (fun a b -> a + mes b) 0

let prod_le p q r s = p r s && q r s

let lex_le p q r s = p r s || (not (p s r) && q r s)

let mk_le f r s = f r <= f s

let mk_sl f r s = f r < f s

let eat s t = s ^ String.trim t

let list_to_string indent f = function
  | [] -> indent ^ "[]"
  | [x] -> indent ^ eat "[" (f indent x ^ "]")
  | x :: xs ->
      List.fold_left (fun s el -> eat (s ^ "\n" ^ indent ^ "; ") (f indent el))
        (indent ^ eat "[ " (f indent x)) xs ^ " ]"

(*stolen from https://github.com/Octachron/ocaml/blob/posets_for_parmatch/typing/parmatch.ml#L1501*)
let get_mins le ps =
  let rec select_rec r = function
    | [] -> r
    | p::ps ->
      if List.exists (fun x -> le x p) r
      then select_rec r ps
      else select_rec (p :: List.filter (fun x -> not (le p x)) r) ps in
  List.rev (select_rec [] ps)
