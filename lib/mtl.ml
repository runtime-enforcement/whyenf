(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util
open Expl
open Interval

module Deque = Core_kernel.Deque

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

let tt = TT
let ff = FF
let p x = P x
(* Propositional operators *)
let neg f = Neg f
let conj f g = Conj(f, g)
let disj f g = Disj(f, g)

(* Temporal operators *)
let prev i f = Prev(i, f)
let next i f = Next(i, f)
let since i f g = Since(i, f, g)
let until i f g = Until(i, f, g)

(* Partially supported *)
let imp f g = Disj(Neg f, g)
let iff f g = Disj(Conj(f, g), Conj(Neg f, Neg g))
let trigger i f g = Neg(Since(i, Neg(f), Neg(g)))
let release i f g = Neg(Until(i, Neg(f), Neg(g)))
let eventually i f = Until(i, TT, f)
let once i f = Since(i, TT, f)
let always i f = Neg(eventually i (Neg f))
let historically i f = Neg(once i (Neg f))

let equal x y = match x, y with
  | TT, TT -> true
  | P x, P y -> x = y
  | Neg f, Neg f' -> f == f'
  | Conj (f, g), Conj (f', g') | Disj (f, g), Disj (f', g') -> f == f' && g == g'
  | Prev (i, f), Prev (i', f') | Next (i, f), Next (i', f') -> i == i' && f == f'
  | Since (i, f, g), Since (i', f', g') | Until (i, f, g), Until (i', f', g') -> i == i' && f == f' && g == g'
  | _ -> false

let rec atoms x = match x with
  | TT | FF -> []
  | P x -> [x]
  | Neg f | Next (_, f) | Prev (_, f) -> atoms f
  | Conj (f1, f2) | Disj (f1, f2)
  | Until (_, f1, f2) | Since (_, f1, f2) -> let a1s = List.fold_right (fun a acc -> if List.mem a acc then acc
                                                                                     else acc @ [a]) (atoms f1) [] in
                                             List.fold_right (fun a acc -> if List.mem a acc then acc
                                                                           else acc @ [a]) (atoms f2) a1s

(* Past height *)
let rec hp x = match x with
  | TT | FF | P _ -> 0
  | Neg f -> hp f
  | Conj (f1, f2) | Disj (f1, f2) -> max (hp f1) (hp f2)
  | Until (i, f1, f2) -> max (hp f1) (hp f2)
  | Next (i, f) -> hp f
  | Prev (i, f) -> hp f + 1
  | Since (i, f1, f2) -> max (hp f1) (hp f2) + 1

(* Future height *)
let rec hf x = match x with
  | TT | FF | P _ -> 0
  | Neg f -> hf f
  | Conj (f1, f2) | Disj (f1, f2) -> max (hf f1) (hf f2)
  | Since (i, f1, f2) -> max (hf f1) (hf f2)
  | Prev (i, f) -> hf f
  | Next (i, f) -> hf f + 1
  | Until (i, f1, f2) -> max (hf f1) (hf f2) + 1

let height f = hp f + hf f

let rec formula_to_string l f = match f with
  | P x -> Printf.sprintf "%s" x
  | TT -> Printf.sprintf "⊤"
  | FF -> Printf.sprintf "⊥"
  | Conj (f, g) -> Printf.sprintf (paren l 4 "%a ∧ %a") (fun x -> formula_to_string 4) f (fun x -> formula_to_string 4) g
  | Disj (f, g) -> Printf.sprintf (paren l 3 "%a ∨ %a") (fun x -> formula_to_string 3) f (fun x -> formula_to_string 4) g
  | Neg f -> Printf.sprintf "¬%a" (fun x -> formula_to_string 5) f
  | Prev (i, f) -> Printf.sprintf (paren l 5 "●%a %a") (fun x -> interval_to_string) i (fun x -> formula_to_string 5) f
  | Next (i, f) -> Printf.sprintf (paren l 5 "○%a %a") (fun x -> interval_to_string) i (fun x -> formula_to_string 5) f
  | Since (i, f, g) -> Printf.sprintf (paren l 0 "%a S%a %a") (fun x -> formula_to_string 5) f (fun x -> interval_to_string) i (fun x -> formula_to_string 5) g
  | Until (i, f, g) -> Printf.sprintf (paren l 0 "%a U%a %a") (fun x -> formula_to_string 5) f (fun x -> interval_to_string) i (fun x -> formula_to_string 5) g
let formula_to_string = formula_to_string 0

let rec f_to_json indent pos f =
  let indent' = "  " ^ indent in
  match f with
  | P a -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"P\",\n%s\"atom\": \"%s\"\n%s}"
             indent pos indent' indent' a indent
  | TT -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"TT\"\n%s}"
               indent pos indent' indent
  | FF -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"FF\"\n%s}"
               indent pos indent' indent
  | Conj (f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Conj\",\n%s,\n%s\n%s}"
                     indent pos indent' (f_to_json indent' "l" f) (f_to_json indent' "r" g) indent
  | Disj (f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Disj\",\n%s,\n%s\n%s}"
                     indent pos indent' (f_to_json indent' "l" f) (f_to_json indent' "r" g) indent
  | Neg f -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Neg\",\n%s\n%s}"
               indent pos indent' (f_to_json indent' "" f) indent
  | Prev (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Prev\",\n%s\"interval\": \"%s\",\n%s\n%s}"
                     indent pos indent' indent' (interval_to_string i) (f_to_json indent' "" f) indent
  | Next (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Next\",\n%s\"interval\": \"%s\",\n%s\n%s}"
                     indent pos indent' indent' (interval_to_string i) (f_to_json indent' "" f) indent
  | Since (i, f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Since\",\n%s\"interval\": \"%s\",\n%s,\n%s\n%s}"
                         indent pos indent' indent' (interval_to_string i) (f_to_json indent' "l" f) (f_to_json indent' "r" g) indent
  | Until (i, f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Until\",\n%s\"interval\": \"%s\",\n%s,\n%s\n%s}"
                         indent pos indent' indent' (interval_to_string i) (f_to_json indent' "l" f) (f_to_json indent' "r" g) indent
  | _ -> ""
let formula_to_json = f_to_json "    " ""

let immediate_subfs x =
  match x with
  | TT -> []
  | FF -> []
  | P x -> []
  | Neg f -> [f]
  | Conj (f, g) -> [f; g]
  | Disj (f, g) -> [f; g]
  | Prev (i, f) -> [f]
  | Since (i, f, g) -> [f; g]
  | Next (i, f) -> [f]
  | Until (i, f, g) -> [f; g]

let rec subfs_bfs xs =
  xs @ (List.concat (List.map (fun x -> subfs_bfs (immediate_subfs x)) xs))

let rec subfs_dfs x = match x with
  | TT -> [tt]
  | FF -> [ff]
  | P x -> [p x]
  | Neg f -> [neg f] @ (subfs_dfs f)
  | Conj (f, g) -> [conj f g] @ (subfs_dfs f) @ (subfs_dfs g)
  | Disj (f, g) -> [disj f g] @ (subfs_dfs f) @ (subfs_dfs g)
  | Prev (i, f) -> [prev i f] @ (subfs_dfs f)
  | Since (i, f, g) -> [since i f g] @ (subfs_dfs f) @ (subfs_dfs g)
  | Next (i, f) -> [next i f] @ (subfs_dfs f)
  | Until (i, f, g) -> [until i f g] @ (subfs_dfs f) @ (subfs_dfs g)
