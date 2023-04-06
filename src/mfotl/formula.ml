(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util.Misc
open Util.Interval
open Pred
open Base

module Deque = Core_kernel.Deque

type formula =
  | TT
  | FF
  | Predicate of string * (term list)
  | Neg of formula
  | Conj of formula * formula
  | Disj of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Exists of string * formula
  | Forall of string * formula
  | Prev of interval * formula
  | Next of interval * formula
  | Once of interval * formula
  | Historically of interval * formula
  | Eventually of interval * formula
  | Always of interval * formula
  | Since of interval * formula * formula
  | Until of interval * formula * formula

let predicate p_name strms =
  let sig_pred = Hashtbl.find_exn Pred.Sig.sig_table p_name in
  if List.length strms = sig_pred.arity then
    let trms = List.map2_exn strms sig_pred.ntconsts
                 (fun s ntc -> if String.equal s (fst ntc) then Var s
                               else Const (string_to_const s (snd ntc))) in
    Predicate (p_name, trms)
  else raise (Invalid_argument (Printf.sprintf "arity of %s is %d" p_name sig_pred.arity))

let tt = TT
let ff = FF
let neg f = Neg f
let conj f g = Conj (f, g)
let disj f g = Disj (f, g)
let imp f g = Imp (f, g)
let iff f g = Iff (f, g)
let exists x f = Exists (x, f)
let forall x f = Forall (x, f)
let prev i f = Prev (i, f)
let next i f = Next (i, f)
let once i f = Once (i, f)
let historically i f = Historically (i, f)
let eventually i f = Eventually (i, f)
let always i f = Always (i, f)
let since i f g = Since (i, f, g)
let until i f g = Until (i, f, g)

(* Rewriting of non-native operators *)
let trigger i f g = Neg (Since (i, Neg (f), Neg (g)))
let release i f g = Neg (Until (i, Neg (f), Neg (g)))

let equal x y = match x, y with
  | TT, TT
    | FF, FF -> true
  | Predicate (r, trms), Predicate (r', trms') -> String.equal r r' && List.equal term_equal trms trms'
  | Neg f, Neg f' -> f == f'
  | Conj (f, g), Conj (f', g')
    | Disj (f, g), Disj (f', g')
    | Imp (f, g), Imp (f', g')
    | Iff (f, g), Iff (f', g') -> f == f' && g == g'
  | Exists (x, f), Exists (x', f')
    | Forall (x, f), Forall (x', f') -> x == x' && f == f'
  | Prev (i, f), Prev (i', f')
    | Next (i, f), Next (i', f')
    | Once (i, f), Once (i', f')
    | Historically (i, f), Historically (i', f')
    | Eventually (i, f), Eventually (i', f')
    | Always (i, f), Always (i', f') -> i == i' && f == f'
  | Since (i, f, g), Since (i', f', g')
    | Until (i, f, g), Until (i', f', g') -> i == i' && f == f' && g == g'
  | _ -> false

(* Past height *)
let rec hp x = match x with
  | TT
    | FF
    | Predicate _ -> 0
  | Neg f
    | Exists (_, f)
    | Forall (_, f) -> hp f
  | Conj (f1, f2)
    | Disj (f1, f2)
    | Imp (f1, f2)
    | Iff (f1, f2) -> max (hp f1) (hp f2)
  | Prev (_, f)
    | Once (_, f)
    | Historically (_, f) -> hp f + 1
  | Eventually (_, f)
    | Always (_, f)
    | Next (_, f) -> hp f
  | Since (_, f1, f2) -> max (hp f1) (hp f2) + 1
  | Until (_, f1, f2) -> max (hp f1) (hp f2)

(* Future height *)
let rec hf x = match x with
  | TT
    | FF
    | Predicate _ -> 0
  | Neg f
    | Exists (_, f)
    | Forall (_, f) -> hf f
  | Conj (f1, f2)
    | Disj (f1, f2)
    | Imp (f1, f2)
    | Iff (f1, f2) -> max (hf f1) (hf f2)
  | Prev (_, f)
    | Once (_, f)
    | Historically (_, f) -> hf f
  | Eventually (_, f)
    | Always (_, f)
    | Next (_, f) -> hf f + 1
  | Since (_, f1, f2) -> max (hf f1) (hf f2)
  | Until (_, f1, f2) -> max (hf f1) (hf f2) + 1

let height f = hp f + hf f

let immediate_subfs x =
  match x with
  | TT
    | FF
    | Predicate _ -> []
  | Neg f
    | Exists (_, f)
    | Forall (_, f)
    | Prev (_, f)
    | Next (_, f)
    | Once (_, f)
    | Historically (_, f)
    | Eventually (_, f)
    | Always (_, f) -> [f]
  | Conj (f, g)
    | Disj (f, g)
    | Imp (f, g)
    | Iff (f, g) -> [f; g]
  | Since (i, f, g)
    | Until (i, f, g) -> [f; g]

let rec subfs_bfs xs =
  xs @ (List.concat (List.map xs (fun x -> subfs_bfs (immediate_subfs x))))

let rec subfs_dfs x = match x with
  | TT -> [tt]
  | FF -> [ff]
  | Predicate (r, ts) -> [Predicate (r, ts)]
  | Neg f -> [neg f] @ (subfs_dfs f)
  | Conj (f, g) -> [conj f g] @ (subfs_dfs f) @ (subfs_dfs g)
  | Disj (f, g) -> [disj f g] @ (subfs_dfs f) @ (subfs_dfs g)
  | Imp (f, g) -> [imp f g] @ (subfs_dfs f) @ (subfs_dfs g)
  | Iff (f, g) -> [iff f g] @ (subfs_dfs f) @ (subfs_dfs g)
  | Exists (x, f) -> [exists x f] @ (subfs_dfs f)
  | Forall (x, f) -> [forall x f] @ (subfs_dfs f)
  | Prev (i, f) -> [prev i f] @ (subfs_dfs f)
  | Next (i, f) -> [next i f] @ (subfs_dfs f)
  | Once (i, f) -> [once i f] @ (subfs_dfs f)
  | Historically (i, f) -> [historically i f] @ (subfs_dfs f)
  | Eventually (i, f) -> [eventually i f] @ (subfs_dfs f)
  | Always (i, f) -> [always i f] @ (subfs_dfs f)
  | Since (i, f, g) -> [since i f g] @ (subfs_dfs f) @ (subfs_dfs g)
  | Until (i, f, g) -> [until i f g] @ (subfs_dfs f) @ (subfs_dfs g)

let rec preds = function
  | TT | FF -> []
  | Predicate (r, ts) -> [Predicate (r, ts)]
  | Neg f | Next (_, f) | Prev (_, f)
    | Once (_, f) | Historically (_, f)
    | Eventually (_, f) | Always (_, f) -> preds f
  | Conj (f1, f2) | Disj (f1, f2)
    | Imp (f1, f2) | Iff (f1, f2)
    | Until (_, f1, f2) | Since (_, f1, f2) -> let a1s = List.fold_left (preds f1) ~init:[]
                                                           ~f:(fun acc a -> if List.mem acc a equal then acc
                                                                            else acc @ [a])  in
                                               let a2s = List.fold_left (preds f2) ~init:[]
                                                           ~f:(fun acc a ->
                                                             if (List.mem acc a equal) || (List.mem a1s a equal) then acc
                                                             else acc @ [a]) in
                                               List.append a1s a2s

let rec trms_to_string str_of trms =
  match trms with
  | [] -> ""
  | (Var x)::trms -> if List.equal term_equal trms [] then x
                     else x ^ ", " ^ (trms_to_string str_of trms)
  | (Const d)::ts -> if List.equal term_equal trms [] then (str_of d)
                     else (str_of d) ^ ", " ^ (trms_to_string str_of ts)

let rec f_to_string str_of l f = match f with
  | TT -> Printf.sprintf "⊤"
  | FF -> Printf.sprintf "⊥"
  | Predicate (r, ts) -> Printf.sprintf "%s(%s)" r (trms_to_string str_of ts)
  | Neg f -> Printf.sprintf "¬%a" (fun x -> f_to_string str_of 5) f
  | Conj (f, g) -> Printf.sprintf (paren l 4 "%a ∧ %a") (fun x -> f_to_string str_of 4) f (fun x -> f_to_string str_of 4) g
  | Disj (f, g) -> Printf.sprintf (paren l 3 "%a ∨ %a") (fun x -> f_to_string str_of 3) f (fun x -> f_to_string str_of 4) g
  | Imp (f, g) -> Printf.sprintf (paren l 5 "%a → %a") (fun x -> f_to_string str_of 5) f (fun x -> f_to_string str_of 5) g
  | Iff (f, g) -> Printf.sprintf (paren l 5 "%a ↔ %a") (fun x -> f_to_string str_of 5) f (fun x -> f_to_string str_of 5) g
  | Exists (x, f) -> Printf.sprintf (paren l 5 "∃%s. %a") x (fun x -> f_to_string str_of 5) f
  | Forall (x, f) -> Printf.sprintf (paren l 5 "∀%s. %a") x (fun x -> f_to_string str_of 5) f
  | Prev (i, f) -> Printf.sprintf (paren l 5 "●%a %a") (fun x -> interval_to_string) i (fun x -> f_to_string str_of 5) f
  | Next (i, f) -> Printf.sprintf (paren l 5 "○%a %a") (fun x -> interval_to_string) i (fun x -> f_to_string str_of 5) f
  | Once (i, f) -> Printf.sprintf (paren l 5 "⧫%a %a") (fun x -> interval_to_string) i (fun x -> f_to_string str_of 5) f
  | Historically (i, f) -> Printf.sprintf (paren l 5 "■%a %a") (fun x -> interval_to_string) i (fun x -> f_to_string str_of 5) f
  | Eventually (i, f) -> Printf.sprintf (paren l 5 "◊%a %a") (fun x -> interval_to_string) i (fun x -> f_to_string str_of 5) f
  | Always (i, f) -> Printf.sprintf (paren l 5 "□%a %a") (fun x -> interval_to_string) i (fun x -> f_to_string str_of 5) f
  | Since (i, f, g) -> Printf.sprintf (paren l 0 "%a S%a %a") (fun x -> f_to_string str_of 5) f
                         (fun x -> interval_to_string) i (fun x -> f_to_string str_of 5) g
  | Until (i, f, g) -> Printf.sprintf (paren l 0 "%a U%a %a") (fun x -> f_to_string str_of 5) f
                         (fun x -> interval_to_string) i (fun x -> f_to_string str_of 5) g
let f_to_string str_of = f_to_string str_of 0

let op_to_string str_of f = match f with
  | TT -> Printf.sprintf "⊤"
  | FF -> Printf.sprintf "⊥"
  | Predicate (r, ts) -> Printf.sprintf "%s(%s)" r (trms_to_string str_of ts)
  | Neg _ -> Printf.sprintf "¬"
  | Conj (_, _) -> Printf.sprintf "∧"
  | Disj (_, _) -> Printf.sprintf "∨"
  | Imp (_, _) -> Printf.sprintf "→"
  | Iff (_, _) -> Printf.sprintf "↔"
  | Exists (_, _) -> Printf.sprintf "∃"
  | Forall (_, _) -> Printf.sprintf "∀"
  | Prev (i, _) -> Printf.sprintf "●%s" (interval_to_string i)
  | Next (i, _) -> Printf.sprintf "○%s" (interval_to_string i)
  | Once (i, f) -> Printf.sprintf "⧫%s" (interval_to_string i)
  | Historically (i, f) -> Printf.sprintf "■%s" (interval_to_string i)
  | Eventually (i, f) -> Printf.sprintf "◊%s" (interval_to_string i)
  | Always (i, f) -> Printf.sprintf "□%s" (interval_to_string i)
  | Since (i, _, _) -> Printf.sprintf "S%s" (interval_to_string i)
  | Until (i, _, _) -> Printf.sprintf "U%s" (interval_to_string i)

let rec f_to_json str_of indent pos f =
  let indent' = "  " ^ indent in
  match f with
  | TT -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"TT\"\n%s}"
            indent pos indent' indent
  | FF -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"FF\"\n%s}"
            indent pos indent' indent
  | Predicate (r, ts) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Predicate\",\n%s\"name\": \"%s\",\n%s\"terms\": \"%s\"\n%s}"
                      indent pos indent' indent' r indent' (trms_to_string str_of ts) indent
  | Neg f -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Neg\",\n%s\n%s}"
               indent pos indent' (f_to_json str_of indent' "" f) indent
  | Conj (f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Conj\",\n%s,\n%s\n%s}"
                     indent pos indent' (f_to_json str_of indent' "l" f) (f_to_json str_of indent' "r" g) indent
  | Disj (f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Disj\",\n%s,\n%s\n%s}"
                     indent pos indent' (f_to_json str_of indent' "l" f) (f_to_json str_of indent' "r" g) indent
  | Imp (f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Imp\",\n%s,\n%s\n%s}"
                    indent pos indent' (f_to_json str_of indent' "l" f) (f_to_json str_of indent' "r" g) indent
  | Iff (f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Iff\",\n%s,\n%s\n%s}"
                    indent pos indent' (f_to_json str_of indent' "l" f) (f_to_json str_of indent' "r" g) indent
  | Exists (x, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Exists\",\n%s\"variable\": \"%s\",\n%s\n%s}"
                       indent pos indent' indent' x (f_to_json str_of indent' "" f) indent
  | Forall (x, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Forall\",\n%s\"variable\": \"%s\",\n%s\n%s}"
                       indent pos indent' indent' x (f_to_json str_of indent' "" f) indent
  | Prev (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Prev\",\n%s\"interval\": \"%s\",\n%s\n%s}"
                     indent pos indent' indent' (interval_to_string i) (f_to_json str_of indent' "" f) indent
  | Next (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Next\",\n%s\"interval\": \"%s\",\n%s\n%s}"
                     indent pos indent' indent' (interval_to_string i) (f_to_json str_of indent' "" f) indent
  | Once (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Once\",\n%s\"interval\": \"%s\",\n%s\n%s}"
                     indent pos indent' indent' (interval_to_string i) (f_to_json str_of indent' "" f) indent
  | Historically (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Historically\",\n%s\"interval\": \"%s\",\n%s\n%s}"
                     indent pos indent' indent' (interval_to_string i) (f_to_json str_of indent' "" f) indent
  | Eventually (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Eventually\",\n%s\"interval\": \"%s\",\n%s\n%s}"
                           indent pos indent' indent' (interval_to_string i) (f_to_json str_of indent' "" f) indent
  | Always (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Always\",\n%s\"interval\": \"%s\",\n%s\n%s}"
                       indent pos indent' indent' (interval_to_string i) (f_to_json str_of indent' "" f) indent
  | Since (i, f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Since\",\n%s\"interval\": \"%s\",\n%s,\n%s\n%s}"
                         indent pos indent' indent' (interval_to_string i) (f_to_json str_of indent' "l" f) (f_to_json str_of indent' "r" g) indent
  | Until (i, f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Until\",\n%s\"interval\": \"%s\",\n%s,\n%s\n%s}"
                         indent pos indent' indent' (interval_to_string i) (f_to_json str_of indent' "l" f) (f_to_json str_of indent' "r" g) indent
  | _ -> ""
let f_to_json str_of = f_to_json str_of "    " ""
