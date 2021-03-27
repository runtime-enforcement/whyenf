(*******************************************************************)
(*    This is part of Explanator2, it is distributed under the     *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util
open Expl
open Interval
open Hashcons

(* MTL formulas *)
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

(* Hash-consing related *)
let hash x = x.hkey
let value x = x.node

(* Word: finite string of letters *)
(* Check what would be better (string list or string) *)
type word = string list

let m = Hashcons.create 271

let hashcons =
  let hash = function
    | TT -> Hashtbl.hash 1
    | FF -> Hashtbl.hash 0
    | P x -> Hashtbl.hash x
    | Neg f -> Hashtbl.hash (2, f.hkey)
    | Conj (f, g) -> Hashtbl.hash (3, f.hkey, g.hkey)
    | Disj (f, g) -> Hashtbl.hash (5, f.hkey, g.hkey)
    | Impl (f, g) -> Hashtbl.hash (37, f.hkey, g.hkey)
    | Iff (f, g) -> Hashtbl.hash (41, f.hkey, g.hkey)
    | Prev (i, f) -> Hashtbl.hash (7, f.hkey)
    | Once (i, f) -> Hashtbl.hash (11, f.hkey)
    | Historically (i, f) -> Hashtbl.hash (13, f.hkey)
    | Since (i, f, g) -> Hashtbl.hash (17, f.hkey, g.hkey)
    | Next (i, f) -> Hashtbl.hash (19, f.hkey)
    | Always (i, f) -> Hashtbl.hash (23, f.hkey)
    | Eventually (i, f) -> Hashtbl.hash (29, f.hkey)
    | Until (i, f, g) -> Hashtbl.hash (31, f.hkey, g.hkey) in
  let equal x y = match x, y with
    | TT, TT -> true
    | P x, P y -> x = y
    | Neg f, Neg f' -> f == f'
    | Conj (f, g), Conj (f', g') | Disj (f, g), Disj (f', g')
    | Impl (f, g), Impl (f', g') | Iff (f, g), Iff (f', g') -> f == f' && g == g'
    | Prev (i, f), Prev (i', f') | Next (i, f), Next (i', f')
    | Once (i, f), Once (i', f') | Historically (i, f), Historically (i', f')
    | Always (i, f), Always (i', f') | Eventually (i, f), Eventually (i', f') -> i == i' && f == f'
    | Since (i, f, g), Since (i', f', g') | Until (i, f, g), Until (i', f', g') -> i == i' && f == f' && g == g'
    | _ -> false in
  Hashcons.hashcons hash equal m

let tt = hashcons TT
let ff = hashcons FF
let p x = hashcons (P x)

(* Propositional operators *)
let neg f = hashcons (Neg f)
let conj f g = hashcons (Conj (f, g))
let disj f g = hashcons (Disj (f, g))
let impl f g = hashcons (Impl (f, g))
let iff f g = hashcons (Iff (f, g))

(* Temporal operators *)
let prev i f = hashcons (Prev (i, f))
let next i f = hashcons (Next (i, f))
let once i f = hashcons (Once (i, f))
let historically i f = hashcons (Historically (i, f))
let always i f = hashcons (Always (i, f))
let eventually i f = hashcons (Eventually (i, f))
let since i f g = hashcons (Since (i, f, g))
let until i f g = hashcons (Until (i, f, g))

(* TODO: operators defined in terms of others must be rewritten *)
let release i f g = neg (until i (neg f) (neg g))
let weak_until i f g = release i g (disj f g)
let trigger i f g = neg (since i (neg f) (neg g))

let rec atoms x = match x.node with
  | TT | FF -> []
  | P x -> [x]
  (* Propositional operators *)
  | Neg f -> atoms f
  | Conj (f1, f2) | Disj (f1, f2)
  | Impl (f1, f2) | Iff (f1, f2) -> List.sort_uniq String.compare (List.append (atoms f1) (atoms f2))
  (* Temporal operators *)
  | Next (i, f) | Always (i, f) | Eventually (i, f)
  | Prev (i, f) | Once (i, f) | Historically (i, f) -> atoms f
  | Until (i, f1, f2) | Since (i, f1, f2) ->
     List.sort_uniq String.compare (List.append (atoms f1) (atoms f2))

(* let mem_word w i c =
 *   if i < List.length w
 *   then List.mem c (List.nth w i)
 *   else invalid_arg "List.mem" *)

(***********************************
 *                                 *
 * wqo: Height                     *
 *                                 *
 ***********************************)

(* Past height *)
let rec hp x = match x.node with
  | TT | FF | P _ -> 0
  | Neg f -> hp f
  | Conj (f1, f2) | Disj (f1, f2)
  | Impl (f1, f2) | Iff (f1, f2) -> max (hp f1) (hp f2)
  | Until (i, f1, f2) -> max (hp f1) (hp f2)
  | Next (i, f) | Always (i, f) | Eventually (i, f) -> hp f
  | Prev (i, f) | Once (i, f) | Historically (i, f) -> hp f + 1
  | Since (i, f1, f2) -> max (hp f1) (hp f2) + 1

(* Future height *)
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

(***********************************
 *                                 *
 * wqo: Size                       *
 *                                 *
 ***********************************)

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
  | VPrev0 -> 1
  | VPrevB i -> 1
  | VPrevA i -> 1
  | VPrev vphi -> 1 + v_size vphi
  | VOnce expls -> 1 + sum v_size expls
  | VHistorically (i, expl) -> 1 + v_size expl
  | VNextB i -> 1
  | VNextA i -> 1
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

(***********************************
 *                                 *
 * Algorithm: Computing optimal    *
 *            proofs               *
 *                                 *
 ***********************************)

let doDisj minimum expl_f1 expl_f2 =
  match expl_f1, expl_f2 with
  | S f1, S f2 -> minimum (S (SDisjL (f1))) (S (SDisjR(f2)))
  | S f1, V _ -> S (SDisjL (f1))
  | V _, S f2 -> S (SDisjR (f2))
  | V f1, V f2 -> V (VDisj (f1, f2))

let doConj minimum expl_f1 expl_f2 =
  match expl_f1, expl_f2 with
  | S f1, S f2 -> S (SConj (f1, f2))
  | S _, V f2 -> V (VConjR (f2))
  | V f1, S _ -> V (VConjL (f1))
  | V f1, V f2 -> minimum (V (VConjL (f1))) (V (VConjR (f2)))

let doPrev minimum i interval ts expl =
  match expl, where_I ts interval with
  | S _ , Below -> V (VPrevB (i))
  | S f , Inside -> S (SPrev (f))
  | S _ , Above -> V (VPrevA (i))
  | V f , Below -> minimum (V (VPrev (f))) (V (VPrevB (i)))
  | V f , Inside -> V (VPrev (f))
  | V f , Above -> minimum (V (VPrev (f))) (V (VPrevA (i)))

let doNext minimum i interval ts expl =
  match expl, where_I ts interval with
  | S _ , Below -> V (VNextB (i))
  | S f , Inside -> S (SNext (f))
  | S _ , Above -> V (VNextA (i))
  | V f , Below -> minimum (V (VNext (f))) (V (VNextB (i)))
  | V f , Inside -> V (VNext (f))
  | V f , Above -> minimum (V (VNext (f))) (V (VNextA (i)))
