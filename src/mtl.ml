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
open Hashcons

(* hash-consing related *)
let hash x = x.hkey
let head x = x.node

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
(* propositional operators *)
let neg f = hashcons (Neg f)
let conj f g = hashcons (Conj (f, g))
let disj f g = hashcons (Disj (f, g))
let impl f g = hashcons (Impl (f, g))
let iff f g = hashcons (Iff (f, g))
(* temporal operators *)
let prev i f = hashcons (Prev (i, f))
let next i f = hashcons (Next (i, f))
let once i f = hashcons (Once (i, f))
let historically i f = hashcons (Historically (i, f))
let always i f = hashcons (Always (i, f))
let eventually i f = hashcons (Eventually (i, f))
let since i f g = hashcons (Since (i, f, g))
let until i f g = hashcons (Until (i, f, g))
let release i f g = neg (until i (neg f) (neg g))
let weak_until i f g = release i g (disj f g)
let trigger i f g = neg (since i (neg f) (neg g))

let rec atoms x = match x.node with
  | TT | FF -> []
  | P x -> [x]
  (* propositional operators *)
  | Neg f -> atoms f
  | Conj (f1, f2) | Disj (f1, f2)
  | Impl (f1, f2) | Iff (f1, f2) -> List.sort_uniq String.compare (List.append (atoms f1) (atoms f2))
  (* temporal operators *)
  | Next (i, f) | Always (i, f) | Eventually (i, f)
  | Prev (i, f) | Once (i, f) | Historically (i, f) -> atoms f
  | Until (i, f1, f2) | Since (i, f1, f2) ->
     List.sort_uniq String.compare (List.append (atoms f1) (atoms f2))
