(*******************************************************************)
(*    This is part of Explanator2, it is distributed under the     *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl
open Expl
open Util
open Interval

type mbuf2 = expl list * expl list
type msaux = (ts * expl) list
type muaux = (ts * expl * expl) list

(* Formula state *) 
type mformula =
  | MTT
  | MFF
  | MP of string
  | MNeg of mformula
  | MConj of mformula * mformula * mbuf2
  | MDisj of mformula * mformula * mbuf2
  | MPrev of interval * mformula * bool * expl list * ts_desc_list
  | MNext of interval * mformula * bool * ts_asc_list
  | MSince of interval * mformula * mformula * mbuf2 * ts_desc_list * msaux
  | MUntil of interval * mformula * mformula * mbuf2 * ts_asc_list * muaux

type mstate = tp * mformula

(* Convert a formula into a formula state *)
let rec minit f =
  match (value f) with
  | TT -> MTT
  | FF -> MFF
  | P (x) -> MP (x)
  | Neg (f) -> MNeg (minit f)
  | Conj (f, g) -> MConj (minit f, minit g, ([], []))
  | Disj (f, g) -> MDisj (minit f, minit g, ([], []))
  | Prev (i, f) -> MPrev (i, minit f, true, [], [])
  | Next (i, f) -> MNext (i, minit f, true, [])
  | Since (i, f, g) -> MSince (i, minit f, minit g, ([], []), [], [])
  | Until (i, f, g) -> MUntil (i, minit f, minit g, ([], []), [], [])
  | _ -> failwith "This formula cannot be monitored"

let mbuf2_add expl_lst1 expl_lst2 (b1, b2) =
  (expl_lst1 @ b1, expl_lst2 @ b2)

(* let mbuf2_take f (b1, b2) =
 *   
 * 
 * let rec meval ts trace mform =
 *   match mform with
 *   | MNeg (mf) -> 
 *   | MAnd (mf, mg, buf) -> 
 *   | MOr (mf, mg, buf) ->
 *   | MPrev (i, mf, b, expl_lst, ts_d_lst) ->
 *   | MNext (i, mf, b, ts_a_lst) ->
 *   | MSince (i, mf, mg, buf, ts_d_lst, msaux) ->
 *   | MUntil (i, mf, mg, buf, ts_a_lst, muaux) -> *)
