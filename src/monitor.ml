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

let mbuf2_add e1 e2 buf =
  (e1 @ fst(buf), e2 @ snd(buf))

let rec mbuf2_take f buf =
  let (e_l1, e_l2) = buf in
  match e_l1, e_l2 with
  | [], _ -> ([], buf)
  | _, [] -> ([], buf)
  | e1 :: e_l1', e2 :: e_l2' ->
     let (e_l3, buf') = mbuf2_take f (e_l1', e_l2') in
     ((f e1 e2) :: e_l3, buf') 

let rec meval minimum ts trace mform =
  match mform with
  (* | MTT ->
   * | MFF -> 
   * | MP (x) ->
   * | MNeg (mf) -> *)
  | MConj (mf, mg, buf) ->
     let f e1 e2 = doConj minimum e1 e2 in
     let (expl_f, mf') = meval minimum ts trace mf in
     let (expl_g, mg') = meval minimum ts trace mg in
     let (expl_z, buf') = mbuf2_take f (mbuf2_add expl_f expl_g buf) in
     (expl_z, MConj (mf', mg', buf'))
  | MDisj (mf, mg, buf) ->
     let f e1 e2 = doDisj minimum e1 e2 in
     let (expl_f, mf') = meval minimum ts trace mf in
     let (expl_g, mg') = meval minimum ts trace mg in
     let (expl_z, buf') = mbuf2_take f (mbuf2_add expl_f expl_g buf) in
     (expl_z, MDisj (mf', mg', buf'))
  (* | MPrev (i, mf, b, expl_lst, ts_d_lst) ->
   * | MNext (i, mf, b, ts_a_lst) ->
   * | MSince (i, mf, mg, buf, ts_d_lst, msaux) ->
   * | MUntil (i, mf, mg, buf, ts_a_lst, muaux) -> *)
  | _ -> failwith "This formula cannot be monitored"
