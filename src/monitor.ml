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

(* Auxiliary data structures *)
type mbuf2 = expl list * expl list

type expl_list = SEList of sexpl list | VEList of vexpl list

(* betas, alpha_betas and alphas are relevant for violations
 * alphas and beta_alphas are relevant for satisfactions     
 *)
type msaux =
  {
    ts_in: ts list;
    ts_out: ts list;
    betas_suffix_in: (ts * vexpl) list; (* list of beta violation proofs *)
    betas_out: (ts * vexpl) list option; (* list of beta violation proofs *)
    alpha_betas: (ts * vexpl) list; (* sorted list of S^- alpha [betas] *)
    beta_alphas_in: (ts * sexpl) list; (* sorted list of S^+ beta [alphas] *)
    beta_alphas_out: (ts * sexpl) list option; (* list of S^+ beta [alphas] *)
  }

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
  | MSince of interval * mformula * mformula * msaux
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
  | Since (i, f, g) ->
     let msaux = { ts_in = [];
                   ts_out = [];
                   betas_suffix_in = [];
                   betas_out = None;
                   alpha_betas = [];
                   beta_alphas_in = [];
                   beta_alphas_out = None;
                 } in MSince (i, minit f, minit g, msaux)
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

(* let update_since interval expl_f expl_g i ts msaux =
 *   let last_ts =
 *     match msaux.ts_in, msaux.ts_out with
 *     | [], [] -> None
 *     | [], h::t -> Some (fst(h))
 *     | h::t, [] -> Some (fst(h)) in
 *   (\* Case 1: \tau_{i-1} does not exist OR \Delta > b *\)
 *   if last_ts = None then *)

let rec meval minimum i ts event mform =
  match mform with
  | MTT -> ([S (STT i)], MTT)
  | MFF -> ([V (VFF i)], MFF)
  | MP a ->
     let s = fst(event) in
     if SS.mem a s then ([S (SAtom (i, a))], MP a)
     else ([V (VAtom (i, a))], MP a)
  | MNeg (mf) ->
     let (expl_f, mf') = meval minimum i ts event mf in
     let expl_z = List.map (fun e ->
                    match e with
                    | S e' -> V (VNeg e')
                    | V e' -> S (SNeg e')
                  ) expl_f in (expl_z, mf')
  | MConj (mf, mg, buf) ->
     let f e1 e2 = doConj minimum e1 e2 in
     let (expl_f, mf') = meval minimum i ts event mf in
     let (expl_g, mg') = meval minimum i ts event mg in
     let (expl_z, buf') = mbuf2_take f (mbuf2_add expl_f expl_g buf) in
     (expl_z, MConj (mf', mg', buf'))
  | MDisj (mf, mg, buf) ->
     let f e1 e2 = doDisj minimum e1 e2 in
     let (expl_f, mf') = meval minimum i ts event mf in
     let (expl_g, mg') = meval minimum i ts event mg in
     let (expl_z, buf') = mbuf2_take f (mbuf2_add expl_f expl_g buf) in
     (expl_z, MDisj (mf', mg', buf'))
  (* | MPrev (interval, mf, b, expl_lst, ts_d_lst) ->
   * | MNext (interval, mf, b, ts_a_lst) -> *)
  (* | MSince (interval, mf, mg, msaux) ->
   *    let (expl_f, mf') = meval minimum i ts event mf in
   *    let (expl_g, mg') = meval minimum i ts event mg in *)     
     
  (* | MUntil (interval, mf, mg, buf, ts_a_lst, muaux) -> *)
  | _ -> failwith "This formula cannot be monitored"

(* let optimal_proof w le =
 *   let minimum_list ps = minsize_list (get_mins le ps) in
 *   let minimum a b = minimum_list [a; b] in *)
