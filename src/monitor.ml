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
    (* list of beta violation proofs *)
    betas_suffix_in: (ts * vexpl) list; 
    (* list of beta violation proofs *)
    betas_out: (ts * vexpl option) list;
    (* sorted list of S^- alpha [betas] *)
    alpha_betas: (ts * vexpl) list;
    (* sorted list of S^+ beta [alphas] *)
    beta_alphas_in: (ts * sexpl) list;
    (* list of S^+ beta [alphas] *)
    beta_alphas_out: (ts * sexpl option) list;
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
                   betas_out = [];
                   alpha_betas = [];
                   beta_alphas_in = [];
                   beta_alphas_out = [];
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

(* let update_since minimum interval expl_f1 expl_f2 i ts msaux =
 *   let last_ts =
 *     match msaux.ts_in, msaux.ts_out with
 *     | [], [] -> None
 *     | _ , h::t -> Some (h)
 *     | h::t, [] -> Some (h) in
 *   let a = get_a_I interval in
 *   (\* Case 1: \tau_{i-1} does not exist *\)
 *   if last_ts = None then
 *     let p = doSinceBase minimum i a expl_f1 expl_f2 in
 *     (match expl_f1, expl_f2 with
 *      | V _ , V f2 ->
 *         (\* alpha_betas = [(ts, ~α, [~β])] *\)
 *         if where_I ts interval = Inside then
 *           (p, { msaux with alpha_betas = [(ts, p)] })
 *         (\* betas_out = [(ts, Some(~β)] *\)
 *         else (p, { msaux with betas_out = [(ts, Some (f2))] })
 *      | S _ , V _ ->
 *         (\* betas_suffix_in = [(ts, ~β)] *\)
 *         if where_I ts interval = Inside then
 *           (p, { msaux with betas_suffix_in = [(ts, f2)] })
 *         (\* betas_out = [(ts, Some(~β))] *\)
 *         else (p, { msaux with betas_out = [(ts, Some (f2))] }) 
 *      | V f1 , S f2 ->
 *         (\* betas_alphas_in = [(ts, β)] *\)
 *         if where_I ts interval = Inside then
 *           (p, { msaux with betas_alphas_in = [(ts, f2)] })
 *         else (p, msaux)
 *      | S f1 , S f2 -> (p, msaux))
 *   (\* Case 2: \tau_{i-1} does exist *\)
 *   else
 *     let delta = ts - last_ts in
 *     (\* Case 2.1: \Delta > b, i.e., last_ts is outside interval *\)
 *     if delta > get_b_I interval then
 *       let p = doSinceBase minimum i a expl_f1 expl_f2 in
 *       (p, msaux)
 *     (\* Case 2.2: \Delta <= b *\)
 *     else *)      

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
  | MConj (mf1, mf2, buf) ->
     let op e1 e2 = doConj minimum e1 e2 in
     let (expl_f1, mf1') = meval minimum i ts event mf1 in
     let (expl_f2, mf2') = meval minimum i ts event mf2 in
     let (expl_f, buf') = mbuf2_take op (mbuf2_add expl_f1 expl_f2 buf) in
     (expl_f, MConj (mf1', mf2', buf'))
  | MDisj (mf1, mf2, buf) ->
     let op e1 e2 = doDisj minimum e1 e2 in
     let (expl_f1, mf1') = meval minimum i ts event mf1 in
     let (expl_f2, mf2') = meval minimum i ts event mf2 in
     let (expl_f, buf') = mbuf2_take op (mbuf2_add expl_f1 expl_f2 buf) in
     (expl_f, MDisj (mf1', mf2', buf'))
  (* | MPrev (interval, mf, b, expl_lst, ts_d_lst) ->
   * | MNext (interval, mf, b, ts_a_lst) -> *)
  (* | MSince (interval, mf1, mf2, msaux) ->
   *    let (expl_f1, mf1') = meval minimum i ts event mf1 in
   *    let (expl_f2, mf2') = meval minimum i ts event mf2 in *)
     
     
  (* | MUntil (interval, mf, mg, buf, ts_a_lst, muaux) -> *)
  | _ -> failwith "This formula cannot be monitored"

(* let optimal_proof w le =
 *   let minimum_list ps = minsize_list (get_mins le ps) in
 *   let minimum a b = minimum_list [a; b] in *)
