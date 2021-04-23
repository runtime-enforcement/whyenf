(*******************************************************************)
(*    This is part of Explanator2, it is distributed under the     *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Core_kernel
open Mtl
open Expl
open Util
open Interval

(* Auxiliary data structures *)
type mbuf2 = expl list * expl list

type expl_list = SEList of sexpl list | VEList of vexpl list

type msaux =
  {
    ts_zero: ts option;
    ts_in: ts list;
    ts_out: ts list;
    
    (* sorted list of S^+ beta [alphas] inside of the interval *)
    beta_alphas_in: (ts * sexpl) Deque.t;
    (* list of S^+ beta [alphas] outside of the interval *)
    beta_alphas_out: (ts * sexpl) list;

    (* sorted list of S^- alpha [betas] *)
    alpha_betas: (ts * vexpl) list;
    (* list of beta violation proofs *)
    betas_suffix_in: (ts * vexpl) list;
    (* list of beta/alpha violations *)
    betas_alphas_out: (ts * vexpl option) list;
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
  | MPrev of interval * mformula * bool * expl list * ts list
  | MNext of interval * mformula * bool * ts list
  | MSince of interval * mformula * mformula * msaux
  | MUntil of interval * mformula * mformula * mbuf2 * ts list * muaux

type mstate = tp * mformula

let cleared_msaux = { ts_zero = None;
                      ts_in = [];
                      ts_out = [];
                      beta_alphas_in = Deque.create ();
                      beta_alphas_out = [];
                      alpha_betas = [];
                      betas_suffix_in = [];
                      betas_alphas_out = [];
                    } 

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
  | Since (i, f, g) -> let msaux = cleared_msaux in
                       MSince (i, minit f, minit g, msaux)
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
 *   let a = get_a_I interval in
 *   let last_ts =
 *     match msaux.ts_in, msaux.ts_out with
 *     | [], [] -> None
 *     | _ , h::t -> Some (h)
 *     | h::t, [] -> Some (h) in
 *   (\* Case 1: \tau_{i-1} does not exist *\)
 *   if last_ts = None then
 *     (\* Update timestamps *\)
 *     let msaux' = if a = 0 then { msaux with ts_zero = Some(ts); ts_in = [ts] }
 *                  else { msaux with ts_zero = Some(ts); ts_out = [ts] } in
 *     let p = doSinceBase minimum i a expl_f1 expl_f2 in
 *     (match expl_f1, expl_f2 with
 *      | V _ , V f2 ->
 *         (\* alpha_betas = [(ts, ~α, [~β])] and betas_suffix_in = [(ts, ~β)] *\)
 *         (p, { msaux' with alpha_betas = [(ts, unV p)]; betas_suffix_in = [(ts, f2)] })
 *      | S _ , V f2 ->
 *         (\* betas_suffix_in = [(ts, ~β)] *\)
 *         (p, { msaux' with betas_suffix_in = [(ts, f2)] })
 *      | _ , S f2 ->
 *         (\* betas_alphas_in = [(ts, β)] *\)
 *         (p, { msaux' with beta_alphas_in = [(ts, f2)] }))
 *   (\* Case 2: \tau_{i-1} exists *\)
 *   else
 *     (\* Case 2.1: \tau_{i} < \tau_{0} + a *\)
 *     if ts < (Option.get msaux.ts_zero) + (get_a_I interval) then
 *       (V (VSinceOut i), { msaux with ts_out = [ts] })
 *     else
 *       let b = match get_b_I interval with
 *         | None -> (Option.get msaux.ts_zero)
 *         | Some(x) -> x in
 *       let delta = ts - (Option.get last_ts) in
 *       (\* Case 2.2: b < \Delta, i.e., last_ts lies outside of the interval *\)
 *       if b < delta then
 *         let p = doSinceBase minimum i a expl_f1 expl_f2 in
 *         (\* TODO: Check if returning cleared_msaux here is correct *\)
 *         (p, cleared_msaux)
 *       (\* Case 2.3: b >= \Delta *\)
 *       else
 *         (\* TODO: Complexity of @ operator is O(n) so this approach 
 *          * might need to be optimized *\)
 *         let ts_all = msaux.ts_in @ msaux.ts_out @ [ts] in
 *         let ltp = get_ltp (ts - a) ts_all in
 *         let etp = get_etp ltp (ts - b) ts_all in
 *         (\* TODO: Check if ltp and etp are None *\)
 *         let l = min i (Option.get ltp) in
 *         let e = Option.get etp in
 *         (match expl_f1, expl_f2 with
 *          | S f1, S f2 ->
 *             let sp = (ts, SSince (f2, [f1])) in
 *             let new_in, b_a_out = split_in_out l ts_all [] (sp::msaux.beta_alphas_out) in
 *             let b_a_in = remove_out_and_worse minimum e msaux.beta_alphas_in new_in in
 *             let msaux' = { msaux with beta_alphas_in = b_a_in;
 *                                       beta_alphas_out = b_a_out } in
 *             let p = sappend (SSince (f2, [])) f1 in
 *             (p, { msaux' with alpha_betas = [(ts, unV p)]; betas_suffix_in = [(ts, f2)] })
 *          (\* | S f1, V _ ->
 *           * | V _ , S f2 ->
 *           * | V f1, V f2 -> *\)
 *          | _ -> let p = doSinceBase minimum i a expl_f1 expl_f2 in (p, cleared_msaux) *)

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

(* let minsize a b = if size a <= size b then a else b
 * let minsize_list = function
 *   | [] -> failwith "empty list for minsize_list"
 *   | x::xs -> List.fold_left minsize x xs
 * 
 * let optimal_proof w le =
 *   let minimum_list ps = minsize_list (get_mins le ps) in
 *   let minimum a b = minimum_list [a; b] in *)
