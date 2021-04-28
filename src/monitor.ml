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
open Core_kernel

type mbuf2 = expl list * expl list

type msaux = {
    ts_zero: ts option
  ; ts_in: ts list
  ; ts_out: ts list
    
    (* sorted deque of S^+ beta [alphas] *)
  ; beta_alphas: (ts * sexpl) Deque.t
    (* deque of S^+ beta [alphas] outside of the interval *)
  ; beta_alphas_out: (ts * sexpl) Deque.t

    (* sorted list of S^- alpha [betas] *)
  ; alpha_betas: (ts * vexpl) Deque.t
    (* list of beta violation proofs *)
  ; betas_suffix_in: (ts * vexpl) list
    (* list of beta/alpha violations *)
  ; betas_alphas_out: (ts * vexpl option * vexpl option) list
  ; }

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

let cleared_msaux = { ts_zero = None
                    ; ts_in = []
                    ; ts_out = []
                    ; beta_alphas = Deque.create ()
                    ; beta_alphas_out = Deque.create ()
                    ; alpha_betas = Deque.create ()
                    ; betas_suffix_in = []
                    ; betas_alphas_out = []
                    ; } 

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
     let msaux = cleared_msaux in
     MSince (i, minit f, minit g, msaux)
  | Until (i, f, g) ->
     MUntil (i, minit f, minit g, ([], []), [], [])
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

let get_last_ts msaux =
  match msaux.ts_in, msaux.ts_out with
  | [], [] -> None
  | _ , h::t -> Some (h)
  | h::t, [] -> Some (h)

(* Here we assume that storing timestamps in ascending order would 
   not be inconvenient *)
let update_ts a ts msaux =
  if a = 0 then
    { msaux with ts_in = ts::msaux.ts_in }
  else
    { msaux with ts_out = ts::msaux.ts_out }

(* This approach should be faster than other possible solutions *)
let add_to_sps_in_deque sps sp_f1 =
  Deque.iteri sps ~f:(fun i (ts, sp) ->
      Deque.set_exn sps i (ts, sappend sp sp_f1))

let split_in_out r ps_out =
  let new_in = 
    Deque.fold ps_out ~init:[]
    ~f:(fun acc (ts, sp) ->
      if ts <= r then (
        Deque.drop_front ps_out;
        (ts, sp)::acc)
      else acc) in
  List.rev new_in

(* let remove_worse minimum ps_in new_in =
 *   List.iter (fun (ts, sp) ->
 *       if (minimum q p) = p then
 *         remove_worse minimum qs p::ps
 *     ) new_in
 * 
 * let update_ssince ts msaux sp_f1 sp_f =
 *   add_to_sps_in_deque msaux.beta_alphas sp_f1;
 *   add_to_sps_in_deque msaux.beta_alphas_out sp_f1;
 *   Deque.enqueue_back msaux.beta_alphas_out (ts, sp_f);
 *   let new_in = split_in_out r msaux.beta_alphas_out in *)

let update_since minimum interval expl_f1 expl_f2 i ts msaux =
  let a = get_a_I interval in
  let last_ts_option = get_last_ts msaux in
  (* Case 1: \tau_{i-1} does not exist *)
  if Option.is_none last_ts_option then ( 
    (* Update list of timestamps *)
    let new_msaux = { (update_ts a ts msaux) with ts_zero = Some(ts) } in
     match expl_f1, expl_f2 with
     | S f1, S f2 ->
        let sp = SSince (f2, [f1]) in
        if a = 0 then 
          (Deque.enqueue_back new_msaux.beta_alphas (ts, sp); (S sp, new_msaux))
        else
          (Deque.enqueue_back new_msaux.beta_alphas (ts, sp);
           Deque.enqueue_back new_msaux.beta_alphas_out (ts, sp);
           (S sp, new_msaux))
     | _ -> failwith "soon")
  (* Case 2: \tau_{i-1} exists *)
  else
    let new_msaux = update_ts a ts msaux in
    let ts_zero = Option.value msaux.ts_zero ~default:0 in
    let last_ts = Option.value last_ts_option ~default:0 in
    (* Case 2.1: \tau_{i} < \tau_{0} + a *)
    if ts < ts_zero + (get_a_I interval) then
      (V (VSinceOut i), { msaux with ts_out = [ts] })
    else
      let b = get_b_I ts_zero interval in
      let delta = ts - last_ts in
      (* Case 2.2: b < \Delta, i.e., last_ts lies outside of the interval *)
      if b < delta then
        let p = doSinceBase minimum i a expl_f1 expl_f2 in
        (p, cleared_msaux)
      (* Case 2.3: b >= \Delta *)
      else
        let l = ts - a in
        let r = ts - b in
        (match expl_f1, expl_f2 with
         | S f1, S f2 ->
            let sp = sappend (SSince (f2, [])) f1 in
            (* let beta_alphas = update_beta_alphas in
             * let beta_alphas_out = update_beta_alphas_out in  *)
            (S sp, msaux)
         (* | S f1, V f2 ->
          * | V f1 , S f2 ->
          * | V f1, V f2 -> *)
         | _ -> failwith "soon")

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
     let expl_z = List.map expl_f (fun e ->
                    match e with
                    | S e' -> V (VNeg e')
                    | V e' -> S (SNeg e')
                  ) in (expl_z, mf')
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
