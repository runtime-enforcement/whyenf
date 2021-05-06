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
  ; beta_alphas: (ts * expl) Deque.t
  (* deque of S^+ beta [alphas] outside of the interval *)
  ; beta_alphas_out: (ts * expl) Deque.t

  (* sorted list of S^- alpha [betas] *)
  ; alpha_betas: (ts * expl) Deque.t
  (* list of beta violation proofs *)
  ; betas_suffix_in: (ts * vexpl) list
  (* list of alpha/beta violations *)
  ; alphas_betas_out: (ts * vexpl option * vexpl option) list
  (* sorted list of alpha violations *)
  ; alphas_out: (ts * expl) Deque.t
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

(* progress * monitoring formula *)
type mstate = int * mformula

let cleared_msaux = { ts_zero = None
                    ; ts_in = []
                    ; ts_out = []
                    ; beta_alphas = Deque.create ()
                    ; beta_alphas_out = Deque.create ()
                    ; alpha_betas = Deque.create ()
                    ; betas_suffix_in = []
                    ; alphas_betas_out = []
                    ; alphas_out = Deque.create ()
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

(* Sort proofs wrt a particular measure, i.e., 
   if p1 < p2 in [p1, p2, p3, ..., pn] then p2
   must be removed (and so on) *)
let update_new_in le new_in =
  let rec aux ps acc =
    match ps with
    | [] -> acc
    | x::x'::xs ->
       if le (snd(x)) (snd(x')) then
         aux xs (x::acc)
       else aux xs (x'::acc)
    | x::xs -> x::acc
  in aux new_in []

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
      match sp with
      | S pf -> Deque.set_exn sps i (ts, S (sappend pf sp_f1))
      | V _ -> raise SEXPL)

let split_in_out r ps_out =
  Deque.fold ps_out ~init:[]
    ~f:(fun acc (ts, sp) ->
      if ts <= r then (
        Deque.drop_front ps_out;
        (ts, sp)::acc)
      else acc)

let remove_worse le ps_in new_in =
  let new_in' = update_new_in le new_in in
  let hd_p = List.hd_exn new_in' in
  Deque.iter ps_in ~f:(fun (ts, sp) ->
      if le (snd(hd_p)) sp then
        Deque.drop_back ps_in
      else ());
  List.iter new_in' ~f:(fun (ts, sp) ->
      Deque.enqueue_back ps_in (ts, sp))

let remove_old l ps_in =
  Deque.iter ps_in ~f:(fun (ts, sp) ->
      if ts <= l then
        Deque.drop_front ps_in)

let update_ssince (l, r) sp_f1 sp_f ts msaux le =
  add_to_sps_in_deque msaux.beta_alphas sp_f1;
  add_to_sps_in_deque msaux.beta_alphas_out sp_f1;
  Deque.enqueue_back msaux.beta_alphas_out (ts, sp_f);
  let new_in = split_in_out r msaux.beta_alphas_out in
  remove_worse le msaux.beta_alphas new_in;
  remove_old l msaux.beta_alphas

let remove_worse_alphas le ts alphas_out vp_f1 =
  Deque.iter alphas_out ~f:(fun (ts, vp) ->
      if le vp_f1 vp then
        Deque.drop_back alphas_out);
  Deque.enqueue_back alphas_out (ts, vp_f1)

(* let update_vsince (l, r) vp_f1 vp_f2 ts msaux le =
 *   let new_msaux = { msaux with
 *                     alphas_betas_out =
 *                       (ts, Some(vp_f1), Some(vp_f2)) :: alphas_betas_out
 *                   } in *)

(* let output_since msaux =
 *   let sp_in_opt = Deque.peek_front msaux.beta_alphas in
 *   if Option.is_some sp_in_opt then
 *     Option.value_exn sp_in_opt
 *   else
 *     let vp_in_opt = Deque.peek_front msaux.alpha_betas in
 *     if Option.is_some vp_in_opt then
 *       Option.value_exn vp_in_opt
 *     else *)
  
let update_since interval i ts p1 p2 msaux le minimum =
  let a = get_a_I interval in
  let last_ts_opt = get_last_ts msaux in
  (* Case 1: \tau_{i-1} does not exist *)
  if Option.is_none last_ts_opt then
    (* Update list of timestamps *)
    let new_msaux = { (update_ts a ts msaux) with ts_zero = Some(ts) } in
    let p = doSinceBase minimum i a p1 p2 in
    (* Update msaux *)
    (match p1, p2 with
     | S f1, S f2 ->
        (* Here we assume S^+ b [] < S^+ b [a] *)
        let sp = S (SSince (f2, [])) in
        Deque.enqueue_back new_msaux.beta_alphas (ts, sp);
        (if a <> 0 then Deque.enqueue_back new_msaux.beta_alphas_out (ts, sp));
        (p, new_msaux)
     
     | V f1, S f2 ->
        let sp = S (SSince (f2, [])) in
        Deque.enqueue_back new_msaux.beta_alphas (ts, sp);
        (if a <> 0 then Deque.enqueue_back new_msaux.beta_alphas_out (ts, sp));
        (p, new_msaux)
    
    | S f1, V f2 ->
        let vp = V (VSinceInf (i, [f2])) in
        Deque.enqueue_back new_msaux.alpha_betas (ts, vp);
        (p, { new_msaux with betas_suffix_in = [(ts, f2)];
                             alphas_betas_out = [(ts, None, Some(f2))]})
    
     | V f1, V f2 ->
        let vp = minimum (V (VSince (i, f1, [f2]))) (V (VSinceInf (i, [f2]))) in
        Deque.enqueue_back new_msaux.alpha_betas (ts, vp);
        Deque.enqueue_back new_msaux.alphas_out (ts, V f1);
        (p, { new_msaux with betas_suffix_in = [(ts, f2)];
                             alphas_betas_out = [(ts, Some(f1), Some(f2))] }))

  (* Case 2: \tau_{i-1} exists *)
  else
    let new_msaux = update_ts a ts msaux in
    let ts_zero = Option.value_exn msaux.ts_zero in
    let last_ts = Option.value_exn last_ts_opt in
    
    (* Case 2.1: \tau_{i} < \tau_{0} + a *)
    if ts < ts_zero + (get_a_I interval) then
      (V (VSinceOut i), { msaux with ts_out = [ts] })
    else
      let b = get_b_I ts_zero interval in
      let delta = ts - last_ts in
      (* Case 2.2: b < \Delta, i.e., last_ts lies outside of the interval *)
      if b < delta then
        let p = doSinceBase minimum i a p1 p2 in
        (p, cleared_msaux)
      (* Case 2.3: b >= \Delta *)
      else
        let l = ts - a in
        let r = ts - b in
        (* match p1, p2 with
         *  | S f1, S f2 ->
         *     let sp_f = S (SSince (f2, [f1])) in
         *     update_ssince (l, r) f1 (sp_f) ts new_msaux le;
         *     (\* TODO: Change output *\)
         *     (sp_f, new_msaux)
         *  | V f1 , S f2 ->
         *     let sp = S (SSince (f2, [])) in
         *     Deque.enqueue_back new_msaux.beta_alphas (ts, sp);
         *     if a = 0 then
         *       (sp, new_msaux)
         *     else
         *       (Deque.enqueue_back new_msaux.beta_alphas_out (ts, sp);
         *        (sp, new_msaux))
         *  | S f1, V f2 ->
         *  | V f1, V f2 ->  *)

let start_monitoring le =
  let minimum_list ps = minsize_list (get_mins le ps) in
  let minimum a b = minimum_list [a; b] in
  
  let rec meval i ts event mform =
    match mform with
    | MTT -> ([S (STT i)], MTT)
    | MFF -> ([V (VFF i)], MFF)
    | MP a ->
       let s = fst(event) in
       if SS.mem a s then ([S (SAtom (i, a))], MP a)
       else ([V (VAtom (i, a))], MP a)
    | MNeg (mf) ->
       let (expl_f, mf') = meval i ts event mf in
       let expl_z = List.map expl_f (fun e ->
                        match e with
                        | S e' -> V (VNeg e')
                        | V e' -> S (SNeg e')
                      ) in (expl_z, mf')
    | MConj (mf1, mf2, buf) ->
       let op e1 e2 = doConj minimum e1 e2 in
       let (expl_f1, mf1') = meval i ts event mf1 in
       let (expl_f2, mf2') = meval i ts event mf2 in
       let (expl_f, buf') = mbuf2_take op (mbuf2_add expl_f1 expl_f2 buf) in
       (expl_f, MConj (mf1', mf2', buf'))
    | MDisj (mf1, mf2, buf) ->
       let op e1 e2 = doDisj minimum e1 e2 in
       let (expl_f1, mf1') = meval i ts event mf1 in
       let (expl_f2, mf2') = meval i ts event mf2 in
       let (expl_f, buf') = mbuf2_take op (mbuf2_add expl_f1 expl_f2 buf) in
       let p = minimum_list expl_f in
       (p, MDisj (mf1', mf2', buf'))
    (* | MPrev (interval, mf, b, expl_lst, ts_d_lst) ->
     * | MNext (interval, mf, b, ts_a_lst) -> *)
    | MSince (interval, mf1, mf2, msaux) ->
       let (expl_f1, mf1') = meval i ts event mf1 in
       let (expl_f2, mf2') = meval i ts event mf2 in
       let p1 = minimum_list expl_f1 in
       let p2 = minimum_list expl_f2 in
       let (expl_f, new_msaux) = update_since interval i ts p1 p2 msaux le minimum in
       (expl_f, MSince (interval, mf1, mf2, msaux))
    (* | MUntil (interval, mf, mg, buf, ts_a_lst, muaux) -> *)
    | _ -> failwith "This formula cannot be monitored" in
  let mstep event mform =
    
