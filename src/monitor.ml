(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl
open Expl
open Util
open Interval

module Deque = Core_kernel.Deque
module List = Core_kernel.List

type mbuf2 = expl list * expl list

type msaux = {
    ts_zero: ts option
  ; ts_in: ts list
  ; ts_out: ts list
    
  (* sorted deque of S^+ beta [alphas] *)
  ; beta_alphas: (ts * expl) Deque.t
  (* deque of S^+ beta [alphas] outside of the interval *)
  ; beta_alphas_out: (ts * expl) Deque.t
    
  (* sorted deque of S^- alpha [betas] *)
  ; alpha_betas: (ts * expl) Deque.t
  (* sorted deque of alpha proofs *)
  ; alphas_out: (ts * vexpl) Deque.t
  (* list of beta violations inside the interval*)
  ; betas_suffix_in: (ts * vexpl) Deque.t
  (* list of alpha/beta violations *)
  ; alphas_betas_out: (ts * vexpl option * vexpl option) Deque.t
  ; }

(* type muaux = {
 *     alphas_beta: ((ts * expl) list) Deque.t
 *   ; 
 *   } *)

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
  (* | MUntil of interval * mformula * mformula * mbuf2 * ts list * muaux *)

type progress = int

type mstate = progress * mformula

let cleared_msaux = { ts_zero = None
                    ; ts_in = []
                    ; ts_out = []
                    ; beta_alphas = Deque.create ()
                    ; beta_alphas_out = Deque.create ()
                    ; alpha_betas = Deque.create ()
                    ; alphas_out = Deque.create ()
                    ; betas_suffix_in = Deque.create ()
                    ; alphas_betas_out = Deque.create ()
                    ; } 

(* Convert formula into a formula state *)
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
  (* | Until (i, f, g) ->
   *    MUntil (i, minit f, minit g, ([], []), [], []) *)
  | _ -> failwith "This formula cannot be monitored"

(* mbuf2: auxiliary data structure for the conj/disj operators *)
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

(* ts update functions *)
let get_last_ts msaux =
  match msaux.ts_in, msaux.ts_out with
  | [], [] -> None
  | _ , h::t -> Some (h)
  | h::t, [] -> Some (h)

let add_first_ts a ts msaux =
  if a = 0 then
    { msaux with
      ts_zero = Some(ts)
    ; ts_in = [ts] }
  else
    { msaux with
      ts_zero = Some(ts)
    ; ts_out = [ts] }

let update_ts (l, r) a ts msaux =
  if a = 0 then
    let new_ts_in =
      List.drop_while msaux.ts_in
        ~f:(fun ts' -> ts' < l) in
    { msaux with ts_in = ts::new_ts_in }
  else
    let new_in =
      List.take_while msaux.ts_out
        ~f:(fun ts' -> ts' <= r) in
    let new_ts_out =
      List.drop_while msaux.ts_out
        ~f:(fun ts' -> ts' <= r) in
    let new_ts_in =
      List.drop_while msaux.ts_in
        ~f:(fun ts' -> ts' < l) in
    { msaux with
      ts_in = new_in @ new_ts_in
    ; ts_out = ts::new_ts_out }

exception VEXPL
exception SEXPL

(* This approach should be faster than other possible solutions *)
let add_to_beta_alphas msaux sp_f1 =
  Deque.iteri msaux.beta_alphas ~f:(fun i (ts, sp) ->
      match sp with
      | S pf -> Deque.set_exn msaux.beta_alphas i (ts, S (sappend pf sp_f1))
      | V _ -> raise SEXPL)

(* Resulting list is in ascending order, e.g.,
   d = [(1, p_1), (2, p_2), ..., (n, p_n)]
   l = [(n, p_n), ...]  *)
let split_in_out_beta_alphas_out msaux r =
  Deque.fold msaux.beta_alphas_out ~init:[]
    ~f:(fun acc (ts, sp) ->
      if ts <= r then (
        Deque.drop_front msaux.beta_alphas_out;
        (ts, sp)::acc)
      else acc)

(* Sort proofs wrt a particular measure, i.e., 
   if |p_1| < |p_2| in [p_1, p_2, p_3, ..., p_n] 
   then p_2 must be removed (and so on).
   The order of resulting list is reversed, which
   means that the smallest element is also the head. *)
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

let update_beta_alphas msaux le new_in =
  let new_in' = update_new_in le new_in in
  let hd_p = List.hd_exn new_in' in
  Deque.iter msaux.beta_alphas ~f:(fun (ts, sp) ->
      if le (snd(hd_p)) sp then
        Deque.drop_back msaux.beta_alphas);
  List.iter new_in' ~f:(fun (ts, sp) ->
      Deque.enqueue_back msaux.beta_alphas (ts, sp))

let remove_old_beta_alphas msaux l =
  Deque.iter msaux.alpha_betas
    ~f:(fun (ts, sp) ->
      if ts <= l then
        Deque.drop_front msaux.alpha_betas)

let update_ssince (l, r) sp_f1 sp_f ts msaux le =
  let _ = add_to_beta_alphas msaux sp_f1 in
  let _ = Deque.enqueue_back msaux.beta_alphas_out (ts, sp_f) in
  let new_in = split_in_out_beta_alphas_out msaux r in
  let _ = update_beta_alphas msaux le new_in in
  remove_old_beta_alphas msaux l

(* let add_to_vps_in_deque vps vp_f2 =
 *   Deque.iteri vps ~f:(fun i (ts, vp) ->
 *       match vp with
 *       | V pf -> Deque.set_exn vps i (ts, V (vappend pf vp_f2))
 *       | S _ -> raise VEXPL) *)

let add_alpha_v msaux le ts vp_f1 =
  Deque.iter msaux.alphas_out ~f:(fun (ts, vp) ->
      if le vp_f1 vp then
        Deque.drop_back msaux.alpha_betas);
  Deque.enqueue_back msaux.alphas_out (ts, vp_f1)

let split_in_out_alphas_betas_out msaux r =
  Deque.fold msaux.alphas_betas_out ~init:[]
    ~f:(fun acc (ts, vp_f1, vp_f2) ->
      if ts <= r then (
        Deque.drop_front msaux.beta_alphas_out;
        (ts, vp_f1, vp_f2)::acc)
      else acc)

let remove_old_alpha_betas msaux l =
  Deque.iter msaux.alpha_betas
    ~f:(fun (ts, _) ->
      if ts <= l then
        Deque.drop_front msaux.alpha_betas)

let remove_old_betas_suffix_in msaux l =
  Deque.iter msaux.betas_suffix_in
    ~f:(fun (ts, _) ->
      if ts <= l then
        Deque.drop_front msaux.betas_suffix_in)

(* let update_vsince (l, r) vp_f1 vp_f2 vp_f ts msaux le =
 *   let _ = add_alpha_v msaux le ts vp_f1 in
 *   let _ = Deque.enqueue_back msaux.alphas_betas_out (ts, Some(vp_f1), Some(vp_f2)) in
 *   let new_in = split_in_out_alphas_betas_out msaux r in
 *   let _ = remove_old_alpha_betas msaux l in
 *   let _ = remove_old_betas_suffix_in msaux l in
 *   
 * 
 *   
 *   let _ = Deque.enqueue_back msaux.betas_suffix_in msaux vp_f2 in
 *   add_to_vps_in_deque msaux.alpha_betas vp_f2;
 *   add_to_vps_in_deque msaux.alpha_betas_out vp_f2;
 *   Deque.enqueue_back msaux.alpha_betas_out vp_f;
 *   let new_msaux = {
 *       msaux with
 *       alphas_betas_out = (ts, Some(vp_f1), Some(vp_f2))::msaux.alphas_betas_out
 *     } in
 *   let betas_in, alphas_betas_out = split_in_out_list r msaux.alphas_betas_out in
 *   let new_in = split_in_out_deque r msaux.alpha_betas_out in *)

let betas_suffix_in_to_list betas_suffix_in =
  Deque.fold' betas_suffix_in ~init:[]
    ~f:(fun acc (ts, vp) -> vp::acc) `back_to_front

let output minimum msaux i =
  if not (Deque.is_empty msaux.beta_alphas) then
    snd(Deque.peek_front_exn msaux.beta_alphas)
  else 
    if (Deque.length msaux.betas_suffix_in) = (List.length msaux.ts_in) then (
      let beta_suffix = betas_suffix_in_to_list msaux.betas_suffix_in in
      let p1 = V (VSinceInf (i, beta_suffix)) in
      if not (Deque.is_empty msaux.alpha_betas) then (
        let p2 = snd(Deque.peek_front_exn msaux.alpha_betas) in
        minimum p1 p2)
      else p1)
    else failwith "Cannot output satisfaction/violation proof"
  
let update_since interval i ts p1 p2 msaux le minimum =
  let a = get_a_I interval in
  let last_ts_opt = get_last_ts msaux in
  (* Case 1: \tau_{i-1} does not exist *)
  if Option.is_none last_ts_opt then
    (* Update list of timestamps *)
    let new_msaux = add_first_ts a ts msaux in
    let p = doSinceBase minimum i a p1 p2 in
    (* Update msaux *)
    (match p1, p2 with
     | S f1, S f2 ->
        Deque.enqueue_back new_msaux.beta_alphas (ts, p);
        (if a <> 0 then Deque.enqueue_back new_msaux.beta_alphas_out (ts, p));
        (p, new_msaux)
     | V f1, S f2 ->
        Deque.enqueue_back new_msaux.beta_alphas (ts, p);
        (if a <> 0 then Deque.enqueue_back new_msaux.beta_alphas_out (ts, p));
        (p, new_msaux)
    | S f1, V f2 ->
       Deque.enqueue_back new_msaux.alpha_betas (ts, p);
       Deque.enqueue_back new_msaux.betas_suffix_in (ts, f2);
       Deque.enqueue_back new_msaux.alphas_betas_out (ts, None, Some(f2));
       (p, new_msaux)
    | V f1, V f2 ->
       Deque.enqueue_back new_msaux.alpha_betas (ts, p);
       Deque.enqueue_back new_msaux.betas_suffix_in (ts, f2);
       Deque.enqueue_back new_msaux.alphas_betas_out (ts, Some(f1), Some(f2));
       (p, new_msaux))
  (* Case 2: \tau_{i-1} exists *)
  else
    let ts_zero = Option.get msaux.ts_zero in
    let last_ts = Option.get last_ts_opt in
    let b = get_b_I ts_zero interval in
    (* TODO: Fix l and r, we should consider the type of the interval *)
    let l = ts - a in
    let r = ts - b in
    let new_msaux = update_ts (l, r) a ts msaux in
    (* Case 2.1: \tau_{i} < \tau_{0} + a *)
    if ts < ts_zero + a then
      let p = V (VSinceOutL i) in
      (p, { new_msaux with ts_out = [ts] })
    else
      let delta = ts - last_ts in
      (* Case 2.2: b < \Delta, i.e., last_ts lies outside of the interval *)
      if b < delta then
        let p = doSinceBase minimum i a p1 p2 in
        (p, cleared_msaux)
      (* Case 2.3: b >= \Delta *)
      else
        match p1, p2 with
         | S f1, S f2 ->
            let sp_f = S (SSince (f2, [f1])) in
            let _ = update_ssince (l, r) f1 sp_f ts new_msaux le in
            let o = output minimum new_msaux i in
            (o, new_msaux)
         | V f1 , S f2 ->
            let new_msaux = { new_msaux with beta_alphas = Deque.create ();
                                             beta_alphas_out = Deque.create () } in
            let o = output minimum new_msaux i in
            (o, new_msaux)
         (* | S f1, V f2 ->
          * | V f1, V f2 ->
          *    let vp_f = V (VSince (i, f1, [f2])) in *)
         | _ -> failwith "soon"
  
let rec meval i ts event mform minimum =
    match mform with
    | MTT -> ([S (STT i)], MTT)
    | MFF -> ([V (VFF i)], MFF)
    | MP a ->
       let s = fst(event) in
       if SS.mem a s then ([S (SAtom (i, a))], MP a)
       else ([V (VAtom (i, a))], MP a)
    | MNeg (mf) ->
       let (expl_f, mf') = meval i ts event mf minimum in
       let expl_z = List.map expl_f (fun e ->
                        match e with
                        | S e' -> V (VNeg e')
                        | V e' -> S (SNeg e')
                      ) in (expl_z, mf')
    | MConj (mf1, mf2, buf) ->
       let op e1 e2 = doConj minimum e1 e2 in
       let (expl_f1, mf1') = meval i ts event mf1 minimum in
       let (expl_f2, mf2') = meval i ts event mf2 minimum in
       let (expl_f, buf') = mbuf2_take op (mbuf2_add expl_f1 expl_f2 buf) in
       (expl_f, MConj (mf1', mf2', buf'))
    | MDisj (mf1, mf2, buf) ->
       let op e1 e2 = doDisj minimum e1 e2 in
       let (expl_f1, mf1') = meval i ts event mf1 minimum in
       let (expl_f2, mf2') = meval i ts event mf2 minimum in
       let (expl_f, buf') = mbuf2_take op (mbuf2_add expl_f1 expl_f2 buf) in
       (expl_f, MDisj (mf1', mf2', buf'))
    (* | MPrev (interval, mf, b, expl_lst, ts_d_lst) ->
     * | MNext (interval, mf, b, ts_a_lst) -> *)
    (* | MSince (interval, mf1, mf2, msaux) ->
     *    let (expl_f1, mf1') = meval i ts event mf1 in
     *    let (expl_f2, mf2') = meval i ts event mf2 in
     *    let p1 = minimum_list expl_f1 in
     *    let p2 = minimum_list expl_f2 in
     *    let (expl_f, new_msaux) = update_since interval i ts p1 p2 msaux le minimum in
     *    (expl_f, MSince (interval, mf1, mf2, msaux)) *)
    (* | MUntil (interval, mf, mg, buf, ts_a_lst, muaux) -> *)
    | _ -> failwith "This formula cannot be monitored"

(* let monitor le f =
 *   let minimum_list ps = minsize_list (get_mins le ps) in
 *   let minimum a b = minimum_list [a; b] in *)
  (* timepoint variable i must be updated at each meval call *)
  
