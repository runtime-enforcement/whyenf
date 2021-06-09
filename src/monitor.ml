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
open Channel
open Interval

module Deque = Core_kernel.Deque
module List = Core_kernel.List

type mbuf2 = expl list * expl list

type msaux = {
    ts_zero: timestamp option
  ; ts_in: timestamp list
  ; ts_out: timestamp list
    
  (* sorted deque of S^+ beta [alphas] *)
  ; beta_alphas: (timestamp * expl) Deque.t
  (* deque of S^+ beta [alphas] outside of the interval *)
  ; beta_alphas_out: (timestamp * expl) Deque.t
    
  (* sorted deque of S^- alpha [betas] *)
  ; alpha_betas: (timestamp * expl) Deque.t
  (* sorted deque of alpha proofs *)
  ; alphas_out: (timestamp * expl) Deque.t
  (* list of beta violations inside the interval*)
  ; betas_suffix_in: (timestamp * vexpl) Deque.t
  (* list of alpha/beta violations *)
  ; alphas_betas_out: (timestamp * vexpl option * vexpl option) Deque.t
  ; }

(* type muaux = {
 *     (\* deque of lists of U^+ beta [alphas] proofs *\)
 *     alphas_beta: ((timestamp * expl) list) Deque.t
 *   (\* most recent sequence of alpha satisfactions w/o holes *\)
 *   ; alphas_suffix: (timestamp * expl) Deque.t
 *   ; } *)

type mformula =
  | MTT
  | MFF
  | MP of string
  | MNeg of mformula
  | MConj of mformula * mformula * mbuf2
  | MDisj of mformula * mformula * mbuf2
  | MPrev of interval * mformula * bool * expl list * timestamp list
  | MNext of interval * mformula * bool * timestamp list
  | MSince of interval * mformula * mformula * msaux
  (* | MUntil of interval * mformula * mformula * mbuf2 * ts list * muaux *)

type progress = int

type mstate = progress * mformula

type context =
  { tp: timepoint
  ; out: output_channel
  }

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
let append_to_beta_alphas msaux sp_f1 =
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

let add_alpha_v msaux le ts vp_f1 =
  Deque.iter msaux.alphas_out ~f:(fun (ts, vp) ->
      if le vp_f1 vp then
        Deque.drop_back msaux.alpha_betas);
  Deque.enqueue_back msaux.alphas_out (ts, vp_f1)

let split_in_out_alphas_betas_out msaux r =
  List.rev (Deque.fold msaux.alphas_betas_out ~init:[]
              ~f:(fun acc (ts, vp_f1, vp_f2) ->
                if ts <= r then (
                  Deque.drop_front msaux.beta_alphas_out;
                  (ts, vp_f1, vp_f2)::acc)
                else acc))
      
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

let update_betas_suffix_in msaux new_in =
  let beta_none =
    List.exists new_in (fun (ts, opt_vp_f1, opt_vp_f2) ->
        opt_vp_f2 = None) in
  if beta_none then
    let _ = Deque.clear msaux.betas_suffix_in in
    let betas_after_none =
      List.fold_right new_in ~init:[]
        ~f:(fun (ts, opt_vp_f1, opt_vp_f2) acc ->
          if acc = [] then
            (if opt_vp_f2 = None then (ts, None)::acc else acc)
          else
            (ts, opt_vp_f2)::acc) in
    List.iter (List.rev betas_after_none)
      ~f:(fun (ts, opt_vp_f2) ->
        match opt_vp_f2 with
        | None -> ()
        | Some (vp_f2) ->
           Deque.enqueue_front msaux.betas_suffix_in (ts, vp_f2))
  else
    List.iter new_in
      ~f:(fun (ts, opt_vp_f1, opt_vp_f2) ->
        match opt_vp_f2 with
        | None -> ()
        | Some(vp_f2) ->
           Deque.enqueue_front msaux.betas_suffix_in (ts, vp_f2))

let append_to_alpha_betas msaux vp_f2 =
  Deque.iteri msaux.alpha_betas ~f:(fun i (ts, vp) ->
      match vp with
      | V pf -> Deque.set_exn msaux.alpha_betas i (ts, V (vappend pf vp_f2))
      | S _ -> raise VEXPL)

(* let update_alpha_betas msaux new_in =
 *   let beta_none =
 *     List.exists new_in (fun (ts, opt_vp_f1, opt_vp_f2) ->
 *         opt_vp_f2 = None) in
 *   if beta_none then
 *     Deque.clear msaux.alpha_betas
 *   else
 *     List.iter new_in
 *       ~f:(fun (ts, opt_vp_f1, opt_vp_f2) ->
 *         match opt_vp_f2 with
 *         | None -> ()
 *         | Some(vp_f2) ->
 *            append_to_alpha_betas msaux vp_f2) *)

let construct_vsinceps new_in tp =
  let opt_idx_none =
    List.findi new_in (fun i (ts, opt_vp_f1, opt_vp_f2) ->
        opt_vp_f2 = None) in
  let idx_none =
    match opt_idx_none with
    | None -> 0
    | Some(i, (_, _,_)) -> i in
  let new_in' =
    List.foldi new_in ~init:[]
      ~f:(fun i acc (ts, opt_vp_f1, opt_vp_f2) ->
        if i > idx_none then acc @ [(ts, opt_vp_f1, opt_vp_f2)]
        else acc) in
  List.foldi new_in' ~init:[]
    ~f:(fun i acc (ts, opt_vp_f1, opt_vp_f2) ->
      match opt_vp_f1 with
      | None -> acc
      | Some(vp_f1) ->
         let vbetas = 
           List.foldi new_in' ~init:[]
             ~f:(fun j acc2 (ts, o1, o2) ->
               match o2 with
               | None -> acc2
               | Some(beta) ->
                  if j >= i then acc2 @ [beta] else acc2) in
         let vp = V (VSince (tp, vp_f1, vbetas)) in
         acc @ [(ts, vp)])

let add_new_ps_alpha_betas msaux new_in tp =
  let new_vps_in = construct_vsinceps new_in tp in
  List.iter new_vps_in (fun (ts, vp) ->
      Deque.enqueue_back msaux.alpha_betas (ts, vp))

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

let update_since_aux (l, r) p_f1 p_f2 ts tp msaux le =
  (match p_f1, p_f2 with
   | S sp_f1 , S sp_f2 ->
      let sp_f = S (SSince (sp_f2, [])) in
      let _ = append_to_beta_alphas msaux sp_f1 in
      Deque.enqueue_back msaux.beta_alphas_out (ts, sp_f)
   | S sp_f1, V _ ->
      append_to_beta_alphas msaux sp_f1
   | V vp_f1, S sp_f2 ->
      let _ = add_alpha_v msaux le ts (V vp_f1) in
      let _ = Deque.enqueue_back msaux.alphas_betas_out (ts, Some(vp_f1), None) in
      let _ = Deque.clear msaux.beta_alphas in
      Deque.clear msaux.beta_alphas_out
   | V vp_f1, V vp_f2 ->
      let _ = add_alpha_v msaux le ts (V vp_f1) in
      let _ = Deque.enqueue_back msaux.alphas_betas_out (ts, Some(vp_f1), Some(vp_f2)) in
      let _ = Deque.clear msaux.beta_alphas in
      Deque.clear msaux.beta_alphas_out);
  (* sat *)
  let new_in_s = split_in_out_beta_alphas_out msaux r in
  let _ = update_beta_alphas msaux le new_in_s in
  let _ = remove_old_beta_alphas msaux l in
  (* viol *)
  let new_in_v = split_in_out_alphas_betas_out msaux r in
  let _ = remove_old_alpha_betas msaux l in
  let _ = remove_old_betas_suffix_in msaux l in
  let _ = update_betas_suffix_in msaux new_in_v in
  add_new_ps_alpha_betas msaux new_in_v tp
  
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
     | _ , S _ ->
        let _ = Deque.enqueue_back new_msaux.beta_alphas (ts, p) in
        (if a <> 0 then Deque.enqueue_back new_msaux.beta_alphas_out (ts, p));
        (p, new_msaux)
    | S _ , V vp_f2 ->
       let _ = Deque.enqueue_back new_msaux.alpha_betas (ts, p) in
       let _ = Deque.enqueue_back new_msaux.betas_suffix_in (ts, vp_f2) in
       let _ = Deque.enqueue_back new_msaux.alphas_betas_out (ts, None, Some(vp_f2)) in
       (p, new_msaux)
    | V f1, V f2 ->
       let _ = Deque.enqueue_back new_msaux.alpha_betas (ts, p) in
       let _ = Deque.enqueue_back new_msaux.betas_suffix_in (ts, f2) in
       let _ = Deque.enqueue_back new_msaux.alphas_betas_out (ts, Some(f1), Some(f2)) in
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
        let _ = update_since_aux (l, r) p1 p2 ts i new_msaux le in
        (output minimum new_msaux i, new_msaux)

let meval' tp ts sap mform minimum minimum_list le = 
  let rec meval tp ts sap mform =
    match mform with
    | MTT -> ([S (STT tp)], MTT)
    | MFF -> ([V (VFF tp)], MFF)
    | MP a ->
       if SS.mem a sap then ([S (SAtom (tp, a))], MP a)
       else ([V (VAtom (tp, a))], MP a)
    | MNeg (mf) ->
       let (ps_f, mf') = meval tp ts sap mf in
       let ps_z = List.map ps_f (fun e ->
                        match e with
                        | S e' -> V (VNeg e')
                        | V e' -> S (SNeg e')
                      ) in (ps_z, mf')
    | MConj (mf1, mf2, buf) ->
       let op e1 e2 = doConj minimum e1 e2 in
       let (ps_f1, mf1') = meval tp ts sap mf1 in
       let (ps_f2, mf2') = meval tp ts sap mf2 in
       let (ps_f, buf') = mbuf2_take op (mbuf2_add ps_f1 ps_f2 buf) in
       (ps_f, MConj (mf1', mf2', buf'))
    | MDisj (mf1, mf2, buf) ->
       let op e1 e2 = doDisj minimum e1 e2 in
       let (ps_f1, mf1') = meval tp ts sap mf1 in
       let (ps_f2, mf2') = meval tp ts sap mf2 in
       let (ps_f, buf') = mbuf2_take op (mbuf2_add ps_f1 ps_f2 buf) in
       (ps_f, MDisj (mf1', mf2', buf'))
    (* | MPrev (interval, mf, b, expl_lst, ts_d_lst) ->
     * | MNext (interval, mf, b, ts_a_lst) -> *)
    | MSince (interval, mf1, mf2, msaux) ->
       let (ps_f1, mf1') = meval tp ts sap mf1 in
       let (ps_f2, mf2') = meval tp ts sap mf2 in
       let p1 = minimum_list ps_f1 in
       let p2 = minimum_list ps_f2 in
       let (p_f, new_msaux) = update_since interval tp ts p1 p2 msaux le minimum in
       ([p_f], MSince (interval, mf1, mf2, msaux))
    (* | MUntil (interval, mf, mg, buf, ts_a_lst, muaux) -> *)
    | _ -> failwith "This formula cannot be monitored" in
  meval tp ts sap mform

let preamble out_ch mode f =
  let out_ch = output_event out_ch "Monitoring " in
  let out_ch = output_event out_ch (formula_to_string f) in
  let out_ch = output_event out_ch (" in mode " ^
                                    (match mode with
                                     | SAT -> "SAT"
                                     | VIOL -> "VIOL"
                                     | ALL -> "ALL")
                                    ^ "\n") in out_ch

let print_proofs out_ch mode ts tp ps =
  match mode with
  | SAT -> List.fold ps ~init:out_ch
             ~f:(fun acc p ->
               match p with
               | S _ -> output_explanation out_ch ((ts, tp), p)
               | V _ -> acc)
  | VIOL -> List.fold ps ~init:out_ch
             ~f:(fun acc p ->
               match p with
               | S _ -> acc
               | V _ -> output_explanation out_ch ((ts, tp), p))
  | ALL -> List.fold ps ~init:out_ch
             ~f:(fun acc p -> output_explanation out_ch ((ts, tp), p))

let monitor in_ch out_ch mode le f =
  let minimum_list ps = minsize_list (get_mins le ps) in
  let minimum a b = minimum_list [a; b] in
  let mf = minit f in
  let rec loop f x = loop f (f x) in
  let s (ctx, ch) =
    let ((sap, ts), ch) = input_event ch ctx.out in
    let (ps, _) = meval' ctx.tp ts sap mf minimum minimum_list le in
    let out' = print_proofs ctx.out mode ts ctx.tp ps in
    let new_ctx = { tp = ctx.tp+1
                  ; out = out' } in
    (new_ctx, ch) in
  let out_ch = preamble out_ch mode f in
  let ctx = { tp = 0; out = out_ch } in
  loop s (ctx, in_ch)
