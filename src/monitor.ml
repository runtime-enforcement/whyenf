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
open Check

module Deque = Core_kernel.Deque
module List = Core_kernel.List

type mbuf2 = expl list * expl list

type msaux = {
    ts_zero: timestamp option
  ; ts_in: timestamp Deque.t
  ; ts_out: timestamp Deque.t
    
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

type muaux = {
    (* deque of lists of U^+ beta [alphas] proofs *)
    alphas_beta: ((timestamp * expl) list) Deque.t
    (* most recent sequence of alpha satisfactions w/o holes *)
  ; alphas_suffix: (timestamp * expl) Deque.t
  ; }

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

type context =
  { tp: timepoint
  (* timepoint wrt current timestamp *)
  ; tp_ts: timepoint
  ; last_ts: timestamp
  ; out_ch: output_channel
  ; mf: mformula
  }

let print_ts_lists msaux =
  Printf.fprintf stdout "%s" (
  (match msaux.ts_zero with
   | None -> ""
   | Some(ts) -> Printf.sprintf "\n\tts_zero = (%d)\n" ts) ^  
  Deque.fold msaux.ts_in ~init:"\n\tts_in = ["
    ~f:(fun acc ts -> acc ^ (Printf.sprintf "%d;" ts)) ^
    (Printf.sprintf "]\n") ^
  Deque.fold msaux.ts_out ~init:"\n\tts_out = ["
    ~f:(fun acc ts -> acc ^ (Printf.sprintf "%d;" ts)) ^
    (Printf.sprintf "]\n")) 

let msaux_to_string msaux =
  "\n\nmsaux: " ^
    (match msaux.ts_zero with
     | None -> ""
     | Some(ts) -> Printf.sprintf "\n\tts_zero = (%d)\n" ts) ^  
    Deque.fold msaux.ts_in ~init:"\n\tts_in = ["
      ~f:(fun acc ts -> acc ^ (Printf.sprintf "%d;" ts)) ^
    (Printf.sprintf "]\n") ^
    Deque.fold msaux.ts_out ~init:"\n\tts_out = ["
      ~f:(fun acc ts -> acc ^ (Printf.sprintf "%d;" ts)) ^
    (Printf.sprintf "]\n") ^
    Deque.fold msaux.beta_alphas ~init:"\n\tbeta_alphas = "
      ~f:(fun acc (ts, ps) ->
        acc ^ (Printf.sprintf "\n\t\t(%d)\n\t\t" ts) ^ Expl.expl_to_string ps) ^
    Deque.fold msaux.beta_alphas_out ~init:"\n\tbeta_alphas_out = "
      ~f:(fun acc (ts, ps) ->
        acc ^ (Printf.sprintf "\n\t\t(%d)\n\t\t" ts) ^ Expl.expl_to_string ps) ^
    Deque.fold msaux.alpha_betas ~init:"\n\talpha_betas = "
      ~f:(fun acc (ts, ps) ->
        acc ^ (Printf.sprintf "\n\t\t(%d)\n\t\t" ts) ^ Expl.expl_to_string ps) ^
    Deque.fold msaux.alphas_out ~init:"\n\talphas_out = "
      ~f:(fun acc (ts, ps) ->
        acc ^ (Printf.sprintf "\n\t\t(%d)\n\t\t" ts) ^ Expl.expl_to_string ps) ^
    Deque.fold msaux.betas_suffix_in ~init:"\n\tbetas_suffix_in = "
      ~f:(fun acc (ts, ps) ->
        acc ^ (Printf.sprintf "\n\t\t(%d)\n\t\t" ts) ^ Expl.v_to_string "" ps) ^
    Deque.fold msaux.alphas_betas_out ~init:"\n\talphas_betas_out = "
      ~f:(fun acc (ts, p1_opt, p2_opt) ->
        match p1_opt, p2_opt with
        | None, None -> acc
        | Some(p1), None -> acc ^ (Printf.sprintf "\n\t\t(%d)\n\t\talpha = " ts) ^
                              Expl.v_to_string "" p1
        | None, Some(p2) -> acc ^ (Printf.sprintf "\n\t\t(%d)\n\t\tbeta = " ts) ^
                              Expl.v_to_string "" p2
        | Some(p1), Some(p2) -> acc ^ (Printf.sprintf "\n\t\t(%d)\n\t\talpha = " ts) ^
                                  Expl.v_to_string "" p1 ^
                                    (Printf.sprintf "\n\t\t(%d)\n\t\tbeta = " ts) ^
                                      Expl.v_to_string "" p2)

let print_msaux out_ch mf =
  match mf with
  | MSince (_, _, _, msaux) ->
     (match out_ch with
      | Output x -> Printf.fprintf x "%s\n\n" (msaux_to_string msaux); out_ch
      | _ -> out_ch)
  | _ -> out_ch

let print_ps_list l =
  List.iter l ~f:(fun (ts, p) -> Printf.fprintf stdout "%s\n" (expl_to_string p))

let cleared_msaux = { ts_zero = None
                    ; ts_in = Deque.create ()
                    ; ts_out = Deque.create ()
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

let update_ts_zero a ts msaux =
  if a = 0 then
    let _ = Deque.enqueue_back msaux.ts_in ts in
    { msaux with ts_zero = Some(ts) }
  else
    let _ = Deque.enqueue_back msaux.ts_out ts in
    { msaux with ts_zero = Some(ts) }

let update_ts (l, r) a ts msaux =
  if a = 0 then
    let _ = Deque.enqueue_back msaux.ts_in ts in
    let ts_in_lst = Deque.to_list msaux.ts_in in
    let _ = List.iter ts_in_lst
              ~f:(fun ts' -> if ts' < l then Deque.drop_front msaux.ts_in) in
    msaux
  else
    let _ = Deque.enqueue_back msaux.ts_out ts in
    let out_lst = Deque.to_list msaux.ts_out in
    let _ = List.iter out_lst
              ~f:(fun ts' -> if ts' <= r then
                               let _ = Deque.enqueue_back msaux.ts_in ts' in
                               Deque.drop_front msaux.ts_out) in
    let in_lst = Deque.to_list msaux.ts_in in
    let _ = List.iter in_lst
              ~f:(fun ts' -> if ts' < l then Deque.drop_front msaux.ts_in) in
    msaux

exception VEXPL
exception SEXPL

(* This approach should be faster than other possible solutions *)
let sappend_to_deque sp1 d =
  let _ = Deque.iteri d ~f:(fun i (ts, ssp) ->
              match ssp with
              | S sp -> Deque.set_exn d i (ts, S (sappend sp sp1))
              | V _ -> raise SEXPL) in d

(* Resulting list is in ascending order, e.g.,
   d = [(1, p_1), (2, p_2), ..., (n, p_n)]
   results in [(n, p_n), ...]  *)
let split_in_out r d =
  let l = List.fold (Deque.to_list d) ~init:[]
            ~f:(fun acc (ts, p) -> if ts <= r then 
                                     let _ = Deque.drop_front d in
                                     (ts, p)::acc
                                   else acc) in (d, l)

let split_in_out2 r d =
  let l = List.rev (List.fold (Deque.to_list d) ~init:[]
                      ~f:(fun acc (ts, vp1_opt, vp2_opt) ->
                        if ts <= r then (
                          Deque.drop_front d;
                          (ts, vp1_opt, vp2_opt)::acc)
                        else acc)) in (d, l)

let add_alphas_out ts vvp1 alphas_out le =
  let _ = Deque.iter alphas_out ~f:(fun (ts, vvp) ->
              if le vvp1 vvp then Deque.drop_back alphas_out) in
  let _ = Deque.enqueue_back alphas_out (ts, vvp1) in alphas_out

(* Sort proofs wrt a particular measure, i.e., 
   if |p_1| < |p_2| in [p_1, p_2, p_3, ..., p_n] 
   then p_2 must be removed (and so on).
   The order of resulting list is reversed, which
   means that the smallest element is also the head. *)
let sort_new_in le new_in =
  let rec aux ps acc =
    match ps with
    | [] -> acc
    | x::x'::xs ->
       if le (snd(x)) (snd(x')) then
         aux xs (x::acc)
       else aux xs (x'::acc)
    | x::xs -> x::acc
  in aux new_in []

let remove_out l d =
  let _ = List.iter (Deque.to_list d) ~f:(fun (ts, _) ->
              if ts < l then Deque.drop_front d) in d

let remove_out2 r d =
  let _ = List.iter (Deque.to_list d) ~f:(fun (ts, _, _) ->
              if ts <= r then Deque.drop_front d) in d

let update_beta_alphas l new_in beta_alphas le minimuml =
  if not (List.is_empty new_in) then (
    let new_in' = sort_new_in le new_in in
    let hd_p = List.hd_exn new_in' in
    let _ = Deque.iter beta_alphas ~f:(fun (ts, sp) ->
                if le (snd(hd_p)) sp then
                  Deque.drop_back beta_alphas) in
    let _ = List.iter new_in' ~f:(fun (ts, sp) ->
                Deque.enqueue_back beta_alphas (ts, sp)) in
    remove_out l beta_alphas)
  else remove_out l beta_alphas

let update_betas_suffix_in l new_in betas_suffix_in =
  if not (List.is_empty new_in) then (
    let exists_none =
      List.exists new_in
        (fun (ts, vp1_opt, vp2_opt) -> vp2_opt = None) in
    if exists_none then (
      let _ = Deque.clear betas_suffix_in in
      let betas_after_none =
        List.rev (
            List.fold new_in ~init:[]
              ~f:(fun acc (ts, vp1_opt, vp2_opt) ->
                if (List.is_empty acc) then
                  (if vp2_opt = None then (ts, None)::acc else acc)
                else (ts, vp2_opt)::acc)) in
      let _ = List.iter betas_after_none
                ~f:(fun (ts, vp2_opt) ->
                  match vp2_opt with
                  | None -> ()
                  | Some (vp2) ->
                     Deque.enqueue_back betas_suffix_in (ts, vp2)) in
      remove_out l betas_suffix_in)
    else (
      let _ = List.iter new_in
                ~f:(fun (ts, vp1_opt, vp2_opt) ->
                  match vp2_opt with
                  | None -> ()
                  | Some(vp2) ->
                     Deque.enqueue_back betas_suffix_in (ts, vp2)) in
      remove_out l betas_suffix_in))
  else remove_out l betas_suffix_in

let vappend_to_deque vp2 d =
  let _ = Deque.iteri d ~f:(fun i (ts, vvp) ->
              match vvp with
              | V vp -> Deque.set_exn d i (ts, V (vappend vp vp2))
              | S _ -> raise VEXPL) in d

let construct_vsinceps tp new_in =
  let idx_none_opt =
    List.findi new_in (fun i (ts, vp1_opt, vp2_opt) ->
        vp2_opt = None) in
  let idx_none =
    match idx_none_opt with
    | None -> 0
    | Some(i, (_, _,_)) -> i in
  let new_in' =
    List.rev(List.foldi new_in ~init:[]
               ~f:(fun i acc (ts, vp1_opt, vp2_opt) ->
                 if i > idx_none then (ts, vp1_opt, vp2_opt)::acc
                 else acc)) in
  List.rev(List.foldi new_in' ~init:[]
             ~f:(fun i acc (ts, vp1_opt, vp2_opt) ->
               match vp1_opt with
               | None -> acc
               | Some(vp1) ->
                  let vbetas =
                    List.rev(List.foldi new_in' ~init:[]
                               ~f:(fun j acc2 (ts, o1, o2) ->
                                 match o2 with
                                 | None -> acc2
                                 | Some(beta) ->
                                    if j >= i then beta::acc2 else acc2)) in
                  let vp = V (VSince (tp, vp1, vbetas)) in
                  (ts, vp)::acc))

let add_new_ps_alpha_betas tp new_in alpha_betas =
  if not (List.is_empty new_in) then (
    let new_vps_in = construct_vsinceps tp new_in in
    let _ = List.iter new_vps_in (fun (ts, vp) ->
                Deque.enqueue_back alpha_betas (ts, vp)) in alpha_betas)
  else alpha_betas

let update_alpha_betas l tp new_in alpha_betas =
  if not (List.is_empty new_in) then (
    let exists_none =
      List.exists new_in (fun (ts, vp1_opt, vp2_opt) -> vp2_opt = None) in
    if exists_none then (let _ = Deque.clear alpha_betas in alpha_betas)
    else (
      let a_bs = List.fold new_in ~init:alpha_betas
                   ~f:(fun d (ts, vp1_opt, vp2_opt) ->
                     match vp2_opt with
                     | None -> d
                     | Some(vp2) -> vappend_to_deque vp2 d) in
      let a_bs' = add_new_ps_alpha_betas tp new_in a_bs in
      remove_out l a_bs'))
  else remove_out l alpha_betas

let betas_suffix_in_to_list betas_suffix_in =
  Deque.fold' betas_suffix_in ~init:[]
    ~f:(fun acc (ts, vp) -> vp::acc) `back_to_front

let optimal_proof tp msaux minimuml =
  if not (Deque.is_empty msaux.beta_alphas) then
    snd(Deque.peek_front_exn msaux.beta_alphas)
  else
    let p1_l = if not (Deque.is_empty msaux.alpha_betas) then
                 [snd(Deque.peek_front_exn msaux.alpha_betas)]
               else [] in
    let p2_l = if not (Deque.is_empty msaux.alphas_out) then
                 let vp_f2 = snd(Deque.peek_front_exn msaux.alphas_out) in
                 match vp_f2 with
                 | V f2 -> [V (VSince (tp, f2, []))]
                 | S _ -> raise VEXPL
               else [] in
    let p3_l = if (Deque.length msaux.betas_suffix_in) = (Deque.length msaux.ts_in) then
                 let betas_suffix = betas_suffix_in_to_list msaux.betas_suffix_in in
                 [V (VSinceInf (tp, betas_suffix))]
               else [] in
    minimuml (p1_l @ p2_l @ p3_l)

let update_msaux ts p1 p2 msaux le minimuml =
  match p1, p2 with
  | S sp1 , S sp2 ->
     let beta_alphas = sappend_to_deque sp1 msaux.beta_alphas in
     let beta_alphas_out = sappend_to_deque sp1 msaux.beta_alphas_out in
     let sp = S (SSince (sp2, [])) in
     let _ = Deque.enqueue_back beta_alphas_out (ts, sp) in
     { msaux with
       beta_alphas = beta_alphas
     ; beta_alphas_out = beta_alphas_out }
  | S sp1, V vp2 ->
     let beta_alphas = sappend_to_deque sp1 msaux.beta_alphas in
     let beta_alphas_out = sappend_to_deque sp1 msaux.beta_alphas_out in
     let _ = Deque.enqueue_back msaux.alphas_betas_out (ts, None, Some(vp2)) in
     { msaux with
       beta_alphas = beta_alphas
     ; beta_alphas_out = beta_alphas_out }
   | V vp1, S sp2 ->
      let alphas_out = add_alphas_out ts (V vp1) msaux.alphas_out le in
      let _ = Deque.enqueue_back msaux.alphas_betas_out (ts, Some(vp1), None) in
      let _ = Deque.clear msaux.beta_alphas in
      let _ = Deque.clear msaux.beta_alphas_out in
      let sp = S (SSince (sp2, [])) in
      let _ = Deque.enqueue_back msaux.beta_alphas_out (ts, sp) in
      { msaux with alphas_out = alphas_out }
   | V vp1, V vp2 ->
      let alphas_out = add_alphas_out ts (V vp1) msaux.alphas_out le in
      let _ = Deque.enqueue_back msaux.alphas_betas_out (ts, Some(vp1), Some(vp2)) in
      let _ = Deque.clear msaux.beta_alphas in
      let _ = Deque.clear msaux.beta_alphas_out in
      { msaux with alphas_out = alphas_out }

let advance_msaux (l, r) ts tp p1 p2 msaux le minimuml =
  let msaux = update_msaux ts p1 p2 msaux le minimuml in
  let beta_alphas_out, new_in_sat = split_in_out r msaux.beta_alphas_out in
  let beta_alphas = update_beta_alphas l new_in_sat msaux.beta_alphas le minimuml in
  let alphas_betas_out, new_in_viol = split_in_out2 r msaux.alphas_betas_out in
  let betas_suffix_in = update_betas_suffix_in l new_in_viol msaux.betas_suffix_in in
  let alpha_betas = update_alpha_betas l tp new_in_viol msaux.alpha_betas in
  let alphas_betas_out = remove_out2 r msaux.alphas_betas_out in
  { msaux with
    beta_alphas = beta_alphas
  ; beta_alphas_out = beta_alphas_out
  ; alpha_betas = alpha_betas
  ; betas_suffix_in = betas_suffix_in
  ; alphas_betas_out = alphas_betas_out }

let update_since interval tp ts p1 p2 msaux le minimuml =
  let a = get_a_I interval in
  (* Case 1: interval has not yet started, i.e., 
     \tau_{tp} < \tau_{0} + a  OR \tau_{tp} - a < 0 *)
  if ((Option.is_some msaux.ts_zero) && ts < (Option.get msaux.ts_zero) + a)
     || ((Option.is_none msaux.ts_zero) && (ts - a) < 0) then
    let l = (-1) in
    let r = (-1) in
    let msaux_ts_updated = if Option.is_none msaux.ts_zero then
                             update_ts_zero a ts msaux
                           else update_ts (l, r) a ts msaux in
    let msaux_updated = advance_msaux (l, r) ts tp p1 p2 msaux_ts_updated le minimuml in
    let p = V (VSinceOutL tp) in
    (p, msaux_updated)
  (* Case 2: \tau_{tp-1} exists *)
  else
    let b = get_b_I (Option.get msaux.ts_zero) interval in
    (* TODO: Fix l and r, we should consider the type of the interval *)
    let l = max 0 (ts - b) in
    let r = ts - a in
    let msaux_ts_updated = update_ts (l, r) a ts msaux in
    let msaux_updated = advance_msaux (l, r) ts tp p1 p2 msaux_ts_updated le minimuml in
    (optimal_proof tp msaux_updated minimuml, msaux_updated)

let doDisj minimum2 expl_f1 expl_f2 =
  match expl_f1, expl_f2 with
  | S f1, S f2 -> minimum2 (S (SDisjL (f1))) (S (SDisjR(f2)))
  | S f1, V _ -> S (SDisjL (f1))
  | V _ , S f2 -> S (SDisjR (f2))
  | V f1, V f2 -> V (VDisj (f1, f2))

let doConj minimum2 expl_f1 expl_f2 =
  match expl_f1, expl_f2 with
  | S f1, S f2 -> S (SConj (f1, f2))
  | S _ , V f2 -> V (VConjR (f2))
  | V f1, S _ -> V (VConjL (f1))
  | V f1, V f2 -> minimum2 (V (VConjL (f1))) (V (VConjR (f2)))

let meval' tp ts sap mform le minimuml =
  let minimum2 a b = minimuml [a; b] in
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
       let op e1 e2 = doConj minimum2 e1 e2 in
       let (ps_f1, mf1') = meval tp ts sap mf1 in
       let (ps_f2, mf2') = meval tp ts sap mf2 in
       let (ps_f, buf') = mbuf2_take op (mbuf2_add ps_f1 ps_f2 buf) in
       (ps_f, MConj (mf1', mf2', buf'))
    | MDisj (mf1, mf2, buf) ->
       let op e1 e2 = doDisj minimum2 e1 e2 in
       let (ps_f1, mf1') = meval tp ts sap mf1 in
       let (ps_f2, mf2') = meval tp ts sap mf2 in
       let (ps_f, buf') = mbuf2_take op (mbuf2_add ps_f1 ps_f2 buf) in
       (ps_f, MDisj (mf1', mf2', buf'))
    (* | MPrev (interval, mf, b, expl_lst, ts_d_lst) ->
     * | MNext (interval, mf, b, ts_a_lst) -> *)
    | MSince (interval, mf1, mf2, msaux) ->
       let (ps_f1, mf1') = meval tp ts sap mf1 in
       let (ps_f2, mf2') = meval tp ts sap mf2 in
       let p1 = minimuml ps_f1 in
       let p2 = minimuml ps_f2 in
       let (p_f, new_msaux) = update_since interval tp ts p1 p2 msaux le minimuml in
       ([p_f], MSince (interval, mf1, mf2, new_msaux))
    (* | MUntil (interval, mf1, mf2, muaux) -> *)
    | _ -> failwith "This formula cannot be monitored" in
  meval tp ts sap mform

let preamble out_ch mode f =
  let out_ch = output_event out_ch "Monitoring " in
  let out_ch = output_event out_ch (formula_to_string f) in
  let out_ch = output_event out_ch (" in mode " ^
                                    (match mode with
                                     | SAT -> "SAT"
                                     | VIOL -> "VIOL"
                                     | ALL -> "ALL"
                                     | BOOL -> "BOOL")
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
  | BOOL -> List.fold ps ~init:out_ch
              ~f:(fun acc p ->
                match p with
                | S _ -> output_boolean out_ch ((ts, tp), true)
                | V _ -> output_boolean out_ch ((ts, tp), false))

(* let check_proof event_list f p =
 *   let f_string = formula_to_string f in
 *   let p_string = Expl.expl_to_string p in
 *   match p with
 *   | S _ -> Check.s_check_prefix event_list f_string p_string
 *   | V _ -> Check.v_check_prefix event_list f_string p_string *)

let monitor in_ch out_ch mode le f =
  let minimuml ps = minsize_list (get_mins le ps) in
  let rec loop f x = loop f (f x) in
  let s (ctx, in_ch) =
    let ((sap, ts), in_ch) = input_event in_ch ctx.out_ch in
    let (ps, mf) = meval' ctx.tp ts sap ctx.mf le minimuml in
    let tp_ts = if ts = ctx.last_ts then ctx.tp_ts+1 else 0 in
    let out_ch = print_proofs ctx.out_ch mode ts tp_ts ps in
    let new_ctx = { tp = ctx.tp+1
                  ; tp_ts = tp_ts
                  ; last_ts = ts
                  ; out_ch = out_ch
                  ; mf = mf} in
    (new_ctx, in_ch) in
  let mf = minit f in
  let out_ch = preamble out_ch mode f in
  let ctx = { tp = 0
            ; tp_ts = 0
            ; last_ts = -1
            ; out_ch = out_ch
            ; mf = mf } in
  loop s (ctx, in_ch)
