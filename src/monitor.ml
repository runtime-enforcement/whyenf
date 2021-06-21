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

(* ts update functions *)
let get_last_ts msaux =
  match (Deque.is_empty msaux.ts_in), (Deque.is_empty msaux.ts_out) with
  | true, true -> None
  | _ , false -> Some(Deque.peek_back_exn msaux.ts_out)
  | false, true -> Some(Deque.peek_back_exn msaux.ts_in)

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
    let _ = Deque.iteri msaux.ts_in
              ~f:(fun i ts' -> if ts' < l then Deque.drop_front msaux.ts_in) in
    msaux
  else
    let _ = Deque.enqueue_back msaux.ts_out ts in
    let _ = Deque.iter msaux.ts_out
              ~f:(fun ts' ->
                if ts' <= r then
                  let _ = Deque.enqueue_back msaux.ts_in ts' in
                  Deque.drop_front msaux.ts_out) in
    
    Printf.fprintf stdout "ts_out = [";
    Deque.iter msaux.ts_out
      ~f:(fun ts' -> Printf.fprintf stdout "%d " ts');
    Printf.fprintf stdout "]\n";
    Printf.fprintf stdout "ts_in = [";
    Deque.iter msaux.ts_in
      ~f:(fun ts' -> Printf.fprintf stdout "%d " ts');
    Printf.fprintf stdout "]\nl = %d\n" l;
    
    let _ = Deque.iter msaux.ts_in
              ~f:(fun ts' -> if ts' < l then
                               (Printf.fprintf stdout "ts_in = [";
                                Deque.iter msaux.ts_in
                                  ~f:(fun ts' -> Printf.fprintf stdout "%d " ts');
                                Printf.fprintf stdout "]\nl = %d\n" l;
                                Printf.fprintf stdout "ts' = %d\n" ts';
                                Deque.drop_front msaux.ts_in)) in
    Printf.fprintf stdout "oi\n";
    msaux

exception VEXPL
exception SEXPL

(* This approach should be faster than other possible solutions *)
let append_to_beta_alphas msaux sp_f1 =
  Deque.iteri msaux.beta_alphas ~f:(fun i (ts, sp) ->
      match sp with
      | S pf -> Deque.set_exn msaux.beta_alphas i (ts, S (sappend pf sp_f1))
      | V _ -> raise SEXPL)

let append_to_beta_alphas_out msaux sp_f1 =
  Deque.iteri msaux.beta_alphas_out ~f:(fun i (ts, sp) ->
      match sp with
      | S pf -> Deque.set_exn msaux.beta_alphas_out i (ts, S (sappend pf sp_f1))
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
  Printf.fprintf stdout "#new_in'=%d\n" (List.length new_in');
  let hd_p = List.hd_exn new_in' in
  Deque.iter msaux.beta_alphas ~f:(fun (ts, sp) ->
      if le (snd(hd_p)) sp then
        Deque.drop_back msaux.beta_alphas);
  List.iter new_in' ~f:(fun (ts, sp) ->
      Deque.enqueue_back msaux.beta_alphas (ts, sp))

let remove_old_beta_alphas msaux l =
  Deque.iter msaux.beta_alphas
    ~f:(fun (ts, sp) -> if ts < l then Deque.drop_front msaux.beta_alphas)

let add_alpha_v msaux le ts vp_f1 =
  Deque.iter msaux.alphas_out ~f:(fun (ts, vp) ->
      if le vp_f1 vp then
        Deque.drop_back msaux.alphas_out);
  Deque.enqueue_back msaux.alphas_out (ts, vp_f1)

let split_in_out_alphas_betas_out msaux r =
  List.rev (
      Deque.fold msaux.alphas_betas_out ~init:[]
        ~f:(fun acc (ts, vp_f1_opt, vp_f2_opt) ->
          if ts <= r then (
            Deque.drop_front msaux.alphas_betas_out;
            (ts, vp_f1_opt, vp_f2_opt)::acc)
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

let remove_old_alphas_betas_out msaux r =
  Deque.iter msaux.alphas_betas_out
    ~f:(fun (ts, _, _) ->
      if ts <= r then
        Deque.drop_front msaux.alphas_betas_out)

let remove_old_alphas_out msaux r =
  Deque.iter msaux.alphas_out
    ~f:(fun (ts, _) ->
      if ts <= r then
        Deque.drop_front msaux.alphas_out)

let update_betas_suffix_in msaux new_in =
  let beta_none =
    List.exists new_in
      (fun (ts, vp_f1_opt, vp_f2_opt) -> vp_f2_opt = None) in
  if beta_none then
    let _ = Deque.clear msaux.betas_suffix_in in
    let betas_after_none =
      List.rev (
          List.fold new_in ~init:[]
            ~f:(fun acc (ts, vp_f1_opt, vp_f2_opt) ->
              if (List.is_empty acc) then
                (if vp_f2_opt = None then (ts, None)::acc else acc)
              else (ts, vp_f2_opt)::acc)) in
    List.iter betas_after_none
      ~f:(fun (ts, vp_f2_opt) ->
        match vp_f2_opt with
        | None -> ()
        | Some (vp_f2) ->
           Deque.enqueue_back msaux.betas_suffix_in (ts, vp_f2))
  else
    List.iter new_in
      ~f:(fun (ts, opt_vp_f1, opt_vp_f2) ->
        match opt_vp_f2 with
        | None -> ()
        | Some(vp_f2) ->
           Deque.enqueue_back msaux.betas_suffix_in (ts, vp_f2))

let append_to_alpha_betas msaux vp_f2 =
  Deque.iteri msaux.alpha_betas ~f:(fun i (ts, vp) ->
      match vp with
      | V pf -> Deque.set_exn msaux.alpha_betas i (ts, V (vappend pf vp_f2))
      | S _ -> raise VEXPL)

let update_alpha_betas msaux new_in =
  let beta_none =
    List.exists new_in (fun (ts, opt_vp_f1, opt_vp_f2) -> opt_vp_f2 = None) in
  if beta_none then
    Deque.clear msaux.alpha_betas
  else
    List.iter new_in
      ~f:(fun (ts, opt_vp_f1, opt_vp_f2) ->
        match opt_vp_f2 with
        | None -> ()
        | Some(vp_f2) ->
           append_to_alpha_betas msaux vp_f2)

let construct_vsinceps new_in tp =
  let opt_idx_none =
    List.findi new_in (fun i (ts, opt_vp_f1, opt_vp_f2) ->
        opt_vp_f2 = None) in
  let idx_none =
    match opt_idx_none with
    | None -> 0
    | Some(i, (_, _,_)) -> i in
  let new_in' =
    List.rev(List.foldi new_in ~init:[]
               ~f:(fun i acc (ts, opt_vp_f1, opt_vp_f2) ->
                 if i > idx_none then (ts, opt_vp_f1, opt_vp_f2)::acc
                 else acc)) in
  List.rev(List.foldi new_in' ~init:[]
             ~f:(fun i acc (ts, opt_vp_f1, opt_vp_f2) ->
               match opt_vp_f1 with
               | None -> acc
               | Some(vp_f1) ->
                  let vbetas =
                    List.rev(List.foldi new_in' ~init:[]
                               ~f:(fun j acc2 (ts, o1, o2) ->
                                 match o2 with
                                 | None -> acc2
                                 | Some(beta) ->
                                    if j >= i then beta::acc2 else acc2)) in
                  let vp = V (VSince (tp, vp_f1, vbetas)) in
                  (ts, vp)::acc))

let add_new_ps_alpha_betas msaux new_in tp =
  Printf.fprintf stdout "new_vps_in = \n";
  let new_vps_in = construct_vsinceps new_in tp in
  List.iter new_vps_in
    ~f:(fun (ts, vp) -> Printf.fprintf stdout "%s\n" (Expl.expl_to_string vp));
  List.iter new_vps_in (fun (ts, vp) ->
      Deque.enqueue_back msaux.alpha_betas (ts, vp))

let betas_suffix_in_to_list betas_suffix_in =
  Deque.fold' betas_suffix_in ~init:[]
    ~f:(fun acc (ts, vp) -> vp::acc) `back_to_front

let optimal_proof minimum_list msaux tp =
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
                 let beta_suffix = betas_suffix_in_to_list msaux.betas_suffix_in in
                 [V (VSinceInf (tp, beta_suffix))]
               else [] in
    minimum_list (p1_l @ p2_l @ p3_l)

let update_since_aux (l, r) p_f1 p_f2 ts tp msaux le =
  (match p_f1, p_f2 with
   | S sp_f1 , S sp_f2 ->
      let sp_f = S (SSince (sp_f2, [])) in
      let _ = append_to_beta_alphas msaux sp_f1 in
      let _ = append_to_beta_alphas_out msaux sp_f1 in
      Deque.enqueue_back msaux.beta_alphas_out (ts, sp_f)
   | S sp_f1, V vp_f2 ->
      let _ = append_to_beta_alphas msaux sp_f1 in
      let _ = append_to_beta_alphas_out msaux sp_f1 in
      Deque.enqueue_back msaux.alphas_betas_out (ts, None, Some(vp_f2))
   | V vp_f1, S sp_f2 ->
      let sp_f = S (SSince (sp_f2, [])) in
      let _ = add_alpha_v msaux le ts (V vp_f1) in
      let _ = Deque.enqueue_back msaux.alphas_betas_out (ts, Some(vp_f1), None) in
      let _ = Deque.clear msaux.beta_alphas in
      let _ = Deque.clear msaux.beta_alphas_out in
      Deque.enqueue_back msaux.beta_alphas_out (ts, sp_f)
   | V vp_f1, V vp_f2 ->
      let _ = add_alpha_v msaux le ts (V vp_f1) in
      let _ = Deque.enqueue_back msaux.alphas_betas_out (ts, Some(vp_f1), Some(vp_f2)) in
      let _ = Deque.clear msaux.beta_alphas in
      Deque.clear msaux.beta_alphas_out);
  (* sat *)
  (* Printf.fprintf stdout "#msaux.beta_alphas_out = %d\n" (Deque.length msaux.beta_alphas_out); *)
  let new_in_s = split_in_out_beta_alphas_out msaux r in
  (* Printf.fprintf stdout "#new_in_s = %d\n" (List.length new_in_s); *)
  (* print_ps_list new_in_s; *)
  (if not (List.is_empty new_in_s) then update_beta_alphas msaux le new_in_s);
  let _ = remove_old_beta_alphas msaux l in
  (* viol *)
  let new_in_v = split_in_out_alphas_betas_out msaux r in
  (if not (List.is_empty new_in_v) then
     let _ = update_betas_suffix_in msaux new_in_v in
     let _ = update_alpha_betas msaux new_in_v in
     add_new_ps_alpha_betas msaux new_in_v tp);
  let _ = remove_old_alpha_betas msaux l in
  let _ = remove_old_betas_suffix_in msaux l in
  let _ = remove_old_alphas_betas_out msaux r in
  remove_old_alphas_out msaux r;
  let _ = Printf.fprintf stdout "l=%d; r=%d\n" l r in
  let _ = Printf.fprintf stdout "tp=%d\n" tp in
  let _ = Printf.fprintf stdout "NEW_MSAUX: %s\n" (msaux_to_string msaux) in
  Printf.fprintf stdout "---------------------------\n"
  
let update_since interval tp ts p1 p2 msaux le minimum minimum_list =
  let a = get_a_I interval in
  (* Case 1: interval has not yet started, i.e., 
     \tau_{tp} < \tau_{0} + a  OR \tau_{tp} - a < 0 *)
  if ((Option.is_some msaux.ts_zero) && ts < (Option.get msaux.ts_zero) + a)
     || ((Option.is_none msaux.ts_zero) && (ts - a) < 0) then
    let l = (-1) in
    let r = (-1) in
    let msaux = if Option.is_none msaux.ts_zero then update_ts_zero a ts msaux
                else update_ts (l, r) a ts msaux in
    let _ = update_since_aux (l, r) p1 p2 ts tp msaux le in
    let p = V (VSinceOutL tp) in
    (p, msaux)
  (* Case 2: \tau_{tp-1} exists *)
  else
    let b = get_b_I (Option.get msaux.ts_zero) interval in
    (* TODO: Fix l and r, we should consider the type of the interval *)
    let l = max 0 (ts - b) in
    let r = ts - a in
    let _ = update_ts (l, r) a ts msaux in
    let _ = update_since_aux (l, r) p1 p2 ts tp msaux le in
    (optimal_proof minimum_list msaux tp, msaux)

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
       let (p_f, new_msaux) = update_since interval tp ts p1 p2 msaux le minimum minimum_list in
       (* let _ = Printf.fprintf stdout "tp=%d\n" tp in *)
       (* let _ = Printf.fprintf stdout "NEW_MSAUX: %s\n" (msaux_to_string msaux) in
        * let _ = Printf.fprintf stdout "---------------------------\n" in *)
       ([p_f], MSince (interval, mf1, mf2, new_msaux))
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

let monitor in_ch out_ch mode le f =
  let minimum_list ps = minsize_list (get_mins le ps) in
  let minimum a b = minimum_list [a; b] in
  let rec loop f x = loop f (f x) in
  let s (ctx, in_ch) =
    let ((sap, ts), in_ch) = input_event in_ch ctx.out_ch in
    let (ps, mf) = meval' ctx.tp ts sap ctx.mf minimum minimum_list le in
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
