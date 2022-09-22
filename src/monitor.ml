(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Io
open Mtl
open Expl
open Util
open Interval
open Checker_interface

module Deque = Core_kernel.Deque
module List = Base.List

exception UNBOUNDED_FUTURE
exception INVALID_EXPL of string
exception EMPTY_DEQUE of string
exception EMPTY_LIST of string
exception NOT_FOUND of string
exception INVALID_TIMESTAMP of string

let minimuml le l = match l with
  | [] -> failwith "empty list for minimuml"
  | x::xs -> List.fold_left xs ~init:x ~f:(fun a b -> if le a b then a else b)

let sappend_to_deque sp1 d =
  let () = Deque.iteri d ~f:(fun i (ts, ssp) ->
              match ssp with
              | S sp -> Deque.set_exn d i (ts, S (sappend sp sp1))
              | V _ -> raise SEXPL) in d

let vappend_to_deque vp2 d =
  let () = Deque.iteri d ~f:(fun i (ts, vvp) ->
              match vvp with
              | V vp -> Deque.set_exn d i (ts, V (vappend vp vp2))
              | S _ -> raise VEXPL) in d

let betas_suffix_in_to_list v_betas_in =
  Deque.fold' v_betas_in ~init:[]
    ~f:(fun acc (ts, vp) -> vp::acc) `back_to_front

let remove_if_pred_front f d =
  let rec aux f d =
    let el = Deque.dequeue_front d in
    match el with
    | None -> ()
    | Some(el') -> if (f el') then aux f d
                   else Deque.enqueue_front d el' in
  let () = aux f d in d

let remove_if_pred_front_ne f d =
  let rec aux f d =
    if (Deque.length d) > 1 then
      let el = Deque.dequeue_front d in
      match el with
      | None -> ()
      | Some(el') -> if (f el') then aux f d
                     else Deque.enqueue_front d el' in
  let () = aux f d in d

let remove_if_pred_back f d =
  let rec aux f d =
    let el = Deque.dequeue_back d in
    match el with
    | None -> ()
    | Some(el') -> if (f el') then aux f d
                   else Deque.enqueue_back d el' in
  let () = aux f d in d

let sorted_append new_in d le =
  let () = Deque.iter new_in ~f:(fun (ts, p) ->
               let _ = remove_if_pred_back (fun (ts', p') -> le p p') d in
               Deque.enqueue_back d (ts, p)) in
  d

let sorted_enqueue (ts, p) d le =
  let _ = remove_if_pred_back (fun (_, p') -> le p p') d in
  let () = Deque.enqueue_back d (ts, p) in d

(* TODO: split_in_out and split_out_in should be rewritten as a single function *)

(* Considering a closed interval [l, r] *)
let split_in_out get_ts (l, r) d =
  let new_in = Deque.create () in
  let rec aux d =
    let el_opt = Deque.dequeue_front d in
    match el_opt with
    | None -> ()
    | Some(el) -> (let ts = get_ts el in
                   if ts <= r then
                     (let () = if ts >= l then Deque.enqueue_back new_in el in aux d)
                   else Deque.enqueue_front d el) in
  let () = aux d in
  (d, new_in)

(* Considering an interval of the form [z, l) *)
let split_out_in get_ts (z, l) d =
  let new_out = Deque.create () in
  let rec aux d =
    let el_opt = Deque.dequeue_front d in
    match el_opt with
    | None -> ()
    | Some(el) -> (let ts = get_ts el in
                   if ts < l then
                     (let () = if ts >= z then Deque.enqueue_back new_out el in aux d)
                   else Deque.enqueue_front d el) in
  let () = aux d in
  (d, new_out)

let etp ts_tp_in ts_tp_out tp =
  match Deque.peek_front ts_tp_in with
  | None -> (match Deque.peek_front ts_tp_out with
             | None -> tp
             | Some (_, tp') -> tp')
  | Some (_, tp') -> tp'

let ready_ts_tps b nts ts_tp_out ts_tp_in =
  let d = Deque.create () in
  let _ = Deque.iter ts_tp_out ~f:(fun (ts, tp) ->
              if ts + b < nts then Deque.enqueue_back d (ts, tp)) in
  let _ = Deque.iter ts_tp_in ~f:(fun (ts, tp) ->
              if ts + b < nts then Deque.enqueue_back d (ts, tp)) in
  d

let first_ts_tp ts_tp_out ts_tp_in =
  match Deque.peek_front ts_tp_out with
  | None -> (match Deque.peek_front ts_tp_in with
             | None -> None
             | Some(ts, tp) -> Some(ts, tp))
  | Some(ts, tp) -> Some(ts, tp)

let add_ts_tp_future a b nts ntp ts_tp_out ts_tp_in =
  (* (ts, tp) update is performed differently if the queues are not empty *)
  let () = if (not (Deque.is_empty ts_tp_out)) || (not (Deque.is_empty ts_tp_in)) then
             let first_ts = match first_ts_tp ts_tp_out ts_tp_in with
               | None -> raise (NOT_FOUND "(ts, tp) deques are empty")
               | Some(ts', _) -> ts' in
             if nts < first_ts + a then
               Deque.enqueue_back ts_tp_out (nts, ntp)
             else
               Deque.enqueue_back ts_tp_in (nts, ntp)
           else
             (if (nts >= a && nts <= b) || (a == 0) then
                Deque.enqueue_back ts_tp_in (nts, ntp)
              else
                Deque.enqueue_back ts_tp_out (nts, ntp)) in
  (ts_tp_out, ts_tp_in)

let adjust_ts_tp_future a first_ts ntp ts_tp_out ts_tp_in =
  let () = Deque.iter ts_tp_in
             ~f:(fun (ts', tp') ->
               if (ts' < first_ts + a) && (tp' < ntp) then Deque.enqueue_back ts_tp_out (ts', tp')) in
  let _ = remove_if_pred_front (fun (ts', tp') -> (ts' < first_ts) && (tp' < ntp)) ts_tp_out in
  let _ = remove_if_pred_front (fun (ts', tp') -> (ts' < first_ts + a) && (tp' < ntp)) ts_tp_in in
  (ts_tp_out, ts_tp_in)

module Once = struct
  type moaux = {
      ts_zero: timestamp option
    ; ts_tp_in: (timestamp * timepoint) Deque.t
    ; ts_tp_out: (timestamp * timepoint) Deque.t
    ; s_alphas_in: (timestamp * expl) Deque.t
    ; s_alphas_out: (timestamp * expl) Deque.t
    ; v_alphas_in: (timestamp * vexpl) Deque.t
    ; v_alphas_out: (timestamp * vexpl) Deque.t
    ; }

  let moaux_to_string { ts_zero
                      ; ts_tp_in
                      ; ts_tp_out
                      ; s_alphas_in
                      ; s_alphas_out
                      ; v_alphas_in
                      ; v_alphas_out } =
    "\n\nmoaux: " ^
      (match ts_zero with
       | None -> ""
       | Some(ts) -> Printf.sprintf "\nts_zero = (%d)\n" ts) ^
      Deque.fold ts_tp_in ~init:"\nts_in = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
      Deque.fold ts_tp_out ~init:"\nts_out = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
      Deque.fold s_alphas_in ~init:"\ns_alphas_in = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string p) ^
      Deque.fold s_alphas_out ~init:"\ns_alphas_out = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string p) ^
      Deque.fold v_alphas_in ~init:"\nv_alphas_in = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.v_to_string "" p) ^
      Deque.fold v_alphas_out ~init:"\nv_alphas_out = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.v_to_string "" p)

  let update_tss (l, r) a ts tp aux =
    if a = 0 then
      let () = Deque.enqueue_back aux.ts_tp_in (ts, tp) in
      let ts_tp_in = remove_if_pred_front (fun (ts', _) -> ts' < l) aux.ts_tp_in in
      { aux with ts_tp_in }
    else
      let () = Deque.enqueue_back aux.ts_tp_out (ts, tp) in
      let () = Deque.iter aux.ts_tp_out
                 ~f:(fun (ts', tp') ->
                   if ts' <= r then
                     Deque.enqueue_back aux.ts_tp_in (ts', tp')) in
      let ts_tp_out = remove_if_pred_front (fun (ts', _) -> ts' <= r) aux.ts_tp_out in
      let ts_tp_in = remove_if_pred_front (fun (ts', _) -> ts' < l) aux.ts_tp_in in
      { aux with ts_tp_out; ts_tp_in }

  let update_s_alphas_in new_in_sat s_alphas_in le =
    if (Deque.is_empty new_in_sat) then s_alphas_in
    else sorted_append new_in_sat s_alphas_in le

  let update_v_alphas_in new_in_viol v_alphas_in =
    let () = Deque.iter new_in_viol (fun (ts, vp) ->
                 Deque.enqueue_back v_alphas_in (ts, vp)) in
    v_alphas_in

  let eval_moaux tp moaux =
    if not (Deque.is_empty moaux.s_alphas_in) then
      S (SOnce (tp, unS(snd(Deque.peek_front_exn moaux.s_alphas_in))))
    else
      let etp = match Deque.is_empty moaux.v_alphas_in with
        | true -> etp moaux.ts_tp_in moaux.ts_tp_out tp
        | false -> v_at (snd(Deque.peek_front_exn moaux.v_alphas_in)) in
      let v_alphas_in' = List.rev(Deque.fold moaux.v_alphas_in ~init:[]
                                    ~f:(fun acc (_, vp1) -> vp1::acc)) in
      V (VOnce (tp, etp, v_alphas_in'))

  let add_to_moaux ts p1 moaux le =
    match p1 with
    | S sp1 -> let () = Deque.enqueue_back moaux.s_alphas_out (ts, (S sp1)) in moaux
    | V vp1 -> let () = Deque.enqueue_back moaux.v_alphas_out (ts, vp1) in moaux

  let remove_from_moaux (l, r) moaux =
    let s_alphas_in = remove_if_pred_front (fun (ts, _) -> ts < l) moaux.s_alphas_in in
    let s_alphas_out = remove_if_pred_front (fun (ts, _) -> ts <= r) moaux.s_alphas_out in
    let v_alphas_in = remove_if_pred_front (fun (ts, _) -> ts < l) moaux.v_alphas_in in
    let v_alphas_out = remove_if_pred_front (fun (ts, _) -> ts <= r) moaux.v_alphas_out in
    { moaux with s_alphas_in
               ; s_alphas_out
               ; v_alphas_in
               ; v_alphas_out }

  let shift_moaux (l, r) ts tp p1 moaux le =
    let moaux = add_to_moaux ts p1 moaux le in
    let s_alphas_out, new_in_sat = split_in_out (fun (ts, _) -> ts) (l, r) moaux.s_alphas_out in
    let s_alphas_in = update_s_alphas_in new_in_sat moaux.s_alphas_in le in
    (* let () = Printf.printf "|v_alphas_out| = %d\n" (Deque.length moaux.v_alphas_out) in *)
    (* let () = Printf.printf "|v_alphas_in| = %d\n" (Deque.length moaux.v_alphas_in) in *)
    let v_alphas_out, new_in_viol = split_in_out (fun (ts, _) -> ts) (l, r) moaux.v_alphas_out in
    let v_alphas_in = update_v_alphas_in new_in_viol moaux.v_alphas_in in
    let moaux = remove_from_moaux (l, r) moaux in
    let moaux = { moaux with s_alphas_out
                           ; s_alphas_in
                           ; v_alphas_out
                           ; v_alphas_in } in
    (* let () = Printf.printf "|v_alphas_out| = %d\n" (Deque.length moaux.v_alphas_out) in *)
    (* let () = Printf.printf "|v_alphas_in| = %d\n" (Deque.length moaux.v_alphas_in) in *)
    moaux

  let update_once interval ts tp p1 moaux le =
    (* let () = Printf.printf "tp = %d\n" tp in *)
    let a = get_a_I interval in
    if ((Option.is_none moaux.ts_zero) && a > 0) ||
         (Option.is_some moaux.ts_zero) && ts < (Option.get moaux.ts_zero) + a then
      let l = (-1) in
      let r = (-1) in
      let ts_zero = if Option.is_none moaux.ts_zero then Some(ts) else moaux.ts_zero in
      let moaux_ts_updated = update_tss (l, r) a ts tp moaux in
      let moaux_updated = shift_moaux (l, r) ts tp p1 moaux_ts_updated le in
      let p = V (VOnceOutL tp) in
      (p, { moaux_updated with ts_zero })
    else
      let ts_zero = if Option.is_none moaux.ts_zero then Some(ts) else moaux.ts_zero in
      let b = get_b_I interval in
      let l = if (Option.is_some b) then max 0 (ts - (Option.get b))
              else (Option.get ts_zero) in
      let r = ts - a in
      let moaux = update_tss (l, r) a ts tp moaux in
      let moaux = shift_moaux (l, r) ts tp p1 moaux le in
      let moaux = { moaux with ts_zero } in
      (* let () = Printf.printf "|v_alphas_out| = %d\n" (Deque.length moaux.v_alphas_out) in *)
      (* let () = Printf.printf "%s\n" (moaux_to_string moaux) in *)
      (eval_moaux tp moaux, moaux)

end

module Historically = struct
  type mhaux = {
      ts_zero: timestamp option
    ; ts_tp_in: (timestamp * timepoint) Deque.t
    ; ts_tp_out: (timestamp * timepoint) Deque.t
    ; s_alphas_in: (timestamp * sexpl) Deque.t
    ; s_alphas_out: (timestamp * sexpl) Deque.t
    ; v_alphas_in: (timestamp * expl) Deque.t
    ; v_alphas_out: (timestamp * expl) Deque.t
    ; }

  let mhaux_to_string { ts_zero
                      ; ts_tp_in
                      ; ts_tp_out
                      ; s_alphas_in
                      ; s_alphas_out
                      ; v_alphas_in
                      ; v_alphas_out } =
    "\n\nmoaux: " ^
      (match ts_zero with
       | None -> ""
       | Some(ts) -> Printf.sprintf "\nts_zero = (%d)\n" ts) ^
      Deque.fold ts_tp_in ~init:"\nts_in = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
      Deque.fold ts_tp_out ~init:"\nts_out = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
      Deque.fold s_alphas_in ~init:"\ns_alphas_in = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.s_to_string "" p) ^
      Deque.fold s_alphas_out ~init:"\ns_alphas_out = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.s_to_string "" p) ^
      Deque.fold v_alphas_in ~init:"\nv_alphas_in = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string p) ^
      Deque.fold v_alphas_in ~init:"\nv_alphas_out = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string p)

  let update_tss (l, r) a ts tp aux =
    if a = 0 then
      let () = Deque.enqueue_back aux.ts_tp_in (ts, tp) in
      let ts_tp_in = remove_if_pred_front (fun (ts', _) -> ts' < l) aux.ts_tp_in in
      { aux with ts_tp_in }
    else
      let () = Deque.enqueue_back aux.ts_tp_out (ts, tp) in
      let () = Deque.iter aux.ts_tp_out
                 ~f:(fun (ts', tp') ->
                   if ts' <= r then
                     Deque.enqueue_back aux.ts_tp_in (ts', tp')) in
      let ts_tp_out = remove_if_pred_front (fun (ts', _) -> ts' <= r) aux.ts_tp_out in
      let ts_tp_in = remove_if_pred_front (fun (ts', _) -> ts' < l) aux.ts_tp_in in
      { aux with ts_tp_out; ts_tp_in }

  let update_s_alphas_in new_in_sat s_alphas_in =
    let () = Deque.iter new_in_sat (fun (ts, sp) ->
                 Deque.enqueue_back s_alphas_in (ts, sp)) in
    s_alphas_in

  let update_v_alphas_in new_in_viol v_alphas_in le =
    if (Deque.is_empty new_in_viol) then v_alphas_in
    else sorted_append new_in_viol v_alphas_in le

  let eval_mhaux tp mhaux =
    if not (Deque.is_empty mhaux.v_alphas_in) then
      V (VHistorically (tp, unV(snd(Deque.peek_front_exn mhaux.v_alphas_in))))
    else
      let etp = match Deque.is_empty mhaux.s_alphas_in with
        | true -> etp mhaux.ts_tp_in mhaux.ts_tp_out tp
        | false -> s_at (snd(Deque.peek_front_exn mhaux.s_alphas_in)) in
      let s_alphas_in' = List.rev(Deque.fold mhaux.s_alphas_in ~init:[]
                                    ~f:(fun acc (_, sp1) -> sp1::acc)) in
      S (SHistorically (tp, etp, s_alphas_in'))

  let add_to_mhaux ts p1 mhaux le =
    match p1 with
    | S sp1 -> let () = Deque.enqueue_back mhaux.s_alphas_out (ts, sp1) in mhaux
    | V vp1 -> let () = Deque.enqueue_back mhaux.v_alphas_out (ts, (V vp1)) in mhaux

  let remove_from_mhaux (l, r) mhaux =
    let s_alphas_in = remove_if_pred_front (fun (ts, _) -> ts < l) mhaux.s_alphas_in in
    let s_alphas_out = remove_if_pred_front (fun (ts, _) -> ts <= r) mhaux.s_alphas_out in
    let v_alphas_in = remove_if_pred_front (fun (ts, _) -> ts < l) mhaux.v_alphas_in in
    let v_alphas_out = remove_if_pred_front (fun (ts, _) -> ts <= r) mhaux.v_alphas_out in
    { mhaux with s_alphas_in
               ; s_alphas_out
               ; v_alphas_in
               ; v_alphas_out }

  let shift_mhaux (l, r) ts tp p1 mhaux le =
    let mhaux_plus_new = add_to_mhaux ts p1 mhaux le in
    let s_alphas_out, new_in_sat = split_in_out (fun (ts, _) -> ts) (l, r) mhaux_plus_new.s_alphas_out in
    let s_alphas_in = update_s_alphas_in new_in_sat mhaux_plus_new.s_alphas_in in
    let v_alphas_out, new_in_viol = split_in_out (fun (ts, _) -> ts) (l, r) mhaux_plus_new.v_alphas_out in
    let v_alphas_in = update_v_alphas_in new_in_viol mhaux_plus_new.v_alphas_in le in
    let mhaux_minus_old = remove_from_mhaux (l, r) mhaux_plus_new in
    { mhaux_minus_old with s_alphas_out
                         ; s_alphas_in
                         ; v_alphas_out
                         ; v_alphas_in}

  let update_historically interval ts tp p1 mhaux le =
    let a = get_a_I interval in
    if ((Option.is_none mhaux.ts_zero) && a > 0) ||
         (Option.is_some mhaux.ts_zero) && ts < (Option.get mhaux.ts_zero) + a then
      let l = (-1) in
      let r = (-1) in
      let ts_zero = if Option.is_none mhaux.ts_zero then Some(ts) else mhaux.ts_zero in
      let mhaux_ts_updated = update_tss (l, r) a ts tp mhaux in
      let mhaux_updated = shift_mhaux (l, r) ts tp p1 mhaux_ts_updated le in
      let p = S (SHistoricallyOutL tp) in
      (p, { mhaux_updated with ts_zero })
    else
      let ts_zero = if Option.is_none mhaux.ts_zero then Some(ts) else mhaux.ts_zero in
      let b = get_b_I interval in
      let l = if (Option.is_some b) then max 0 (ts - (Option.get b))
              else (Option.get ts_zero) in
      let r = ts - a in
      let mhaux_ts_updated = update_tss (l, r) a ts tp mhaux in
      let mhaux_updated = shift_mhaux (l, r) ts tp p1 mhaux_ts_updated le in
      (eval_mhaux tp { mhaux_updated with ts_zero }, { mhaux_updated with ts_zero })

end

module Eventually = struct
  type meaux = {
      ts_tp_out: (timestamp * timepoint) Deque.t
    ; ts_tp_in: (timestamp * timepoint) Deque.t
    ; s_alphas_in: (timestamp * expl) Deque.t
    ; v_alphas_in: (timestamp * vexpl) Deque.t
    ; optimal_proofs: (timestamp * expl) Deque.t
    ; }

  let meaux_to_string { ts_tp_out
                      ; ts_tp_in
                      ; s_alphas_in
                      ; v_alphas_in
                      ; optimal_proofs } =
    "\n\nmeaux: " ^
      Deque.fold ts_tp_out ~init:"\nts_out = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
      Deque.fold ts_tp_in ~init:"\nts_in = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
      Deque.fold s_alphas_in ~init:"\ns_alphas_in = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string p) ^
      Deque.fold v_alphas_in ~init:"\nv_alphas_in = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.v_to_string "" p) ^
      Deque.fold optimal_proofs ~init:"\noptimal_proofs = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string p)

  let drop_first_ts_tp meaux =
    match Deque.peek_front meaux.ts_tp_out with
    | None -> Deque.drop_front meaux.ts_tp_in
    | Some (_) -> Deque.drop_front meaux.ts_tp_out

  let adjust_meaux a (nts, ntp) meaux le =
    let current_tp = match first_ts_tp meaux.ts_tp_out meaux.ts_tp_in with
      | None -> raise (NOT_FOUND "tp not found")
      | Some(_, tp') -> tp' in
    let () = drop_first_ts_tp meaux in
    let (first_ts, first_tp) = match first_ts_tp meaux.ts_tp_out meaux.ts_tp_in with
      | None -> (nts, ntp)
      | Some(ts', tp') -> (ts', tp') in
    (* let () = Printf.printf "adjust_meaux current_tp = %d; (first_ts, first_tp) = (%d,%d)\n" current_tp first_ts first_tp in *)
    let s_alphas_in = remove_if_pred_front (fun (ts', p) -> (ts' < first_ts + a) || (p_at p < first_tp)) meaux.s_alphas_in in
    let v_alphas_in = remove_if_pred_front (fun (ts', vp) -> ts' < first_ts + a || (v_at vp < first_tp)) meaux.v_alphas_in in
    let (ts_tp_out, ts_tp_in) = adjust_ts_tp_future a first_ts ntp meaux.ts_tp_out meaux.ts_tp_in in
    { meaux with ts_tp_out; ts_tp_in; s_alphas_in; v_alphas_in }

  let eval_step_meaux a (nts, ntp) ts tp meaux le =
    (* let () = Printf.printf "eval_step_meaux nts = %d; ntp = %d\n" nts ntp in *)
    let () = if not (Deque.is_empty meaux.s_alphas_in) then
               (match Deque.peek_front_exn meaux.s_alphas_in with
                | (_, S sp) -> Deque.enqueue_back meaux.optimal_proofs
                                 (ts, S (SEventually (tp, unS(snd(Deque.peek_front_exn meaux.s_alphas_in)))))
                | _ -> raise VEXPL)
             else
               (let ltp = match Deque.peek_back meaux.v_alphas_in with
                  | None -> snd(Deque.peek_back_exn meaux.ts_tp_out)
                  | Some (_, vp2) -> v_at vp2 in
                let v_alphas_in' = List.rev(Deque.fold meaux.v_alphas_in ~init:[]
                                              ~f:(fun acc (_, vp1) -> vp1::acc)) in
                Deque.enqueue_back meaux.optimal_proofs (ts, V (VEventually (tp, ltp, v_alphas_in')))) in
  let meaux = adjust_meaux a (nts, ntp) meaux le in meaux

  let shift_meaux (a, b) (nts, ntp) le meaux =
    let ts_tps = ready_ts_tps b nts meaux.ts_tp_out meaux.ts_tp_in in
    Deque.fold ts_tps ~init:meaux
      ~f:(fun meaux' (ts, tp) -> eval_step_meaux a (nts, ntp) ts tp meaux' le)

  let add_subps a (ts, tp) p1 le meaux =
    let first_ts = match first_ts_tp meaux.ts_tp_out meaux.ts_tp_in with
      | None -> 0
      | Some(ts', _) -> ts' in
    match p1 with
    | S sp1 -> if ts >= (first_ts + a) then
                 let s_alphas_in = sorted_enqueue (ts, (S sp1)) meaux.s_alphas_in le in
                 { meaux with s_alphas_in }
               else meaux
    | V vp1 -> if ts >= (first_ts + a) then
                 let () = Deque.enqueue_back meaux.v_alphas_in (ts, vp1) in meaux
               else meaux

  let update_eventually interval nts ntp p le meaux =
    let a = get_a_I interval in
    let b = match get_b_I interval with
      | None -> raise UNBOUNDED_FUTURE
      | Some(b') -> b' in
    let meaux = shift_meaux (a, b) (nts, ntp) le meaux in
    let (ts_tp_out, ts_tp_in) = add_ts_tp_future a b nts ntp meaux.ts_tp_out meaux.ts_tp_in in
    let meaux = { meaux with ts_tp_out; ts_tp_in } in
    let meaux = add_subps a (nts, ntp) p le meaux in
    meaux

  let rec eval_eventually d interval nts ntp le meaux =
    let a = get_a_I interval in
    let b = match get_b_I interval with
      | None -> raise UNBOUNDED_FUTURE
      | Some(b') -> b' in
    let meaux = shift_meaux (a, b) (nts, ntp) le meaux in
    match Deque.peek_back meaux.optimal_proofs with
    | None -> (nts, d, meaux)
    | Some(ts, _) -> if ts + b < nts then
                       let (ts', op) = Deque.dequeue_back_exn meaux.optimal_proofs in
                       let (_, ops, meaux) = eval_eventually d interval nts ntp le meaux in
                       let _ = Deque.enqueue_back ops op in
                       (ts', ops, meaux)
                     else (ts, d, meaux)

end

module Always = struct
  type maaux = {
      ts_tp_out: (timestamp * timepoint) Deque.t
    ; ts_tp_in: (timestamp * timepoint) Deque.t
    ; v_alphas_in: (timestamp * expl) Deque.t
    ; s_alphas_in: (timestamp * sexpl) Deque.t
    ; optimal_proofs: (timestamp * expl) Deque.t
    ; }

  let maaux_to_string { ts_tp_out
                      ; ts_tp_in
                      ; v_alphas_in
                      ; s_alphas_in
                      ; optimal_proofs } =
    "\n\nmaaux: " ^
      Deque.fold ts_tp_out ~init:"\nts_out = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
      Deque.fold ts_tp_in ~init:"\nts_in = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
      Deque.fold v_alphas_in ~init:"\nv_alphas_in = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string p) ^
      Deque.fold s_alphas_in ~init:"\ns_alphas_in = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.s_to_string "" p) ^
      Deque.fold optimal_proofs ~init:"\noptimal_proofs = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string p)

  let drop_first_ts_tp maaux =
    match Deque.peek_front maaux.ts_tp_out with
    | None -> Deque.drop_front maaux.ts_tp_in
    | Some (_) -> Deque.drop_front maaux.ts_tp_out

  let adjust_maaux a (nts, ntp) maaux le =
    let current_tp = match first_ts_tp maaux.ts_tp_out maaux.ts_tp_in with
      | None -> raise (NOT_FOUND "tp not found")
      | Some(_, tp') -> tp' in
    let () = drop_first_ts_tp maaux in
    let (first_ts, first_tp) = match first_ts_tp maaux.ts_tp_out maaux.ts_tp_in with
      | None -> (nts, ntp)
      | Some(ts', tp') -> (ts', tp') in
    let v_alphas_in = remove_if_pred_front (fun (ts', p) -> (ts' < first_ts + a) || (p_at p < first_tp)) maaux.v_alphas_in in
    let s_alphas_in = remove_if_pred_front (fun (ts', sp) -> ts' < first_ts + a || (s_at sp < first_tp)) maaux.s_alphas_in in
    let (ts_tp_out, ts_tp_in) = adjust_ts_tp_future a first_ts ntp maaux.ts_tp_out maaux.ts_tp_in in
    { maaux with ts_tp_out; ts_tp_in; s_alphas_in; v_alphas_in }

  let eval_step_maaux a (nts, ntp) ts tp maaux le =
    let () = if not (Deque.is_empty maaux.v_alphas_in) then
               (match Deque.peek_front_exn maaux.v_alphas_in with
                | (_, V vp) -> Deque.enqueue_back maaux.optimal_proofs
                                 (ts, V (VAlways (tp, unV(snd(Deque.peek_front_exn maaux.v_alphas_in)))))
                | _ -> raise VEXPL)
             else
               (let ltp = match Deque.peek_back maaux.s_alphas_in with
                  | None -> snd(Deque.peek_back_exn maaux.ts_tp_out)
                  | Some (_, sp) -> s_at sp in
                let s_alphas_in' = List.rev(Deque.fold maaux.s_alphas_in ~init:[]
                                              ~f:(fun acc (_, sp) -> sp::acc)) in
                Deque.enqueue_back maaux.optimal_proofs (ts, S (SAlways (tp, ltp, s_alphas_in')))) in
  let maaux = adjust_maaux a (nts, ntp) maaux le in maaux

  let shift_maaux (a, b) (nts, ntp) le maaux =
    let ts_tps = ready_ts_tps b nts maaux.ts_tp_out maaux.ts_tp_in in
    Deque.fold ts_tps ~init:maaux
      ~f:(fun maaux' (ts, tp) -> eval_step_maaux a (nts, ntp) ts tp maaux' le)

  let add_subps a (ts, tp) p1 le maaux =
    let first_ts = match first_ts_tp maaux.ts_tp_out maaux.ts_tp_in with
      | None -> 0
      | Some(ts', _) -> ts' in
    match p1 with
    | V vp1 -> if ts >= (first_ts + a) then
                 let v_alphas_in = sorted_enqueue (ts, (V vp1)) maaux.v_alphas_in le in
                 { maaux with v_alphas_in }
               else maaux
    | S sp1 -> if ts >= (first_ts + a) then
                 let () = Deque.enqueue_back maaux.s_alphas_in (ts, sp1) in maaux
               else maaux

  let update_always interval nts ntp p le maaux =
    (* let () = Printf.printf "update_until nts = %d; ntp = %d\n" nts ntp in *)
    let a = get_a_I interval in
    let b = match get_b_I interval with
      | None -> raise UNBOUNDED_FUTURE
      | Some(b') -> b' in
    let maaux = shift_maaux (a, b) (nts, ntp) le maaux in
    let (ts_tp_out, ts_tp_in) = add_ts_tp_future a b nts ntp maaux.ts_tp_out maaux.ts_tp_in in
    let maaux = { maaux with ts_tp_out; ts_tp_in } in
    let maaux = add_subps a (nts, ntp) p le maaux in
    maaux

  let rec eval_always d interval nts ntp le maaux =
    let a = get_a_I interval in
    let b = match get_b_I interval with
      | None -> raise UNBOUNDED_FUTURE
      | Some(b') -> b' in
    let maaux = shift_maaux (a, b) (nts, ntp) le maaux in
    match Deque.peek_back maaux.optimal_proofs with
    | None -> (nts, d, maaux)
    | Some(ts, _) -> if ts + b < nts then
                       let (ts', op) = Deque.dequeue_back_exn maaux.optimal_proofs in
                       let (_, ops, maaux) = eval_always d interval nts ntp le maaux in
                       let _ = Deque.enqueue_back ops op in
                       (ts', ops, maaux)
                     else (ts, d, maaux)

end

module Since = struct
  type msaux = {
      ts_zero: timestamp option
    ; ts_tp_in: (timestamp * timepoint) Deque.t
    ; ts_tp_out: (timestamp * timepoint) Deque.t

    (* sorted deque of S^+ beta [alphas] *)
    ; s_beta_alphas_in: (timestamp * expl) Deque.t
    (* deque of S^+ beta [alphas] outside of the interval *)
    ; s_beta_alphas_out: (timestamp * expl) Deque.t

    (* sorted deque of S^- alpha [betas] *)
    ; v_alpha_betas_in: (timestamp * expl) Deque.t
    (* sorted deque of alpha proofs *)
    ; v_alphas_out: (timestamp * expl) Deque.t
    (* list of beta violations inside the interval *)
    ; v_betas_in: (timestamp * vexpl) Deque.t
    (* list of alpha/beta violations *)
    ; v_alphas_betas_out: (timestamp * vexpl option * vexpl option) Deque.t
    ; }

  let print_ts_lists msaux =
    Printf.fprintf stdout "%s" (
    (match msaux.ts_zero with
     | None -> ""
     | Some(ts) -> Printf.sprintf "\n\tts_zero = (%d)\n" ts) ^
    Deque.fold msaux.ts_tp_in ~init:"\n\tts_in = ["
      ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
    Deque.fold msaux.ts_tp_out ~init:"\n\tts_out = ["
      ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n"))

  let msaux_to_string { ts_zero
                      ; ts_tp_in
                      ; ts_tp_out
                      ; s_beta_alphas_in
                      ; s_beta_alphas_out
                      ; v_alpha_betas_in
                      ; v_alphas_out
                      ; v_betas_in
                      ; v_alphas_betas_out } =
    "\n\nmsaux: " ^
      (match ts_zero with
       | None -> ""
       | Some(ts) -> Printf.sprintf "\nts_zero = (%d)\n" ts) ^
      Deque.fold ts_tp_in ~init:"\nts_in = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
      Deque.fold ts_tp_out ~init:"\nts_out = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
      Deque.fold s_beta_alphas_in ~init:"\ns_beta_alphas_in = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps) ^
      Deque.fold s_beta_alphas_out ~init:"\ns_beta_alphas_out = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps) ^
      Deque.fold v_alpha_betas_in ~init:"\nv_alpha_betas_in = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps) ^
      Deque.fold v_alphas_out ~init:"\nv_alphas_out = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps) ^
      Deque.fold v_betas_in ~init:"\nv_betas_in = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.v_to_string "" ps) ^
      Deque.fold v_alphas_betas_out ~init:"\nv_alphas_betas_out = "
        ~f:(fun acc (ts, p1_opt, p2_opt) ->
          match p1_opt, p2_opt with
          | None, None -> acc
          | Some(p1), None -> acc ^ (Printf.sprintf "\n(%d)\nalpha = " ts) ^
                              Expl.v_to_string "" p1
          | None, Some(p2) -> acc ^ (Printf.sprintf "\n(%d)\nbeta = " ts) ^
                              Expl.v_to_string "" p2
          | Some(p1), Some(p2) -> acc ^ (Printf.sprintf "\n(%d)\nalpha = " ts) ^
                                  Expl.v_to_string "" p1 ^
                                  (Printf.sprintf "\n(%d)\nbeta = " ts) ^
                                  Expl.v_to_string "" p2)

  let update_ts_tps (l, r) a ts tp aux =
    if a = 0 then
      let () = Deque.enqueue_back aux.ts_tp_in (ts, tp) in
      let ts_tp_in = remove_if_pred_front (fun (ts', _) -> ts' < l) aux.ts_tp_in in
      { aux with ts_tp_in }
    else
      let () = Deque.enqueue_back aux.ts_tp_out (ts, tp) in
      let () = Deque.iter aux.ts_tp_out
                ~f:(fun (ts', tp') ->
                  if ts' <= r then
                    Deque.enqueue_back aux.ts_tp_in (ts', tp')) in
      let ts_tp_out = remove_if_pred_front (fun (ts', _) -> ts' <= r) aux.ts_tp_out in
      let ts_tp_in = remove_if_pred_front (fun (ts', _) -> ts' < l) aux.ts_tp_in in
      { aux with ts_tp_out; ts_tp_in }

  let add_v_alphas_out ts vvp' v_alphas_out le =
    let alphas_out' = remove_if_pred_back (fun (_, vvp) -> le vvp' vvp) v_alphas_out in
    let () = Deque.enqueue_back alphas_out' (ts, vvp')
    in v_alphas_out

  let update_s_beta_alphas_in new_in s_beta_alphas_in le =
    if (Deque.is_empty new_in) then s_beta_alphas_in
    else sorted_append new_in s_beta_alphas_in le

  let update_v_betas_in new_in v_betas_in =
    let () = Deque.iter new_in
              ~f:(fun (ts, _, vp2_opt) ->
                match vp2_opt with
                | None -> Deque.clear v_betas_in
                | Some(vp2) -> Deque.enqueue_back v_betas_in (ts, vp2))
    in v_betas_in

  let construct_vsinceps tp new_in =
    Deque.fold new_in ~init:(Deque.create ())
      ~f:(fun acc (ts, vp1_opt, vp2_opt) ->
        match vp1_opt with
        | None ->
           (match vp2_opt with
            | None -> (let () = Deque.clear acc in acc)
            | Some(vp2) -> (let new_acc = vappend_to_deque vp2 acc in new_acc))
        | Some(vp1) ->
           (match vp2_opt with
            | None -> (let () = Deque.clear acc in acc)
            | Some(vp2) -> (let new_acc = vappend_to_deque vp2 acc in
                            let vp = V (VSince (tp, vp1, [vp2])) in
                            let () = Deque.enqueue_back new_acc (ts, vp) in
                            new_acc)))

  let add_new_ps_v_alpha_betas_in tp new_in v_alpha_betas_in le =
    let new_vps_in = construct_vsinceps tp new_in in
    if not (Deque.is_empty new_vps_in) then
      sorted_append new_vps_in v_alpha_betas_in le
    else v_alpha_betas_in

  let update_v_alpha_betas_in_tps tp v_alpha_betas_in =
    let () = Deque.iteri v_alpha_betas_in ~f:(fun i (ts, vvp) ->
                 match vvp with
                 | V (VSince (tp', vp1, vp2s)) -> Deque.set_exn v_alpha_betas_in i (ts, V (VSince (tp, vp1, vp2s)))
                 | _ -> raise (INVALID_EXPL "Explanation should be VSince")) in
    v_alpha_betas_in

  let update_v_alpha_betas_in tp new_in v_alpha_betas_in le =
    let alpha_betas_vapp = Deque.fold new_in ~init:v_alpha_betas_in
                             ~f:(fun d (_, _, vp2_opt) ->
                               match vp2_opt with
                               | None -> let _ = Deque.clear v_alpha_betas_in in d
                               | Some(vp2) -> vappend_to_deque vp2 d) in
    let alpha_betas' = add_new_ps_v_alpha_betas_in tp new_in alpha_betas_vapp le in
    (update_v_alpha_betas_in_tps tp alpha_betas')

  let add_to_msaux ts p1 p2 msaux le =
    match p1, p2 with
    | S sp1, S sp2 ->
       (* s_beta_alphas_in *)
       let s_beta_alphas_in = sappend_to_deque sp1 msaux.s_beta_alphas_in in
       (* s_beta_alphas_out *)
       let s_beta_alphas_out = sappend_to_deque sp1 msaux.s_beta_alphas_out in
       let sp = S (SSince (sp2, [])) in
       let () = Deque.enqueue_back s_beta_alphas_out (ts, sp) in
       (* v_alphas_betas_out *)
       let () = Deque.enqueue_back msaux.v_alphas_betas_out (ts, None, None) in
       { msaux with s_beta_alphas_in; s_beta_alphas_out }
    | S sp1, V vp2 ->
       (* s_beta_alphas_in *)
       let s_beta_alphas_in = sappend_to_deque sp1 msaux.s_beta_alphas_in in
       let s_beta_alphas_out = sappend_to_deque sp1 msaux.s_beta_alphas_out in
       (* v_alphas_betas_out *)
       let () = Deque.enqueue_back msaux.v_alphas_betas_out (ts, None, Some(vp2)) in
       { msaux with s_beta_alphas_in; s_beta_alphas_out }
    | V vp1, S sp2 ->
       (* s_beta_alphas_in *)
       let () = Deque.clear msaux.s_beta_alphas_in in
       (* s_beta_alphas_out *)
       let () = Deque.clear msaux.s_beta_alphas_out in
       let sp = S (SSince (sp2, [])) in
       let () = Deque.enqueue_back msaux.s_beta_alphas_out (ts, sp) in
       (* v_alphas_out *)
       let v_alphas_out = add_v_alphas_out ts (V vp1) msaux.v_alphas_out le in
       (* v_alphas_betas_out *)
       let () = Deque.enqueue_back msaux.v_alphas_betas_out (ts, Some(vp1), None) in
       { msaux with v_alphas_out }
    | V vp1, V vp2 ->
       (* s_beta_alphas_in *)
       let () = Deque.clear msaux.s_beta_alphas_in in
       (* s_beta_alphas_out *)
       let () = Deque.clear msaux.s_beta_alphas_out in
       (* v_alphas_out *)
       let v_alphas_out = add_v_alphas_out ts (V vp1) msaux.v_alphas_out le in
       (* v_alphas_betas_out *)
       let () = Deque.enqueue_back msaux.v_alphas_betas_out (ts, Some(vp1), Some(vp2)) in
       { msaux with v_alphas_out }

  let remove_from_msaux (l, r) msaux =
    let s_beta_alphas_in = remove_if_pred_front (fun (ts, _) -> ts < l) msaux.s_beta_alphas_in in
    let v_alpha_betas_in = remove_if_pred_front (fun (ts, _) -> ts < l) msaux.v_alpha_betas_in in
    let v_alphas_out = remove_if_pred_front (fun (ts, _) -> ts <= r) msaux.v_alphas_out in
    let v_betas_in = remove_if_pred_front (fun (ts, _) -> ts < l) msaux.v_betas_in in
    { msaux with s_beta_alphas_in
               ; v_alpha_betas_in
               ; v_alphas_out
               ; v_betas_in }

  let shift_msaux (l, r) ts tp p1 p2 msaux le =
    let msaux_plus_new = add_to_msaux ts p1 p2 msaux le in
    let msaux_minus_old = remove_from_msaux (l, r) msaux_plus_new in
    let s_beta_alphas_out, new_in_sat = split_in_out (fun (ts, _) -> ts) (l, r) msaux_minus_old.s_beta_alphas_out in
    let s_beta_alphas_in = update_s_beta_alphas_in new_in_sat msaux_minus_old.s_beta_alphas_in le in
    let v_alphas_betas_out, new_in_viol = split_in_out (fun (ts, _, _) -> ts) (l, r) msaux_minus_old.v_alphas_betas_out in
    let v_betas_in = update_v_betas_in new_in_viol msaux_minus_old.v_betas_in in
    let v_alpha_betas_in = update_v_alpha_betas_in tp new_in_viol msaux_minus_old.v_alpha_betas_in le in
    { msaux_minus_old with s_beta_alphas_in
                         ; s_beta_alphas_out
                         ; v_alpha_betas_in
                         ; v_betas_in }


  let eval_msaux tp le msaux =
    if not (Deque.is_empty msaux.s_beta_alphas_in) then
      snd(Deque.peek_front_exn msaux.s_beta_alphas_in)
    else
      let p1 = if not (Deque.is_empty msaux.v_alpha_betas_in) then
                 [snd(Deque.peek_front_exn msaux.v_alpha_betas_in)]
               else [] in
      let p2 = if not (Deque.is_empty msaux.v_alphas_out) then
                 let vp_f2 = snd(Deque.peek_front_exn msaux.v_alphas_out) in
                 match vp_f2 with
                 | V f2 -> [V (VSince (tp, f2, []))]
                 | S _ -> raise VEXPL
               else [] in
      let p3 = if (Deque.length msaux.v_betas_in) = (Deque.length msaux.ts_tp_in) then
                 let etp = match Deque.is_empty msaux.v_betas_in with
                   | true -> etp msaux.ts_tp_in msaux.ts_tp_out tp
                   | false -> v_at (snd(Deque.peek_front_exn msaux.v_betas_in)) in
                 let betas_suffix = betas_suffix_in_to_list msaux.v_betas_in in
                 [V (VSinceInf (tp, etp, betas_suffix))]
               else [] in
      minimuml le (p1 @ p2 @ p3)

  let update_since interval ts tp p1 p2 msaux le =
    let a = get_a_I interval in
    (* Case 1: interval has not yet started, i.e.,
     a > 0 OR (\tau_{tp} - a) < 0 *)
    let ts_zero = if Option.is_none msaux.ts_zero then Some(ts) else msaux.ts_zero in
    if ((Option.is_none msaux.ts_zero) && a > 0) ||
         (Option.is_some msaux.ts_zero) && ts < (Option.get msaux.ts_zero) + a then
      let l = (-1) in
      let r = (-1) in
      let msaux = { msaux with ts_zero } in
      let msaux = update_ts_tps (l, r) a ts tp msaux in
      let msaux = shift_msaux (l, r) ts tp p1 p2 msaux le in
      let p = V (VSinceOutL tp) in
      (p, msaux)
    (* Case 2: there exists a \tau_{tp'} inside the interval s.t. tp' < tp *)
    else
      let b = get_b_I interval in
      let l = if (Option.is_some b) then max 0 (ts - (Option.get b))
              else (Option.get ts_zero) in
      let r = ts - a in
      let msaux = { msaux with ts_zero } in
      let msaux = update_ts_tps (l, r) a ts tp msaux in
      let msaux = shift_msaux (l, r) ts tp p1 p2 msaux le in
      let p = eval_msaux tp le msaux in
      (p, msaux)
end

module Until = struct
  type muaux = {
      ts_tp_in: (timestamp * timepoint) Deque.t
    ; ts_tp_out: (timestamp * timepoint) Deque.t
    (* deque of sorted deques of U^+ beta [alphas] proofs where
     * ts corresponds to the timestamp of the beta proof *)
    ; alphas_beta: ((timestamp * expl) Deque.t) Deque.t
    (* most recent sequence of alpha satisfactions w/o holes *)
    ; alphas_suffix: (timestamp * sexpl) Deque.t
    (* deque of sorted deques of U^- ~alpha [~betas] proofs where
     * ts corresponds to the timestamp of the ~alpha proof *)
    ; betas_alpha: ((timestamp * expl) Deque.t) Deque.t
    (* sorted deque of alpha proofs outside the interval *)
    ; v_alphas_out: (timestamp * expl) Deque.t
    (* deque of alpha violations inside the interval *)
    ; alphas_in: (timestamp * expl) Deque.t
    (* deque of beta violations inside the interval *)
    ; betas_suffix_in: (timestamp * vexpl) Deque.t
    ; optimal_proofs: (timestamp * expl) Deque.t
    ; }

  let muaux_to_string { ts_tp_in
                      ; ts_tp_out
                      ; alphas_beta
                      ; alphas_suffix
                      ; betas_alpha
                      ; v_alphas_out
                      ; alphas_in
                      ; betas_suffix_in
                      ; optimal_proofs } =
    "\n\nmuaux: " ^
      Deque.fold ts_tp_in ~init:"\nts_tp_in = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d,%d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
      Deque.fold ts_tp_out ~init:"\nts_tp_out = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d,%d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
      Deque.foldi alphas_beta ~init:"\nalphas_beta = \n"
        ~f:(fun i acc1 d ->
          acc1 ^ Printf.sprintf "\n%d.\n" i ^
          Deque.fold d ~init:"["
            ~f:(fun acc2 (ts, ps) ->
              acc2 ^ (Printf.sprintf "\n(%d)\n" ts) ^
              Expl.expl_to_string ps) ^ "\n]\n") ^
      Deque.fold alphas_suffix ~init:"\nalphas_suffix = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.s_to_string "" ps) ^
      Deque.foldi betas_alpha ~init:"\nbetas_alpha = \n"
        ~f:(fun i acc1 d ->
          acc1 ^ Printf.sprintf "\n%d.\n" i ^
          Deque.fold d ~init:"["
            ~f:(fun acc2 (ts, ps) ->
              acc2 ^ (Printf.sprintf "\n(%d)\n" ts) ^
              Expl.expl_to_string ps) ^ "\n]\n") ^
      Deque.fold v_alphas_out ~init:"\nv_alphas_out = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps) ^
      Deque.fold alphas_in ~init:"\nalphas_in = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps) ^
      Deque.fold betas_suffix_in ~init:"\nbetas_suffix_in = "
        ~f:(fun acc (ts, p) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.v_to_string "" p) ^
      Deque.fold optimal_proofs ~init:"\noptimal_proofs = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps)

  let print_subf_pol p1 p2 =
    match p1, p2 with
    | S _, S _ -> Printf.printf "SS\n"
    | S _, V _ -> Printf.printf "SV\n"
    | V _, S _ -> Printf.printf "VS\n"
    | V _, V _ -> Printf.printf "VV\n"

  let ts_of_tp tp muaux =
    match (Deque.find muaux.ts_tp_out ~f:(fun (ts', tp') -> tp = tp')) with
    | None -> (match (Deque.find muaux.ts_tp_in ~f:(fun (ts', tp') -> tp = tp')) with
               | None -> raise (NOT_FOUND "ts not found")
               | Some(ts, _) -> ts)
    | Some(ts, _) -> ts

  let step_sdrop_tp tp alphas_beta =
    Deque.fold alphas_beta ~init:(Deque.create ())
               ~f:(fun acc (ts, ssp) ->
                 (match ssp with
                  | S sp -> if tp = (s_at sp) then
                              (match sdrop sp with
                               | None -> acc
                               | Some(sp') -> let () = Deque.enqueue_back acc (ts, S sp') in acc)
                            else let () = Deque.enqueue_back acc (ts, ssp) in acc
                  | V _ -> raise SEXPL))

  let step_vdrop_ts a first_ts betas_alpha muaux =
    let rec vdrop_until vp =
      let is_out = match Deque.find ~f:(fun (_, tp') -> (v_etp vp) = tp') muaux.ts_tp_in with
        | None -> true
        | Some(ts', _) -> ts' < (first_ts + a) in
      if is_out then
        (match vdrop vp with
         | None -> None
         | Some(vp') -> vdrop_until vp')
      else Some(vp) in
    Deque.fold betas_alpha ~init:(Deque.create ())
      ~f:(fun acc (ts, vvp) ->
        (match vvp with
         | V vp -> (match vdrop_until vp with
                    | None -> acc
                    | Some (vp') -> let () = Deque.enqueue_back acc (ts, V vp') in acc)
         | S _ -> raise VEXPL))

  let remove_out_less2_lts lim d =
    let () = Deque.iteri d ~f:(fun i d' ->
                 Deque.set_exn d i
                   (Deque.fold d' ~init:(Deque.create ())
                      ~f:(fun acc (ts, p) ->
                        let () = if ts >= lim then Deque.enqueue_back acc (ts, p) in acc))) in
    let _ = remove_if_pred_front_ne (fun d' -> Deque.is_empty d') d in
    d

  (* TODO: Remove the functions below (use Deque.to_list) *)
  let alphas_suffix_to_list alphas_suffix =
    List.rev(Deque.fold alphas_suffix ~init:[] ~f:(fun acc (_, sp1) -> sp1::acc))

  let betas_suffix_in_to_list betas_suffix_in =
    List.rev(Deque.fold betas_suffix_in ~init:[] ~f:(fun acc (_, vp2) -> vp2::acc))

  let add_subps a (ts, tp) p1 p2 le muaux =
    let first_ts = match first_ts_tp muaux.ts_tp_out muaux.ts_tp_in with
      | None -> 0
      | Some(ts', _) -> ts' in
    match p1, p2 with
    | S sp1, S sp2 ->
       (* alphas_beta *)
       let () = if ts >= (first_ts + a) then
                  (let cur_alphas_beta = Deque.peek_back_exn muaux.alphas_beta in
                   let sp = S (SUntil (sp2, (alphas_suffix_to_list muaux.alphas_suffix))) in
                   let cur_alphas_beta_sorted = sorted_enqueue (ts, sp) cur_alphas_beta le in
                   let () = Deque.drop_back muaux.alphas_beta in
                   Deque.enqueue_back muaux.alphas_beta cur_alphas_beta_sorted) in
       (* betas_alpha (add empty deque) *)
       let _ = if not (Deque.is_empty (Deque.peek_back_exn muaux.betas_alpha)) then
                 Deque.enqueue_back muaux.betas_alpha (Deque.create ()) in
       (* alphas_suffix *)
       let _ = Deque.enqueue_back muaux.alphas_suffix (ts, sp1) in
       (* v_betas_in *)
       let () = if ts >= (first_ts + a) then Deque.clear muaux.betas_suffix_in in
       muaux
    | S sp1, V vp2 ->
       (* alphas_suffix *)
       let _ = Deque.enqueue_back muaux.alphas_suffix (ts, sp1) in
       (* v_betas_in *)
       let () = if ts >= (first_ts + a) then Deque.enqueue_back muaux.betas_suffix_in (ts, vp2) in
       muaux
    | V vp1, S sp2 ->
       (* alphas_beta *)
       let () = if ts >= (first_ts + a) then
                  (let cur_alphas_beta = Deque.peek_back_exn muaux.alphas_beta in
                   let sp = S (SUntil (sp2, (alphas_suffix_to_list muaux.alphas_suffix))) in
                   let cur_alphas_beta_sorted = sorted_enqueue (ts, sp) cur_alphas_beta le in
                   let () = Deque.drop_back muaux.alphas_beta in
                   let () = Deque.enqueue_back muaux.alphas_beta cur_alphas_beta_sorted in
                   (* alphas_beta (append empty deque) *)
                   if not (Deque.is_empty (Deque.peek_back_exn muaux.alphas_beta)) then
                     Deque.enqueue_back muaux.alphas_beta (Deque.create ())) in
       (* betas_alpha (add empty deque) *)
       let _ = if not (Deque.is_empty (Deque.peek_back_exn muaux.betas_alpha)) then
                 Deque.enqueue_back muaux.betas_alpha (Deque.create ()) in
       (* alphas_suffix *)
       let _ = Deque.clear muaux.alphas_suffix in
       (* alphas_in *)
       let () = if ts >= (first_ts + a) then Deque.enqueue_back muaux.alphas_in (ts, V vp1)
                else (let _ = remove_if_pred_back (fun (_, p') -> le (V vp1) p') muaux.v_alphas_out in
                      Deque.enqueue_back muaux.v_alphas_out (ts, V vp1)) in
       (* v_betas_in *)
       let () = if ts >= (first_ts + a) then Deque.clear muaux.betas_suffix_in in
       muaux
    | V vp1, V vp2 ->
       (* alphas_beta (add empty deque) *)
       let _ = if not (Deque.is_empty (Deque.peek_back_exn muaux.alphas_beta)) then
                 Deque.enqueue_back muaux.alphas_beta (Deque.create ()) in
       (* alphas_suffix *)
       let _ = Deque.clear muaux.alphas_suffix in
       (* v_betas_in *)
       let () = if ts >= (first_ts + a) then Deque.enqueue_back muaux.betas_suffix_in (ts, vp2) in
       (* betas_alpha *)
       let () = if ts >= (first_ts + a) then
                  (let cur_betas_alpha = Deque.peek_back_exn muaux.betas_alpha in
                   let vp = V (VUntil (tp, vp1, (betas_suffix_in_to_list muaux.betas_suffix_in))) in
                   let cur_betas_alpha_sorted = sorted_enqueue (ts, vp) cur_betas_alpha le in
                   let () = Deque.drop_back muaux.betas_alpha in
                   Deque.enqueue_back muaux.betas_alpha cur_betas_alpha_sorted) in
       (* alphas_in *)
       let () = if ts >= (first_ts + a) then Deque.enqueue_back muaux.alphas_in (ts, V vp1)
                else (let _ = remove_if_pred_back (fun (_, p') -> le (V vp1) p') muaux.v_alphas_out in
                      Deque.enqueue_back muaux.v_alphas_out (ts, V vp1)) in
       muaux

  let drop_muaux_tp tp muaux =
    match Deque.peek_front muaux.alphas_beta with
    | None -> raise (EMPTY_DEQUE "alphas_beta")
    | Some(front_alphas_beta) -> if not (Deque.is_empty front_alphas_beta) then
                                   let front_index = Deque.front_index_exn muaux.alphas_beta in
                                   Deque.set_exn muaux.alphas_beta front_index (step_sdrop_tp tp front_alphas_beta)

  let drop_muaux_ts a ts muaux =
    Deque.iteri muaux.betas_alpha ~f:(fun i d ->
        Deque.set_exn muaux.betas_alpha i (step_vdrop_ts a ts d muaux))

  let drop_muaux_single_ts current_tp muaux =
      let first_betas_alpha = Deque.fold (Deque.peek_front_exn muaux.betas_alpha) ~init:(Deque.create ())
                                ~f:(fun acc (ts', vvp) ->
                                  (match vvp with
                                   | V vp -> if (v_etp vp) <= current_tp then
                                               (match vdrop vp with
                                                | None -> acc
                                                | Some (vp') -> let () = Deque.enqueue_back acc (ts', V vp') in acc)
                                             else (let () = Deque.enqueue_back acc (ts', V vp) in acc)
                                   | S _ -> raise VEXPL)) in
      let () = Deque.drop_front muaux.betas_alpha in
      Deque.enqueue_front muaux.betas_alpha first_betas_alpha

  let drop_first_ts_tp muaux =
    match Deque.peek_front muaux.ts_tp_out with
    | None -> Deque.drop_front muaux.ts_tp_in
    | Some (_) -> Deque.drop_front muaux.ts_tp_out

  let adjust_muaux a (nts, ntp) le muaux =
    let eval_tp = match first_ts_tp muaux.ts_tp_out muaux.ts_tp_in with
      | None -> raise (NOT_FOUND "tp not found")
      | Some(_, tp') -> tp' in
    let () = drop_first_ts_tp muaux in
    let (first_ts, first_tp) = match first_ts_tp muaux.ts_tp_out muaux.ts_tp_in with
      | None -> (nts, ntp)
      | Some(ts', tp') -> (ts', tp') in
    (* betas_alpha *)
    let () = Deque.iteri muaux.betas_alpha ~f:(fun i d ->
                 Deque.set_exn muaux.betas_alpha i
                   (remove_if_pred_front (fun (ts', p) -> (ts' < first_ts + a) || ((p_at p) < first_tp)) d)) in
    let () = if a = 0 then
               drop_muaux_single_ts eval_tp muaux
             else
               drop_muaux_ts a first_ts muaux in
    let _ = remove_if_pred_front_ne (fun d' -> Deque.is_empty d') muaux.betas_alpha in
    (* ts_tp_in and ts_tp_out *)
    let (ts_tp_out, ts_tp_in) = adjust_ts_tp_future a first_ts ntp muaux.ts_tp_out muaux.ts_tp_in in
    let muaux = { muaux with ts_tp_out; ts_tp_in } in
    (* alphas_beta *)
    let () = drop_muaux_tp eval_tp muaux in
    let () = Deque.iteri muaux.alphas_beta ~f:(fun i d ->
                 Deque.set_exn muaux.alphas_beta i
                   (remove_if_pred_front (fun (ts', p) -> match p with
                                                          | S sp -> (ts_of_tp (s_ltp sp) muaux) < (first_ts + a)
                                                          | V _ -> raise SEXPL) d)) in
    let _ = remove_if_pred_front_ne (fun d' -> Deque.is_empty d') muaux.alphas_beta in
    (* alphas_suffix *)
    let _ = remove_if_pred_front (fun (_, sp) -> (s_at sp) < first_tp) muaux.alphas_suffix in
    (* alphas_in and v_alphas_out *)
    let _ = remove_if_pred_front (fun (_, p) -> (p_at p) < first_tp) muaux.v_alphas_out in
    let alphas_in, new_out_alphas = split_out_in (fun (ts', _) -> ts') (first_ts, (first_ts + a)) muaux.alphas_in in
    (* let () = Printf.printf "\nnew_out_alphas = \n" in
     * let () = Deque.iter new_out_alphas ~f:(fun (ts, p) -> Printf.printf "%s\n" (Expl.expl_to_string p)) in *)
    let v_alphas_out = sorted_append new_out_alphas muaux.v_alphas_out le in
    (* v_betas_in *)
    let betas_suffix_in = remove_if_pred_front (fun (_, vp) ->
                              match Deque.peek_front muaux.ts_tp_in with
                              | None -> (match Deque.peek_back muaux.ts_tp_out with
                                         | None -> (v_at vp) <= ntp
                                         | Some(_, tp') -> (v_at vp) <= tp')
                              | Some (_, tp') -> (v_at vp) < tp') muaux.betas_suffix_in in
    { muaux with alphas_in
               ; v_alphas_out
               ; betas_suffix_in }

  let eval_step_muaux a (nts, ntp) ts tp le muaux =
    (* let () = Printf.printf "eval_step_muaux ts = %d; tp = %d\n" ts tp in *)
    (* let () = Printf.printf "\nbefore: %s\n" (muaux_to_string muaux) in *)
    let optimal_proofs_len = Deque.length muaux.optimal_proofs in
    let cur_alphas_beta = Deque.peek_front_exn muaux.alphas_beta in
    let () = (if not (Deque.is_empty cur_alphas_beta) then
                (match Deque.peek_front_exn cur_alphas_beta with
                 | (_, S sp) -> if tp = (s_at sp) then
                                  Deque.enqueue_back muaux.optimal_proofs (ts, S sp)
                 | _ -> raise VEXPL)) in
    let () = (if (Deque.length muaux.optimal_proofs) = optimal_proofs_len then
                (let p1 = if not (Deque.is_empty muaux.betas_alpha) then
                            let cur_betas_alpha = Deque.peek_front_exn muaux.betas_alpha in
                            (if not (Deque.is_empty cur_betas_alpha) then
                               match Deque.peek_front_exn cur_betas_alpha with
                               | (_, V VUntil(_, vp1, vp2s)) -> (match Deque.peek_front muaux.ts_tp_in with
                                                                 | None -> []
                                                                 | Some(_, first_tp_in) ->
                                                                    if (v_etp (VUntil(tp, vp1, vp2s))) = first_tp_in then
                                                                      [V (VUntil(tp, vp1, vp2s))]
                                                                    else [])
                               | _ -> raise (INVALID_EXPL "Explanation should be VUntil")
                             else [])
                          else [] in
                 let p2 = if not (Deque.is_empty muaux.v_alphas_out) then
                            let vvp1 = snd(Deque.peek_front_exn muaux.v_alphas_out) in
                            match vvp1 with
                            | V vp1 -> [V (VUntil (tp, vp1, []))]
                            | S _ -> raise VEXPL
                          else [] in
                 let p3 = let betas_suffix = betas_suffix_in_to_list muaux.betas_suffix_in in
                          if (List.length betas_suffix) = (Deque.length muaux.ts_tp_in) then
                            let ltp = match Deque.peek_back muaux.betas_suffix_in with
                              | None -> snd(Deque.peek_back_exn muaux.ts_tp_out)
                              | Some(_, vp2) -> (v_at vp2) in
                            [V (VUntilInf (tp, ltp, betas_suffix))]
                          else [] in
                 let cps = p1 @ p2 @ p3 in
                 if List.length cps > 0 then
                   Deque.enqueue_back muaux.optimal_proofs (ts, minimuml le cps))) in
    let muaux = adjust_muaux a (nts, ntp) le muaux in
    (* let () = Printf.printf "\nafter: %s\n" (muaux_to_string muaux) in *)
    muaux

  let shift_muaux (a, b) (nts, ntp) le muaux =
    (* let () = Printf.printf "shift_muaux nts = %d; ntp = %d\n" nts ntp in *)
    let ts_tps = ready_ts_tps b nts muaux.ts_tp_out muaux.ts_tp_in in
    Deque.fold ts_tps ~init:muaux
      ~f:(fun muaux' (ts, tp) -> eval_step_muaux a (nts, ntp) ts tp le muaux')

  let update_until interval nts ntp p1 p2 le muaux =
    (* let () = Printf.printf "update_until nts = %d; ntp = %d\n" nts ntp in *)
    let a = get_a_I interval in
    let b = match get_b_I interval with
      | None -> raise UNBOUNDED_FUTURE
      | Some(b') -> b' in
    let muaux = shift_muaux (a, b) (nts, ntp) le muaux in
    let (ts_tp_out, ts_tp_in) = add_ts_tp_future a b nts ntp muaux.ts_tp_out muaux.ts_tp_in in
    let muaux = { muaux with ts_tp_out; ts_tp_in } in
    let muaux = add_subps a (nts, ntp) p1 p2 le muaux in
    muaux

  let rec eval_until d interval nts ntp le muaux =
    let a = get_a_I interval in
    let b = match get_b_I interval with
      | None -> raise UNBOUNDED_FUTURE
      | Some(b') -> b' in
    let muaux = shift_muaux (a, b) (nts, ntp) le muaux in
    match Deque.peek_back muaux.optimal_proofs with
    | None -> (nts, d, muaux)
    | Some(ts, _) -> if ts + b < nts then
                       let (ts', op) = Deque.dequeue_back_exn muaux.optimal_proofs in
                       let (_, ops, muaux) = eval_until d interval nts ntp le muaux in
                       let _ = Deque.enqueue_back ops op in
                       (ts', ops, muaux)
                     else (ts, d, muaux)
end

module Prev_Next = struct

  type operator = Prev | Next

  let rec mprev_next_aux op interval buf tss le =
      let t = Deque.dequeue_front_exn tss in
      let t' = Deque.peek_front_exn tss in
      let p = Deque.dequeue_front_exn buf in
      let (ps, buf', tss') = mprev_next op interval buf tss le in
      let p1_l = (match p with
                  | S sp -> if (mem_I (t' - t) interval) then
                              (match op with
                               | Prev -> [S (SPrev sp)]
                               | Next -> [S (SNext sp)])
                            else []
                  | V vp -> (match op with
                             | Prev -> [V (VPrev vp)]
                             | Next -> [V (VNext vp)])) in
      let p2_l = if (below_I (t' - t) interval) then
                   (match op with
                    | Prev -> [V (VPrevOutL ((p_at p)+1))]
                    | Next -> [V (VNextOutL ((p_at p)-1))])
                 else [] in
      let p3_l = if (above_I (t' - t) interval) then
                   (match op with
                    | Prev -> [V (VPrevOutR ((p_at p)+1))]
                    | Next -> [V (VNextOutR ((p_at p)-1))])
                 else [] in
      let () = Deque.enqueue_front ps (minimuml le (p1_l @ p2_l @ p3_l)) in
      (ps, buf', tss')
  and mprev_next op interval buf tss le =
    match (Deque.is_empty buf, Deque.is_empty tss) with
    | true, _ -> ((Deque.create ()), (Deque.create ()), tss)
    | _, true -> ((Deque.create ()), buf, (Deque.create ()))
    | false, false when ((Deque.length tss) = 1) -> ((Deque.create ()), buf, tss)
    | false, false -> mprev_next_aux op interval buf tss le

end

(* mbuf2: auxiliary data structure for binary operators *)
type mbuf2 = expl Deque.t * expl Deque.t

let mbuf2_add p1s p2s (d1, d2) =
  let () = Deque.iter p1s ~f:(fun p1 -> Deque.enqueue_back d1 p1) in
  let () = Deque.iter p2s ~f:(fun p2 -> Deque.enqueue_back d2 p2) in
  (d1, d2)

let rec mbuf2_take f (p1s, p2s) =
  match (Deque.is_empty p1s, Deque.is_empty p2s) with
  | true, _ -> (Deque.create (), (p1s, p2s))
  | _, true -> (Deque.create (), (p1s, p2s))
  | false, false -> let p1 = Deque.dequeue_front_exn p1s in
                    let p2 = Deque.dequeue_front_exn p2s in
                    let (p3s, buf') = mbuf2_take f (p1s, p2s) in
                    let _ = Deque.enqueue_front p3s (f p1 p2) in
                    (p3s, buf')

let rec mbuft_take f z ps ts_tps =
  match (Deque.is_empty ps, Deque.is_empty ts_tps) with
  | true, _ -> (z, ps, ts_tps)
  | _, true -> (z, ps, ts_tps)
  | false, false -> let p = Deque.dequeue_front_exn ps in
                    let (ts, tp) = Deque.dequeue_front_exn ts_tps in
                    mbuft_take f (f p ts tp z) ps ts_tps

let rec mbuf2t_take f z (p1s, p2s) ts_tps =
  match (Deque.is_empty p1s, Deque.is_empty p2s, Deque.is_empty ts_tps) with
  | true, _, _ -> (z, (p1s, p2s), ts_tps)
  | _, true, _ -> (z, (p1s, p2s), ts_tps)
  | _, _, true -> (z, (p1s, p2s), ts_tps)
  | false, false, false -> let p1 = Deque.dequeue_front_exn p1s in
                           let p2 = Deque.dequeue_front_exn p2s in
                           let (ts, tp) = Deque.dequeue_front_exn ts_tps in
                           mbuf2t_take f (f p1 p2 ts tp z) (p1s, p2s) ts_tps

type mformula =
  | MTT
  | MFF
  | MP of string
  | MNeg of mformula
  | MConj of mformula * mformula * mbuf2
  | MDisj of mformula * mformula * mbuf2
  | MPrev of interval * mformula * bool * expl Deque.t * timestamp Deque.t
  | MNext of interval * mformula * bool * timestamp Deque.t
  | MOnce of interval * mformula * (timestamp * timepoint) Deque.t * Once.moaux
  | MHistorically of interval * mformula * (timestamp * timepoint) Deque.t * Historically.mhaux
  | MEventually of interval * mformula * expl Deque.t * (timestamp * timepoint) Deque.t * Eventually.meaux
  | MAlways of interval * mformula * expl Deque.t * (timestamp * timepoint) Deque.t * Always.maaux
  | MSince of interval * mformula * mformula * mbuf2 * (timestamp * timepoint) Deque.t * Since.msaux
  | MUntil of interval * mformula * mformula * mbuf2 * (timestamp * timepoint) Deque.t * Until.muaux

let rec mformula_to_string l f =
  match f with
  | MP x -> Printf.sprintf "%s" x
  | MTT -> Printf.sprintf "⊤"
  | MFF -> Printf.sprintf "⊥"
  | MConj (f, g, _) -> Printf.sprintf (paren l 4 "%a ∧ %a") (fun x -> mformula_to_string 4) f (fun x -> mformula_to_string 4) g
  | MDisj (f, g, _) -> Printf.sprintf (paren l 3 "%a ∨ %a") (fun x -> mformula_to_string 3) f (fun x -> mformula_to_string 4) g
  | MNeg f -> Printf.sprintf "¬%a" (fun x -> mformula_to_string 5) f
  | MPrev (i, f, _, _, _) -> Printf.sprintf (paren l 5 "●%a %a") (fun x -> interval_to_string) i (fun x -> mformula_to_string 5) f
  | MNext (i, f, _, _) -> Printf.sprintf (paren l 5 "○%a %a") (fun x -> interval_to_string) i (fun x -> mformula_to_string 5) f
  | MOnce (i, f, _, _) -> Printf.sprintf (paren l 5 "⧫%a %a") (fun x -> interval_to_string) i (fun x -> mformula_to_string 5) f
  | MHistorically (i, f, _, _) -> Printf.sprintf (paren l 5 "■%a %a") (fun x -> interval_to_string) i (fun x -> mformula_to_string 5) f
  | MEventually (i, f, _, _, _) -> Printf.sprintf (paren l 5 "◊%a %a") (fun x -> interval_to_string) i (fun x -> mformula_to_string 5) f
  | MAlways (i, f, _, _, _) -> Printf.sprintf (paren l 5 "□%a %a") (fun x -> interval_to_string) i (fun x -> mformula_to_string 5) f
  | MSince (i, f, g, _, _, _) -> Printf.sprintf (paren l 0 "%a S%a %a") (fun x -> mformula_to_string 5) f (fun x -> interval_to_string) i (fun x -> mformula_to_string 5) g
  | MUntil (i, f, g, _, _, _) -> Printf.sprintf (paren l 0 "%a U%a %a") (fun x -> mformula_to_string 5) f (fun x -> interval_to_string) i (fun x -> mformula_to_string 5) g
let mformula_to_string = mformula_to_string 0

let relevant_ap mf =
  let rec aux mf =
    match mf with
    | MP x -> [x]
    | MTT -> []
    | MFF -> []
    | MConj (f, g, _) -> aux f @ aux g
    | MDisj (f, g, _) -> aux f @ aux g
    | MNeg f -> aux f
    | MPrev (i, f, _, _, _) -> aux f
    | MNext (i, f, _, _) -> aux f
    | MOnce (i, f, _, _) -> aux f
    | MHistorically (i, f, _, _) -> aux f
    | MEventually (i, f, _, _, _) -> aux f
    | MAlways (i, f, _, _, _) -> aux f
    | MSince (i, f, g, _, _, _) -> aux f @ aux g
    | MUntil (i, f, g, _, _, _) -> aux f @ aux g in
  let lst_with_dup = aux mf in
  List.fold_left lst_with_dup ~init:[] ~f:(fun acc s ->
      if (List.mem acc s ~equal:(fun x y -> x = y)) then acc
      else s::acc)

let filter_ap sap mf_ap =
  Util.SS.filter (fun s -> List.mem mf_ap s ~equal:(fun x y -> x = y)) sap

type state =
  { tp: timepoint
  ; mf: mformula
  ; events: (Util.SS.t * timestamp) list
  ; tp_ts: (timepoint, timestamp) Hashtbl.t
  }

let print_ps_list l =
  List.iter l ~f:(fun (ts, p) -> Printf.fprintf stdout "%s\n" (expl_to_string p))

(* Convert formula into a formula state *)
let rec minit f =
  match f with
  | TT -> MTT
  | FF -> MFF
  | P (x) -> MP (x)
  | Neg (f) -> MNeg (minit f)
  | Conj (f, g) ->
     let buf = (Deque.create (), Deque.create ()) in
     MConj (minit f, minit g, buf)
  | Disj (f, g) ->
     let buf = (Deque.create (), Deque.create ()) in
     MDisj (minit f, minit g, buf)
  | Prev (i, f) -> MPrev (i, minit f, true, (Deque.create ()), (Deque.create ()))
  | Next (i, f) -> MNext (i, minit f, true, (Deque.create ()))
  | Once (i, f) ->
     let moaux = { Once.ts_zero = None
                 ; ts_tp_in = Deque.create ()
                 ; ts_tp_out = Deque.create ()
                 ; s_alphas_in = Deque.create ()
                 ; s_alphas_out = Deque.create ()
                 ; v_alphas_in = Deque.create ()
                 ; v_alphas_out = Deque.create ()
                 ; } in
     MOnce (i, minit f, Deque.create (), moaux)
  | Historically (i, f) ->
     let mhaux = { Historically.ts_zero = None
                 ; ts_tp_in = Deque.create ()
                 ; ts_tp_out = Deque.create ()
                 ; s_alphas_in = Deque.create ()
                 ; s_alphas_out = Deque.create ()
                 ; v_alphas_in = Deque.create ()
                 ; v_alphas_out = Deque.create ()
                 ; } in
     MHistorically (i, minit f, Deque.create (), mhaux)
  | Eventually (i, f) ->
     let meaux = { Eventually.ts_tp_in = Deque.create ()
                 ; ts_tp_out = Deque.create ()
                 ; s_alphas_in = Deque.create ()
                 ; v_alphas_in = Deque.create ()
                 ; optimal_proofs = Deque.create ()
                 ; } in
     MEventually (i, minit f, Deque.create (), Deque.create (), meaux)
  | Always (i, f) ->
     let maaux = { Always.ts_tp_in = Deque.create ()
                 ; ts_tp_out = Deque.create ()
                 ; v_alphas_in = Deque.create ()
                 ; s_alphas_in = Deque.create ()
                 ; optimal_proofs = Deque.create ()
                 ; } in
     MAlways (i, minit f, Deque.create (), Deque.create (), maaux)
  | Since (i, f, g) ->
     let buf = (Deque.create (), Deque.create ()) in
     let msaux = { Since.ts_zero = None
                 ; ts_tp_in = Deque.create ()
                 ; ts_tp_out = Deque.create ()
                 ; s_beta_alphas_in = Deque.create ()
                 ; s_beta_alphas_out = Deque.create ()
                 ; v_alpha_betas_in = Deque.create ()
                 ; v_alphas_out = Deque.create ()
                 ; v_betas_in = Deque.create ()
                 ; v_alphas_betas_out = Deque.create ()
                 ; } in
     MSince (i, minit f, minit g, buf, Deque.create (), msaux)
  | Until (i, f, g) ->
     let buf = (Deque.create (), Deque.create ()) in
     let empty_d1 = Deque.create () in
     let empty_d2 = Deque.create () in
     let alphas_beta = Deque.create () in
     let betas_alpha = Deque.create () in
     let _ = Deque.enqueue_front alphas_beta empty_d1 in
     let _ = Deque.enqueue_front betas_alpha empty_d2 in
     let muaux = { Until.ts_tp_in = Deque.create ()
                 ; ts_tp_out = Deque.create ()
                 ; alphas_beta = alphas_beta
                 ; alphas_suffix = Deque.create ()
                 ; betas_alpha = betas_alpha
                 ; v_alphas_out = Deque.create ()
                 ; alphas_in = Deque.create ()
                 ; betas_suffix_in = Deque.create ()
                 ; optimal_proofs = Deque.create ()
                 } in
     MUntil (i, minit f, minit g, buf, Deque.create (), muaux)
  | _ -> failwith "This formula cannot be monitored"

let do_disj expl_f1 expl_f2 le =
  match expl_f1, expl_f2 with
  | S f1, S f2 -> minimuml le [(S (SDisjL (f1))); (S (SDisjR(f2)))]
  | S f1, V _ -> S (SDisjL (f1))
  | V _ , S f2 -> S (SDisjR (f2))
  | V f1, V f2 -> V (VDisj (f1, f2))

let do_conj expl_f1 expl_f2 le =
  match expl_f1, expl_f2 with
  | S f1, S f2 -> S (SConj (f1, f2))
  | S _ , V f2 -> V (VConjR (f2))
  | V f1, S _ -> V (VConjL (f1))
  | V f1, V f2 -> minimuml le [(V (VConjL (f1))); (V (VConjR (f2)))]

let meval' ts tp sap mform le =
  let rec meval tp ts sap mform =
    match mform with
    | MTT -> let d = Deque.create () in
             let _ = Deque.enqueue_back d (S (STT tp)) in
             (ts, d, MTT)
    | MFF -> let d = Deque.create () in
             let _ = Deque.enqueue_back d (V (VFF tp)) in
             (ts, d, MFF)
    | MP a ->
       let d = Deque.create () in
       let _ = if Util.SS.mem a sap then Deque.enqueue_back d (S (SAtom (tp, a)))
               else Deque.enqueue_back d (V (VAtom (tp, a))) in
       (ts, d, MP a)
    | MNeg (mf) ->
       let (_, ps, mf') = meval tp ts sap mf in
       let ps' = Deque.fold ps ~init:(Deque.create ())
                   ~f:(fun d p ->
                     match p with
                     | S p' -> let _ = Deque.enqueue_back d (V (VNeg p')) in d
                     | V p' -> let _ = Deque.enqueue_back d (S (SNeg p')) in d) in
       (ts, ps', MNeg(mf'))
    | MConj (mf1, mf2, buf) ->
       let op p1 p2 = do_conj p1 p2 le in
       let (_, p1s, mf1') = meval tp ts sap mf1 in
       let (_, p2s, mf2') = meval tp ts sap mf2 in
       let (ps, buf') = mbuf2_take op (mbuf2_add p1s p2s buf) in
       (ts, ps, MConj (mf1', mf2', buf'))
    | MDisj (mf1, mf2, buf) ->
       let op p1 p2 = do_disj p1 p2 le in
       let (_, p1s, mf1') = meval tp ts sap mf1 in
       let (_, p2s, mf2') = meval tp ts sap mf2 in
       let (ps, buf') = mbuf2_take op (mbuf2_add p1s p2s buf) in
       (ts, ps, MDisj (mf1', mf2', buf'))
    | MPrev (interval, mf, first, buf, tss) ->
       let (_, ps, mf') = meval tp ts sap mf in
       let () = Deque.iter ps ~f:(fun p -> Deque.enqueue_back buf p) in
       let () = Deque.enqueue_back tss ts in
       let (ps', buf', tss') = Prev_Next.mprev_next Prev interval buf tss le in
       (ts, (if first then (let () = Deque.enqueue_front ps' (V VPrev0) in ps')
         else ps'), MPrev (interval, mf', false, buf', tss'))
    | MNext (interval, mf, first, tss) ->
       let (_, ps, mf') = meval tp ts sap mf in
       let () = Deque.enqueue_back tss ts in
       let first = if first && (Deque.length ps) > 0 then (let () = Deque.drop_front ps in false) else first in
       let (ps', _, tss') = Prev_Next.mprev_next Next interval ps tss le in
       (ts, ps', MNext (interval, mf', first, tss'))
    | MOnce (interval, mf, ts_tps, moaux) ->
       let (_, ps, mf') = meval tp ts sap mf in
       let _ = Deque.enqueue_back ts_tps (ts, tp) in
       let ((ps, moaux'), buf', ts_tps') =
         mbuft_take
           (fun p ts tp (ps, aux) ->
             let (op, aux) = Once.update_once interval ts tp p aux le in
             let () = Deque.enqueue_back ps op in
             (ps, aux))
           (Deque.create (), moaux) ps ts_tps in
       (ts, ps, MOnce (interval, mf', ts_tps', moaux'))
    | MHistorically (interval, mf, ts_tps, mhaux) ->
       let (_, ps, mf') = meval tp ts sap mf in
       let _ = Deque.enqueue_back ts_tps (ts, tp) in
       let ((ps, mhaux'), buf', ts_tps') =
         mbuft_take
           (fun p ts tp (ps, aux) ->
             let (op, aux) = Historically.update_historically interval ts tp p aux le in
             let () = Deque.enqueue_back ps op in
             (ps, aux))
           (Deque.create (), mhaux) ps ts_tps in
       (ts, ps, MHistorically (interval, mf', ts_tps', mhaux'))
    | MEventually (interval, mf, buf, nts_ntps, meaux) ->
       let (_, ps, mf') = meval tp ts sap mf in
       let () = Deque.enqueue_back nts_ntps (ts, tp) in
       let () = Deque.iter ps ~f:(fun p -> Deque.enqueue_back buf p) in
       let (meaux', buf', nts_ntps') =
         mbuft_take
           (fun p ts tp aux -> Eventually.update_eventually interval ts tp p le aux)
           meaux buf nts_ntps in
       let (nts, ntp) = match Deque.peek_front nts_ntps' with
         | None -> (ts, tp)
         | Some(nts', ntp') -> (nts', ntp') in
       let (ts', ps, meaux'') = Eventually.eval_eventually (Deque.create ()) interval ts tp le meaux' in
       (ts', ps, MEventually (interval, mf', buf', nts_ntps', meaux''))
    | MAlways (interval, mf, buf, nts_ntps, maaux) ->
       let (_, ps, mf') = meval tp ts sap mf in
       let () = Deque.enqueue_back nts_ntps (ts, tp) in
       let () = Deque.iter ps ~f:(fun p -> Deque.enqueue_back buf p) in
       let (maaux', buf', nts_ntps') =
         mbuft_take
           (fun p ts tp aux -> Always.update_always interval ts tp p le aux)
           maaux buf nts_ntps in
       let (nts, ntp) = match Deque.peek_front nts_ntps' with
         | None -> (ts, tp)
         | Some(nts', ntp') -> (nts', ntp') in
       let (ts', ps, maaux'') = Always.eval_always (Deque.create ()) interval ts tp le maaux' in
       (ts', ps, MAlways (interval, mf', buf', nts_ntps', maaux''))
    | MSince (interval, mf1, mf2, buf, ts_tps, msaux) ->
       let (_, p1s, mf1') = meval tp ts sap mf1 in
       let (_, p2s, mf2') = meval tp ts sap mf2 in
       let _ = Deque.enqueue_back ts_tps (ts, tp) in
       let ((ps, msaux'), buf', tss_tps') =
         mbuf2t_take
           (fun p1 p2 ts tp (ps, aux) ->
             let (op, aux) = Since.update_since interval ts tp p1 p2 aux le in
             let () = Deque.enqueue_back ps op in
             (ps, aux))
           (Deque.create (), msaux) (mbuf2_add p1s p2s buf) ts_tps in
       (ts, ps, MSince (interval, mf1', mf2', buf', tss_tps', msaux'))
    | MUntil (interval, mf1, mf2, buf, nts_ntps, muaux) ->
       let (_, p1s, mf1') = meval tp ts sap mf1 in
       let (_, p2s, mf2') = meval tp ts sap mf2 in
       let () = Deque.enqueue_back nts_ntps (ts, tp) in
       let (muaux', buf', nts_ntps') =
         mbuf2t_take
           (fun p1 p2 ts tp aux -> Until.update_until interval ts tp p1 p2 le aux)
           muaux (mbuf2_add p1s p2s buf) nts_ntps in
       let (nts, ntp) = match Deque.peek_front nts_ntps' with
         | None -> (ts, tp)
         | Some(nts', ntp') -> (nts', ntp') in
       let (ts', ps, muaux'') = Until.eval_until (Deque.create ()) interval nts ntp le muaux in
       (ts', ps, MUntil (interval, mf1', mf2', buf', nts_ntps', muaux'')) in
  meval tp ts sap mform

let monitor_cli in_ch out_ch mode out_mode check le is_opt f =
  let mf = minit f in
  let mf_ap = relevant_ap mf in
  let st = { tp = 0
            ; mf = mf
            ; events = []
            ; tp_ts = Hashtbl.create 0
            } in
  (match out_mode with
   | PLAIN | DEBUG -> preamble_stdout out_ch mode f
   | JSON -> preamble_json out_ch f);
  let s (st, in_ch) =
    let ((sap, ts), in_ch) = input_event in_ch out_ch in
    let sap_filtered = filter_ap sap mf_ap in
    let events_updated = (sap_filtered, ts)::st.events in
    let (ts', ps, mf_updated) = meval' ts st.tp sap_filtered st.mf le in
    let lps = Deque.to_list ps in
    let checker_ps = if check then Some (check_ps is_opt events_updated f lps) else None in
    let () = output_ps out_ch mode out_mode ts' [] f lps checker_ps in
    let st_updated =
      { st with
        tp = st.tp+1
      ; mf = mf_updated
      ; events = events_updated
      } in
    (st_updated, in_ch) in
  loop s (st, in_ch)

let monitor_vis obj_opt log le f =
  let events = parse_lines_from_string log in
  let (mf, st) = match obj_opt with
    | None -> let mf = minit f in
              (mf, { tp = 0
                   ; mf = mf
                   ; events = []
                   ; tp_ts = Hashtbl.create 100
              })
    | Some (mf', st') -> (mf', st') in
  let mf_ap = relevant_ap mf in
  match events with
  | Ok es ->
     (let ((m, s), o) = List.fold_map es ~init:(mf, st) ~f:(fun (mf', st') (sap, ts) ->
                            let last_ts = match Hashtbl.find_opt st.tp_ts (st'.tp-1) with
                              | None -> ts
                              | Some(ts') -> ts' in
                            if last_ts <= ts then
                              (Hashtbl.add st.tp_ts st'.tp ts;
                               let sap_filtered = filter_ap sap mf_ap in
                               let (ts', ps, mf_updated) = meval' ts st'.tp sap_filtered mf' le in
                               let cbs_opt = None in
                               let expls = json_expls st.tp_ts f (Deque.to_list ps) cbs_opt in
                               let atoms = json_atoms f sap_filtered st'.tp ts in
                               let st_updated = { st with
                                                  tp = st'.tp+1
                                                ; mf = mf_updated } in
                               ((mf_updated, st_updated), (expls, atoms)))
                            else raise (INVALID_TIMESTAMP "Timestamp violates monotonicity constraint")) in
      let expls = List.map o (fun (e, _) -> e) in
      let expls' = String.concat ",\n" (List.filter expls (fun e -> not (String.equal e ""))) in
      let atoms = List.map o (fun (_, a) -> a) in
      let atoms' = String.concat ",\n" (List.filter atoms (fun a -> not (String.equal a ""))) in
      let ident = "    " in
      let json = (Printf.sprintf "{\n") ^
                   (Printf.sprintf "%s\"expls\": [\n%s],\n" ident expls') ^
                     (Printf.sprintf "%s\"atoms\": [\n%s]\n}" ident atoms') in
      (Some(m, s), json))
  | Error err -> (None, json_error err)
