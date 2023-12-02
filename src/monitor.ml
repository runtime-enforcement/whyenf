(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Core
open Etc
open Expl
open Pred

let minp_list = Proof.Size.minp_list
let minp_bool = Proof.Size.minp_bool
let minp = Proof.Size.minp

let s_append_deque sp1 d =
  Fdeque.map d ~f:(fun (ts, ssp) ->
      match ssp with
      | Proof.S sp -> (ts, Proof.S (Proof.s_append sp sp1))
      | V _ -> raise (Invalid_argument "found V proof in S deque"))

let v_append_deque vp2 d =
  Fdeque.map d ~f:(fun (ts, vvp) ->
      match vvp with
      | Proof.V vp -> (ts, Proof.V (Proof.v_append vp vp2))
      | S _ -> raise (Invalid_argument "found S proof in V deque"))

let remove_cond_front f deque =
  let rec remove_cond_front_rec d = match Fdeque.dequeue_front d with
    | None -> d
    | Some(el', d') -> if (f el') then remove_cond_front_rec d'
                       else Fdeque.enqueue_front d' el' in
  remove_cond_front_rec deque

let remove_cond_back f deque =
  let rec remove_cond_back_rec d = match Fdeque.dequeue_back d with
    | None -> d
    | Some(el', d') -> if (f el') then remove_cond_back_rec d'
                       else Fdeque.enqueue_back d' el' in
  remove_cond_back_rec deque

let remove_cond_front_ne f deque =
  let rec remove_cond_front_ne_rec d =
    if (Fdeque.length d) > 1 then
      (match Fdeque.dequeue_front d with
       | None -> d
       | Some(el', d') -> if (f el') then remove_cond_front_ne_rec d'
                          else Fdeque.enqueue_front d' el')
    else d in
  remove_cond_front_ne_rec deque

let sorted_append new_in deque =
  Fdeque.fold new_in ~init:deque ~f:(fun d (ts, p) ->
      let d' = remove_cond_back (fun (_, p') -> minp_bool p p') d in
      Fdeque.enqueue_back d' (ts, p))

let sorted_enqueue (ts, p) deque =
  let d' = remove_cond_back (fun (_, p') -> minp_bool p p') deque in
  Fdeque.enqueue_back d' (ts, p)

(* split_in_out considers a closed interval [l, r] *)
let split_in_out get_ts (l, r) deque =
  let new_in = Fdeque.empty in
  let rec split_in_out_rec d nd =
    match Fdeque.dequeue_front d with
    | None -> (d, nd)
    | Some(el', d') -> let ts = get_ts el' in
                       if ts <= r then
                         (if ts >= l then
                            split_in_out_rec d' (Fdeque.enqueue_back nd el')
                          else split_in_out_rec d' nd)
                       else (d, nd) in
  split_in_out_rec deque new_in

(* split_out_in considers an interval of the form [z, l) *)
let split_out_in get_ts (z, l) deque =
  let new_out = Fdeque.empty in
  let rec split_out_in_rec d nd =
    match Fdeque.dequeue_front d with
    | None -> (nd, d)
    | Some(el', d') -> let ts = get_ts el' in
                       if ts < l then
                         (if ts >= z then
                            split_out_in_rec d' (Fdeque.enqueue_back nd el')
                          else split_out_in_rec d' nd)
                       else (nd, d) in
  split_out_in_rec deque new_out

let etp tstps_in tstps_out tp =
  match Fdeque.peek_front tstps_in with
  | None -> (match Fdeque.peek_front tstps_out with
             | None -> tp
             | Some (_, tp') -> tp')
  | Some (_, tp') -> tp'

let ready_tstps b nts tstps_out tstps_in =
  let tstps' = Fdeque.fold tstps_out ~init:Fdeque.empty ~f:(fun tstps (ts, tp) ->
                   if ts + b < nts then Fdeque.enqueue_back tstps (ts, tp) else tstps) in
  Fdeque.fold tstps_in ~init:tstps' ~f:(fun tstps (ts, tp) ->
      if ts + b < nts then Fdeque.enqueue_back tstps (ts, tp) else tstps)

let first_ts_tp tstps_out tstps_in =
  match Fdeque.peek_front tstps_out with
  | None -> (match Fdeque.peek_front tstps_in with
             | None -> None
             | Some(ts, tp) -> Some(ts, tp))
  | Some(ts, tp) -> Some(ts, tp)

let drop_first_ts_tp tstps_out tstps_in =
  match Fdeque.peek_front tstps_out with
  | None -> (tstps_out, Fdeque.drop_front_exn tstps_in)
  | Some _ -> (Fdeque.drop_front_exn tstps_out, tstps_in)

let add_tstp_future a b nts ntp tstps_out tstps_in =
  (* (ts, tp) update is performed differently if the queues are not empty *)
  if not (Fdeque.is_empty tstps_out) || not (Fdeque.is_empty tstps_in) then
    let first_ts = match first_ts_tp tstps_out tstps_in with
      | None -> raise (Failure "tstps deques are empty")
      | Some(ts', _) -> ts' in
    if nts < first_ts + a then (Fdeque.enqueue_back tstps_out (nts, ntp), tstps_in)
    else (tstps_out, Fdeque.enqueue_back tstps_in (nts, ntp))
  else
    (if Int.equal a 0 then (tstps_out, Fdeque.enqueue_back tstps_in (nts, ntp))
     else (Fdeque.enqueue_back tstps_out (nts, ntp), tstps_in))

let shift_tstps_future a first_ts ntp tstps_out tstps_in =
  let tstps_out' = Fdeque.fold tstps_in ~init:tstps_out ~f:(fun tstps_out' (ts', tp') ->
                       if (ts' < first_ts + a) && (tp' < ntp) then
                         Fdeque.enqueue_back tstps_out' (ts', tp')
                       else tstps_out') in
  (remove_cond_front (fun (ts', tp') -> (ts' < first_ts) && (tp' < ntp)) tstps_out',
   remove_cond_front (fun (ts', tp') -> (ts' < first_ts + a) && (tp' < ntp)) tstps_in)

let shift_tstps_past (l, r) a ts tp tstps_in tstps_out =
  if a = 0 then
    (remove_cond_front (fun (ts', _) -> ts' < l) (Fdeque.enqueue_back tstps_in (ts, tp)), tstps_out)
  else
    let tstps_out' = Fdeque.enqueue_back tstps_out (ts, tp) in
    (remove_cond_front (fun (ts', _) -> ts' < l)
       (Fdeque.fold tstps_out' ~init:tstps_in ~f:(fun tstps_in' (ts', tp') ->
            if ts' <= r then Fdeque.enqueue_back tstps_in' (ts', tp')
            else tstps_in')),
     remove_cond_front (fun (ts', _) -> ts' <= r) tstps_out')

let tstps_to_string ts_zero tstps_in tstps_out =
  (match ts_zero with
   | None -> ""
   | Some(ts) -> Printf.sprintf "\n\tts_zero = (%d)\n" ts) ^
    Fdeque.fold tstps_in ~init:"\n\ttstps_in = ["
      ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
        Fdeque.fold tstps_out ~init:"\n\ttstps_out = ["
          ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
          (Printf.sprintf "]\n")

module Buf2 = struct

  type ('a, 'b) t = 'a list * 'b list

  let add xs ys (l1, l2) = (l1 @ xs, l2 @ ys)

  let rec take f = function
    | [], ys -> ([], ([], ys))
    | xs, [] -> ([], (xs, []))
    | x::xs, y::ys -> let (zs, buf2') = take f (xs, ys) in
                      ((f x y)::zs, buf2')

end

module Buft = struct

  type ('a, 'b) t = 'a list * 'b list

  let rec another_take f = function
    | [], ys  -> ([], ([], ys))
    | xs, []  -> ([], (xs, []))
    | xs, [y] -> ([], (xs, [y]))
    | x::xs, y::y'::ys -> let (zs, buft') = another_take f (xs, y'::ys) in
                          ((f x y y')::zs, buft')

  let rec take f z = function
    | [], ys -> (z, [], ys)
    | xs, [] -> (z, xs, [])
    | x::xs, (a,b)::ys -> take f (f x a b z) (xs, ys)

end

module Buf2t = struct

  type ('a, 'b, 'c) t = ('a list * 'b list) * 'c list

  let add xs ys (l1, l2) = (l1 @ xs, l2 @ ys)

  let rec take f w (xs, ys) zs = match (xs, ys), zs with
    | ([], ys), zs -> (w, (([], ys), zs))
    | (xs, []), zs -> (w, ((xs, []), zs))
    | (xs, ys), [] -> (w, ((xs, ys), []))
    | (x::xs, y::ys), (a,b)::zs -> take f (f x y a b w) (xs, ys) zs

end


module Once = struct

  type t = { ts_zero: timestamp option
           ; tstps_in: (timestamp * timepoint) Fdeque.t
           ; tstps_out: (timestamp * timepoint) Fdeque.t
           ; s_alphas_in: (timestamp * Proof.t) Fdeque.t
           ; s_alphas_out: (timestamp * Proof.t) Fdeque.t
           ; v_alphas_in: (timestamp * Proof.vp) Fdeque.t
           ; v_alphas_out: (timestamp * Proof.vp) Fdeque.t }

  let init () = { ts_zero = None
                ; tstps_in = Fdeque.empty
                ; tstps_out = Fdeque.empty
                ; s_alphas_in = Fdeque.empty
                ; s_alphas_out = Fdeque.empty
                ; v_alphas_in = Fdeque.empty
                ; v_alphas_out = Fdeque.empty }

  let to_string { ts_zero
                      ; tstps_in
                      ; tstps_out
                      ; s_alphas_in
                      ; s_alphas_out
                      ; v_alphas_in
                      ; v_alphas_out } =
    ("\n\nOnce state: " ^ (tstps_to_string ts_zero tstps_in tstps_out) ^
       Fdeque.fold s_alphas_in ~init:"\ns_alphas_in = "
         ~f:(fun acc (ts, p) ->
           acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
         Fdeque.fold s_alphas_out ~init:"\ns_alphas_out = "
           ~f:(fun acc (ts, p) ->
             acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
           Fdeque.fold v_alphas_in ~init:"\nv_alphas_in = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.v_to_string "" p) ^
             Fdeque.fold v_alphas_out ~init:"\nv_alphas_out = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.v_to_string "" p))

  let update_s_alphas_in new_in_sat s_alphas_in =
    if not (Fdeque.is_empty new_in_sat) then
      sorted_append new_in_sat s_alphas_in
    else s_alphas_in

  let update_v_alphas_in new_in_vio v_alphas_in =
    Fdeque.fold new_in_vio ~init:v_alphas_in ~f:(fun v_alphas_in' (ts, vp) ->
        Fdeque.enqueue_back v_alphas_in' (ts, vp))

  let add_subps ts p1 moaux = match p1 with
    | Proof.S sp1 -> { moaux with s_alphas_out = Fdeque.enqueue_back moaux.s_alphas_out (ts, (Proof.S sp1)) }
    | V vp1 -> { moaux with v_alphas_out = Fdeque.enqueue_back moaux.v_alphas_out (ts, vp1) }

  let clean (l, r) moaux =
    { moaux with s_alphas_in = remove_cond_front (fun (ts, _) -> ts < l) moaux.s_alphas_in
               ; s_alphas_out = remove_cond_front (fun (ts, _) -> ts <= r) moaux.s_alphas_out
               ; v_alphas_in = remove_cond_front (fun (ts, _) -> ts < l) moaux.v_alphas_in
               ; v_alphas_out = remove_cond_front (fun (ts, _) -> ts <= r) moaux.v_alphas_out }

  let shift_sat (l, r) s_alphas_out s_alphas_in =
    let (s_alphas_out', new_in_sat) = split_in_out (fun (ts, _) -> ts) (l, r) s_alphas_out in
    (s_alphas_out', update_s_alphas_in new_in_sat s_alphas_in)

  let shift_vio (l, r) v_alphas_out v_alphas_in =
    let (v_alphas_out', new_in_vio) = split_in_out (fun (ts, _) -> ts) (l, r) v_alphas_out in
    (v_alphas_out', update_v_alphas_in new_in_vio v_alphas_in)

  let shift (l, r) a ts tp moaux =
    let (tstps_in, tstps_out) = shift_tstps_past (l, r) a ts tp moaux.tstps_in moaux.tstps_out in
    let (s_alphas_out, s_alphas_in) = shift_sat (l,r) moaux.s_alphas_out moaux.s_alphas_in in
    let (v_alphas_out, v_alphas_in) = shift_vio (l,r) moaux.v_alphas_out moaux.v_alphas_in in
    clean (l, r) { moaux with tstps_in
                            ; tstps_out
                            ; s_alphas_out
                            ; s_alphas_in
                            ; v_alphas_out
                            ; v_alphas_in }

  let eval tp moaux =
    if not (Fdeque.is_empty moaux.s_alphas_in) then
      [Proof.S (SOnce (tp, Proof.unS(snd(Fdeque.peek_front_exn moaux.s_alphas_in))))]
    else
      let etp = match Fdeque.is_empty moaux.v_alphas_in with
        | true -> etp moaux.tstps_in moaux.tstps_out tp
        | false -> Proof.v_at (snd(Fdeque.peek_front_exn moaux.v_alphas_in)) in
      [Proof.V (VOnce (tp, etp, Fdeque.map moaux.v_alphas_in ~f:snd))]

  let update i ts tp p1 moaux =
    let a = Interval.left i in
    let moaux_z = if Option.is_none moaux.ts_zero then
                    { moaux with ts_zero = Some(ts) }
                  else moaux in
    let moaux_subps = add_subps ts p1 moaux_z in
    if ts < (Option.value_exn moaux_subps.ts_zero) + a then
      ({ moaux_subps with tstps_out = Fdeque.enqueue_back moaux_subps.tstps_out (ts, tp) },
       [Proof.V (VOnceOut tp)])
    else
      let b = Interval.right i in
      let l = if (Option.is_some b) then max 0 (ts - (Option.value_exn b))
              else (Option.value_exn moaux_subps.ts_zero) in
      let r = ts - a in
      let moaux_shifted = shift (l, r) a ts tp moaux_subps in
      (moaux_shifted, eval tp moaux_shifted)

end


module Eventually = struct

  type t = { tstps_out: (timestamp * timepoint) Fdeque.t
           ; tstps_in: (timestamp * timepoint) Fdeque.t
           ; s_alphas_in: (timestamp * Proof.t) Fdeque.t
           ; v_alphas_in: (timestamp * Proof.vp) Fdeque.t
           ; optimal_proofs: (timestamp * Proof.t) Fdeque.t }

  let init () = { tstps_out = Fdeque.empty
                ; tstps_in = Fdeque.empty
                ; s_alphas_in = Fdeque.empty
                ; v_alphas_in = Fdeque.empty
                ; optimal_proofs = Fdeque.empty }

  let to_string { tstps_out
                ; tstps_in
                ; s_alphas_in
                ; v_alphas_in
                ; optimal_proofs } =
    ("\n\nEventually state: " ^ (tstps_to_string None tstps_in tstps_out) ^
       Fdeque.fold s_alphas_in ~init:"\ns_alphas_in = "
         ~f:(fun acc (ts, p) ->
           acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
         Fdeque.fold v_alphas_in ~init:"\nv_alphas_in = "
           ~f:(fun acc (ts, p) ->
             acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.v_to_string "" p) ^
           Fdeque.fold optimal_proofs ~init:"\noptimal_proofs = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p))

  let adjust a (nts, ntp) meaux =
    let (tstps_out, tstps_in) = drop_first_ts_tp meaux.tstps_out meaux.tstps_in in
    let (first_ts, first_tp) = match first_ts_tp tstps_out tstps_in with
      | None -> (nts, ntp)
      | Some(ts', tp') -> (ts', tp') in
    let (tstps_out', tstps_in') = shift_tstps_future a first_ts ntp tstps_out tstps_in in
    let s_alphas_in' = remove_cond_front (fun (ts', p) ->
                           ts' < first_ts + a || (Proof.p_at p < first_tp)) meaux.s_alphas_in in
    let v_alphas_in' = remove_cond_front (fun (ts', vp) ->
                           ts' < first_ts + a || (Proof.v_at vp < first_tp)) meaux.v_alphas_in in
    { meaux with tstps_out = tstps_out'
               ; tstps_in = tstps_in'
               ; s_alphas_in = s_alphas_in'
               ; v_alphas_in = v_alphas_in' }

  let eval_step a (nts, ntp) ts tp meaux =
    let optimal_proofs =
      (if not (Fdeque.is_empty meaux.s_alphas_in) then
         (match Fdeque.peek_front_exn meaux.s_alphas_in with
          | (_, S sp) -> Fdeque.enqueue_back meaux.optimal_proofs
                           (ts, S (SEventually (tp, Proof.unS(snd(Fdeque.peek_front_exn meaux.s_alphas_in)))))
          | _ -> raise (Invalid_argument "found V proof in S deque"))
       else
         (let ltp = match Fdeque.peek_back meaux.v_alphas_in with
            | None -> snd(Fdeque.peek_back_exn meaux.tstps_out)
            | Some (_, vp2) -> Proof.v_at vp2 in
          Fdeque.enqueue_back meaux.optimal_proofs
            (ts, V (VEventually (tp, ltp, Fdeque.map meaux.v_alphas_in ~f:snd))))) in
    { (adjust a (nts, ntp) meaux) with optimal_proofs }

  let shift (a, b) (nts, ntp) meaux =
    let tstps = ready_tstps b nts meaux.tstps_out meaux.tstps_in in
    Fdeque.fold tstps ~init:meaux ~f:(fun meaux' (ts, tp) ->
        eval_step a (nts, ntp) ts tp meaux')

  let add_subp a (ts, tp) (p1: Proof.t) meaux =
    let first_ts = match first_ts_tp meaux.tstps_out meaux.tstps_in with
      | None -> 0
      | Some(ts', _) -> ts' in
    match p1 with
    | S sp1 -> if ts >= first_ts + a then
                 { meaux with s_alphas_in = sorted_enqueue (ts, (S sp1)) meaux.s_alphas_in }
               else meaux
    | V vp1 -> if ts >= first_ts + a then
                 { meaux with v_alphas_in = Fdeque.enqueue_back meaux.v_alphas_in (ts, vp1) }
               else meaux

  let update i nts ntp p meaux =
    let a = Interval.left i in
    let b = match Interval.right i with
      | None -> raise (Invalid_argument "Eventually interval is unbounded")
      | Some(b') -> b' in
    let meaux_shifted = shift (a, b) (nts, ntp) meaux in
    let (tstps_out, tstps_in) = add_tstp_future a b nts ntp meaux_shifted.tstps_out meaux_shifted.tstps_in in
    add_subp a (nts, ntp) p { meaux_shifted with tstps_out; tstps_in }

  let rec eval i nts ntp (meaux, ops) =
    let a = Interval.left i in
    let b = match Interval.right i with
      | None -> raise (Invalid_argument "Eventually interval is unbounded")
      | Some(b') -> b' in
    let meaux_shifted = shift (a, b) (nts, ntp) meaux in
    match Fdeque.peek_back meaux_shifted.optimal_proofs with
    | None -> (meaux, ops)
    | Some(ts, _) -> if ts + b < nts then
                       let ((_, op), optimal_proofs) = Fdeque.dequeue_back_exn meaux_shifted.optimal_proofs in
                       let (meaux', ops') = eval i nts ntp ({ meaux_shifted with optimal_proofs }, ops) in
                       (meaux', ops' @ [op])
                     else (meaux, ops)

end


module Historically = struct

  type t = { ts_zero: timestamp option
           ; tstps_in: (timestamp * timepoint) Fdeque.t
           ; tstps_out: (timestamp * timepoint) Fdeque.t
           ; s_alphas_in: (timestamp * Proof.sp) Fdeque.t
           ; s_alphas_out: (timestamp * Proof.sp) Fdeque.t
           ; v_alphas_in: (timestamp * Proof.t) Fdeque.t
           ; v_alphas_out: (timestamp * Proof.t) Fdeque.t }

  let init () = { ts_zero = None
                ; tstps_in = Fdeque.empty
                ; tstps_out = Fdeque.empty
                ; s_alphas_in = Fdeque.empty
                ; s_alphas_out = Fdeque.empty
                ; v_alphas_in = Fdeque.empty
                ; v_alphas_out = Fdeque.empty }

  let to_string { ts_zero
                ; tstps_in
                ; tstps_out
                ; s_alphas_in
                ; s_alphas_out
                ; v_alphas_in
                ; v_alphas_out } =
    ("\n\nHistorically state: " ^ (tstps_to_string ts_zero tstps_in tstps_out) ^
       Fdeque.fold s_alphas_in ~init:"\ns_alphas_in = "
         ~f:(fun acc (ts, sp) ->
           acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.s_to_string "" sp) ^
         Fdeque.fold s_alphas_out ~init:"\ns_alphas_out = "
           ~f:(fun acc (ts, sp) ->
             acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.s_to_string "" sp) ^
           Fdeque.fold v_alphas_in ~init:"\nv_alphas_in = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
             Fdeque.fold v_alphas_in ~init:"\nv_alphas_out = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p))

  let update_s_alphas_in new_in_sat s_alphas_in =
    Fdeque.fold new_in_sat ~init:s_alphas_in ~f:(fun s_alphas_in' (ts, sp) ->
        Fdeque.enqueue_back s_alphas_in' (ts, sp))

  let update_v_alphas_in new_in_vio v_alphas_in =
    if not (Fdeque.is_empty new_in_vio) then
      sorted_append new_in_vio v_alphas_in
    else v_alphas_in

  let add_subps ts (p1: Proof.t) mhaux = match p1 with
    | S sp1 -> { mhaux with s_alphas_out = Fdeque.enqueue_back mhaux.s_alphas_out (ts, sp1) }
    | V vp1 -> { mhaux with v_alphas_out = Fdeque.enqueue_back mhaux.v_alphas_out (ts, (V vp1)) }

  let shift_sat (l, r) s_alphas_out s_alphas_in =
    let (s_alphas_out', new_in_sat) = split_in_out (fun (ts, _) -> ts) (l, r) s_alphas_out in
    (s_alphas_out', update_s_alphas_in new_in_sat s_alphas_in)

  let shift_vio (l, r) v_alphas_out v_alphas_in =
    let (v_alphas_out', new_in_viol) = split_in_out (fun (ts, _) -> ts) (l, r) v_alphas_out in
    (v_alphas_out', update_v_alphas_in new_in_viol v_alphas_in)

  let clean (l, r) mhaux =
    { mhaux with s_alphas_in = remove_cond_front (fun (ts, _) -> ts < l) mhaux.s_alphas_in
               ; s_alphas_out = remove_cond_front (fun (ts, _) -> ts <= r) mhaux.s_alphas_out
               ; v_alphas_in = remove_cond_front (fun (ts, _) -> ts < l) mhaux.v_alphas_in
               ; v_alphas_out = remove_cond_front (fun (ts, _) -> ts <= r) mhaux.v_alphas_out }

  let shift (l, r) a ts tp mhaux =
    let (tstps_in, tstps_out) = shift_tstps_past (l, r) a ts tp mhaux.tstps_in mhaux.tstps_out in
    let (s_alphas_out, s_alphas_in) = shift_sat (l,r) mhaux.s_alphas_out mhaux.s_alphas_in in
    let (v_alphas_out, v_alphas_in) = shift_vio (l,r) mhaux.v_alphas_out mhaux.v_alphas_in in
    clean (l, r) { mhaux with tstps_in
                            ; tstps_out
                            ; s_alphas_out
                            ; s_alphas_in
                            ; v_alphas_out
                            ; v_alphas_in }

  let eval tp mhaux =
    if not (Fdeque.is_empty mhaux.v_alphas_in) then
      [Proof.V (VHistorically (tp, Proof.unV(snd(Fdeque.peek_front_exn mhaux.v_alphas_in))))]
    else
      let etp = match Fdeque.is_empty mhaux.s_alphas_in with
        | true -> etp mhaux.tstps_in mhaux.tstps_out tp
        | false -> Proof.s_at (snd(Fdeque.peek_front_exn mhaux.s_alphas_in)) in
      [S (SHistorically (tp, etp, Fdeque.map mhaux.s_alphas_in ~f:snd))]

  let update i ts tp p1 mhaux =
    let a = Interval.left i in
    let mhaux_z = if Option.is_none mhaux.ts_zero then
                    { mhaux with ts_zero = Some(ts) }
                  else mhaux in
    let mhaux_subps = add_subps ts p1 mhaux_z in
    if ts < (Option.value_exn mhaux_subps.ts_zero) + a then
      ({ mhaux_subps with tstps_out = Fdeque.enqueue_back mhaux_subps.tstps_out (ts, tp) },
       [Proof.S (SHistoricallyOut tp)])
    else
      let b = Interval.right i in
      let l = if (Option.is_some b) then max 0 (ts - (Option.value_exn b))
              else (Option.value_exn mhaux_subps.ts_zero) in
      let r = ts - a in
      let mhaux_shifted = shift (l, r) a ts tp mhaux_subps in
      (mhaux_shifted, eval tp mhaux_shifted)

end

module Always = struct

  type t = { tstps_out: (timestamp * timepoint) Fdeque.t
           ; tstps_in: (timestamp * timepoint) Fdeque.t
           ; v_alphas_in: (timestamp * Proof.t) Fdeque.t
           ; s_alphas_in: (timestamp * Proof.sp) Fdeque.t
           ; optimal_proofs: (timestamp * Proof.t) Fdeque.t }

  let init () = { tstps_out = Fdeque.empty
                ; tstps_in = Fdeque.empty
                ; v_alphas_in = Fdeque.empty
                ; s_alphas_in = Fdeque.empty
                ; optimal_proofs = Fdeque.empty }

  let to_string { tstps_out
                ; tstps_in
                ; v_alphas_in
                ; s_alphas_in
                ; optimal_proofs } =
    ("\n\nAlways state: " ^ (tstps_to_string None tstps_in tstps_out) ^
       Fdeque.fold v_alphas_in ~init:"\nv_alphas_in = "
         ~f:(fun acc (ts, p) ->
           acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
         Fdeque.fold s_alphas_in ~init:"\ns_alphas_in = "
           ~f:(fun acc (ts, sp) ->
             acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.s_to_string "" sp) ^
           Fdeque.fold optimal_proofs ~init:"\noptimal_proofs = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p))

  let adjust a (nts, ntp) maaux =
    let (tstps_out, tstps_in) = drop_first_ts_tp maaux.tstps_out maaux.tstps_in in
    let (first_ts, first_tp) = match first_ts_tp tstps_out tstps_in with
      | None -> (nts, ntp)
      | Some(ts', tp') -> (ts', tp') in
    let (tstps_out', tstps_in') = shift_tstps_future a first_ts ntp tstps_out tstps_in in
    let s_alphas_in' = remove_cond_front (fun (ts', sp) ->
                           ts' < first_ts + a || (Proof.s_at sp < first_tp)) maaux.s_alphas_in in
    let v_alphas_in' = remove_cond_front (fun (ts', p) ->
                           ts' < first_ts + a || (Proof.p_at p < first_tp)) maaux.v_alphas_in in
    { maaux with tstps_out = tstps_out'
               ; tstps_in = tstps_in'
               ; v_alphas_in = v_alphas_in'
               ; s_alphas_in = s_alphas_in' }

  let eval_step a (nts, ntp) ts tp maaux =
    let optimal_proofs =
      (if not (Fdeque.is_empty maaux.v_alphas_in) then
         (match Fdeque.peek_front_exn maaux.v_alphas_in with
          | (_, V vp) -> Fdeque.enqueue_back maaux.optimal_proofs
                           (ts, V (VAlways (tp, Proof.unV(snd(Fdeque.peek_front_exn maaux.v_alphas_in)))))
          | _ -> raise (Invalid_argument "found S proof in V deque"))
       else
         (let ltp = match Fdeque.peek_back maaux.s_alphas_in with
            | None -> snd(Fdeque.peek_back_exn maaux.tstps_out)
            | Some (_, sp) -> Proof.s_at sp in
          Fdeque.enqueue_back maaux.optimal_proofs (ts, S (SAlways (tp, ltp, Fdeque.map maaux.s_alphas_in ~f:snd))))) in
    { (adjust a (nts, ntp) maaux) with optimal_proofs }

  let shift (a, b) (nts, ntp) maaux =
    let tstps = ready_tstps b nts maaux.tstps_out maaux.tstps_in in
    Fdeque.fold tstps ~init:maaux ~f:(fun maaux' (ts, tp) ->
        eval_step a (nts, ntp) ts tp maaux')

  let add_subp a (ts, tp) (p1: Proof.t) maaux =
    let first_ts = match first_ts_tp maaux.tstps_out maaux.tstps_in with
      | None -> 0
      | Some(ts', _) -> ts' in
    match p1 with
    | V vp1 -> if ts >= first_ts + a then
                 { maaux with v_alphas_in = sorted_enqueue (ts, (V vp1)) maaux.v_alphas_in }
               else maaux
    | S sp1 -> if ts >= (first_ts + a) then
                 { maaux with s_alphas_in = Fdeque.enqueue_back maaux.s_alphas_in (ts, sp1) }
               else maaux

  let update i nts ntp p maaux =
    let a = Interval.left i in
    let b = match Interval.right i with
      | None -> raise (Invalid_argument "Always interval is unbounded")
      | Some(b') -> b' in
    let maaux_shifted = shift (a, b) (nts, ntp) maaux in
    let (tstps_out, tstps_in) = add_tstp_future a b nts ntp maaux_shifted.tstps_out maaux_shifted.tstps_in in
    add_subp a (nts, ntp) p { maaux_shifted with tstps_out; tstps_in }

  let rec eval i nts ntp (maaux, ops) =
    let a = Interval.left i in
    let b = match Interval.right i with
      | None -> raise (Invalid_argument "Always interval is unbounded")
      | Some(b') -> b' in
    let maaux_shifted = shift (a, b) (nts, ntp) maaux in
    match Fdeque.peek_back maaux_shifted.optimal_proofs with
    | None -> (maaux, ops)
    | Some(ts, _) -> if ts + b < nts then
                       let ((_, op), optimal_proofs) = Fdeque.dequeue_back_exn maaux_shifted.optimal_proofs in
                       let (maaux', ops') = eval i nts ntp ({ maaux_shifted with optimal_proofs }, ops) in
                       (maaux', ops' @ [op])
                     else (maaux, ops)

end

module Since = struct

  type t = { ts_zero: timestamp option
           ; tstps_in: (timestamp * timepoint) Fdeque.t
           ; tstps_out: (timestamp * timepoint) Fdeque.t
           ; s_beta_alphas_in: (timestamp * Proof.t) Fdeque.t
           ; s_beta_alphas_out: (timestamp * Proof.t) Fdeque.t
           ; v_alpha_betas_in: (timestamp * Proof.t) Fdeque.t
           ; v_alphas_out: (timestamp * Proof.t) Fdeque.t
           ; v_betas_in: (timestamp * Proof.vp) Fdeque.t
           ; v_alphas_betas_out: (timestamp * Proof.vp option * Proof.vp option) Fdeque.t }

  let init () = { ts_zero = None
                ; tstps_in = Fdeque.empty
                ; tstps_out = Fdeque.empty
                ; s_beta_alphas_in = Fdeque.empty
                ; s_beta_alphas_out = Fdeque.empty
                ; v_alpha_betas_in = Fdeque.empty
                ; v_alphas_out = Fdeque.empty
                ; v_betas_in = Fdeque.empty
                ; v_alphas_betas_out = Fdeque.empty }

  let to_string { ts_zero
                ; tstps_in
                ; tstps_out
                ; s_beta_alphas_in
                ; s_beta_alphas_out
                ; v_alpha_betas_in
                ; v_alphas_out
                ; v_betas_in
                ; v_alphas_betas_out } =
    ("\n\nSince state: " ^ (tstps_to_string ts_zero tstps_in tstps_out) ^
       Fdeque.fold s_beta_alphas_in ~init:"\ns_beta_alphas_in = "
         ~f:(fun acc (ts, p) ->
           acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
         Fdeque.fold s_beta_alphas_out ~init:"\ns_beta_alphas_out = "
           ~f:(fun acc (ts, p) ->
             acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
           Fdeque.fold v_alpha_betas_in ~init:"\nv_alpha_betas_in = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
             Fdeque.fold v_alphas_out ~init:"\nv_alphas_out = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
               Fdeque.fold v_betas_in ~init:"\nv_betas_in = "
                 ~f:(fun acc (ts, p) ->
                   acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.v_to_string "" p) ^
                 Fdeque.fold v_alphas_betas_out ~init:"\nv_alphas_betas_out = "
                   ~f:(fun acc (ts, p1_opt, p2_opt) ->
                     match p1_opt, p2_opt with
                     | None, None -> acc
                     | Some(p1), None -> acc ^ (Printf.sprintf "\n(%d)\nalpha = " ts) ^ Proof.v_to_string "" p1
                     | None, Some(p2) -> acc ^ (Printf.sprintf "\n(%d)\nbeta = " ts) ^ Proof.v_to_string "" p2
                     | Some(p1), Some(p2) -> acc ^ (Printf.sprintf "\n(%d)\nalpha = " ts) ^ Proof.v_to_string "" p1 ^
                                               (Printf.sprintf "\n(%d)\nbeta = " ts) ^ Proof.v_to_string "" p2))

  let update_s_beta_alphas_in new_in s_beta_alphas_in =
    if not (Fdeque.is_empty new_in) then
      sorted_append new_in s_beta_alphas_in
    else s_beta_alphas_in

  let update_v_betas_in new_in v_betas_in =
    Fdeque.fold new_in ~init:v_betas_in ~f:(fun v_betas_in' (ts, _, vp2_opt) ->
        match vp2_opt with
        | None -> Fdeque.empty
        | Some(vp2) -> Fdeque.enqueue_back v_betas_in' (ts, vp2))

  let construct_vsinceps tp new_in =
    Fdeque.fold new_in ~init:Fdeque.empty
      ~f:(fun acc (ts, vp1_opt, vp2_opt) ->
        match vp1_opt with
        | None -> (match vp2_opt with
                   | None -> Fdeque.empty
                   | Some(vp2) -> v_append_deque vp2 acc)
        | Some(vp1) -> (match vp2_opt with
                        | None -> Fdeque.empty
                        | Some(vp2) -> let acc' = v_append_deque vp2 acc in
                                       let vp2s = Fdeque.enqueue_back Fdeque.empty vp2 in
                                       let vp = Proof.V (VSince (tp, vp1, vp2s)) in
                                       Fdeque.enqueue_back acc' (ts, vp)))

  let add_new_ps_v_alpha_betas_in tp new_in v_alpha_betas_in =
    let new_vsinceps_in = construct_vsinceps tp new_in in
    if not (Fdeque.is_empty new_vsinceps_in) then
      sorted_append new_vsinceps_in v_alpha_betas_in
    else v_alpha_betas_in

  let update_v_alpha_betas_in_tps tp v_alpha_betas_in =
    Fdeque.map v_alpha_betas_in ~f:(fun (ts, vvp) ->
        match vvp with
        | Proof.V (VSince (_, vp1, vp2s)) -> (ts, Proof.V (VSince (tp, vp1, vp2s)))
        | _ -> raise (Invalid_argument "found S proof in V deque"))

  let update_v_alpha_betas_in tp new_in v_alpha_betas_in =
    let v_alpha_betas_in_vapp = Fdeque.fold new_in ~init:v_alpha_betas_in ~f:(fun v_alpha_betas_in' (_, _, vp2_opt) ->
                                    match vp2_opt with
                                    | None -> Fdeque.empty
                                    | Some(vp2) -> v_append_deque vp2 v_alpha_betas_in') in
    let v_alpha_betas_in' = add_new_ps_v_alpha_betas_in tp new_in v_alpha_betas_in_vapp in
    update_v_alpha_betas_in_tps tp v_alpha_betas_in'

  let add_subps ts (p1: Proof.t) (p2: Proof.t) msaux =
    match p1, p2 with
    | S sp1, S sp2 ->
       let s_beta_alphas_in = s_append_deque sp1 msaux.s_beta_alphas_in in
       let s_beta_alphas_out = s_append_deque sp1 msaux.s_beta_alphas_out in
       let s_beta_alphas_out' = Fdeque.enqueue_back s_beta_alphas_out (ts, Proof.S (SSince (sp2, Fdeque.empty))) in
       let v_alphas_betas_out = Fdeque.enqueue_back msaux.v_alphas_betas_out (ts, None, None) in
       { msaux with s_beta_alphas_in; s_beta_alphas_out = s_beta_alphas_out'; v_alphas_betas_out }
    | S sp1, V vp2 ->
       let s_beta_alphas_in = s_append_deque sp1 msaux.s_beta_alphas_in in
       let s_beta_alphas_out = s_append_deque sp1 msaux.s_beta_alphas_out in
       let v_alphas_betas_out = Fdeque.enqueue_back msaux.v_alphas_betas_out (ts, None, Some(vp2)) in
       { msaux with s_beta_alphas_in; s_beta_alphas_out; v_alphas_betas_out }
    | V vp1, S sp2 ->
       let s_beta_alphas_out = Fdeque.enqueue_back Fdeque.empty (ts, Proof.S (SSince (sp2, Fdeque.empty))) in
       let v_alphas_out = sorted_enqueue (ts, (V vp1)) msaux.v_alphas_out in
       let v_alphas_betas_out = Fdeque.enqueue_back msaux.v_alphas_betas_out (ts, Some(vp1), None) in
       { msaux with s_beta_alphas_in = Fdeque.empty; s_beta_alphas_out; v_alphas_out; v_alphas_betas_out }
    | V vp1, V vp2 ->
       let v_alphas_out = sorted_enqueue (ts, (V vp1)) msaux.v_alphas_out in
       let v_alphas_betas_out = Fdeque.enqueue_back msaux.v_alphas_betas_out (ts, Some(vp1), Some(vp2)) in
       { msaux with s_beta_alphas_in = Fdeque.empty; s_beta_alphas_out = Fdeque.empty; v_alphas_out; v_alphas_betas_out }

  let shift_sat (l, r) s_beta_alphas_out s_beta_alphas_in =
    let (s_beta_alphas_out', new_in_sat) = split_in_out (fun (ts, _) -> ts) (l, r) s_beta_alphas_out in
    (s_beta_alphas_out', update_s_beta_alphas_in new_in_sat s_beta_alphas_in)

  let shift_vio (l, r) tp v_alphas_betas_out v_alpha_betas_in v_betas_in =
    let (v_alphas_betas_out', new_in_vio) = split_in_out (fun (ts, _, _) -> ts) (l, r) v_alphas_betas_out in
    let v_betas_in = update_v_betas_in new_in_vio v_betas_in in
    (v_alphas_betas_out', update_v_alpha_betas_in tp new_in_vio v_alpha_betas_in, v_betas_in)

  let clean (l, r) msaux =
    { msaux with s_beta_alphas_in = remove_cond_front (fun (ts, _) -> ts < l) msaux.s_beta_alphas_in
               ; v_alpha_betas_in = remove_cond_front (fun (ts, _) -> ts < l) msaux.v_alpha_betas_in
               ; v_alphas_out = remove_cond_front (fun (ts, _) -> ts <= r) msaux.v_alphas_out
               ; v_betas_in = remove_cond_front (fun (ts, _) -> ts < l) msaux.v_betas_in }

  let shift (l, r) a ts tp msaux =
    let (tstps_in, tstps_out) = shift_tstps_past (l, r) a ts tp msaux.tstps_in msaux.tstps_out in
    let (s_beta_alphas_out, s_beta_alphas_in) = shift_sat (l,r) msaux.s_beta_alphas_out msaux.s_beta_alphas_in in
    let (v_alphas_betas_out, v_alpha_betas_in, v_betas_in) =
      shift_vio (l, r) tp msaux.v_alphas_betas_out msaux.v_alpha_betas_in msaux.v_betas_in in
    clean (l, r) ({ msaux with
                    tstps_in
                  ; tstps_out
                  ; s_beta_alphas_in
                  ; s_beta_alphas_out
                  ; v_alpha_betas_in
                  ; v_betas_in
                  ; v_alphas_betas_out })

  let eval tp msaux =
    if not (Fdeque.is_empty msaux.s_beta_alphas_in) then
      [snd(Fdeque.peek_front_exn msaux.s_beta_alphas_in)]
    else
      let cp1 = if not (Fdeque.is_empty msaux.v_alpha_betas_in) then
                  [snd(Fdeque.peek_front_exn msaux.v_alpha_betas_in)]
                else [] in
      let cp2 = if not (Fdeque.is_empty msaux.v_alphas_out) then
                  let vp_f2 = snd(Fdeque.peek_front_exn msaux.v_alphas_out) in
                  match vp_f2 with
                  | V f2 -> [Proof.V (VSince (tp, f2, Fdeque.empty))]
                  | S _ -> raise (Invalid_argument "found S proof in V deque")
                else [] in
      let cp3 = if Int.equal (Fdeque.length msaux.v_betas_in) (Fdeque.length msaux.tstps_in) then
                  let etp = match Fdeque.is_empty msaux.v_betas_in with
                    | true -> etp msaux.tstps_in msaux.tstps_out tp
                    | false -> Proof.v_at (snd(Fdeque.peek_front_exn msaux.v_betas_in)) in
                  [Proof.V (VSinceInf (tp, etp, Fdeque.map msaux.v_betas_in ~f:snd))]
                else [] in
      [minp_list (cp1 @ cp2 @ cp3)]

  let update i ts tp p1 p2 msaux =
    let a = Interval.left i in
    let msaux_z = if Option.is_none msaux.ts_zero then
                    { msaux with ts_zero = Some(ts) }
                  else msaux in
    let msaux_subps = add_subps ts p1 p2 msaux_z in
    if ts < (Option.value_exn msaux_subps.ts_zero) + a then
      ({ msaux_subps with tstps_out = Fdeque.enqueue_back msaux_subps.tstps_out (ts, tp) },
       [Proof.V (VSinceOut tp)])
    else
      (let b = Interval.right i in
       let l = if (Option.is_some b) then max 0 (ts - (Option.value_exn b))
               else (Option.value_exn msaux_subps.ts_zero) in
       let r = ts - a in
       let msaux_shifted = shift (l, r) a ts tp msaux_subps in
       (msaux_shifted, eval tp msaux_shifted))

end

module Until = struct

  type t = { tstps_in: (timestamp * timepoint) Fdeque.t
           ; tstps_out: (timestamp * timepoint) Fdeque.t
           ; s_alphas_beta: ((timestamp * Proof.t) Fdeque.t) Fdeque.t
           ; s_alphas_suffix: (timestamp * Proof.sp) Fdeque.t
           ; v_betas_alpha: ((timestamp * Proof.t) Fdeque.t) Fdeque.t
           ; v_alphas_out: (timestamp * Proof.t) Fdeque.t
           ; v_alphas_in: (timestamp * Proof.t) Fdeque.t
           ; v_betas_suffix_in: (timestamp * Proof.vp) Fdeque.t
           ; optimal_proofs: (timestamp * Proof.t) Fdeque.t }

  let init () = { tstps_in = Fdeque.empty
                ; tstps_out = Fdeque.empty
                ; s_alphas_beta = Fdeque.enqueue_back Fdeque.empty Fdeque.empty
                ; s_alphas_suffix = Fdeque.empty
                ; v_betas_alpha = Fdeque.enqueue_back Fdeque.empty Fdeque.empty
                ; v_alphas_out = Fdeque.empty
                ; v_alphas_in = Fdeque.empty
                ; v_betas_suffix_in = Fdeque.empty
                ; optimal_proofs = Fdeque.empty }

  let to_string { tstps_in
                ; tstps_out
                ; s_alphas_beta
                ; s_alphas_suffix
                ; v_betas_alpha
                ; v_alphas_out
                ; v_alphas_in
                ; v_betas_suffix_in
                ; optimal_proofs } =
    ("\n\nUntil state: " ^ (tstps_to_string None tstps_in tstps_out) ^
       Fdeque.fold s_alphas_beta ~init:"\ns_alphas_beta = \n"
         ~f:(fun acc1 d ->
           acc1 ^ "\n" ^
             Fdeque.fold d ~init:"[" ~f:(fun acc2 (ts, p) ->
                 acc2 ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^ "\n]\n") ^
         Fdeque.fold s_alphas_suffix ~init:"\ns_alphas_suffix = "
           ~f:(fun acc (ts, p) ->
             acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.s_to_string "" p) ^
           Fdeque.fold v_betas_alpha ~init:"\nv_betas_alpha = \n"
             ~f:(fun acc1 d ->
               acc1 ^ "\n" ^
                 Fdeque.fold d ~init:"[" ~f:(fun acc2 (ts, p) ->
                     acc2 ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^ "\n]\n") ^
             Fdeque.fold v_alphas_out ~init:"\nv_alphas_out = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
               Fdeque.fold v_alphas_in ~init:"\nv_alphas_in = "
                 ~f:(fun acc (ts, p) ->
                   acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
                 Fdeque.fold v_betas_suffix_in ~init:"\nv_betas_suffix_in = "
                   ~f:(fun acc (ts, p) ->
                     acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.v_to_string "" p) ^
                   Fdeque.fold optimal_proofs ~init:"\noptimal_proofs = "
                     ~f:(fun acc (ts, p) ->
                       acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p))

  let ts_of_tp tp tstps_in tstps_out =
    match (Fdeque.find tstps_out ~f:(fun (ts', tp') -> tp = tp')) with
    | None -> (match (Fdeque.find tstps_in ~f:(fun (ts', tp') -> tp = tp')) with
               | None -> raise (Failure "ts not found")
               | Some(ts, _) -> ts)
    | Some(ts, _) -> ts

  (* TODO: Rewrite this function with map instead of fold *)
  let step_sdrop_tp tp s_alphas_beta =
    Fdeque.fold s_alphas_beta ~init:Fdeque.empty
      ~f:(fun s_alphas_beta' (ts, ssp) ->
        match ssp with
        | Proof.S sp -> if tp = (Proof.s_at sp) then
                          (match Proof.s_drop sp with
                           | None -> s_alphas_beta'
                           | Some(sp') -> Fdeque.enqueue_back s_alphas_beta' (ts, Proof.S sp'))
                        else (Fdeque.enqueue_back s_alphas_beta' (ts, ssp))
        | V _ -> raise (Invalid_argument "found V proof in S deque"))

  let step_vdrop_ts a first_ts v_betas_alpha tstps_in =
    let rec vdrop_until vp =
      let is_out = match Fdeque.find ~f:(fun (_, tp') -> (Proof.v_etp vp) = tp') tstps_in with
        | None -> true
        | Some(ts', _) -> ts' < (first_ts + a) in
      if is_out then
        (match Proof.v_drop vp with
         | None -> None
         | Some(vp') -> vdrop_until vp')
      else Some(vp) in
    Fdeque.fold v_betas_alpha ~init:Fdeque.empty
      ~f:(fun v_betas_alpha' (ts, vvp) ->
        (match vvp with
         | Proof.V vp -> (match vdrop_until vp with
                          | None -> v_betas_alpha'
                          | Some (vp') -> Fdeque.enqueue_back v_betas_alpha' (ts, Proof.V vp'))
         | S _ -> raise (Invalid_argument "found S proof in V deque")))

  let remove_out_less2_lts lim d =
    remove_cond_front_ne (fun d' -> Fdeque.is_empty d')
      (Fdeque.map d ~f:(fun d' ->
           (Fdeque.fold d' ~init:Fdeque.empty ~f:(fun acc (ts, p) ->
                if ts >= lim then
                  Fdeque.enqueue_back acc (ts, p)
                else acc))))

  let add_subps a (ts, tp) (p1: Proof.t) (p2: Proof.t) muaux =
    let first_ts = match first_ts_tp muaux.tstps_out muaux.tstps_in with
      | None -> 0
      | Some(ts', _) -> ts' in
    match p1, p2 with
    | S sp1, S sp2 ->
       let s_alphas_beta = if ts >= first_ts + a then
                             let cur_s_alphas_beta = Fdeque.peek_back_exn muaux.s_alphas_beta in
                             let sp = Proof.S (SUntil (sp2, Fdeque.map muaux.s_alphas_suffix ~f:snd)) in
                             let cur_s_alphas_beta_add = sorted_enqueue (ts, sp) cur_s_alphas_beta in
                             Fdeque.enqueue_back (Fdeque.drop_back_exn muaux.s_alphas_beta) cur_s_alphas_beta_add
                           else muaux.s_alphas_beta in
       let v_betas_alpha = if not (Fdeque.is_empty (Fdeque.peek_back_exn muaux.v_betas_alpha)) then
                             Fdeque.enqueue_back muaux.v_betas_alpha Fdeque.empty
                           else muaux.v_betas_alpha in
       let s_alphas_suffix = Fdeque.enqueue_back muaux.s_alphas_suffix (ts, sp1) in
       let v_betas_suffix_in = if ts >= first_ts + a then Fdeque.empty
                               else muaux.v_betas_suffix_in in
       { muaux with s_alphas_beta; v_betas_alpha; s_alphas_suffix; v_betas_suffix_in }
    | S sp1, V vp2 ->
       let s_alphas_suffix = Fdeque.enqueue_back muaux.s_alphas_suffix (ts, sp1) in
       let v_betas_suffix_in = if ts >= first_ts + a then
                                 Fdeque.enqueue_back muaux.v_betas_suffix_in (ts, vp2)
                               else muaux.v_betas_suffix_in in
       { muaux with s_alphas_suffix; v_betas_suffix_in }
    | V vp1, S sp2 ->
       let s_alphas_beta = if ts >= first_ts + a then
                             (let cur_s_alphas_beta = Fdeque.peek_back_exn muaux.s_alphas_beta in
                              let ssp = Proof.S (SUntil (sp2, Fdeque.map muaux.s_alphas_suffix ~f:snd)) in
                              let cur_s_alphas_beta_add = sorted_enqueue (ts, ssp) cur_s_alphas_beta in
                              let s_alphas_beta' = Fdeque.enqueue_back (Fdeque.drop_back_exn muaux.s_alphas_beta)
                                                     cur_s_alphas_beta_add in
                              if not (Fdeque.is_empty (Fdeque.peek_back_exn s_alphas_beta')) then
                                Fdeque.enqueue_back s_alphas_beta' Fdeque.empty
                              else s_alphas_beta')
                           else muaux.s_alphas_beta in
       let v_betas_alpha = if not (Fdeque.is_empty (Fdeque.peek_back_exn muaux.v_betas_alpha)) then
                             Fdeque.enqueue_back muaux.v_betas_alpha Fdeque.empty
                           else muaux.v_betas_alpha in
       let s_alphas_suffix = Fdeque.empty in
       let (v_alphas_in, v_alphas_out) = if ts >= first_ts + a then
                                           (Fdeque.enqueue_back muaux.v_alphas_in (ts, Proof.V vp1),
                                            muaux.v_alphas_out)
                                         else (muaux.v_alphas_in, sorted_enqueue (ts, V vp1) muaux.v_alphas_out) in
       let v_betas_suffix_in = if ts >= first_ts + a then Fdeque.empty
                               else muaux.v_betas_suffix_in in
       { muaux with s_alphas_beta; v_betas_alpha; s_alphas_suffix; v_alphas_in; v_alphas_out; v_betas_suffix_in }
    | V vp1, V vp2 ->
       let s_alphas_beta = if not (Fdeque.is_empty (Fdeque.peek_back_exn muaux.s_alphas_beta)) then
                             Fdeque.enqueue_back muaux.s_alphas_beta Fdeque.empty
                           else muaux.s_alphas_beta in
       let s_alphas_suffix = Fdeque.empty in
       let v_betas_suffix_in = if ts >= first_ts + a then
                                 Fdeque.enqueue_back muaux.v_betas_suffix_in (ts, vp2)
                               else muaux.v_betas_suffix_in in
       let v_betas_alpha = if ts >= first_ts + a then
                             (let cur_v_betas_alpha = Fdeque.peek_back_exn muaux.v_betas_alpha in
                              let vvp = Proof.V (VUntil (tp, vp1, Fdeque.map v_betas_suffix_in ~f:snd)) in
                              let cur_v_betas_alpha_add = sorted_enqueue (ts, vvp) cur_v_betas_alpha in
                              Fdeque.enqueue_back (Fdeque.drop_back_exn muaux.v_betas_alpha)
                                cur_v_betas_alpha_add)
                           else muaux.v_betas_alpha in
       let (v_alphas_in, v_alphas_out) = if ts >= first_ts + a then
                                           (Fdeque.enqueue_back muaux.v_alphas_in (ts, Proof.V vp1),
                                            muaux.v_alphas_out)
                                         else (muaux.v_alphas_in, sorted_enqueue (ts, V vp1) muaux.v_alphas_out) in
       { muaux with s_alphas_beta; s_alphas_suffix; v_betas_suffix_in; v_betas_alpha; v_alphas_in; v_alphas_out }

  let drop_tp tp s_alphas_beta =
    match Fdeque.peek_front s_alphas_beta with
    | None -> raise (Etc.Empty_deque "alphas_beta")
    | Some(cur_s_alphas_beta) ->
       if not (Fdeque.is_empty cur_s_alphas_beta) then
         Fdeque.enqueue_front (Fdeque.drop_front_exn s_alphas_beta)
           (step_sdrop_tp tp cur_s_alphas_beta)
       else s_alphas_beta

  let drop_v_ts a ts v_betas_alpha tstps_in =
    Fdeque.map v_betas_alpha ~f:(fun d -> step_vdrop_ts a ts d tstps_in)

  let drop_v_single_ts cur_tp v_betas_alpha =
    let first_v_betas_alpha = Fdeque.fold (Fdeque.peek_front_exn v_betas_alpha) ~init:Fdeque.empty
                                ~f:(fun first_v_betas_alpha' (ts', vvp) ->
                                  match vvp with
                                  | Proof.V vp -> if Proof.v_etp vp <= cur_tp then
                                                    (match Proof.v_drop vp with
                                                     | None -> first_v_betas_alpha'
                                                     | Some (vp') -> Fdeque.enqueue_back first_v_betas_alpha'
                                                                       (ts', Proof.V vp'))
                                                  else Fdeque.enqueue_back first_v_betas_alpha' (ts', Proof.V vp)
                                  | S _ -> raise (Invalid_argument "found S proof in V deque")) in
    Fdeque.enqueue_front (Fdeque.drop_front_exn v_betas_alpha) first_v_betas_alpha

  let adjust a (nts, ntp) { tstps_in
                          ; tstps_out
                          ; s_alphas_beta
                          ; s_alphas_suffix
                          ; v_betas_alpha
                          ; v_alphas_out
                          ; v_alphas_in
                          ; v_betas_suffix_in
                          ; optimal_proofs } =
    let eval_tp = match first_ts_tp tstps_out tstps_in with
      | None -> raise (Failure "tp not found")
      | Some(_, tp') -> tp' in
    let (tstps_out', tstps_in') = drop_first_ts_tp tstps_out tstps_in in
    let (first_ts, first_tp) = match first_ts_tp tstps_out' tstps_in' with
      | None -> (nts, ntp)
      | Some(ts', tp') -> (ts', tp') in
    (* v_betas_alpha *)
    let v_betas_alpha_step1 = Fdeque.map v_betas_alpha ~f:(fun d ->
                                  remove_cond_front (fun (ts', p) ->
                                      (ts' < first_ts + a) || ((Proof.p_at p) < first_tp)) d) in
    let v_betas_alpha_step2 = if a = 0 then
                                drop_v_single_ts eval_tp v_betas_alpha_step1
                              else drop_v_ts a first_ts v_betas_alpha_step1 tstps_in' in
    let v_betas_alpha_step3 = remove_cond_front_ne (fun d' -> Fdeque.is_empty d') v_betas_alpha_step2 in
    (* tstp_out and tstp_in *)
    let (tstps_out'', tstps_in'') = shift_tstps_future a first_ts ntp tstps_out' tstps_in' in
    (* s_alphas_beta *)
    let s_alphas_beta_step1 = drop_tp eval_tp s_alphas_beta in
    let s_alphas_beta_step2 = Fdeque.map s_alphas_beta_step1 ~f:(fun d ->
                                  (remove_cond_front (fun (ts', p) ->
                                       match p with
                                       | Proof.S sp -> (ts_of_tp (Proof.s_ltp sp)
                                                          tstps_in'' tstps_out'') < (first_ts + a)
                                       | V _ -> raise (Invalid_argument "found V proof in S deque")) d)) in
    let s_alphas_beta_step3 = remove_cond_front_ne (fun d' -> Fdeque.is_empty d') s_alphas_beta_step2 in
    (* s_alphas_suffix *)
    let s_alphas_suffix' = remove_cond_front (fun (_, sp) -> (Proof.s_at sp) < first_tp) s_alphas_suffix in
    (* v_alphas_in and v_alphas_out *)
    let v_alphas_out_step1 = remove_cond_front (fun (_, p) -> (Proof.p_at p) < first_tp) v_alphas_out in
    let (new_out_v_alphas, v_alphas_in') = split_out_in (fun (ts', _) -> ts')
                                             (first_ts, (first_ts + a)) v_alphas_in in
    let v_alphas_out' = sorted_append new_out_v_alphas v_alphas_out_step1 in
    (* v_betas_in *)
    let v_betas_suffix_in' = remove_cond_front (fun (_, vp) ->
                                 match Fdeque.peek_front tstps_in'' with
                                 | None -> (match Fdeque.peek_back tstps_out'' with
                                            | None -> (Proof.v_at vp) <= ntp
                                            | Some(_, tp') -> (Proof.v_at vp) <= tp')
                                 | Some (_, tp') -> (Proof.v_at vp) < tp') v_betas_suffix_in in
    { tstps_in = tstps_in''
    ; tstps_out = tstps_out''
    ; s_alphas_beta = s_alphas_beta_step3
    ; s_alphas_suffix = s_alphas_suffix'
    ; v_betas_alpha = v_betas_alpha_step3
    ; v_alphas_out = v_alphas_out'
    ; v_alphas_in = v_alphas_in'
    ; v_betas_suffix_in = v_betas_suffix_in'
    ; optimal_proofs }

  let eval_step a (nts, ntp) ts tp muaux =
    let cur_alphas_beta = Fdeque.peek_front_exn muaux.s_alphas_beta in
    let optimal_proofs_step1 = if not (Fdeque.is_empty cur_alphas_beta) then
                                 (match Fdeque.peek_front_exn cur_alphas_beta with
                                  | (_, S sp) -> if tp = Proof.s_at sp then
                                                   Fdeque.enqueue_back muaux.optimal_proofs (ts, S sp)
                                                 else muaux.optimal_proofs
                                  | _ -> raise (Invalid_argument "found V proof in S deque"))
                               else muaux.optimal_proofs in
    let optimal_proofs_step2 =
      if Int.equal (Fdeque.length optimal_proofs_step1) (Fdeque.length muaux.optimal_proofs) then
        (let c1 = if not (Fdeque.is_empty muaux.v_betas_alpha) then
                    let cur_betas_alpha = Fdeque.peek_front_exn muaux.v_betas_alpha in
                    (if not (Fdeque.is_empty cur_betas_alpha) then
                       match Fdeque.peek_front_exn cur_betas_alpha with
                       | (_, V VUntil(_, vp1, vp2s)) ->
                          (match Fdeque.peek_front muaux.tstps_in with
                           | None -> []
                           | Some(_, first_tp_in) ->
                              if Proof.v_etp (VUntil(tp, vp1, vp2s)) = first_tp_in then
                                [Proof.V (VUntil(tp, vp1, vp2s))]
                              else [])
                       | _ -> raise (Invalid_argument "proof should be VUntil")
                     else [])
                  else [] in
         let c2 = if not (Fdeque.is_empty muaux.v_alphas_out) then
                    let vvp1 = snd(Fdeque.peek_front_exn muaux.v_alphas_out) in
                    match vvp1 with
                    | V vp1 -> [Proof.V (VUntil (tp, vp1, Fdeque.empty))]
                    | S _ -> raise (Invalid_argument "found S proof in V deque")
                  else [] in
         let c3 = if Int.equal (Fdeque.length muaux.v_betas_suffix_in) (Fdeque.length muaux.tstps_in) then
                    let ltp = match Fdeque.peek_back muaux.v_betas_suffix_in with
                      | None -> snd(Fdeque.peek_back_exn muaux.tstps_out)
                      | Some(_, vp2) -> (Proof.v_at vp2) in
                    [Proof.V (VUntilInf (tp, ltp, Fdeque.map muaux.v_betas_suffix_in ~f:snd))]
                  else [] in
         let cps = c1 @ c2 @ c3 in
         if List.length cps > 0 then
           Fdeque.enqueue_back muaux.optimal_proofs (ts, minp_list cps)
         else muaux.optimal_proofs)
      else optimal_proofs_step1 in
    adjust a (nts, ntp) { muaux with optimal_proofs = optimal_proofs_step2 }

  let shift (a, b) (nts, ntp) muaux =
    let tstps = ready_tstps b nts muaux.tstps_out muaux.tstps_in in
    Fdeque.fold tstps ~init:muaux ~f:(fun muaux' (ts, tp) ->
        eval_step a (nts, ntp) ts tp muaux')

  let update i nts ntp p1 p2 muaux =
    let a = Interval.left i in
    let b = match Interval.right i with
      | None -> raise (Invalid_argument "Until interval is unbounded")
      | Some(b') -> b' in
    let muaux_shifted = shift (a, b) (nts, ntp) muaux in
    let (tstps_out, tstps_in) = add_tstp_future a b nts ntp muaux_shifted.tstps_out muaux_shifted.tstps_in in
    add_subps a (nts, ntp) p1 p2 { muaux_shifted with tstps_out; tstps_in }

  let rec eval i nts ntp (muaux, ops) =
    let a = Interval.left i in
    let b = match Interval.right i with
      | None -> raise (Invalid_argument "Until interval is unbounded")
      | Some(b') -> b' in
    let muaux_shifted = shift (a, b) (nts, ntp) muaux in
    match Fdeque.peek_back muaux.optimal_proofs with
    | None -> (muaux, ops)
    | Some(ts, _) -> if ts + b < nts then
                       let ((_, op), optimal_proofs) = Fdeque.dequeue_back_exn muaux_shifted.optimal_proofs in
                       let (muaux', ops') = eval i nts ntp ({ muaux_shifted with optimal_proofs }, ops) in
                       (muaux', ops' @ [op])
                     else (muaux, ops)

end

module Prev_Next = struct

  type operator = Prev | Next

  let update_eval op i p ts ts' =
    let c1 = (match p with
              | Proof.S sp -> if Interval.mem (ts' - ts) i then
                                (match op with
                                 | Prev -> [Proof.S (SPrev sp)]
                                 | Next -> [S (SNext sp)])
                              else []
              | V vp -> (match op with
                         | Prev -> [V (VPrev vp)]
                         | Next -> [V (VNext vp)])) in
    let c2 = if Interval.below (ts' - ts) i then
               (match op with
                | Prev -> [Proof.V (VPrevOutL ((Proof.p_at p)+1))]
                | Next -> [V (VNextOutL ((Proof.p_at p)-1))])
             else [] in
    let c3 = if (Interval.above (ts' - ts) i) then
               (match op with
                | Prev -> [Proof.V (VPrevOutR ((Proof.p_at p)+1))]
                | Next -> [V (VNextOutR ((Proof.p_at p)-1))])
             else [] in
    minp_list (c1 @ c2 @ c3)

end

module MFormula = struct

  type t =
    | MTT
    | MFF
    | MEqConst      of string * Dom.t
    | MPredicate    of string * Term.t list
    | MNeg          of t
    | MAnd          of t * t * (Expl.t, Expl.t) Buf2.t
    | MOr           of t * t * (Expl.t, Expl.t) Buf2.t
    | MImp          of t * t * (Expl.t, Expl.t) Buf2.t
    | MIff          of t * t * (Expl.t, Expl.t) Buf2.t
    | MExists       of string * Dom.tt * t
    | MForall       of string * Dom.tt * t
    | MPrev         of Interval.t * t * bool * (Expl.t, timestamp) Buft.t
    | MNext         of Interval.t * t * bool * timestamp list
    | MOnce         of Interval.t * t * (timestamp * timepoint) list * Once.t Expl.Pdt.t
    | MEventually   of Interval.t * t * (Expl.t, timestamp * timepoint) Buft.t * Eventually.t Expl.Pdt.t
    | MHistorically of Interval.t * t * (timestamp * timepoint) list * Historically.t Expl.Pdt.t
    | MAlways       of Interval.t * t * (Expl.t, timestamp * timepoint) Buft.t * Always.t Expl.Pdt.t
    | MSince        of Interval.t * t * t * (Expl.t, Expl.t, timestamp * timepoint) Buf2t.t * Since.t Expl.Pdt.t
    | MUntil        of Interval.t * t * t * (Expl.t, Expl.t, timestamp * timepoint) Buf2t.t * Until.t Expl.Pdt.t

  let rec var_tt x = function
    | MTT | MFF -> []
    | MEqConst _ -> []
    | MPredicate (r, trms) -> (match (List.findi trms ~f:(fun i y -> Pred.Term.equal (Var x) y)) with
                               | None -> []
                               | Some (i, _) -> let props = Hashtbl.find_exn Pred.Sig.table r in
                                                [snd (List.nth_exn props.ntconsts i)])
    | MNeg f
      | MExists (_, _, f)
      | MForall (_, _, f)
      | MPrev (_, f, _, _)
      | MNext (_, f, _, _)
      | MOnce (_, f, _, _)
      | MEventually (_, f, _, _)
      | MHistorically (_, f, _, _)
      | MAlways (_, f, _, _) -> var_tt x f
    | MAnd (f, g, _)
      | MOr (f, g, _)
      | MImp (f, g, _)
      | MIff (f, g, _)
      | MSince (_, f, g, _, _)
      | MUntil (_, f, g, _, _) -> var_tt x f @ var_tt x g

  let rec init = function
    | Formula.TT -> MTT
    | Formula.FF -> MFF
    | Formula.EqConst (x, c) -> MEqConst (x, c)
    | Formula.Predicate (r, trms) -> MPredicate (r, trms)
    | Formula.Neg (f) -> MNeg (init f)
    | Formula.And (_, f, g) -> MAnd (init f, init g, ([], []))
    | Formula.Or (_, f, g) -> MOr (init f, init g, ([], []))
    | Formula.Imp (_, f, g) -> MImp (init f, init g, ([], []))
    | Formula.Iff (_, _, f, g) -> MIff (init f, init g, ([], []))
    | Formula.Exists (x, f) -> let mf = init f in MExists (x, List.hd_exn (var_tt x mf), mf)
    | Formula.Forall (x, f) -> let mf = init f in MForall (x, List.hd_exn (var_tt x mf), mf)
    | Formula.Prev (i, f) -> MPrev (i, init f, true, ([], []))
    | Formula.Next (i, f) -> MNext (i, init f, true, [])
    | Formula.Once (i, f) -> MOnce (i, init f, [], Leaf (Once.init ()))
    | Formula.Eventually (i, f) -> MEventually (i, init f, ([], []), Leaf (Eventually.init ()))
    | Formula.Historically (i, f) -> MHistorically (i, init f, [], Leaf (Historically.init ()))
    | Formula.Always (i, f) -> MAlways (i, init f, ([], []), Leaf (Always.init ()))
    | Formula.Since (_, i, f, g) -> MSince (i, init f, init g, (([], []), []), Leaf (Since.init ()))
    | Formula.Until (_, i, f, g) -> MUntil (i, init f, init g, (([], []), []), Leaf (Until.init ()))

  let rec to_string_rec l = function
    | MTT -> Printf.sprintf "⊤"
    | MFF -> Printf.sprintf "⊥"
    | MEqConst (x, c) -> Printf.sprintf "%s = %s" x (Dom.to_string c)
    | MPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
    | MNeg f -> Printf.sprintf "¬%a" (fun x -> to_string_rec 5) f
    | MAnd (f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a ∧ %a") (fun x -> to_string_rec 4) f (fun x -> to_string_rec 4) g
    | MOr (f, g, _) -> Printf.sprintf (Etc.paren l 3 "%a ∨ %a") (fun x -> to_string_rec 3) f (fun x -> to_string_rec 4) g
    | MImp (f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a → %a") (fun x -> to_string_rec 4) f (fun x -> to_string_rec 4) g
    | MIff (f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a ↔ %a") (fun x -> to_string_rec 4) f (fun x -> to_string_rec 4) g
    | MExists (x, _, f) -> Printf.sprintf (Etc.paren l 5 "∃%s. %a") x (fun x -> to_string_rec 5) f
    | MForall (x, _, f) -> Printf.sprintf (Etc.paren l 5 "∀%s. %a") x (fun x -> to_string_rec 5) f
    | MPrev (i, f, _, _) -> Printf.sprintf (Etc.paren l 5 "●%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
    | MNext (i, f, _, _) -> Printf.sprintf (Etc.paren l 5 "○%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
    | MOnce (i, f, _, _) -> Printf.sprintf (Etc.paren l 5 "⧫%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
    | MEventually (i, f, _, _) -> Printf.sprintf (Etc.paren l 5 "◊%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
    | MHistorically (i, f, _, _) -> Printf.sprintf (Etc.paren l 5 "■%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
    | MAlways (i, f, _, _) -> Printf.sprintf (Etc.paren l 5 "□%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
    | MSince (i, f, g, _, _) -> Printf.sprintf (Etc.paren l 0 "%a S%a %a") (fun x -> to_string_rec 5) f (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) g
    | MUntil (i, f, g, _, _) -> Printf.sprintf (Etc.paren l 0 "%a U%a %a") (fun x -> to_string_rec 5) f (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) g
  let to_string = to_string_rec 0

end

include MFormula

let do_neg = function
  | Proof.S sp -> Proof.V (VNeg sp)
  | V vp -> S (SNeg vp)

let do_and (p1: Proof.t) (p2: Proof.t) : Proof.t list = match p1, p2 with
  | S sp1, S sp2 -> [S (SAnd (sp1, sp2))]
  | S _ , V vp2 -> [V (VAndR (vp2))]
  | V vp1, S _ -> [V (VAndL (vp1))]
  | V vp1, V vp2 -> [(V (VAndL (vp1))); (V (VAndR (vp2)))]

let do_or (p1: Proof.t) (p2: Proof.t) : Proof.t list = match p1, p2 with
  | S sp1, S sp2 -> [(S (SOrL (sp1))); (S (SOrR(sp2)))]
  | S sp1, V _ -> [S (SOrL (sp1))]
  | V _ , S sp2 -> [S (SOrR (sp2))]
  | V vp1, V vp2 -> [V (VOr (vp1, vp2))]

let do_imp (p1: Proof.t) (p2: Proof.t) : Proof.t list = match p1, p2 with
  | S _, S sp2 -> [S (SImpR sp2)]
  | S sp1, V vp2 -> [V (VImp (sp1, vp2))]
  | V vp1, S sp2 -> [S (SImpL vp1); S (SImpR sp2)]
  | V vp1, V _ -> [S (SImpL vp1)]

let do_iff (p1: Proof.t) (p2: Proof.t) : Proof.t = match p1, p2 with
  | S sp1, S sp2 -> S (SIffSS (sp1, sp2))
  | S sp1, V vp2 -> V (VIffSV (sp1, vp2))
  | V vp1, S sp2 -> V (VIffVS (vp1, sp2))
  | V vp1, V vp2 -> S (SIffVV (vp1, vp2))

let do_exists_leaf x tc = function
  | Proof.S sp -> [Proof.S (SExists (x, Dom.tt_default tc, sp))]
  | V vp -> [Proof.V (VExists (x, Part.trivial vp))]

let do_exists_node x tc part =
  if Part.exists part Proof.isS then
    (let sats = Part.filter part (fun p -> Proof.isS p) in
     (Part.values (Part.map2_dedup Proof.equal sats (fun (s, p) ->
                       match p with
                       | S sp -> (let witness = Setc.some_elt tc s in
                                  (Setc.Finite (Set.of_list (module Dom) [witness]),
                                   Proof.S (Proof.SExists (x, Setc.some_elt tc s, sp))))
                       | V vp -> raise (Invalid_argument "found V proof in S list")))))
  else [V (Proof.VExists (x, Part.map_dedup Proof.v_equal part Proof.unV))]

let do_forall_leaf x tc = function
  | Proof.S sp -> [Proof.S (SForall (x, Part.trivial sp))]
  | V vp -> [Proof.V (VForall (x, Dom.tt_default tc, vp))]

let do_forall_node x tc part =
  if Part.for_all part Proof.isS then
    [Proof.S (SForall (x, Part.map part Proof.unS))]
  else
    (let vios = Part.filter part (fun p -> Proof.isV p) in
     (Part.values (Part.map2_dedup Proof.equal vios (fun (s, p) ->
                       match p with
                       | S sp -> raise (Invalid_argument "found S proof in V list")
                       | V vp -> (let witness = Setc.some_elt tc s in
                                  (Setc.Finite (Set.of_list (module Dom) [witness]),
                                   Proof.V (Proof.VForall (x, Setc.some_elt tc s, vp))))))))

let rec match_terms trms ds map =
  match trms, ds with
  | [], [] -> Some(map)
  | Term.Const c :: trms, d :: ds -> if Dom.equal c d then match_terms trms ds map else None
  | Var x :: trms, d :: ds -> (match match_terms trms ds map with
                               | None -> None
                               | Some(map') -> (match Map.find map' x with
                                                | None -> let map'' = Map.add_exn map' ~key:x ~data:d in Some(map'')
                                                | Some z -> (if Dom.equal d z then Some map' else None)))
  | _, _ -> None

let print_maps maps =
  Stdio.print_endline "> Map:";
  List.iter maps ~f:(fun map -> Map.iteri map ~f:(fun ~key:k ~data:v ->
                                    Stdio.printf "%s -> %s\n" (Term.to_string k) (Dom.to_string v)))

let rec pdt_of tp r trms (vars: string list) maps : Expl.t = match vars with
  | [] -> if List.is_empty maps then Leaf (V (VPred (tp, r, trms)))
          else Leaf (S (SPred (tp, r, trms)))
  | x :: vars ->
     let ds = List.fold maps ~init:[]
                ~f:(fun acc map -> match Map.find map x with
                                   | None -> acc
                                   | Some(d) -> d :: acc) in
     let find_maps d = List.fold maps ~init:[]
                         ~f:(fun acc map -> match Map.find map x with
                                            | None -> acc
                                            | Some(d') -> if Dom.equal d d' then
                                                            map :: acc
                                                          else acc) in
     let part = Part.tabulate_dedup (Pdt.eq Proof.equal) (Set.of_list (module Dom) ds)
                  (fun d -> pdt_of tp r trms vars (find_maps d)) (pdt_of tp r trms vars []) in
     Node (x, part)

let rec meval vars ts tp (db: Db.t) = function
  | MTT -> ([Pdt.Leaf (Proof.S (STT tp))], MTT)
  | MFF -> ([Leaf (V (VFF tp))], MFF)
  | MEqConst (x, d) ->
     let l1 = Pdt.Leaf (Proof.S (SEqConst (tp, x, d))) in
     let l2 = Pdt.Leaf (Proof.V (VEqConst (tp, x, d))) in
     let expl = Pdt.Node (x, [(Setc.Complement (Set.of_list (module Dom) [d]), l2);
                              (Setc.Finite (Set.of_list (module Dom) [d]), l1)]) in
     ([expl], MEqConst (x, d))
  | MPredicate (r, trms) ->
     let db' = Set.filter db ~f:(fun evt -> String.equal r (fst(evt))) in
     if List.is_empty trms then
       (let expl = if Set.is_empty db' then Pdt.Leaf (Proof.V (VPred (tp, r, trms)))
                   else Leaf (S (SPred (tp, r, trms))) in
        ([expl], MPredicate (r, trms)))
     else
       let maps = Set.fold db' ~init:[] ~f:(fun acc evt -> match_terms trms (snd evt) (Map.empty (module String)) :: acc) in
       let maps' = List.map (List.filter maps ~f:(fun map_opt -> match map_opt with
                                                                 | None -> false
                                                                 | Some(map) -> not (Map.is_empty map)))
                     ~f:(fun map_opt -> Option.value_exn map_opt) in
       let fv = Set.elements (Formula.fv (Predicate (r, trms))) in
       let fv_vars = List.filter vars ~f:(fun var -> List.mem fv var ~equal:String.equal) in
       let expl = pdt_of tp r trms fv_vars maps' in
       ([expl], MPredicate (r, trms))
  | MNeg (mf) ->
     let (expls, mf') = meval vars ts tp db mf in
     let f_expls = List.map expls ~f:(fun expl -> (Pdt.apply1_reduce Proof.equal vars (fun p -> do_neg p) expl)) in
     (f_expls, MNeg(mf'))
  | MAnd (mf1, mf2, buf2) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (f_expls, buf2') =
       Buf2.take
         (fun expl1 expl2 -> Pdt.apply2_reduce Proof.equal vars (fun p1 p2 -> minp_list (do_and p1 p2)) expl1 expl2)
         (Buf2.add expls1 expls2 buf2) in
     (f_expls, MAnd (mf1', mf2', buf2'))
  | MOr (mf1, mf2, buf2) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (f_expls, buf2') =
       Buf2.take
         (fun expl1 expl2 -> Pdt.apply2_reduce Proof.equal vars (fun p1 p2 -> minp_list (do_or p1 p2)) expl1 expl2)
         (Buf2.add expls1 expls2 buf2) in
     (f_expls, MOr (mf1', mf2', buf2'))
  | MImp (mf1, mf2, buf2) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (f_expls, buf2') =
       Buf2.take
         (fun expl1 expl2 -> Pdt.apply2_reduce Proof.equal vars (fun p1 p2 -> minp_list (do_imp p1 p2)) expl1 expl2)
         (Buf2.add expls1 expls2 buf2) in
     (f_expls, MImp (mf1', mf2', buf2'))
  | MIff (mf1, mf2, buf2) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (f_expls, buf2') =
       Buf2.take
         (fun expl1 expl2 -> Pdt.apply2_reduce Proof.equal vars (fun p1 p2 -> do_iff p1 p2) expl1 expl2)
         (Buf2.add expls1 expls2 buf2) in
     (f_expls, MIff (mf1', mf2', buf2'))
  | MExists (x, tc, mf) ->
     let (expls, mf') = meval (vars @ [x]) ts tp db mf in
     let f_expls = List.map expls ~f:(fun expl ->
                       Pdt.hide_reduce Proof.equal (vars @ [x]) (fun p -> minp_list (do_exists_leaf x tc p))
                         (fun p -> minp_list (do_exists_node x tc p)) expl) in
     (f_expls, MExists(x, tc, mf'))
  | MForall (x, tc, mf) ->
     let (expls, mf') = meval (vars @ [x]) ts tp db mf in
     let f_expls = List.map expls ~f:(fun expl ->
                       Pdt.hide_reduce Proof.equal (vars @ [x]) (fun p -> minp_list (do_forall_leaf x tc p))
                         (fun p -> minp_list (do_forall_node x tc p)) expl) in
     (f_expls, MForall(x, tc, mf'))
  | MPrev (i, mf, first, (buf, tss)) ->
     let (expls, mf') = meval vars ts tp db mf in
     let (f_expls, (buf', tss')) =
       Buft.another_take
         (fun expl ts ts' -> Pdt.apply1_reduce Proof.equal vars (fun p -> Prev_Next.update_eval Prev i p ts ts') expl)
         (buf @ expls, tss @ [ts]) in
     ((if first then (Leaf (V VPrev0) :: f_expls) else f_expls), MPrev (i, mf', false, (buf', tss')))
  | MNext (i, mf, first, tss) ->
     let (expls, mf') = meval vars ts tp db mf in
     let (expls', first) = if first && (List.length expls) > 0 then (List.tl_exn expls, false)
                           else (expls, first) in
     let (f_expls, (buf', tss')) =
       Buft.another_take
         (fun expl ts ts' -> Pdt.apply1_reduce Proof.equal vars (fun p -> Prev_Next.update_eval Next i p ts ts') expl)
         (expls', tss @ [ts]) in
     (f_expls, MNext (i, mf', first, tss'))
  | MOnce (i, mf, tstps, moaux_pdt) ->
     let (expls, mf') = meval vars ts tp db mf in
     let ((moaux_pdt', expls'), buf', tstps') =
       Buft.take
         (fun expl ts tp (aux_pdt, es) ->
           let (aux_pdt', es') =
             Pdt.split_prod (Pdt.apply2 vars (fun p aux -> Once.update i ts tp p aux) expl aux_pdt) in
           (aux_pdt', es @ (Pdt.split_list es')))
         (moaux_pdt, []) (expls, (tstps @ [(ts,tp)])) in
     let expls'' = List.map expls' ~f:(Pdt.reduce Proof.equal) in
     (expls'', MOnce (i, mf', tstps', moaux_pdt'))
  | MEventually (i, mf, (buf, ntstps), meaux_pdt) ->
     let (expls, mf') = meval vars ts tp db mf in
     let (meaux_pdt', buf', ntstps') =
       Buft.take
         (fun expl ts tp aux_pdt -> Pdt.apply2 vars (fun p aux -> Eventually.update i ts tp p aux) expl aux_pdt)
         meaux_pdt (buf @ expls, (ntstps @ [(ts,tp)])) in
     let (nts, ntp) = match ntstps' with
       | [] -> (ts, tp)
       | (nts', ntp') :: _ -> (nts', ntp') in
     let (meaux_pdt', es') =
       Pdt.split_prod (Pdt.apply1 vars (fun aux -> Eventually.eval i nts ntp (aux, [])) meaux_pdt') in
     let expls' = Pdt.split_list es' in
     let expls'' = List.map expls' ~f:(Pdt.reduce Proof.equal) in
     (expls'', MEventually (i, mf', (buf', ntstps'), meaux_pdt'))
  | MHistorically (i, mf, tstps, mhaux_pdt) ->
     let (expls, mf') = meval vars ts tp db mf in
     let ((mhaux_pdt', expls'), buf', tstps') =
       Buft.take
         (fun expl ts tp (aux_pdt, es) ->
           let (aux_pdt', es') =
             Pdt.split_prod (Pdt.apply2 vars (fun p aux -> Historically.update i ts tp p aux) expl aux_pdt) in
           (aux_pdt', es @ (Pdt.split_list es')))
         (mhaux_pdt, []) (expls, (tstps @ [(ts,tp)])) in
     let expls'' = List.map expls' ~f:(Pdt.reduce Proof.equal) in
     (expls'', MHistorically (i, mf', tstps', mhaux_pdt'))
  | MAlways (i, mf, (buf, ntstps), maaux_pdt) ->
     let (expls, mf') = meval vars ts tp db mf in
     let (maaux_pdt', buf', ntstps') =
       Buft.take
         (fun expl ts tp aux_pdt -> Pdt.apply2 vars (fun p aux -> Always.update i ts tp p aux) expl aux_pdt)
         maaux_pdt (buf @ expls, (ntstps @ [(ts,tp)])) in
     let (nts, ntp) = match ntstps' with
       | [] -> (ts, tp)
       | (nts', ntp') :: _ -> (nts', ntp') in
     let (maaux_pdt', es') =
       Pdt.split_prod (Pdt.apply1 vars (fun aux -> Always.eval i nts ntp (aux, [])) maaux_pdt') in
     let expls' = Pdt.split_list es' in
     let expls'' = List.map expls' ~f:(Pdt.reduce Proof.equal) in
     (expls'', MAlways (i, mf', (buf', ntstps'), maaux_pdt'))
  | MSince (i, mf1, mf2, (buf2, tstps), msaux_pdt) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let ((msaux_pdt', expls'), (buf2', tstps')) =
       Buf2t.take
         (fun expl1 expl2 ts tp (aux_pdt, es) ->
           let (aux_pdt', es') =
             Pdt.split_prod (Pdt.apply3 vars (fun p1 p2 aux -> Since.update i ts tp p1 p2 aux) expl1 expl2 aux_pdt) in
           (aux_pdt', es @ (Pdt.split_list es')))
         (msaux_pdt, []) (Buf2.add expls1 expls2 buf2) (tstps @ [(ts,tp)]) in
     let expls'' = List.map expls' ~f:(Pdt.reduce Proof.equal) in
     (expls'', MSince (i, mf1', mf2', (buf2', tstps'), msaux_pdt'))
  | MUntil (i, mf1, mf2, (buf2, ntstps), muaux_pdt) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (muaux_pdt', (buf2', ntstps')) =
       Buf2t.take
         (fun expl1 expl2 ts tp aux_pdt ->
           Pdt.apply3 vars (fun p1 p2 aux -> Until.update i ts tp p1 p2 aux) expl1 expl2 aux_pdt)
         muaux_pdt (Buf2.add expls1 expls2 buf2) (ntstps @ [(ts,tp)]) in
     let (nts, ntp) = match ntstps' with
       | [] -> (ts, tp)
       | (nts', ntp') :: _ -> (nts', ntp') in
     let (muaux_pdt', es') =
       Pdt.split_prod (Pdt.apply1 vars (fun aux -> Until.eval i nts ntp (aux, [])) muaux_pdt') in
     let expls' = Pdt.split_list es' in
     let expls'' = List.map expls' ~f:(Pdt.reduce Proof.equal) in
     (expls'', MUntil (i, mf1', mf2', (buf2', ntstps'), muaux_pdt'))

module MState = struct

  type t = { mf: MFormula.t
           ; tp_cur: timepoint                        (* current time-point evaluated    *)
           ; tp_out: timepoint                        (* last time-point that was output *)
           ; ts_waiting: timestamp Queue.t
           ; tsdbs: (timestamp * Db.t) Queue.t
           ; tpts: (timepoint, timestamp) Hashtbl.t }

  let init mf = { mf = mf
                ; tp_cur = 0
                ; tp_out = -1
                ; ts_waiting = Queue.create ()
                ; tsdbs = Queue.create ()
                ; tpts = Hashtbl.create (module Int) }

  let to_string { mf
                ; tp_cur
                ; tp_out
                ; ts_waiting
                ; tsdbs
                ; tpts } =
    "\nMState: \n\n" ^
      Printf.sprintf "mf = %s\n" (MFormula.to_string mf) ^
        Printf.sprintf "tp_cur = %d\n" tp_cur ^
          Printf.sprintf "tp_out = %d\n" tp_out ^
            "\nts_waiting = [" ^ (String.concat ~sep:", "
                                    (Queue.to_list (Queue.map ts_waiting ~f:Int.to_string))) ^ "]\n" ^
              "\ntsdbs = [" ^ (String.concat ~sep:", "
                                 (Queue.to_list (Queue.map tsdbs ~f:(fun (ts, db) ->
                                                     Printf.sprintf "(%d):\n %s\n" ts (Db.to_string db))))) ^ "]\n" ^
                "\ntpts = [" ^ (String.concat ~sep:", "
                                  (Hashtbl.fold tpts ~init:[] ~f:(fun ~key:tp ~data:ts acc ->
                                       acc @ [Printf.sprintf "(%d, %d)" tp ts]))) ^ "]\n"

end

let mstep mode vars ts db (ms: MState.t) =
  let (expls, mf') = meval vars ts ms.tp_cur db ms.mf in
  Queue.enqueue ms.ts_waiting ts;
  let tstps = List.zip_exn (List.take (Queue.to_list ms.ts_waiting) (List.length expls))
                (List.range ms.tp_cur (ms.tp_cur + List.length expls)) in
  let tsdbs = match mode with
    | Out.Plain.VERIFIED
      | Out.Plain.DEBUG -> Queue.enqueue ms.tsdbs (ts, db); ms.tsdbs
    | _ -> ms.tsdbs in
  (List.zip_exn tstps expls,
   { ms with
     mf = mf'
   ; tp_cur = ms.tp_cur + 1
   ; ts_waiting = queue_drop ms.ts_waiting (List.length expls)
   ; tsdbs = tsdbs })

let exec mode measure f inc =
  let rec step pb_opt ms =
    match Other_parser.Trace.parse_from_channel inc pb_opt with
    | None -> ()
    | Some (more, pb) ->
       (let (tstp_expls, ms') = mstep mode (Set.elements (Formula.fv f)) pb.ts pb.db ms in
        (match mode with
         | Out.Plain.UNVERIFIED -> Out.Plain.expls pb.ts tstp_expls None None None mode
         | Out.Plain.LATEX -> Out.Plain.expls pb.ts tstp_expls None None (Some(f)) mode
         | Out.Plain.LIGHT -> Out.Plain.expls pb.ts tstp_expls None None None mode
         | Out.Plain.DEBUGVIS -> raise (Failure "function exec is undefined for the mode debugvis")
         | Out.Plain.VERIFIED ->
            let c = Checker_interface.check (Queue.to_list ms'.tsdbs) f (List.map tstp_expls ~f:snd) in
            Out.Plain.expls pb.ts tstp_expls (Some(c)) None None mode
         | Out.Plain.DEBUG ->
            let c = Checker_interface.check (Queue.to_list ms'.tsdbs) f (List.map tstp_expls ~f:snd) in
            let paths = Checker_interface.false_paths (Queue.to_list ms'.tsdbs) f (List.map tstp_expls ~f:snd) in
            Out.Plain.expls pb.ts tstp_expls (Some(c)) (Some(paths)) None mode);
        if more then step (Some(pb)) ms') in
  let mf = init f in
  let ms = MState.init mf in
  step None ms

let exec_vis (obj_opt: MState.t option) f log =
  let step (ms: MState.t) db =
    try
      (match Other_parser.Trace.parse_from_string db with
       | None -> None
       | Some (_, pb) ->
          (let last_ts = Hashtbl.fold ms.tpts ~init:0 ~f:(fun ~key:_ ~data:ts l_ts -> if ts > l_ts then ts else l_ts) in
           if pb.ts >= last_ts then
             let (tstps_expls, ms') = mstep Out.Plain.UNVERIFIED (Set.elements (Formula.fv f)) pb.ts pb.db ms in
             let tp_out' = List.fold tstps_expls ~init:ms'.tp_out
                             ~f:(fun acc ((ts, tp), _) -> Hashtbl.add_exn ms.tpts ~key:(acc + 1) ~data:ts; acc + 1) in
             let json_expls = Out.Json.expls ms.tpts f (List.map tstps_expls ~f:snd) in
             let json_db = Out.Json.db pb.ts ms.tp_cur pb.db f in
             Some (None, (json_expls, [json_db]),
                   { ms' with tp_out = tp_out' })
           else raise (Failure "trace is not monotonic")))
    with Failure msg -> Some (Some(msg), ([], []), ms) in
  let ms = match obj_opt with
    | None -> let mf = init f in
              MState.init mf
    | Some (ms') -> { ms' with tp_cur = ms'.tp_out + (Queue.length ms'.ts_waiting) + 1 } in
  let str_dbs = List.map (List.filter (String.split log ~on:'@') ~f:(fun s -> not (String.is_empty s)))
                  ~f:(fun s -> "@" ^ s) in
  let (fail_msg_opt, (json_expls, json_dbs), ms') =
    List.fold str_dbs ~init:(None, ([], []), ms)
      ~f:(fun (fail_msg_opt, (json_es, json_dbs), m) str_db ->
        match step m str_db with
        | None -> (fail_msg_opt, (json_es, json_dbs), m)
        | Some (fail_msg_opt', (json_es', json_dbs'), m') ->
           (fail_msg_opt', (json_es @ json_es', json_dbs @ json_dbs'), m')) in
  let json = Out.Json.aggregate json_dbs json_expls in
  match fail_msg_opt with
  | None -> (ms', json)
  | Some (fail_msg) -> Stdio.print_endline fail_msg; (ms, json)
