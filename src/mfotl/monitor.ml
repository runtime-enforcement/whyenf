(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Core_kernel
open Etc
open Expl
open Pred

let minp_list = Proof.Size.minp_list
let minp_bool = Proof.Size.minp_bool
let minp = Proof.Size.minp

let s_append_deque sp1 d =
  Deque.iteri d ~f:(fun i (ts, ssp) ->
      match ssp with
      | Proof.S sp -> Deque.set_exn d i (ts, S (Proof.s_append sp sp1))
      | V _ -> raise (Invalid_argument "found V proof in S deque"))

let v_append_deque vp2 d =
  Deque.iteri d ~f:(fun i (ts, vvp) ->
      match vvp with
      | Proof.V vp -> Deque.set_exn d i (ts, V (Proof.v_append vp vp2))
      | S _ -> raise (Invalid_argument "found S proof in V deque"))

let snd_deque d =
  Deque.fold d ~init:(Deque.create ()) ~f:(fun acc (ts, p) ->
      Deque.enqueue_back acc p; acc)

let remove_cond_front f d =
  let rec remove_cond_front_rec f d = match Deque.dequeue_front d with
    | None -> ()
    | Some(el') -> if (f el') then remove_cond_front_rec f d
                   else Deque.enqueue_front d el' in
  remove_cond_front_rec f d

let remove_cond_front_ne f d =
  let rec remove_cond_front_ne_rec f d =
    if (Deque.length d) > 1 then
      (match Deque.dequeue_front d with
       | None -> ()
       | Some(el') -> if (f el') then remove_cond_front_ne_rec f d
                      else Deque.enqueue_front d el') in
  remove_cond_front_ne_rec f d

let remove_cond_back f d =
  let rec remove_cond_back_rec f d =
    match Deque.dequeue_back d with
    | None -> ()
    | Some(el') -> if (f el') then remove_cond_back_rec f d
                   else Deque.enqueue_back d el' in
  remove_cond_back_rec f d

let sorted_append new_in d =
  Deque.iter new_in ~f:(fun (ts, p) ->
      remove_cond_back (fun (ts', p') -> minp_bool p p') d;
      Deque.enqueue_back d (ts, p))

let sorted_enqueue (ts, p) d =
  remove_cond_back (fun (_, p') -> minp_bool p p') d;
  Deque.enqueue_back d (ts, p)

(* TODO: split_in_out and split_out_in should be rewritten as a single function *)
(* split_in_out considers a closed interval [l, r] *)
let split_in_out get_ts (l, r) d =
  let new_in = Deque.create () in
  let rec split_in_out_rec d =
    match Deque.dequeue_front d with
    | None -> ()
    | Some(el) -> let ts = get_ts el in
                  if ts <= r then
                    (if ts >= l then (Deque.enqueue_back new_in el; split_in_out_rec d)
                     else Deque.enqueue_front d el) in
  new_in

(* split_out_in considers an interval of the form [z, l) *)
let split_out_in get_ts (z, l) d =
  let new_out = Deque.create () in
  let rec split_out_in_rec d =
    match Deque.dequeue_front d with
    | None -> ()
    | Some(el) -> let ts = get_ts el in
                  if ts < l then
                    (if ts >= z then (Deque.enqueue_back new_out el; split_out_in_rec d)
                     else Deque.enqueue_front d el) in
  new_out

let etp tstps_in tstps_out tp =
  match Deque.peek_front tstps_in with
  | None -> (match Deque.peek_front tstps_out with
             | None -> tp
             | Some (_, tp') -> tp')
  | Some (_, tp') -> tp'

let ready_tstps b nts tstps_out tstps_in =
  let d = Deque.create () in
  Deque.iter tstps_out ~f:(fun (ts, tp) ->
      if ts + b < nts then Deque.enqueue_back d (ts, tp));
  Deque.iter tstps_in ~f:(fun (ts, tp) ->
      if ts + b < nts then Deque.enqueue_back d (ts, tp)); d

let first_ts_tp tstps_out tstps_in =
  match Deque.peek_front tstps_out with
  | None -> (match Deque.peek_front tstps_in with
             | None -> None
             | Some(ts, tp) -> Some(ts, tp))
  | Some(ts, tp) -> Some(ts, tp)

let drop_first_ts_tp tstps_out tstps_in =
  match Deque.peek_front tstps_out with
  | None -> Deque.drop_front tstps_in
  | Some _ -> Deque.drop_front tstps_out

let add_tstp_future a b nts ntp tstps_out tstps_in =
  (* (ts, tp) update is performed differently if the queues are not empty *)
  if not (Deque.is_empty tstps_out) || not (Deque.is_empty tstps_in) then
    let first_ts = match first_ts_tp tstps_out tstps_in with
      | None -> raise (Failure "tstps deques are empty")
      | Some(ts', _) -> ts' in
    if nts < first_ts + a then Deque.enqueue_back tstps_out (nts, ntp)
    else Deque.enqueue_back tstps_in (nts, ntp)
  else
    (if nts >= a && nts <= b || a == 0 then
       Deque.enqueue_back tstps_in (nts, ntp)
     else Deque.enqueue_back tstps_out (nts, ntp))

let shift_tstps_future a first_ts ntp tstps_out tstps_in =
  Deque.iter tstps_in ~f:(fun (ts', tp') ->
      if (ts' < first_ts + a) && (tp' < ntp) then
        Deque.enqueue_back tstps_out (ts', tp'));
  remove_cond_front (fun (ts', tp') -> (ts' < first_ts) && (tp' < ntp)) tstps_out;
  remove_cond_front (fun (ts', tp') -> (ts' < first_ts + a) && (tp' < ntp)) tstps_in

let shift_tstps_past (l, r) a ts tp tstps_in tstps_out =
  if a = 0 then
    (Deque.enqueue_back tstps_in (ts, tp);
     remove_cond_front (fun (ts', _) -> ts' < l) tstps_in)
  else
    (Deque.enqueue_back tstps_out (ts, tp);
     Deque.iter tstps_out ~f:(fun (ts', tp') ->
         if ts' <= r then Deque.enqueue_back tstps_in (ts', tp'));
     remove_cond_front (fun (ts', _) -> ts' <= r) tstps_out;
     remove_cond_front (fun (ts', _) -> ts' < l) tstps_in)

let print_tstps ts_zero tstps_in tstps_out =
  (match ts_zero with
   | None -> ""
   | Some(ts) -> Printf.sprintf "\n\tts_zero = (%d)\n" ts) ^
    Deque.fold tstps_in ~init:"\n\ttstps_in = ["
      ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
        Deque.fold tstps_out ~init:"\n\ttstps_out = ["
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

  type ('a, 'b, 'c) t = 'a list * 'b list * 'c list

  let rec take f w = function
    | [], ys, zs -> (w, ([], ys, zs))
    | xs, [], zs -> (w, (xs, [], zs))
    | xs, ys, [] -> (w, (xs, ys, []))
    | x::xs, y::ys, (a,b)::zs -> take f (f x y a b w) (xs, ys, zs)

end


module Once = struct

  type t = { mutable ts_zero: timestamp option
           ; tstps_in: (timestamp * timepoint) Deque.t
           ; tstps_out: (timestamp * timepoint) Deque.t
           ; s_alphas_in: (timestamp * Proof.t) Deque.t
           ; s_alphas_out: (timestamp * Proof.t) Deque.t
           ; v_alphas_in: (timestamp * Proof.vp) Deque.t
           ; v_alphas_out: (timestamp * Proof.vp) Deque.t }

  let init () = { ts_zero = None
                ; tstps_in = Deque.create ()
                ; tstps_out = Deque.create ()
                ; s_alphas_in = Deque.create ()
                ; s_alphas_out = Deque.create ()
                ; v_alphas_in = Deque.create ()
                ; v_alphas_out = Deque.create () }

  let moaux_to_string { ts_zero
                      ; tstps_in
                      ; tstps_out
                      ; s_alphas_in
                      ; s_alphas_out
                      ; v_alphas_in
                      ; v_alphas_out } =
    ("\n\nOnce state: " ^ (print_tstps ts_zero tstps_in tstps_out) ^
       Deque.fold s_alphas_in ~init:"\ns_alphas_in = "
         ~f:(fun acc (ts, p) ->
           acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
         Deque.fold s_alphas_out ~init:"\ns_alphas_out = "
           ~f:(fun acc (ts, p) ->
             acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
           Deque.fold v_alphas_in ~init:"\nv_alphas_in = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.v_to_string "" p) ^
             Deque.fold v_alphas_out ~init:"\nv_alphas_out = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.v_to_string "" p))

  let update_s_alphas_in new_in_sat s_alphas_in =
    if not (Deque.is_empty new_in_sat) then
      sorted_append new_in_sat s_alphas_in

  let update_v_alphas_in new_in_vio v_alphas_in =
    Deque.iter new_in_vio ~f:(fun (ts, vp) ->
        Deque.enqueue_back v_alphas_in (ts, vp))

  let add_subps ts p1 s_alphas_out v_alphas_out = match p1 with
    | Proof.S sp1 -> Deque.enqueue_back s_alphas_out (ts, (Proof.S sp1))
    | V vp1 -> Deque.enqueue_back v_alphas_out (ts, vp1)

  let remove (l, r) moaux =
    remove_cond_front (fun (ts, _) -> ts < l) moaux.s_alphas_in;
    remove_cond_front (fun (ts, _) -> ts <= r) moaux.s_alphas_out;
    remove_cond_front (fun (ts, _) -> ts < l) moaux.v_alphas_in;
    remove_cond_front (fun (ts, _) -> ts <= r) moaux.v_alphas_out

  let shift_sat (l, r) s_alphas_out s_alphas_in =
    let new_in_sat = split_in_out (fun (ts, _) -> ts) (l, r) s_alphas_out in
    update_s_alphas_in new_in_sat s_alphas_in

  let shift_vio (l, r) v_alphas_out v_alphas_in =
    let new_in_vio = split_in_out (fun (ts, _) -> ts) (l, r) v_alphas_out in
    update_v_alphas_in new_in_vio v_alphas_in

  let shift (l, r) a ts tp moaux =
    shift_tstps_past (l, r) a ts tp moaux.tstps_in moaux.tstps_out;
    shift_sat (l,r) moaux.s_alphas_out moaux.s_alphas_in;
    shift_vio (l,r) moaux.v_alphas_out moaux.v_alphas_in;
    remove (l, r) moaux

  let eval tp moaux =
    if not (Deque.is_empty moaux.s_alphas_in) then
      [Proof.S (SOnce (tp, Proof.unS(snd(Deque.peek_front_exn moaux.s_alphas_in))))]
    else
      let etp = match Deque.is_empty moaux.v_alphas_in with
        | true -> etp moaux.tstps_in moaux.tstps_out tp
        | false -> Proof.v_at (snd(Deque.peek_front_exn moaux.v_alphas_in)) in
      [Proof.V (VOnce (tp, etp, snd_deque moaux.v_alphas_in))]

  let update i ts tp p1 moaux =
    let a = Interval.left i in
    (if Option.is_none moaux.ts_zero then moaux.ts_zero <- Some(ts));
    add_subps ts p1 moaux.s_alphas_out moaux.v_alphas_out;
    if ts < (Option.value_exn moaux.ts_zero) + a then
      (Deque.enqueue_back moaux.tstps_out (ts, tp);
       (moaux, [Proof.V (VOnceOut tp)]))
    else
      let b = Interval.right i in
      let l = if (Option.is_some b) then max 0 (ts - (Option.value_exn b))
              else (Option.value_exn moaux.ts_zero) in
      let r = ts - a in
      shift (l, r) a ts tp moaux;
      (moaux, eval tp moaux)

end


module Eventually = struct

  type t = { tstps_out: (timestamp * timepoint) Deque.t
           ; tstps_in: (timestamp * timepoint) Deque.t
           ; s_alphas_in: (timestamp * Proof.t) Deque.t
           ; v_alphas_in: (timestamp * Proof.vp) Deque.t
           ; optimal_proofs: (timestamp * Proof.t) Deque.t }

  let init () = { tstps_out = Deque.create ()
                ; tstps_in = Deque.create ()
                ; s_alphas_in = Deque.create ()
                ; v_alphas_in = Deque.create ()
                ; optimal_proofs = Deque.create () }

  let to_string { tstps_out
                ; tstps_in
                ; s_alphas_in
                ; v_alphas_in
                ; optimal_proofs } =
    ("\n\nEventually state: " ^ (print_tstps None tstps_in tstps_out) ^
       Deque.fold s_alphas_in ~init:"\ns_alphas_in = "
         ~f:(fun acc (ts, p) ->
           acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
         Deque.fold v_alphas_in ~init:"\nv_alphas_in = "
           ~f:(fun acc (ts, p) ->
             acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.v_to_string "" p) ^
           Deque.fold optimal_proofs ~init:"\noptimal_proofs = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p))

  let adjust a (nts, ntp) meaux =
    drop_first_ts_tp meaux.tstps_out meaux.tstps_in;
    let (first_ts, first_tp) = match first_ts_tp meaux.tstps_out meaux.tstps_in with
      | None -> (nts, ntp)
      | Some(ts', tp') -> (ts', tp') in
    remove_cond_front (fun (ts', p) -> ts' < first_ts + a || (Proof.p_at p < first_tp)) meaux.s_alphas_in;
    remove_cond_front (fun (ts', vp) -> ts' < first_ts + a || (Proof.v_at vp < first_tp)) meaux.v_alphas_in;
    shift_tstps_future a first_ts ntp meaux.tstps_out meaux.tstps_in

  let eval_step a (nts, ntp) ts tp meaux =
    (if not (Deque.is_empty meaux.s_alphas_in) then
       (match Deque.peek_front_exn meaux.s_alphas_in with
        | (_, S sp) -> Deque.enqueue_back meaux.optimal_proofs
                         (ts, S (SEventually (tp, Proof.unS(snd(Deque.peek_front_exn meaux.s_alphas_in)))))
        | _ -> raise (Invalid_argument "found V proof in S deque"))
     else
       (let ltp = match Deque.peek_back meaux.v_alphas_in with
          | None -> snd(Deque.peek_back_exn meaux.tstps_out)
          | Some (_, vp2) -> Proof.v_at vp2 in
        Deque.enqueue_back meaux.optimal_proofs (ts, V (VEventually (tp, ltp, snd_deque meaux.v_alphas_in)))));
    adjust a (nts, ntp) meaux

  let shift (a, b) (nts, ntp) meaux =
    let tstps = ready_tstps b nts meaux.tstps_out meaux.tstps_in in
    Deque.iter tstps ~f:(fun (ts, tp) -> eval_step a (nts, ntp) ts tp meaux)

  let add_subp a (ts, tp) (p1: Proof.t) meaux =
    let first_ts = match first_ts_tp meaux.tstps_out meaux.tstps_in with
      | None -> 0
      | Some(ts', _) -> ts' in
    match p1 with
    | S sp1 -> if ts >= first_ts + a then
                 sorted_enqueue (ts, (S sp1)) meaux.s_alphas_in
    | V vp1 -> if ts >= first_ts + a then
                 Deque.enqueue_back meaux.v_alphas_in (ts, vp1)

  let update i nts ntp p meaux =
    let a = Interval.left i in
    let b = match Interval.right i with
      | None -> raise (Invalid_argument "Eventually interval is unbounded")
      | Some(b') -> b' in
    shift (a, b) (nts, ntp) meaux;
    add_tstp_future a b nts ntp meaux.tstps_out meaux.tstps_in;
    add_subp a (nts, ntp) p meaux;
    meaux

  let rec eval i nts ntp (meaux, ops) =
    let a = Interval.left i in
    let b = match Interval.right i with
      | None -> raise (Invalid_argument "Eventually interval is unbounded")
      | Some(b') -> b' in
    shift (a, b) (nts, ntp) meaux;
    match Deque.peek_back meaux.optimal_proofs with
    | None -> (meaux, ops)
    | Some(ts, _) -> if ts + b < nts then
                       let (ts', op) = Deque.dequeue_back_exn meaux.optimal_proofs in
                       let (meaux', ops') = eval i nts ntp (meaux, ops) in
                       (meaux', ops' @ [op])
                     else (meaux, ops)

end


module Historically = struct

  type t = { mutable ts_zero: timestamp option
           ; tstps_in: (timestamp * timepoint) Deque.t
           ; tstps_out: (timestamp * timepoint) Deque.t
           ; s_alphas_in: (timestamp * Proof.sp) Deque.t
           ; s_alphas_out: (timestamp * Proof.sp) Deque.t
           ; v_alphas_in: (timestamp * Proof.t) Deque.t
           ; v_alphas_out: (timestamp * Proof.t) Deque.t }

  let init () = { ts_zero = None
                ; tstps_in = Deque.create ()
                ; tstps_out = Deque.create ()
                ; s_alphas_in = Deque.create ()
                ; s_alphas_out = Deque.create ()
                ; v_alphas_in = Deque.create ()
                ; v_alphas_out = Deque.create () }

  let to_string { ts_zero
                ; tstps_in
                ; tstps_out
                ; s_alphas_in
                ; s_alphas_out
                ; v_alphas_in
                ; v_alphas_out } =
    ("\n\nHistorically state: " ^ (print_tstps ts_zero tstps_in tstps_out) ^
       Deque.fold s_alphas_in ~init:"\ns_alphas_in = "
         ~f:(fun acc (ts, sp) ->
           acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.s_to_string "" sp) ^
         Deque.fold s_alphas_out ~init:"\ns_alphas_out = "
           ~f:(fun acc (ts, sp) ->
             acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.s_to_string "" sp) ^
           Deque.fold v_alphas_in ~init:"\nv_alphas_in = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
             Deque.fold v_alphas_in ~init:"\nv_alphas_out = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p))

  let update_s_alphas_in new_in_sat s_alphas_in =
    Deque.iter new_in_sat (fun (ts, sp) ->
        Deque.enqueue_back s_alphas_in (ts, sp))

  let update_v_alphas_in new_in_vio v_alphas_in =
    if not (Deque.is_empty new_in_vio) then
      sorted_append new_in_vio v_alphas_in

  let add_subps ts (p1: Proof.t) mhaux = match p1 with
    | S sp1 -> Deque.enqueue_back mhaux.s_alphas_out (ts, sp1)
    | V vp1 -> Deque.enqueue_back mhaux.v_alphas_out (ts, (V vp1))

  let shift_sat (l, r) s_alphas_out s_alphas_in =
    let new_in_sat = split_in_out (fun (ts, _) -> ts) (l, r) s_alphas_out in
    update_s_alphas_in new_in_sat s_alphas_in

  let shift_vio (l, r) v_alphas_out v_alphas_in =
    let new_in_viol = split_in_out (fun (ts, _) -> ts) (l, r) v_alphas_out in
    update_v_alphas_in new_in_viol v_alphas_in

  let clean (l, r) mhaux =
    remove_cond_front (fun (ts, _) -> ts < l) mhaux.s_alphas_in;
    remove_cond_front (fun (ts, _) -> ts <= r) mhaux.s_alphas_out;
    remove_cond_front (fun (ts, _) -> ts < l) mhaux.v_alphas_in;
    remove_cond_front (fun (ts, _) -> ts <= r) mhaux.v_alphas_out

  let shift (l, r) a ts tp mhaux =
    shift_tstps_past (l, r) a ts tp mhaux.tstps_in mhaux.tstps_out;
    shift_sat (l,r) mhaux.s_alphas_out mhaux.s_alphas_in;
    shift_vio (l,r) mhaux.v_alphas_out mhaux.v_alphas_in;
    clean (l, r) mhaux

  let eval tp mhaux =
    if not (Deque.is_empty mhaux.v_alphas_in) then
      Proof.V (VHistorically (tp, Proof.unV(snd(Deque.peek_front_exn mhaux.v_alphas_in))))
    else
      let etp = match Deque.is_empty mhaux.s_alphas_in with
        | true -> etp mhaux.tstps_in mhaux.tstps_out tp
        | false -> Proof.s_at (snd(Deque.peek_front_exn mhaux.s_alphas_in)) in
      S (SHistorically (tp, etp, snd_deque mhaux.s_alphas_in))

  let update i ts tp p1 mhaux =
    let a = Interval.left i in
    (if Option.is_none mhaux.ts_zero then mhaux.ts_zero <- Some(ts));
    add_subps ts p1 mhaux;
    if ts < (Option.value_exn mhaux.ts_zero) + a then
      (Deque.enqueue_back mhaux.tstps_out (ts, tp);
       (Proof.S (SHistoricallyOut tp), mhaux))
    else
      let b = Interval.right i in
      let l = if (Option.is_some b) then max 0 (ts - (Option.value_exn b))
              else (Option.value_exn mhaux.ts_zero) in
      let r = ts - a in
      shift (l, r) a ts tp mhaux;
      (eval tp mhaux, mhaux)

end

module Always = struct

  type t = { tstps_out: (timestamp * timepoint) Deque.t
           ; tstps_in: (timestamp * timepoint) Deque.t
           ; v_alphas_in: (timestamp * Proof.t) Deque.t
           ; s_alphas_in: (timestamp * Proof.sp) Deque.t
           ; optimal_proofs: (timestamp * Proof.t) Deque.t }

  let init () = { tstps_out = Deque.create ()
                ; tstps_in = Deque.create ()
                ; v_alphas_in = Deque.create ()
                ; s_alphas_in = Deque.create ()
                ; optimal_proofs = Deque.create () }

  let to_string { tstps_out
                ; tstps_in
                ; v_alphas_in
                ; s_alphas_in
                ; optimal_proofs } =
    ("\n\nAlways state: " ^ (print_tstps None tstps_in tstps_out) ^
       Deque.fold v_alphas_in ~init:"\nv_alphas_in = "
         ~f:(fun acc (ts, p) ->
           acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
         Deque.fold s_alphas_in ~init:"\ns_alphas_in = "
           ~f:(fun acc (ts, sp) ->
             acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.s_to_string "" sp) ^
           Deque.fold optimal_proofs ~init:"\noptimal_proofs = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p))

  let adjust a (nts, ntp) maaux =
    drop_first_ts_tp maaux.tstps_out maaux.tstps_in;
    let (first_ts, first_tp) = match first_ts_tp maaux.tstps_out maaux.tstps_in with
      | None -> (nts, ntp)
      | Some(ts', tp') -> (ts', tp') in
    remove_cond_front (fun (ts', p) -> ts' < first_ts + a || (Proof.p_at p < first_tp)) maaux.v_alphas_in;
    remove_cond_front (fun (ts', sp) -> ts' < first_ts + a || (Proof.s_at sp < first_tp)) maaux.s_alphas_in;
    shift_tstps_future a first_ts ntp maaux.tstps_out maaux.tstps_in

  let eval_step a (nts, ntp) ts tp maaux =
    (if not (Deque.is_empty maaux.v_alphas_in) then
       (match Deque.peek_front_exn maaux.v_alphas_in with
        | (_, V vp) -> Deque.enqueue_back maaux.optimal_proofs
                         (ts, V (VAlways (tp, Proof.unV(snd(Deque.peek_front_exn maaux.v_alphas_in)))))
        | _ -> raise (Invalid_argument "found S proof in V deque"))
     else
       (let ltp = match Deque.peek_back maaux.s_alphas_in with
          | None -> snd(Deque.peek_back_exn maaux.tstps_out)
          | Some (_, sp) -> Proof.s_at sp in
        Deque.enqueue_back maaux.optimal_proofs (ts, S (SAlways (tp, ltp, snd_deque maaux.s_alphas_in)))));
    adjust a (nts, ntp) maaux

  let shift (a, b) (nts, ntp) maaux =
    let tstps = ready_tstps b nts maaux.tstps_out maaux.tstps_in in
    Deque.iter tstps ~f:(fun (ts, tp) -> eval_step a (nts, ntp) ts tp maaux)

  let add_subps a (ts, tp) (p1: Proof.t) maaux =
    let first_ts = match first_ts_tp maaux.tstps_out maaux.tstps_in with
      | None -> 0
      | Some(ts', _) -> ts' in
    match p1 with
    | V vp1 -> if ts >= first_ts + a then
                 sorted_enqueue (ts, (V vp1)) maaux.v_alphas_in
    | S sp1 -> if ts >= (first_ts + a) then
                 Deque.enqueue_back maaux.s_alphas_in (ts, sp1)

  let update i nts ntp p maaux =
    let a = Interval.left i in
    let b = match Interval.right i with
      | None -> raise (Invalid_argument "Always interval is unbounded")
      | Some(b') -> b' in
    shift (a, b) (nts, ntp) maaux;
    add_tstp_future a b nts ntp maaux.tstps_out maaux.tstps_in;
    add_subps a (nts, ntp) p maaux

  let rec eval d i nts ntp maaux =
    let a = Interval.left i in
    let b = match Interval.right i with
      | None -> raise (Invalid_argument "Always interval is unbounded")
      | Some(b') -> b' in
    shift (a, b) (nts, ntp) maaux;
    match Deque.peek_back maaux.optimal_proofs with
    | None -> (nts, d, maaux)
    | Some(ts, _) -> if ts + b < nts then
                       let (ts', op) = Deque.dequeue_back_exn maaux.optimal_proofs in
                       let (_, ops, maaux) = eval d i nts ntp maaux in
                       Deque.enqueue_back ops op;
                       (ts', ops, maaux)
                     else (ts, d, maaux)

end

module Since = struct

  type t = { mutable ts_zero: timestamp option
           ; tstps_in: (timestamp * timepoint) Deque.t
           ; tstps_out: (timestamp * timepoint) Deque.t
           ; s_beta_alphas_in: (timestamp * Proof.t) Deque.t
           ; s_beta_alphas_out: (timestamp * Proof.t) Deque.t
           ; v_alpha_betas_in: (timestamp * Proof.t) Deque.t
           ; v_alphas_out: (timestamp * Proof.t) Deque.t
           ; v_betas_in: (timestamp * Proof.vp) Deque.t
           ; v_alphas_betas_out: (timestamp * Proof.vp option * Proof.vp option) Deque.t }

  let init () = { ts_zero = None
                ; tstps_in = Deque.create ()
                ; tstps_out = Deque.create ()
                ; s_beta_alphas_in = Deque.create ()
                ; s_beta_alphas_out = Deque.create ()
                ; v_alpha_betas_in = Deque.create ()
                ; v_alphas_out = Deque.create ()
                ; v_betas_in = Deque.create ()
                ; v_alphas_betas_out = Deque.create () }

  let to_string { ts_zero
                ; tstps_in
                ; tstps_out
                ; s_beta_alphas_in
                ; s_beta_alphas_out
                ; v_alpha_betas_in
                ; v_alphas_out
                ; v_betas_in
                ; v_alphas_betas_out } =
    ("\n\nSince state: " ^ (print_tstps ts_zero tstps_in tstps_out) ^
       Deque.fold s_beta_alphas_in ~init:"\ns_beta_alphas_in = "
         ~f:(fun acc (ts, p) ->
           acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
         Deque.fold s_beta_alphas_out ~init:"\ns_beta_alphas_out = "
           ~f:(fun acc (ts, p) ->
             acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
           Deque.fold v_alpha_betas_in ~init:"\nv_alpha_betas_in = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
             Deque.fold v_alphas_out ~init:"\nv_alphas_out = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
               Deque.fold v_betas_in ~init:"\nv_betas_in = "
                 ~f:(fun acc (ts, p) ->
                   acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.v_to_string "" p) ^
                 Deque.fold v_alphas_betas_out ~init:"\nv_alphas_betas_out = "
                   ~f:(fun acc (ts, p1_opt, p2_opt) ->
                     match p1_opt, p2_opt with
                     | None, None -> acc
                     | Some(p1), None -> acc ^ (Printf.sprintf "\n(%d)\nalpha = " ts) ^ Proof.v_to_string "" p1
                     | None, Some(p2) -> acc ^ (Printf.sprintf "\n(%d)\nbeta = " ts) ^ Proof.v_to_string "" p2
                     | Some(p1), Some(p2) -> acc ^ (Printf.sprintf "\n(%d)\nalpha = " ts) ^ Proof.v_to_string "" p1 ^
                                               (Printf.sprintf "\n(%d)\nbeta = " ts) ^ Proof.v_to_string "" p2))

  let add_v_alphas_out ts vvp' v_alphas_out =
    remove_cond_back (fun (_, vvp) -> minp_bool vvp' vvp) v_alphas_out;
    Deque.enqueue_back v_alphas_out (ts, vvp')

  let update_s_beta_alphas_in new_in s_beta_alphas_in =
    if not (Deque.is_empty new_in) then
      sorted_append new_in s_beta_alphas_in

  let update_v_betas_in new_in v_betas_in =
    Deque.iter new_in ~f:(fun (ts, _, vp2_opt) ->
        match vp2_opt with
        | None -> Deque.clear v_betas_in
        | Some(vp2) -> Deque.enqueue_back v_betas_in (ts, vp2))

  let construct_vsinceps tp new_in =
    Deque.fold new_in ~init:(Deque.create ())
      ~f:(fun acc (ts, vp1_opt, vp2_opt) ->
        match vp1_opt with
        | None -> (match vp2_opt with
                   | None -> Deque.clear acc; acc
                   | Some(vp2) -> v_append_deque vp2 acc; acc)
        | Some(vp1) -> (match vp2_opt with
                        | None -> Deque.clear acc; acc
                        | Some(vp2) -> v_append_deque vp2 acc;
                                       let vp2s = Deque.create () in
                                       Deque.enqueue_back vp2s vp2;
                                       let vp = Proof.V (VSince (tp, vp1, vp2s)) in
                                       Deque.enqueue_back acc (ts, vp); acc))

  let add_new_ps_v_alpha_betas_in tp new_in v_alpha_betas_in =
    let new_vps_in = construct_vsinceps tp new_in in
    if not (Deque.is_empty new_vps_in) then
      sorted_append new_vps_in v_alpha_betas_in

  let update_v_alpha_betas_in_tps tp v_alpha_betas_in =
    Deque.iteri v_alpha_betas_in ~f:(fun i (ts, vvp) ->
        match vvp with
        | Proof.V (VSince (tp', vp1, vp2s)) -> Deque.set_exn v_alpha_betas_in i (ts, V (VSince (tp, vp1, vp2s)))
        | _ -> raise (Invalid_argument "found S proof in V deque"))

  let update_v_alpha_betas_in tp new_in v_alpha_betas_in =
    Deque.iter new_in ~f:(fun (_, _, vp2_opt) ->
        match vp2_opt with
        | None -> Deque.clear v_alpha_betas_in
        | Some(vp2) -> v_append_deque vp2 v_alpha_betas_in);
    add_new_ps_v_alpha_betas_in tp new_in v_alpha_betas_in;
    update_v_alpha_betas_in_tps tp v_alpha_betas_in

  let add_subps ts (p1: Proof.t) (p2: Proof.t) msaux =
    match p1, p2 with
    | S sp1, S sp2 ->
       (* s_beta_alphas_in *)
       s_append_deque sp1 msaux.s_beta_alphas_in;
       (* s_beta_alphas_out *)
       s_append_deque sp1 msaux.s_beta_alphas_out;
       let sp = Proof.S (SSince (sp2, Deque.create ())) in
       Deque.enqueue_back msaux.s_beta_alphas_out (ts, sp);
       (* v_alphas_betas_out *)
       Deque.enqueue_back msaux.v_alphas_betas_out (ts, None, None)
    | S sp1, V vp2 ->
       (* s_beta_alphas_in *)
       s_append_deque sp1 msaux.s_beta_alphas_in;
       s_append_deque sp1 msaux.s_beta_alphas_out;
       (* v_alphas_betas_out *)
       Deque.enqueue_back msaux.v_alphas_betas_out (ts, None, Some(vp2))
    | V vp1, S sp2 ->
       (* s_beta_alphas_in *)
       Deque.clear msaux.s_beta_alphas_in;
       (* s_beta_alphas_out *)
       Deque.clear msaux.s_beta_alphas_out;
       let sp = Proof.S (SSince (sp2, Deque.create ())) in
       Deque.enqueue_back msaux.s_beta_alphas_out (ts, sp);
       (* v_alphas_out *)
       add_v_alphas_out ts (V vp1) msaux.v_alphas_out;
       (* v_alphas_betas_out *)
       Deque.enqueue_back msaux.v_alphas_betas_out (ts, Some(vp1), None)
    | V vp1, V vp2 ->
       (* s_beta_alphas_in *)
       Deque.clear msaux.s_beta_alphas_in;
       (* s_beta_alphas_out *)
       Deque.clear msaux.s_beta_alphas_out;
       (* v_alphas_out *)
       add_v_alphas_out ts (V vp1) msaux.v_alphas_out;
       (* v_alphas_betas_out *)
       Deque.enqueue_back msaux.v_alphas_betas_out (ts, Some(vp1), Some(vp2))

  let shift_sat (l, r) s_beta_alphas_out s_beta_alphas_in =
    let new_in_sat = split_in_out (fun (ts, _) -> ts) (l, r) s_beta_alphas_out in
    update_s_beta_alphas_in new_in_sat s_beta_alphas_in

  let shift_vio (l, r) tp v_alphas_betas_out v_alpha_betas_in v_betas_in =
    let new_in_vio = split_in_out (fun (ts, _, _) -> ts) (l, r) v_alphas_betas_out in
    update_v_betas_in new_in_vio v_betas_in;
    update_v_alpha_betas_in tp new_in_vio v_alpha_betas_in

  let clean (l, r) msaux =
    remove_cond_front (fun (ts, _) -> ts < l) msaux.s_beta_alphas_in;
    remove_cond_front (fun (ts, _) -> ts < l) msaux.v_alpha_betas_in;
    remove_cond_front (fun (ts, _) -> ts <= r) msaux.v_alphas_out;
    remove_cond_front (fun (ts, _) -> ts < l) msaux.v_betas_in

  let shift (l, r) a ts tp msaux =
    shift_tstps_past (l, r) a ts tp msaux.tstps_in msaux.tstps_out;
    shift_sat (l,r) msaux.s_beta_alphas_out msaux.s_beta_alphas_in;
    shift_vio (l,r) tp msaux.v_alphas_betas_out msaux.v_alpha_betas_in msaux.v_betas_in;
    clean (l, r) msaux

  let eval tp msaux =
    if not (Deque.is_empty msaux.s_beta_alphas_in) then
      [snd(Deque.peek_front_exn msaux.s_beta_alphas_in)]
    else
      let cp1 = if not (Deque.is_empty msaux.v_alpha_betas_in) then
                  [snd(Deque.peek_front_exn msaux.v_alpha_betas_in)]
                else [] in
      let cp2 = if not (Deque.is_empty msaux.v_alphas_out) then
                  let vp_f2 = snd(Deque.peek_front_exn msaux.v_alphas_out) in
                  match vp_f2 with
                  | V f2 -> [Proof.V (VSince (tp, f2, Deque.create ()))]
                  | S _ -> raise (Invalid_argument "found S proof in V deque")
                else [] in
      let cp3 = if Int.equal (Deque.length msaux.v_betas_in) (Deque.length msaux.tstps_in) then
                  let etp = match Deque.is_empty msaux.v_betas_in with
                    | true -> etp msaux.tstps_in msaux.tstps_out tp
                    | false -> Proof.v_at (snd(Deque.peek_front_exn msaux.v_betas_in)) in
                  [Proof.V (VSinceInf (tp, etp, snd_deque msaux.v_betas_in))]
                else [] in
      (cp1 @ cp2 @ cp3)

  let update i ts tp p1 p2 msaux =
    let a = Interval.left i in
    (if Option.is_none msaux.ts_zero then msaux.ts_zero <- Some(ts));
    add_subps ts p1 p2 msaux;
    if ts < (Option.value_exn msaux.ts_zero) + a then
      (Deque.enqueue_back msaux.tstps_out (ts, tp);
       ([Proof.V (VSinceOut tp)], msaux))
    else
      (let b = Interval.right i in
       let l = if (Option.is_some b) then max 0 (ts - (Option.value_exn b))
               else (Option.value_exn msaux.ts_zero) in
       let r = ts - a in
       shift (l, r) a ts tp msaux;
       (eval tp msaux, msaux))

end

module Until = struct

  type t = { tstps_in: (timestamp * timepoint) Deque.t
           ; tstps_out: (timestamp * timepoint) Deque.t
           ; s_alphas_beta: ((timestamp * Proof.t) Deque.t) Deque.t
           ; s_alphas_suffix: (timestamp * Proof.sp) Deque.t
           ; v_betas_alpha: ((timestamp * Proof.t) Deque.t) Deque.t
           ; v_alphas_out: (timestamp * Proof.t) Deque.t
           ; v_alphas_in: (timestamp * Proof.t) Deque.t
           ; v_betas_suffix_in: (timestamp * Proof.vp) Deque.t
           ; optimal_proofs: (timestamp * Proof.t) Deque.t }

  let init () = let s_alphas_beta = Deque.create () in
                let v_betas_alpha = Deque.create () in
                Deque.enqueue_back s_alphas_beta (Deque.create ());
                Deque.enqueue_back v_betas_alpha (Deque.create ());
                { tstps_in = Deque.create ()
                ; tstps_out = Deque.create ()
                ; s_alphas_beta = s_alphas_beta
                ; s_alphas_suffix = Deque.create ()
                ; v_betas_alpha = v_betas_alpha
                ; v_alphas_out = Deque.create ()
                ; v_alphas_in = Deque.create ()
                ; v_betas_suffix_in = Deque.create ()
                ; optimal_proofs = Deque.create () }

  let to_string { tstps_in
                ; tstps_out
                ; s_alphas_beta
                ; s_alphas_suffix
                ; v_betas_alpha
                ; v_alphas_out
                ; v_alphas_in
                ; v_betas_suffix_in
                ; optimal_proofs } =
    ("\n\nUntil state: " ^ (print_tstps None tstps_in tstps_out) ^
       Deque.foldi s_alphas_beta ~init:"\ns_alphas_beta = \n" ~f:(fun i acc1 d ->
           acc1 ^ Printf.sprintf "\n%d.\n" i ^
             Deque.fold d ~init:"[" ~f:(fun acc2 (ts, p) ->
                 acc2 ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^ "\n]\n") ^
         Deque.fold s_alphas_suffix ~init:"\ns_alphas_suffix = "
           ~f:(fun acc (ts, p) ->
             acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.s_to_string "" p) ^
           Deque.foldi v_betas_alpha ~init:"\nv_betas_alpha = \n"
             ~f:(fun i acc1 d ->
               acc1 ^ Printf.sprintf "\n%d.\n" i ^
                 Deque.fold d ~init:"[" ~f:(fun acc2 (ts, p) ->
                     acc2 ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^ "\n]\n") ^
             Deque.fold v_alphas_out ~init:"\nv_alphas_out = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
               Deque.fold v_alphas_in ~init:"\nv_alphas_in = "
                 ~f:(fun acc (ts, p) ->
                   acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p) ^
                 Deque.fold v_betas_suffix_in ~init:"\nv_betas_suffix_in = "
                   ~f:(fun acc (ts, p) ->
                     acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.v_to_string "" p) ^
                   Deque.fold optimal_proofs ~init:"\noptimal_proofs = "
                     ~f:(fun acc (ts, p) ->
                       acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Proof.to_string "" p))

  let ts_of_tp tp tstps_in tstps_out =
    match (Deque.find tstps_out ~f:(fun (ts', tp') -> tp = tp')) with
    | None -> (match (Deque.find tstps_in ~f:(fun (ts', tp') -> tp = tp')) with
               | None -> raise (Failure "ts not found")
               | Some(ts, _) -> ts)
    | Some(ts, _) -> ts

  let step_sdrop_tp tp s_alphas_beta =
    Deque.fold s_alphas_beta ~init:(Deque.create ())
      ~f:(fun acc (ts, ssp) ->
        match ssp with
        | Proof.S sp -> if tp = (Proof.s_at sp) then
                          (match Proof.s_drop sp with
                           | None -> acc
                           | Some(sp') -> Deque.enqueue_back acc (ts, Proof.S sp'); acc)
                        else (Deque.enqueue_back acc (ts, ssp); acc)
        | V _ -> raise (Invalid_argument "found V proof in S deque"))

  let step_vdrop_ts a first_ts v_betas_alpha tstps_in =
    let rec vdrop_until vp =
      let is_out = match Deque.find ~f:(fun (_, tp') -> (Proof.v_etp vp) = tp') tstps_in with
        | None -> true
        | Some(ts', _) -> ts' < (first_ts + a) in
      if is_out then
        (match Proof.v_drop vp with
         | None -> None
         | Some(vp') -> vdrop_until vp')
      else Some(vp) in
    Deque.fold v_betas_alpha ~init:(Deque.create ())
      ~f:(fun acc (ts, vvp) ->
        (match vvp with
         | Proof.V vp -> (match vdrop_until vp with
                          | None -> acc
                          | Some (vp') -> Deque.enqueue_back acc (ts, Proof.V vp'); acc)
         | S _ -> raise (Invalid_argument "found S proof in V deque")))

  let remove_out_less2_lts lim d =
    Deque.iteri d ~f:(fun i d' ->
        Deque.set_exn d i
          (Deque.fold d' ~init:(Deque.create ()) ~f:(fun acc (ts, p) ->
               if ts >= lim then (Deque.enqueue_back acc (ts, p); acc)
               else acc)));
    remove_cond_front_ne (fun d' -> Deque.is_empty d') d

  let add_subps a (ts, tp) (p1: Proof.t) (p2: Proof.t) muaux =
    let first_ts = match first_ts_tp muaux.tstps_out muaux.tstps_in with
      | None -> 0
      | Some(ts', _) -> ts' in
    match p1, p2 with
    | S sp1, S sp2 ->
       (* alphas_beta *)
       (if ts >= first_ts + a then
          let cur_alphas_beta = Deque.peek_back_exn muaux.s_alphas_beta in
          let sp = Proof.S (SUntil (sp2, snd_deque muaux.s_alphas_suffix)) in
          sorted_enqueue (ts, sp) cur_alphas_beta);
       (* betas_alpha (add empty deque) *)
       (if not (Deque.is_empty (Deque.peek_back_exn muaux.v_betas_alpha)) then
          Deque.enqueue_back muaux.v_betas_alpha (Deque.create ()));
       (* alphas_suffix *)
       Deque.enqueue_back muaux.s_alphas_suffix (ts, sp1);
       (* v_betas_in *)
       (if ts >= (first_ts + a) then Deque.clear muaux.v_betas_suffix_in)
    | S sp1, V vp2 ->
       (* alphas_suffix *)
       Deque.enqueue_back muaux.s_alphas_suffix (ts, sp1);
       (* v_betas_in *)
       (if ts >= (first_ts + a) then Deque.enqueue_back muaux.v_betas_suffix_in (ts, vp2))
    | V vp1, S sp2 ->
       (* alphas_beta *)
       (if ts >= first_ts + a then
          let cur_alphas_beta = Deque.peek_back_exn muaux.s_alphas_beta in
          let sp = Proof.S (SUntil (sp2, snd_deque muaux.s_alphas_suffix)) in
          sorted_enqueue (ts, sp) cur_alphas_beta);
       (* betas_alpha (add empty deque) *)
       (if not (Deque.is_empty (Deque.peek_back_exn muaux.v_betas_alpha)) then
          Deque.enqueue_back muaux.v_betas_alpha (Deque.create ()));
       (* alphas_suffix *)
       Deque.clear muaux.s_alphas_suffix;
       (* alphas_in *)
       (if ts >= first_ts + a then Deque.enqueue_back muaux.v_alphas_in (ts, Proof.V vp1)
        else (remove_cond_back (fun (_, p') -> minp_bool (Proof.V vp1) p') muaux.v_alphas_out;
              Deque.enqueue_back muaux.v_alphas_out (ts, V vp1)));
       (* v_betas_in *)
       (if ts >= (first_ts + a) then Deque.clear muaux.v_betas_suffix_in)
    | V vp1, V vp2 ->
       (* alphas_beta (add empty deque) *)
       (if not (Deque.is_empty (Deque.peek_back_exn muaux.s_alphas_beta)) then
          Deque.enqueue_back muaux.s_alphas_beta (Deque.create ()));
       (* alphas_suffix *)
       Deque.clear muaux.s_alphas_suffix;
       (* v_betas_in *)
       (if ts >= (first_ts + a) then Deque.enqueue_back muaux.v_betas_suffix_in (ts, vp2));
       (* betas_alpha *)
       (if ts >= (first_ts + a) then
          let cur_betas_alpha = Deque.peek_back_exn muaux.v_betas_alpha in
          let vp = Proof.V (VUntil (tp, vp1, snd_deque muaux.v_betas_suffix_in)) in
          sorted_enqueue (ts, vp) cur_betas_alpha);
       (* alphas_in *)
       (if ts >= (first_ts + a) then Deque.enqueue_back muaux.v_alphas_in (ts, V vp1)
        else (remove_cond_back (fun (_, p') -> minp_bool (V vp1) p') muaux.v_alphas_out;
              Deque.enqueue_back muaux.v_alphas_out (ts, V vp1)))

  let drop_tp tp s_alphas_beta =
    match Deque.peek_front s_alphas_beta with
    | None -> raise (Etc.Empty_deque "alphas_beta")
    | Some(front_alphas_beta) ->
       if not (Deque.is_empty front_alphas_beta) then
         let front_index = Deque.front_index_exn s_alphas_beta in
         Deque.set_exn s_alphas_beta front_index (step_sdrop_tp tp front_alphas_beta)

  let drop_v_ts a ts muaux =
    Deque.iteri muaux.v_betas_alpha ~f:(fun i d ->
        Deque.set_exn muaux.v_betas_alpha i (step_vdrop_ts a ts d muaux.tstps_in))

  let drop_v_single_ts cur_tp muaux =
    let first_betas_alpha =
      Deque.fold (Deque.peek_front_exn muaux.v_betas_alpha) ~init:(Deque.create ())
        ~f:(fun acc (ts', vvp) -> (match vvp with
                                   | V vp -> if Proof.v_etp vp <= cur_tp then
                                               (match Proof.v_drop vp with
                                                | None -> acc
                                                | Some (vp') -> Deque.enqueue_back acc (ts', Proof.V vp'); acc)
                                             else (Deque.enqueue_back acc (ts', Proof.V vp); acc)
                                   | S _ -> raise (Invalid_argument "found S proof in V deque"))) in
    Deque.drop_front muaux.v_betas_alpha;
    Deque.enqueue_front muaux.v_betas_alpha first_betas_alpha

  let adjust a (nts, ntp) muaux =
    let eval_tp = match first_ts_tp muaux.tstps_out muaux.tstps_in with
      | None -> raise (Failure "tp not found")
      | Some(_, tp') -> tp' in
    drop_first_ts_tp muaux.tstps_out muaux.tstps_in;
    let (first_ts, first_tp) = match first_ts_tp muaux.tstps_out muaux.tstps_in with
      | None -> (nts, ntp)
      | Some(ts', tp') -> (ts', tp') in
    (* betas_alpha *)
    Deque.iter muaux.v_betas_alpha ~f:(fun d ->
        remove_cond_front (fun (ts', p) -> (ts' < first_ts + a) || ((Proof.p_at p) < first_tp)) d);
    (if a = 0 then drop_v_single_ts eval_tp muaux
     else drop_v_ts a first_ts muaux);
    remove_cond_front_ne (fun d' -> Deque.is_empty d') muaux.v_betas_alpha;
    (* ts_tp_in and ts_tp_out *)
    shift_tstps_future a first_ts ntp muaux.tstps_out muaux.tstps_in;
    (* alphas_beta *)
    drop_tp eval_tp muaux.s_alphas_beta;
    Deque.iter muaux.s_alphas_beta ~f:(fun d ->
        (remove_cond_front (fun (ts', p) ->
             match p with
             | Proof.S sp -> (ts_of_tp (Proof.s_ltp sp) muaux.tstps_in muaux.tstps_out) < (first_ts + a)
             | V _ -> raise (Invalid_argument "found V proof in S deque")) d));
    remove_cond_front_ne (fun d' -> Deque.is_empty d') muaux.s_alphas_beta;
    (* alphas_suffix *)
    remove_cond_front (fun (_, sp) -> (Proof.s_at sp) < first_tp) muaux.s_alphas_suffix;
    (* alphas_in and v_alphas_out *)
    remove_cond_front (fun (_, p) -> (Proof.p_at p) < first_tp) muaux.v_alphas_out;
    let new_out_alphas = split_out_in (fun (ts', _) -> ts') (first_ts, (first_ts + a)) muaux.v_alphas_in in
    sorted_append new_out_alphas muaux.v_alphas_out;
    (* v_betas_in *)
    remove_cond_front (fun (_, vp) ->
        match Deque.peek_front muaux.tstps_in with
        | None -> (match Deque.peek_back muaux.tstps_out with
                   | None -> (Proof.v_at vp) <= ntp
                   | Some(_, tp') -> (Proof.v_at vp) <= tp')
        | Some (_, tp') -> (Proof.v_at vp) < tp') muaux.v_betas_suffix_in

  let eval_step a (nts, ntp) ts tp muaux =
    let optimal_proofs_len = Deque.length muaux.optimal_proofs in
    let cur_alphas_beta = Deque.peek_front_exn muaux.s_alphas_beta in
    (if not (Deque.is_empty cur_alphas_beta) then
       (match Deque.peek_front_exn cur_alphas_beta with
        | (_, S sp) -> if tp = Proof.s_at sp then
                         Deque.enqueue_back muaux.optimal_proofs (ts, S sp)
        | _ -> raise (Invalid_argument "found V proof in S deque")));
    (if Deque.length muaux.optimal_proofs = optimal_proofs_len then
       (let c1 = if not (Deque.is_empty muaux.v_betas_alpha) then
                   let cur_betas_alpha = Deque.peek_front_exn muaux.v_betas_alpha in
                   (if not (Deque.is_empty cur_betas_alpha) then
                      match Deque.peek_front_exn cur_betas_alpha with
                      | (_, V VUntil(_, vp1, vp2s)) ->
                         (match Deque.peek_front muaux.tstps_in with
                          | None -> []
                          | Some(_, first_tp_in) ->
                             if Proof.v_etp (VUntil(tp, vp1, vp2s)) = first_tp_in then
                               [Proof.V (VUntil(tp, vp1, vp2s))]
                             else [])
                      | _ -> raise (Invalid_argument "proof should be VUntil")
                    else [])
                 else [] in
        let c2 = if not (Deque.is_empty muaux.v_alphas_out) then
                   let vvp1 = snd(Deque.peek_front_exn muaux.v_alphas_out) in
                   match vvp1 with
                   | V vp1 -> [Proof.V (VUntil (tp, vp1, Deque.create ()))]
                   | S _ -> raise (Invalid_argument "found S proof in V deque")
                 else [] in
        let c3 = if (Deque.length muaux.v_betas_suffix_in) = (Deque.length muaux.tstps_in) then
                   let ltp = match Deque.peek_back muaux.v_betas_suffix_in with
                     | None -> snd(Deque.peek_back_exn muaux.tstps_out)
                     | Some(_, vp2) -> (Proof.v_at vp2) in
                   [Proof.V (VUntilInf (tp, ltp, snd_deque muaux.v_betas_suffix_in))]
                 else [] in
        let cps = c1 @ c2 @ c3 in
        if List.length cps > 0 then
          Deque.enqueue_back muaux.optimal_proofs (ts, minp_list cps)));
    adjust a (nts, ntp) muaux

  let shift_muaux (a, b) (nts, ntp) muaux =
    let tstps = ready_tstps b nts muaux.tstps_out muaux.tstps_in in
    Deque.iter tstps ~f:(fun (ts, tp) -> eval_step a (nts, ntp) ts tp muaux)

  let update i nts ntp p1 p2 muaux =
    let a = Interval.left i in
    let b = match Interval.right i with
      | None -> raise (Invalid_argument "Until interval is unbounded")
      | Some(b') -> b' in
    shift_muaux (a, b) (nts, ntp) muaux;
    add_tstp_future a b nts ntp muaux.tstps_out muaux.tstps_in;
    add_subps a (nts, ntp) p1 p2 muaux

  let rec eval d i nts ntp muaux =
    let a = Interval.left i in
    let b = match Interval.right i with
      | None -> raise (Invalid_argument "Until interval is unbounded")
      | Some(b') -> b' in
    shift_muaux (a, b) (nts, ntp) muaux;
    match Deque.peek_back muaux.optimal_proofs with
    | None -> (nts, d, muaux)
    | Some(ts, _) -> if ts + b < nts then
                       let (ts', op) = Deque.dequeue_back_exn muaux.optimal_proofs in
                       let (_, ops, muaux) = eval d i nts ntp muaux in
                       Deque.enqueue_back ops op; (ts', ops, muaux)
                     else (ts, d, muaux)

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
    | MPredicate    of string * Term.t list
    | MNeg          of t
    | MAnd          of t * t * (Expl.t, Expl.t) Buf2.t
    | MOr           of t * t * (Expl.t, Expl.t) Buf2.t
    | MImp          of t * t * (Expl.t, Expl.t) Buf2.t
    | MIff          of t * t * (Expl.t, Expl.t) Buf2.t
    | MExists       of Term.t * t
    | MForall       of Term.t * t
    | MPrev         of Interval.t * t * bool * (Expl.t, timestamp) Buft.t
    | MNext         of Interval.t * t * bool * timestamp list
    | MOnce         of Interval.t * t * (timestamp * timepoint) list * Once.t Expl.Pdt.t
    | MEventually   of Interval.t * t * (Expl.t, timestamp * timepoint) Buft.t * Eventually.t Expl.Pdt.t
    | MHistorically of Interval.t * t * (timestamp * timepoint) list * Historically.t Expl.Pdt.t
    | MAlways       of Interval.t * t * (Expl.t, timestamp * timepoint) Buft.t * Always.t Expl.Pdt.t
    | MSince        of Interval.t * t * t * (Expl.t, Expl.t, timestamp * timepoint) Buf2t.t * Since.t Expl.Pdt.t
    | MUntil        of Interval.t * t * t * (Expl.t, Expl.t, timestamp * timepoint) Buf2t.t * Until.t Expl.Pdt.t

  let rec init = function
    | Formula.TT -> MTT
    | Formula.FF -> MFF
    | Formula.Predicate (r, trms) -> MPredicate (r, trms)
    | Formula.Neg (f) -> MNeg (init f)
    | Formula.And (f, g) -> MAnd (init f, init g, ([], []))
    | Formula.Or (f, g) -> MOr (init f, init g, ([], []))
    | Formula.Imp (f, g) -> MImp (init f, init g, ([], []))
    | Formula.Iff (f, g) -> MIff (init f, init g, ([], []))
    | Formula.Exists (x, f) -> MExists (x, init f)
    | Formula.Forall (x, f) -> MForall (x, init f)
    | Formula.Prev (i, f) -> MPrev (i, init f, true, ([], []))
    | Formula.Next (i, f) -> MNext (i, init f, true, [])
    | Formula.Once (i, f) -> MOnce (i, init f, [], Leaf (Once.init ()))
    | Formula.Eventually (i, f) -> MEventually (i, init f, ([], []), Leaf (Eventually.init ()))
    | Formula.Historically (i, f) -> MHistorically (i, init f, [], Leaf (Historically.init ()))
    | Formula.Always (i, f) -> MAlways (i, init f, ([], []), Leaf (Always.init ()))
    | Formula.Since (i, f, g) -> MSince (i, init f, init g, ([], [], []), Leaf (Since.init ()))
    | Formula.Until (i, f, g) -> MUntil (i, init f, init g, ([], [], []), Leaf (Until.init ()))

  let rec to_string_rec l = function
    | MTT -> Printf.sprintf "⊤"
    | MFF -> Printf.sprintf "⊥"
    | MPredicate (r, trms) -> Printf.sprintf "%step(%step)" r (Term.list_to_string trms)
    | MNeg f -> Printf.sprintf "¬%a" (fun x -> to_string_rec 5) f
    | MAnd (f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a ∧ %a") (fun x -> to_string_rec 4) f (fun x -> to_string_rec 4) g
    | MOr (f, g, _) -> Printf.sprintf (Etc.paren l 3 "%a ∨ %a") (fun x -> to_string_rec 3) f (fun x -> to_string_rec 4) g
    | MImp (f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a → %a") (fun x -> to_string_rec 4) f (fun x -> to_string_rec 4) g
    | MIff (f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a ↔ %a") (fun x -> to_string_rec 4) f (fun x -> to_string_rec 4) g
    | MExists (Var x, f) -> Printf.sprintf (Etc.paren l 5 "∃%step. %a") x (fun x -> to_string_rec 5) f
    | MForall (Var x, f) -> Printf.sprintf (Etc.paren l 5 "∀%step. %a") x (fun x -> to_string_rec 5) f
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

let rec match_terms trms ds map =
  match trms, ds with
  | [], [] -> Some(map)
  | Term.Const c :: trms, d :: ds -> if Domain.equal c d then match_terms trms ds map else None
  | Var x :: trms, d :: ds -> (match match_terms trms ds map with
                               | None -> None
                               | Some(map') -> (match Map.find map' (Term.Var x) with
                                                | None -> let map'' = Map.add_exn map' (Term.Var x) d in Some(map'')
                                                | Some z -> (if Domain.equal d z then Some map' else None)))
  | _, _ -> None

let print_maps maps =
  Stdio.print_endline "> Map:";
  List.iter maps ~f:(fun map -> Map.iteri map (fun ~key:k ~data:v ->
                                    Stdio.printf "%s -> %s\n" (Term.to_string k) (Domain.to_string v)))

let rec pdt_of tp r trms vars maps : Expl.t = match vars with
  | [] -> if List.is_empty maps then Leaf (V (VPred (tp, r, trms)))
          else Leaf (S (SPred (tp, r, trms)))
  | x :: vars ->
     let (fmaps, ds) = List.unzip (List.fold maps ~init:[]
                                     ~f:(fun acc map -> match Map.find map x with
                                                        | None -> acc
                                                        | Some(d) -> (map, d) :: acc)) in
     let part = Part.tabulate ds (fun d -> pdt_of tp r trms vars fmaps) (pdt_of tp r trms vars []) in
     Node (x, part)

let rec meval vars ts tp (db: Db.t) = function
  | MTT -> ([Pdt.Leaf (Proof.S (STT tp))], MTT)
  | MFF -> ([Leaf (V (VFF tp))], MFF)
  | MPredicate (r, trms) ->
     let db' = Set.filter db (fun evt -> String.equal r (fst(evt))) in
     let maps = Set.fold db' ~init:[] ~f:(fun acc evt -> match_terms trms (snd evt) (Map.empty (module Term)) :: acc) in
     let maps' = List.map (List.filter maps ~f:(fun map_opt -> match map_opt with
                                                               | None -> false
                                                               | Some(map) -> not (Map.is_empty map)))
                   ~f:(fun map_opt -> Option.value_exn map_opt) in
     let fv = Set.elements (Formula.fv (Predicate (r, trms))) in
     let fv_vars = List.filter vars ~f:(fun var -> List.mem fv var ~equal:Pred.Term.equal) in
     let expl = pdt_of tp r trms fv_vars maps' in
     ([expl], MPredicate (r, trms))
  | MNeg (mf) ->
     let (expls, mf') = meval vars ts tp db mf in
     let f_expls = List.map expls ~f:(fun expl -> (Pdt.apply1 vars (fun p -> do_neg p) expl)) in
     (f_expls, MNeg(mf'))
  | MAnd (mf1, mf2, buf2) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (f_expls, buf2') =
       Buf2.take
         (fun expl1 expl2 -> Pdt.apply2 vars (fun p1 p2 -> minp_list (do_and p1 p2)) expl1 expl2)
         (Buf2.add expls1 expls2 buf2) in
     (f_expls, MAnd (mf1', mf2', buf2'))
  | MOr (mf1, mf2, buf2) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (f_expls, buf2') =
       Buf2.take
         (fun expl1 expl2 -> Pdt.apply2 vars (fun p1 p2 -> minp_list (do_or p1 p2)) expl1 expl2)
         (Buf2.add expls1 expls2 buf2) in
     (f_expls, MOr (mf1', mf2', buf2'))
  | MImp (mf1, mf2, buf2) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (f_expls, buf2') =
       Buf2.take
         (fun expl1 expl2 -> Pdt.apply2 vars (fun p1 p2 -> minp_list (do_imp p1 p2)) expl1 expl2)
         (Buf2.add expls1 expls2 buf2) in
     (f_expls, MImp (mf1', mf2', buf2'))
  | MIff (mf1, mf2, buf2) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (f_expls, buf2') =
       Buf2.take
         (fun expl1 expl2 -> Pdt.apply2 vars (fun p1 p2 -> do_iff p1 p2) expl1 expl2)
         (Buf2.add expls1 expls2 buf2) in
     (f_expls, MIff (mf1', mf2', buf2'))
  | MPrev (i, mf, first, (buf, tss)) ->
     let (expls, mf') = meval vars ts tp db mf in
     let (f_expls, (buf', tss')) =
       Buft.another_take
         (fun expl ts ts' -> Pdt.apply1 vars (fun p -> Prev_Next.update_eval Prev i p ts ts') expl)
         (buf @ expls, tss @ [ts]) in
     ((if first then (Leaf (V VPrev0) :: f_expls) else f_expls), MPrev (i, mf', false, (buf', tss')))
  | MNext (i, mf, first, tss) ->
     let (expls, mf') = meval vars ts tp db mf in
     let (expls', first) = if first && (List.length expls) > 0 then (List.tl_exn expls, false)
                           else (expls, first) in
     let (f_expls, (buf', tss')) =
       Buft.another_take
         (fun expl ts ts' -> Pdt.apply1 vars (fun p -> Prev_Next.update_eval Next i p ts ts') expl)
         (expls', tss @ [ts]) in
     (f_expls, MNext (i, mf', first, tss'))
  | MOnce (i, mf, tstps, moaux_pdt) ->
     let (expls, mf') = meval vars ts tp db mf in
     let ((moaux_pdt', expls'), buf', tstps') =
       Buft.take
         (fun expl ts tp (aux_pdt, es) ->
           let (aux_pdt', es') = Pdt.split_prod (Pdt.apply2 vars (fun p aux ->
                                                     Once.update i ts tp p aux) expl aux_pdt) in
           (aux_pdt', Pdt.split_list es'))
         (moaux_pdt, []) (expls, (tstps @ [(ts,tp)])) in
     (expls', MOnce (i, mf', tstps', moaux_pdt'))
  | MEventually (i, mf, (buf, ntstps), meaux_pdt) ->
     let (expls, mf') = meval vars ts tp db mf in
     let (meaux_pdt', buf', ntstps') =
       Buft.take
         (fun expl ts tp aux_pdt -> Pdt.apply2 vars (fun p aux -> Eventually.update i ts tp p aux) expl aux_pdt)
         meaux_pdt (buf @ expls, (ntstps @ [(ts,tp)])) in
     let (nts, ntp) = match ntstps' with
       | [] -> (ts, tp)
       | (nts', ntp') :: _ -> (nts', ntp') in
     let (meaux_pdt', es') = Pdt.split_prod
                               (Pdt.apply1 vars (fun aux -> Eventually.eval i nts ntp (aux, [])) meaux_pdt') in
     let expls' = Pdt.split_list es' in
     (expls', MEventually (i, mf', (buf', ntstps'), meaux_pdt'))
  (*   | MHistorically (interval, mf, ts_tps, mhaux) -> *)
  (*      let (_, ps, mf') = meval tp ts sap mf in *)
  (*      let _ = Deque.enqueue_back ts_tps (ts, tp) in *)
  (*      let ((ps, mhaux'), buf', ts_tps') = *)
  (*        mbuft_take *)
  (*          (fun p ts tp (ps, aux) -> *)
  (*            let (op, aux) = Historically.update_historically interval ts tp p aux le in *)
  (*            let () = Deque.enqueue_back ps op in *)
  (*            (ps, aux)) *)
  (*          (Deque.create (), mhaux) ps ts_tps in *)
  (*      (ts, ps, MHistorically (interval, mf', ts_tps', mhaux')) *)
  (*   | MAlways (interval, mf, buf, nts_ntps, maaux) -> *)
  (*      (\* let () = Printf.printf "meval ts = %d; tp = %d\n" ts tp in *\) *)
  (*      let (_, ps, mf') = meval tp ts sap mf in *)
  (*      let () = Deque.enqueue_back nts_ntps (ts, tp) in *)
  (*      let () = Deque.iter ps ~f:(fun p -> Deque.enqueue_back buf p) in *)
  (*      let (maaux', buf', nts_ntps') = *)
  (*        mbuft_take *)
  (*          (fun p ts tp aux -> Always.update_always interval ts tp p le aux) *)
  (*          maaux buf nts_ntps in *)
  (*      let (nts, ntp) = match Deque.peek_front nts_ntps' with *)
  (*        | None -> (ts, tp) *)
  (*        | Some(nts', ntp') -> (nts', ntp') in *)
  (*      let (ts', ps, maaux'') = Always.eval_always (Deque.create ()) interval nts ntp le maaux' in *)
  (*      (ts', ps, MAlways (interval, mf', buf', nts_ntps', maaux'')) *)
  (*   | MSince (interval, mf1, mf2, buf, ts_tps, msaux) -> *)
  (*      let (_, p1s, mf1') = meval tp ts sap mf1 in *)
  (*      let (_, p2s, mf2') = meval tp ts sap mf2 in *)
  (*      let _ = Deque.enqueue_back ts_tps (ts, tp) in *)
  (*      let ((ps, msaux'), buf', tss_tps') = *)
  (*        mbuf2t_take *)
  (*          (fun p1 p2 ts tp (ps, aux) -> *)
  (*            let (op, aux) = Since.update_since interval ts tp p1 p2 aux le in *)
  (*            let () = Deque.enqueue_back ps op in *)
  (*            (ps, aux)) *)
  (*          (Deque.create (), msaux) (mbuf2_add p1s p2s buf) ts_tps in *)
  (*      (ts, ps, MSince (interval, mf1', mf2', buf', tss_tps', msaux')) *)
  (*   | MUntil (interval, mf1, mf2, buf, nts_ntps, muaux) -> *)
  (*      let (_, p1s, mf1') = meval tp ts sap mf1 in *)
  (*      let (_, p2s, mf2') = meval tp ts sap mf2 in *)
  (*      let () = Deque.enqueue_back nts_ntps (ts, tp) in *)
  (*      let (muaux', buf', nts_ntps') = *)
  (*        mbuf2t_take *)
  (*          (fun p1 p2 ts tp aux -> Until.update_until interval ts tp p1 p2 le aux) *)
  (*          muaux (mbuf2_add p1s p2s buf) nts_ntps in *)
  (*      let (nts, ntp) = match Deque.peek_front nts_ntps' with *)
  (*        | None -> (ts, tp) *)
  (*        | Some(nts', ntp') -> (nts', ntp') in *)
  (*      let (ts', ps, muaux'') = Until.eval_until (Deque.create ()) interval nts ntp le muaux in *)
  (*      (ts', ps, MUntil (interval, mf1', mf2', buf', nts_ntps', muaux'')) *)
  | _ -> failwith "not yet"

module MState = struct

  type t = { mf: MFormula.t
           ; tp_out: timepoint
           ; ts_waiting: timestamp Queue.t
           ; tsdbs: (timestamp * Db.t) Queue.t }

  let init mf = { mf = mf
                ; tp_out = -1
                ; ts_waiting = Queue.create ()
                ; tsdbs = Queue.create () }

end

let tp = ref (-1)
let next_tp () = tp := !tp + 1; !tp

let mstep mode vars ts db (ms: MState.t) =
  let tp = next_tp () in
  let (expls, mf') = meval vars ts tp db ms.mf in
  Queue.enqueue ms.ts_waiting ts;
  let tstps = List.zip_exn (Queue.to_list ms.ts_waiting) (List.range tp (tp + List.length expls)) in
  let tsdbs = match mode with
    | Out.Plain.UNVERIFIED -> ms.tsdbs
    | _ -> Queue.enqueue ms.tsdbs (ts, db); ms.tsdbs in
  (List.zip_exn tstps expls,
   { ms with
     mf = mf'
   ; tp_out = ms.tp_out + (List.length expls)
   ; ts_waiting = queue_drop ms.ts_waiting (List.length expls)
   ; tsdbs = tsdbs })

let exec mode measure f inc =
  let rec step pb_opt ms =
    let (more, pb) = Other_parser.Trace.parse inc pb_opt in
    let (tstp_expls, ms') = mstep mode (Set.elements (Formula.fv f)) pb.ts pb.db ms in
    (* Stdio.printf "parsed DB: \n%s\n" (Db.to_string pb.db); *)
    (match mode with
     | Out.Plain.UNVERIFIED -> Out.Plain.expls tstp_expls None mode
     | _ -> let c = Checker_interface.check (Queue.to_list ms'.tsdbs) f (List.map tstp_expls ~f:snd) in
            Out.Plain.expls tstp_expls (Some(c)) mode);
    if more then step (Some(pb)) ms' in
  let mf = init f in
  let ms = MState.init mf in
  step None ms
