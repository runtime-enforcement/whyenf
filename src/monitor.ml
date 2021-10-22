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
module List = Core_kernel.List

exception INVALID_EXPL
exception EMPTY_DEQUE
exception UNEXPECTED_BEHAVIOR

(* TODO: Rewrite every occurrence of Deque.to_list in this file *)

let sappend_to_deque sp1 d =
  let _ = Deque.iteri d ~f:(fun i (ts, ssp) ->
              match ssp with
              | S sp -> Deque.set_exn d i (ts, S (sappend sp sp1))
              | V _ -> raise SEXPL) in d

let vappend_to_deque vp2 d =
  let _ = Deque.iteri d ~f:(fun i (ts, vvp) ->
              match vvp with
              | V vp -> Deque.set_exn d i (ts, V (vappend vp vp2))
              | S _ -> raise VEXPL) in d

let betas_suffix_in_to_list betas_suffix_in =
  Deque.fold' betas_suffix_in ~init:[]
    ~f:(fun acc (ts, vp) -> vp::acc) `back_to_front

(* Sort proofs wrt a particular measure, i.e.,
   if |p_1| <= |p_2| in [p_1, p_2, p_3, ..., p_n]
   then p_2 must be removed (and so on).
   In the resulting list, the smallest element
   will be in the tail. *)
let sort_ps le new_in =
  let rec aux ps acc =
    match ps with
    | [] -> acc
    | p::p'::ps' ->
       if le (snd(p)) (snd(p')) then
         aux ps' (p::acc)
       else aux ps' (p'::acc)
    | p::[] -> p::acc in
  let almost_sorted = aux new_in [] in
  match almost_sorted with
  | [] -> []
  | p::[] -> [p]
  | p::p'::ps -> if le (snd(p)) (snd(p')) then
                   (List.rev (p::ps))
                 else (List.rev (p'::ps))

let sort_ps2 le l =
  let rec aux ps acc =
    match ps with
    | [] -> acc
    | (ets1, lts1, x)::(ets2, lts2, x')::xs ->
       if le x x' then
         aux xs ((ets1, lts1, x)::acc)
       else aux xs ((ets2, lts2, x')::acc)
    | x::xs -> x::acc
  in aux l []

module Past = struct
  type msaux = {
      ts_zero: timestamp option
    ; ts_tp_in: (timestamp * timepoint) Deque.t
    ; ts_tp_out: (timestamp * timepoint) Deque.t

    (* sorted deque of S^+ beta [alphas] *)
    ; beta_alphas: (timestamp * expl) Deque.t
    (* deque of S^+ beta [alphas] outside of the interval *)
    ; beta_alphas_out: (timestamp * expl) Deque.t

    (* sorted deque of S^- alpha [betas] *)
    ; alpha_betas: (timestamp * expl) Deque.t
    (* sorted deque of alpha proofs *)
    ; alphas_out: (timestamp * expl) Deque.t
    (* list of beta violations inside the interval *)
    ; betas_suffix_in: (timestamp * vexpl) Deque.t
    (* list of alpha/beta violations *)
    ; alphas_betas_out: (timestamp * vexpl option * vexpl option) Deque.t
    ; }

  let print_ts_lists { ts_zero; ts_tp_in; ts_tp_out } =
    Printf.fprintf stdout "%s" (
    (match ts_zero with
     | None -> ""
     | Some(ts) -> Printf.sprintf "\n\tts_zero = (%d)\n" ts) ^
    Deque.fold ts_tp_in ~init:"\n\tts_in = ["
      ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n") ^
    Deque.fold ts_tp_out ~init:"\n\tts_out = ["
      ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%d, %d);" ts tp)) ^
      (Printf.sprintf "]\n"))

  let msaux_to_string { ts_zero
                      ; ts_tp_in
                      ; ts_tp_out
                      ; beta_alphas
                      ; beta_alphas_out
                      ; alpha_betas
                      ; alphas_out
                      ; betas_suffix_in
                      ; alphas_betas_out } =
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
      Deque.fold beta_alphas ~init:"\nbeta_alphas = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps) ^
      Deque.fold beta_alphas_out ~init:"\nbeta_alphas_out = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps) ^
      Deque.fold alpha_betas ~init:"\nalpha_betas = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps) ^
      Deque.fold alphas_out ~init:"\nalphas_out = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps) ^
      Deque.fold betas_suffix_in ~init:"\nbetas_suffix_in = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.v_to_string "" ps) ^
      Deque.fold alphas_betas_out ~init:"\nalphas_betas_out = "
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

  let update_ts (l, r) a ts tp msaux =
    if a = 0 then
      let _ = Deque.enqueue_back msaux.ts_tp_in (ts, tp) in
      let _ = List.iter (Deque.to_list msaux.ts_tp_in)
                ~f:(fun (ts', _) -> if ts' < l then Deque.drop_front msaux.ts_tp_in) in
      msaux
    else
      let _ = Deque.enqueue_back msaux.ts_tp_out (ts, tp) in
      let _ = List.iter (Deque.to_list msaux.ts_tp_out)
                ~f:(fun (ts', tp') -> if ts' <= r then
                                        let _ = Deque.enqueue_back msaux.ts_tp_in (ts', tp') in
                                        Deque.drop_front msaux.ts_tp_out) in
      let _ = List.iter (Deque.to_list msaux.ts_tp_in)
                ~f:(fun (ts', _) -> if ts' < l then Deque.drop_front msaux.ts_tp_in) in
      msaux

  (* Resulting list is in ascending order, e.g.,
   d = [(1, p_1), (2, p_2), ..., (n, p_n)]
   results in [(n, p_n), ...]  *)
  let split_in_out (l, r) d =
    let l = List.fold (Deque.to_list d) ~init:[]
              ~f:(fun acc (ts, p) ->
                if ts <= r then (
                  let _ = Deque.drop_front d in
                  if ts >= l then (ts, p)::acc
                  else acc)
                else acc)
    in (d, l)

  let split_in_out2 (l, r) d =
    let l = List.rev (List.fold (Deque.to_list d) ~init:[]
                        ~f:(fun acc (ts, vp1_opt, vp2_opt) ->
                          if ts <= r then (
                            let _ = Deque.drop_front d in
                            if ts >= l then (ts, vp1_opt, vp2_opt)::acc
                            else acc)
                          else acc))
    in (d, l)

  let remove_out_less l d =
    let _ = List.iter (Deque.to_list d)
              ~f:(fun (ts, _) -> if ts < l then Deque.drop_front d)
    in d

  let remove_out_leq r d =
    let _ = List.iter (Deque.to_list d)
              ~f:(fun (ts, _) -> if ts <= r then Deque.drop_front d)
    in d

  let remove_out_less2 l d =
    let _ = List.iter (Deque.to_list d)
              ~f:(fun (ts, _, _) -> if ts < l then Deque.drop_front d)
    in d

  let add_alphas_out ts vvp1 alphas_out le =
    let _ = List.iter (List.rev(Deque.to_list alphas_out))
              ~f:(fun (_, vvp) ->
                if le vvp1 vvp then Deque.drop_back alphas_out) in
    let _ = Deque.enqueue_back alphas_out (ts, vvp1)
    in alphas_out

  let update_beta_alphas new_in beta_alphas le =
    if (List.is_empty new_in) then
      beta_alphas
    else (
      let _ = Printf.printf "\nnew_in = \n" in
      let _ = List.iter new_in ~f:(fun (ts, ps) ->
                  Printf.printf "\n(%d)\n%s\n" ts (Expl.expl_to_string ps)) in
      let new_in' = List.rev(sort_ps le new_in) in
      let _ = Printf.printf "\nnew_in' = \n" in
      let _ = List.iter new_in ~f:(fun (ts, ps) ->
                  Printf.printf "\n(%d)\n%s\n" ts (Expl.expl_to_string ps)) in
      let hd_p = List.hd_exn new_in' in
      let _ = Deque.iter beta_alphas ~f:(fun (ts, sp) ->
                  if le (snd(hd_p)) sp then
                    Deque.drop_back beta_alphas) in
      let _ = List.iter new_in' ~f:(fun (ts, sp) ->
                  Deque.enqueue_back beta_alphas (ts, sp))
      in beta_alphas)

  let update_betas_suffix_in new_in betas_suffix_in =
    if (List.is_empty new_in) then
      betas_suffix_in
    else (
      if List.exists new_in
           (fun (_, _, vp2_opt) ->
             Option.is_none vp2_opt)
      then (
        let _ = Deque.clear betas_suffix_in in
        let new_in' = List.rev (List.take_while (List.rev new_in)
                                  ~f:(fun (_, _, vp2_opt) ->
                                    Option.is_some vp2_opt)) in
        let _ = List.iter new_in'
                  ~f:(fun (ts, _, vp2_opt) ->
                    match vp2_opt with
                    | None -> ()
                    | Some (vp2) -> Deque.enqueue_back betas_suffix_in (ts, vp2))
        in betas_suffix_in)
      else (
        let _ = List.iter new_in
                  ~f:(fun (ts, _, vp2_opt) ->
                    match vp2_opt with
                    | None -> ()
                    | Some(vp2) -> Deque.enqueue_back betas_suffix_in (ts, vp2))
        in betas_suffix_in))

  let construct_vsinceps tp new_in =
    List.rev(List.fold new_in ~init:[]
               ~f:(fun acc (ts, vp1_opt, vp2_opt) ->
                 match vp1_opt with
                 | None ->
                    let vp2 = Option.get vp2_opt in
                    List.map ~f:(fun (ts, vvp) ->
                        match vvp with
                        | V vp -> (ts, V (vappend vp vp2))
                        | S _ -> raise VEXPL) acc
                 | Some(vp1) ->
                    let vp2 = Option.get vp2_opt in
                    let new_acc =
                      List.map ~f:(fun (ts, vvp) ->
                          match vvp with
                          | V vp -> (ts, V (vappend vp vp2))
                          | S _ -> raise VEXPL) acc in
                    let vp = V (VSince (tp, vp1, [vp2])) in
                    (ts, vp)::new_acc))

  let add_new_ps_alpha_betas tp new_in alpha_betas le =
    let new_vps_in = construct_vsinceps tp new_in in
    let vps = sort_ps le (List.rev((Deque.to_list alpha_betas) @ new_vps_in)) in
    let _ = Deque.clear alpha_betas in
    let _ = List.iter vps ~f:(fun (ts, vp) ->
                Deque.enqueue_back alpha_betas (ts, vp))
    in alpha_betas

  let update_alpha_betas_tps tp alpha_betas =
    let alpha_betas_updated = Deque.create () in
    let _ = Deque.iter alpha_betas
              ~f:(fun (ts, vvp) ->
                match vvp with
                | V vp -> (match vp with
                           | VSince (tp', vp1, vp2s) ->
                              Deque.enqueue_back alpha_betas_updated (ts, V (VSince (tp, vp1, vp2s)))
                           | _ -> raise INVALID_EXPL)
                | S _ -> raise VEXPL)
    in alpha_betas_updated

  let update_alpha_betas tp new_in alpha_betas le =
    if (List.is_empty new_in) then
      (update_alpha_betas_tps tp alpha_betas)
    else (
      if List.exists new_in
           ~f:(fun (_, _, vp2_opt) ->
             Option.is_none vp2_opt)
      then
        let _ = Deque.clear alpha_betas in
        let new_in_vbeta_seq = List.rev (List.take_while (List.rev new_in)
                                           ~f:(fun (_, _, vp2_opt) ->
                                             Option.is_some vp2_opt)) in
        let alpha_betas' = add_new_ps_alpha_betas tp new_in_vbeta_seq alpha_betas le in
        (update_alpha_betas_tps tp alpha_betas')
      else (
        let alpha_betas_vapp = List.fold new_in ~init:alpha_betas
                                 ~f:(fun d (_, _, vp2_opt) ->
                                   match vp2_opt with
                                   | None -> raise UNEXPECTED_BEHAVIOR
                                   | Some(vp2) -> vappend_to_deque vp2 d) in
        let alpha_betas' = add_new_ps_alpha_betas tp new_in alpha_betas_vapp le in
        (update_alpha_betas_tps tp alpha_betas')))

  let etp ts_tp_in ts_tp_out tp =
    let lst = (Deque.to_list ts_tp_in) @ (Deque.to_list ts_tp_out) in
    match List.hd(lst) with
    | None -> tp
    | Some (_, tp') -> tp'

  let optimal_proof tp msaux =
    if not (Deque.is_empty msaux.beta_alphas) then
      [snd(Deque.peek_front_exn msaux.beta_alphas)]
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
      let p3_l = if (Deque.length msaux.betas_suffix_in) = (Deque.length msaux.ts_tp_in) then
                   let etp = match Deque.is_empty msaux.betas_suffix_in with
                     | true -> etp msaux.ts_tp_in msaux.ts_tp_out tp
                     | false -> v_at (snd(Deque.peek_front_exn msaux.betas_suffix_in)) in
                   let betas_suffix = betas_suffix_in_to_list msaux.betas_suffix_in in
                   [V (VSinceInf (tp, etp, betas_suffix))]
                 else [] in
      (p1_l @ p2_l @ p3_l)

  let add_to_msaux ts p1 p2 msaux le =
    match p1, p2 with
    | S sp1, S sp2 ->
       let beta_alphas = sappend_to_deque sp1 msaux.beta_alphas in
       let beta_alphas_out = sappend_to_deque sp1 msaux.beta_alphas_out in
       let sp = S (SSince (sp2, [])) in
       let _ = Deque.enqueue_back beta_alphas_out (ts, sp) in
       let _ = Deque.enqueue_back msaux.alphas_betas_out (ts, None, None) in
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

  let remove_from_msaux (l, r) msaux =
    let beta_alphas = remove_out_less l msaux.beta_alphas in
    let beta_alphas_out = remove_out_less l msaux.beta_alphas_out in
    let alpha_betas = remove_out_less l msaux.alpha_betas in
    let alphas_out = remove_out_leq r msaux.alphas_out in
    let betas_suffix_in = remove_out_less l msaux.betas_suffix_in in
    let alphas_betas_out = remove_out_less2 l msaux.alphas_betas_out in
    { msaux with
      beta_alphas = beta_alphas
    ; beta_alphas_out = beta_alphas_out
    ; alpha_betas = alpha_betas
    ; alphas_out = alphas_out
    ; betas_suffix_in = betas_suffix_in
    ; alphas_betas_out = alphas_betas_out }

  let advance_msaux (l, r) tp ts p1 p2 msaux le =
    let msaux_plus_new = add_to_msaux ts p1 p2 msaux le in
    let msaux_minus_old = remove_from_msaux (l, r) msaux_plus_new in
    let beta_alphas_out, new_in_sat = split_in_out (l, r) msaux_minus_old.beta_alphas_out in
    let beta_alphas = update_beta_alphas new_in_sat msaux_minus_old.beta_alphas le in
    let alphas_betas_out, new_in_viol = split_in_out2 (l, r) msaux_minus_old.alphas_betas_out in
    let betas_suffix_in = update_betas_suffix_in new_in_viol msaux_minus_old.betas_suffix_in in
    let alpha_betas = update_alpha_betas tp new_in_viol msaux_minus_old.alpha_betas le in
    { msaux_minus_old with
      beta_alphas = beta_alphas
    ; beta_alphas_out = beta_alphas_out
    ; alpha_betas = alpha_betas
    ; betas_suffix_in = betas_suffix_in }

  let update_since interval tp ts p1 p2 msaux le =
    let a = get_a_I interval in
    (* Case 1: interval has not yet started, i.e.,
     \tau_{tp} < \tau_{0} + a OR \tau_{tp} - a < 0 *)
    if ((Option.is_none msaux.ts_zero) && (ts - a) < 0) ||
         (Option.is_some msaux.ts_zero) && ts < (Option.get msaux.ts_zero) + a then
      let l = (-1) in
      let r = (-1) in
      let msaux_ts_zero_updated = if Option.is_none msaux.ts_zero then
                                    { msaux with ts_zero = Some(ts) }
                                  else msaux in
      let msaux_ts_updated = update_ts (l, r) a ts tp msaux_ts_zero_updated in
      let msaux_updated = advance_msaux (l, r) tp ts p1 p2 msaux_ts_updated le in
      let p = V (VSinceOutL tp) in
      ([p], msaux_updated)
    (* Case 2: \tau_{tp-1} exists *)
    else
      let b = get_b_I interval in
      let l = if (Option.is_some b) then max 0 (ts - (Option.get b))
              else (Option.get msaux.ts_zero) in
      let r = ts - a in
      let msaux_ts_updated = update_ts (l, r) a ts tp msaux in
      let msaux_updated = advance_msaux (l, r) tp ts p1 p2 msaux_ts_updated le in
      (optimal_proof tp msaux_updated, msaux_updated)
end

module Future = struct
  type muaux = {
      ts_tp_in: (timestamp * timepoint) Deque.t
    ; ts_tp_out: (timestamp * timepoint) Deque.t
    (* deque of sorted deques of U^+ beta [alphas] proofs where (ets, lts, expl):
     * etc corresponds to the timestamp of the first alpha proof
     * lts corresponds to the timestamp of the beta proof *)
    ; alphas_beta: ((timestamp * timestamp * expl) Deque.t) Deque.t
    (* most recent sequence of alpha satisfactions w/o holes *)
    ; alphas_suffix: (timestamp * sexpl) Deque.t
    (* deque of sorted deques of U^- ~alpha [~betas] proofs where (ets, lts, expl):
     * ets corresponds to the timestamp of the first ~beta proof
     * lts corresponds to the timestamp of the ~alpha proof *)
    ; betas_alpha: ((timestamp * timestamp * expl) Deque.t) Deque.t
    (* deque of alpha proofs outside the interval *)
    ; alphas_out: (timestamp * expl) Deque.t
    (* deque of alpha violations inside the interval *)
    ; alphas_in: (timestamp * timepoint * vexpl option) Deque.t
    (* deque of beta violations inside the interval *)
    ; betas_suffix_in: (timestamp * vexpl) Deque.t
    ; optimal_proofs: (timestamp * expl) Deque.t
    ; }

  let muaux_to_string { ts_tp_in
                      ; ts_tp_out
                      ; alphas_beta
                      ; alphas_suffix
                      ; betas_alpha
                      ; alphas_out
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
            ~f:(fun acc2 (ts1, ts2, ps) ->
              acc2 ^ (Printf.sprintf "\n(%d, %d)\n" ts1 ts2) ^
              Expl.expl_to_string ps) ^ "\n]\n") ^
      Deque.fold alphas_suffix ~init:"\nalphas_suffix = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.s_to_string "" ps) ^
      Deque.foldi betas_alpha ~init:"\nbetas_alpha = \n"
        ~f:(fun i acc1 d ->
          acc1 ^ Printf.sprintf "\n%d.\n" i ^
          Deque.fold d ~init:"["
            ~f:(fun acc2 (ts1, ts2, ps) ->
              acc2 ^ (Printf.sprintf "\n(%d, %d)\n" ts1 ts2) ^
              Expl.expl_to_string ps) ^ "\n]\n") ^
      Deque.fold alphas_out ~init:"\nalphas_out = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps) ^
      Deque.fold alphas_in ~init:"\nalphas_in = "
        ~f:(fun acc (ts1, ts2, ps) ->
          match ps with
          | None -> acc
          | Some(ps') ->
             acc ^ (Printf.sprintf "\n(%d, %d)\n" ts1 ts2) ^ Expl.v_to_string "" ps') ^
      Deque.fold betas_suffix_in ~init:"\nbetas_suffix_in = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.v_to_string "" ps) ^
      Deque.fold optimal_proofs ~init:"\noptimal_proofs = "
        ~f:(fun acc (ts, ps) ->
          acc ^ (Printf.sprintf "\n(%d)\n" ts) ^ Expl.expl_to_string ps)

  let current_ts_tp ts_tp_out ts_tp_in =
    match Deque.peek_front ts_tp_out with
    | None -> (match Deque.peek_front ts_tp_in with
               | None -> None
               | Some (ts, tp) -> Some(tp))
    | Some (ts, tp) -> Some(tp)

  let shift_sdrop l alphas_beta =
    Deque.fold alphas_beta ~init:(Deque.create ())
      ~f:(fun acc (ets, lts, ssp) ->
        if lts < l then acc
        else (match ssp with
              | S sp -> (match sdrop sp with
                         | None -> acc
                         | Some (sp') -> let _ = Deque.enqueue_back acc (ets, lts, S sp') in acc)
              | V _ -> raise SEXPL))

  let shift_vdrop l betas_alpha =
    Deque.fold betas_alpha ~init:(Deque.create ())
      ~f:(fun acc (ets, lts, vvp) ->
        if lts < l then acc
        else (match vvp with
              | V vp -> (match vdrop vp with
                         | None -> acc
                         | Some (vp') -> let _ = Deque.enqueue_back acc (ets, lts, V vp') in acc)
              | S _ -> raise VEXPL))

  let add_ts l ts tp ts_tp_out ts_tp_in =
    let _ = Deque.enqueue_back  ts_tp_in (ts, tp) in
    let _ = Deque.iter ts_tp_in
              ~f:(fun (ts', tp') ->
                if ts' < l then
                  let _ = Deque.enqueue_back ts_tp_out (ts', tp') in
                  Deque.drop_front ts_tp_in)
    in (ts_tp_out, ts_tp_in)

  let remove_out_less_dd lim d =
    let _ = Deque.iter d ~f:(fun d' ->
                List.iter (Deque.to_list d') ~f:(fun (ts1, ts2, _) ->
                    if ts2 < lim then Deque.drop_front d'))
    in d

  let remove_out_less lim d =
    let _ = List.iter (Deque.to_list d)
              ~f:(fun (ts, _) -> if ts < lim then Deque.drop_front d)
    in d

  let remove_out_less2 lim d =
    let _ = List.iter (Deque.to_list d)
              ~f:(fun (ts, _, _) -> if ts < lim then Deque.drop_front d)
    in d

  let split_in_out (l, r) d =
    let l = List.fold (Deque.to_list d) ~init:[]
              ~f:(fun acc (ts, p) ->
                if ts >= l then (
                  let _ = Deque.drop_front d in
                  if ts <= r then (ts, p)::acc
                  else acc)
                else acc)
    in (d, l)

  let split_in_out2 z l d =
    let lst = List.fold (Deque.to_list d) ~init:[]
                ~f:(fun acc (ts, _, vp1_opt) ->
                  if ts < l then (
                    let _ = Deque.drop_front d in
                    if ts >= z then
                      (match vp1_opt with
                       | None -> acc
                       | Some(vp1) -> (ts, V vp1)::acc)
                       else acc)
                    else acc)
    in (d, lst)

  let add_alphas_out ts vvp1 alphas_out le =
    let _ = List.iter (Deque.to_list alphas_out)
              ~f:(fun (_, vvp) ->
                if le vvp1 vvp then Deque.drop_front alphas_out) in
    let _ = Deque.enqueue_front alphas_out (ts, vvp1)
    in alphas_out

  let update_alphas_out ts alphas_out new_out_alphas le =
    let new_out_alphas_sorted = List.rev(sort_ps le new_out_alphas) in
    List.fold_left (List.rev (new_out_alphas_sorted)) ~init:(Deque.create ())
      ~f:(fun acc (_, vvp1) -> add_alphas_out ts vvp1 alphas_out le)

  let alphas_suffix_to_list alphas_suffix =
    List.rev(List.fold_left (Deque.to_list alphas_suffix) ~init:[]
               ~f:(fun acc (_, sp1) -> sp1::acc))

  let betas_suffix_in_to_list betas_suffix_in =
    List.rev(List.fold_left (Deque.to_list betas_suffix_in) ~init:[]
               ~f:(fun acc (_, vp2) -> vp2::acc))

  let add_p1_p2 lts tp p1 p2 muaux le =
    match p1, p2 with
    | S sp1, S sp2 ->
       Printf.printf "SS\n";
       (* alphas_beta *)
       let cur_alphas_beta = Deque.peek_back_exn muaux.alphas_beta in
       let p1 = S (SUntil (sp2, (alphas_suffix_to_list muaux.alphas_suffix))) in
       let ets = match Deque.peek_front muaux.alphas_suffix with
         | Some(ts, _) -> ts
         | None -> lts in
       let _ = Deque.enqueue_back cur_alphas_beta (ets, lts, p1) in
       let cur_alphas_beta_sorted_list = sort_ps2 le (List.rev (Deque.to_list cur_alphas_beta)) in
       let _ = Deque.clear cur_alphas_beta in
       let _ = List.iter cur_alphas_beta_sorted_list ~f:(fun (e, l, p) ->
                   Deque.enqueue_back cur_alphas_beta (e, l, p)) in
       let _ = Deque.drop_back muaux.alphas_beta in
       let _ = Deque.enqueue_back muaux.alphas_beta cur_alphas_beta in
       (* alphas_suffix *)
       let _ = Deque.enqueue_back muaux.alphas_suffix (lts, sp1) in
       (* alphas_in *)
       let _ = Deque.enqueue_back muaux.alphas_in (lts, tp, None) in
       (* betas_suffix_in *)
       let _ = Deque.clear muaux.betas_suffix_in in
       muaux
    | S sp1, V vp2 ->
       Printf.printf "SV\n";
       (* betas_alpha (add empty deque) *)
       let _ = if not (Deque.is_empty (Deque.peek_back_exn muaux.betas_alpha)) then
                 Deque.enqueue_back muaux.betas_alpha (Deque.create ()) in
       (* alphas_suffix *)
       let _ = Deque.enqueue_back muaux.alphas_suffix (lts, sp1) in
       (* alphas_in *)
       let _ = Deque.enqueue_back muaux.alphas_in (lts, tp, None) in
       (* betas_suffix_in *)
       let _ = Deque.enqueue_back muaux.betas_suffix_in (lts, vp2) in
       muaux
    | V vp1, S sp2 ->
       Printf.printf "VS\n";
       (* alphas_beta *)
       let cur_alphas_beta = if not (Deque.is_empty (Deque.peek_back_exn muaux.alphas_beta))
                             then Deque.create ()
                             else Deque.peek_back_exn muaux.alphas_beta in
       let p1 = S (SUntil (sp2, (alphas_suffix_to_list muaux.alphas_suffix))) in
       let ets = match Deque.peek_front muaux.alphas_suffix with
         | Some(ts, _) -> ts
         | None -> lts in
       let _ = Deque.enqueue_back cur_alphas_beta (ets, lts, p1) in
       let cur_alphas_beta_sorted_list = sort_ps2 le (List.rev (Deque.to_list cur_alphas_beta)) in
       let _ = Deque.clear cur_alphas_beta in
       let _ = List.iter cur_alphas_beta_sorted_list ~f:(fun (e, l, p) ->
                   Deque.enqueue_back cur_alphas_beta (e, l, p)) in
       let _ = if not (Deque.is_empty (Deque.peek_back_exn muaux.alphas_beta)) then
                 Deque.drop_back muaux.alphas_beta in
       let _ = Deque.enqueue_back muaux.alphas_beta cur_alphas_beta in
       (* append empty deque *)
       let _ = if not (Deque.is_empty (Deque.peek_back_exn muaux.alphas_beta)) then
                 Deque.enqueue_back muaux.alphas_beta (Deque.create ()) in
       (* alphas_suffix *)
       let _ = Deque.clear muaux.alphas_suffix in
       (* alphas_in *)
       let _ = Deque.enqueue_back muaux.alphas_in (lts, tp, Some(vp1)) in
       (* betas_suffix_in *)
       let _ = Deque.clear muaux.betas_suffix_in in
       muaux
    | V vp1, V vp2 ->
       Printf.printf "VV\n";
       (* alphas_suffix *)
       let _ = Deque.clear muaux.alphas_suffix in
       (* betas_suffix_in *)
       let _ = Deque.enqueue_back muaux.betas_suffix_in (lts, vp2) in
       (* betas_alpha *)
       let cur_betas_alpha = if not (Deque.is_empty (Deque.peek_back_exn muaux.betas_alpha))
                             then Deque.create ()
                             else Deque.peek_back_exn muaux.betas_alpha in
       let vp = V (VUntil (tp, vp1, (betas_suffix_in_to_list muaux.betas_suffix_in))) in
       let ets = match Deque.peek_front muaux.betas_suffix_in with
         | Some(ts, _) -> ts
         | None -> lts in
       let _ = Deque.enqueue_back cur_betas_alpha (ets, lts, vp) in
       let cur_betas_alpha_sorted_list = sort_ps2 le (List.rev (Deque.to_list cur_betas_alpha)) in
       let _ = Deque.clear cur_betas_alpha in
       let _ = List.iter cur_betas_alpha_sorted_list ~f:(fun (e, l, p) ->
                   Deque.enqueue_back cur_betas_alpha (e, l, p)) in
       let _ = Printf.printf "|muaux.betas_alpha| = %d\n" (Deque.length muaux.betas_alpha) in
       let _ = if not (Deque.is_empty (Deque.peek_back_exn muaux.betas_alpha)) then
                 Deque.drop_back muaux.betas_alpha in
       let _ = Deque.enqueue_back muaux.betas_alpha cur_betas_alpha in
       let _ = Printf.printf "|muaux.betas_alpha| = %d\n" (Deque.length muaux.betas_alpha) in
       (* alphas_in *)
       let _ = Deque.enqueue_back muaux.alphas_in (lts, tp, Some(vp1)) in
       muaux

  let remove_from_muaux z l muaux =
    let alphas_suffix = remove_out_less z muaux.alphas_suffix in
    let alphas_out = remove_out_less z muaux.alphas_out in
    let betas_suffix_in = remove_out_less l muaux.betas_suffix_in in
    { muaux with
      alphas_suffix = alphas_suffix
    ; alphas_out = alphas_out
    ; betas_suffix_in = betas_suffix_in }

  let drop_alphas_beta f_drop alphas_beta =
    let _ = (match Deque.peek_front alphas_beta with
             | None -> failwith "muaux.alphas_beta must never be empty"
             | Some(front_alphas_beta) -> if not (Deque.is_empty front_alphas_beta) then
                                            let _ = Deque.drop_front alphas_beta in
                                            let front_alphas_beta' = f_drop front_alphas_beta in
                                            if not (Deque.is_empty front_alphas_beta') then
                                              Deque.enqueue_front alphas_beta front_alphas_beta'
                                            else (if Deque.is_empty alphas_beta then
                                                    Deque.enqueue_front alphas_beta front_alphas_beta')) in
    alphas_beta

  let drop_betas_alpha f_drop betas_alpha =
    let _ = (match Deque.peek_front betas_alpha with
             | None -> failwith "muaux.betas_alpha must never be empty"
             | Some(front_betas_alpha) -> if not (Deque.is_empty front_betas_alpha) then
                                            let _ = Deque.drop_front betas_alpha in
                                            let front_betas_alpha' = f_drop front_betas_alpha in
                                            if not (Deque.is_empty front_betas_alpha') then
                                              Deque.enqueue_front betas_alpha front_betas_alpha'
                                            else (if Deque.is_empty betas_alpha then
                                                    Deque.enqueue_front betas_alpha front_betas_alpha')) in
    betas_alpha

  let drop_muaux l muaux =
    let alphas_beta = drop_alphas_beta (shift_sdrop l) muaux.alphas_beta in
    let betas_alpha = drop_betas_alpha (shift_vdrop l) muaux.betas_alpha in
    { muaux with
      alphas_beta
    ; betas_alpha }

  let ready_tss_tps ts_tp_out ts_tp_in nts b =
    let d = Deque.create () in
    let _ = Deque.iter ts_tp_out ~f:(fun (ts, tp) ->
                if ts + b < nts then Deque.enqueue_back d (ts, tp)) in
    let _ = Deque.iter ts_tp_in ~f:(fun (ts, tp) ->
                if ts + b < nts then Deque.enqueue_back d (ts, tp)) in
    d

  let shift_muaux' l ts muaux le =
    let muaux_minus_old = remove_from_muaux ts l muaux in
    let muaux_dropped = drop_muaux l muaux_minus_old in
    let alphas_in, new_out_alphas = split_in_out2 ts l muaux.alphas_in in
    let alphas_out = update_alphas_out ts muaux.alphas_out new_out_alphas le in
    { muaux_dropped with
      alphas_in
    ; alphas_out }

  let shift_muaux l ts tp muaux le minimuml =
    let _ = Printf.printf "shift_muaux ts = %d; tp = %d\n" ts tp in
    (* U^+ (satisfaction) case *)
    let _ = if not (Deque.is_empty muaux.alphas_beta) then
              let cur_alphas_beta = Deque.peek_front_exn muaux.alphas_beta in
              if not (Deque.is_empty cur_alphas_beta) then
                (match Deque.peek_front_exn cur_alphas_beta with
                 | (_, _, S sp) -> Deque.enqueue_back muaux.optimal_proofs (ts, S sp)
                 | _ -> raise VEXPL)
              (* U^-/U_{\infty}^- (violation) cases *)
              else (let p1_l = if not (Deque.is_empty muaux.betas_alpha) then
                                 let cur_betas_alpha = Deque.peek_front_exn muaux.betas_alpha in
                                 (if not (Deque.is_empty cur_betas_alpha) then
                                    match Deque.peek_front_exn cur_betas_alpha with
                                    | (_, _, V VUntil(_, vp1, vp2s)) -> [V (VUntil(tp, vp1, vp2s))]
                                    | _ -> raise INVALID_EXPL
                                  else [])
                               else [] in
                    let p2_l = if not (Deque.is_empty muaux.alphas_out) then
                                 let vvp1 = snd(Deque.peek_front_exn muaux.alphas_out) in
                                 match vvp1 with
                                 | V vp1 -> let _ = Deque.drop_front muaux.alphas_out in
                                            [V (VUntil (tp, vp1, []))]
                                 | S _ -> raise VEXPL
                               else [] in
                    let p3_l = if (Deque.length muaux.betas_suffix_in) = (Deque.length muaux.ts_tp_in) then
                                 let ltp = v_at (snd(Deque.peek_back_exn muaux.betas_suffix_in)) in
                                 let betas_suffix = betas_suffix_in_to_list muaux.betas_suffix_in in
                                 [V (VUntilInf (tp, ltp, betas_suffix))]
                               else [] in
                    Deque.enqueue_back muaux.optimal_proofs (ts, minimuml (p1_l @ p2_l @ p3_l))) in
    let muaux' = shift_muaux' l ts muaux le in
    muaux'

  let update_until interval ts tp p1 p2 muaux le minimuml =
    let a = get_a_I interval in
    let b = match get_b_I interval with
      | None -> failwith "Unbounded interval for future operators is not supported"
      | Some(b') -> b' in
    (* let z = max 0 (ts - b) in *)
    let l = max 0 (ts - (b - a)) in
    (* Printf.fprintf stdout "z = %d; l = %d; r = %d\n" z l ts; *)
    let tss_tps = ready_tss_tps muaux.ts_tp_out muaux.ts_tp_in ts b in
    let muaux_shifted = Deque.fold tss_tps ~init:muaux
                          ~f:(fun muaux (ts', tp') -> shift_muaux l ts' tp' muaux le minimuml) in
    let (ts_tp_out, ts_tp_in) = add_ts l ts tp muaux_shifted.ts_tp_out muaux_shifted.ts_tp_in in
    let muaux_plus_ts_tp = { muaux_shifted with ts_tp_out = ts_tp_out; ts_tp_in = ts_tp_in } in
    let muaux_plus_p1_p2 = add_p1_p2 ts tp p1 p2 muaux_plus_ts_tp le
    in muaux_plus_p1_p2

  let rec eval_until d interval nts muaux =
    (* let _ = Printf.printf "eval tp = %d; ts = %d; nts = %d\n" tp ts nts in *)
    let b = match get_b_I interval with
      | None -> failwith "Unbounded interval for future operators is not supported"
      | Some(b') -> b' in
    match Deque.peek_front muaux.optimal_proofs with
    | None -> (d, muaux)
    | Some(ts, _) -> if ts + b < nts then
                        (* let _ = Printf.printf "should output something\n" in *)
                       let (_, op) = Deque.dequeue_front_exn muaux.optimal_proofs in
                       let (ops, muaux) = eval_until d interval nts muaux in
                       let _ = Deque.enqueue_back ops op in
                       (ops, muaux)
                     else (d, muaux)
end

(* mbuf2: auxiliary data structure for binary operators *)
type mbuf2 = expl Deque.t * expl Deque.t

let mbuf2_add p1s p2s (d1, d2) =
  let _ = Deque.iter p1s ~f:(fun p1 -> Deque.enqueue_front d1 p1) in
  let _ = Deque.iter p2s ~f:(fun p2 -> Deque.enqueue_front d2 p2) in
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

let rec mbuf2t_take f z (p1s, p2s) tss_tps =
  match (Deque.is_empty p1s, Deque.is_empty p2s, Deque.is_empty tss_tps) with
  | true, _, _ -> (z, (p1s, p2s), tss_tps)
  | _, true, _ -> (z, (p1s, p2s), tss_tps)
  | _, _, true -> (z, (p1s, p2s), tss_tps)
  | false, false, false -> let p1 = Deque.dequeue_front_exn p1s in
                           let p2 = Deque.dequeue_front_exn p2s in
                           let (ts, tp) = Deque.dequeue_front_exn tss_tps in
                           mbuf2t_take f (f p1 p2 ts tp z) (p1s, p2s) tss_tps

type mformula =
  | MTT
  | MFF
  | MP of string
  | MNeg of mformula
  | MConj of mformula * mformula * mbuf2
  | MDisj of mformula * mformula * mbuf2
  | MPrev of interval * mformula * bool * expl list * timestamp list
  | MNext of interval * mformula * bool * timestamp list
  | MSince of interval * mformula * mformula * mbuf2 * (timestamp * timepoint) Deque.t * Past.msaux
  | MUntil of interval * mformula * mformula * mbuf2 * (timestamp * timepoint) Deque.t * Future.muaux

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
    | MSince (i, f, g, _, _, _) -> aux f @ aux g
    | MUntil (i, f, g, _, _, _) -> aux f @ aux g in
  let lst_with_dup = aux mf in
  List.fold_left lst_with_dup ~init:[] ~f:(fun acc s ->
      if (List.mem acc s ~equal:(fun x y -> x = y)) then acc
      else s::acc)

let filter_ap sap mf_ap =
  Util.SS.filter (fun s -> List.mem mf_ap s ~equal:(fun x y -> x = y)) sap

type context =
  { tp: timepoint
  ; mf: mformula
  ; events: (Util.SS.t * timestamp) list
  }

let print_ps_list l =
  List.iter l ~f:(fun (ts, p) -> Printf.fprintf stdout "%s\n" (expl_to_string p))

(* Convert formula into a formula state *)
let rec minit f =
  match (value f) with
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
  | Prev (i, f) -> MPrev (i, minit f, true, [], [])
  | Next (i, f) -> MNext (i, minit f, true, [])
  | Since (i, f, g) ->
     let buf = (Deque.create (), Deque.create ()) in
     let msaux = { Past.ts_zero = None
                 ; ts_tp_in = Deque.create ()
                 ; ts_tp_out = Deque.create ()
                 ; beta_alphas = Deque.create ()
                 ; beta_alphas_out = Deque.create ()
                 ; alpha_betas = Deque.create ()
                 ; alphas_out = Deque.create ()
                 ; betas_suffix_in = Deque.create ()
                 ; alphas_betas_out = Deque.create ()
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
     let muaux = { Future.ts_tp_in = Deque.create ()
                 ; ts_tp_out = Deque.create ()
                 ; alphas_beta = alphas_beta
                 ; alphas_suffix = Deque.create ()
                 ; betas_alpha = betas_alpha
                 ; alphas_out = Deque.create ()
                 ; alphas_in = Deque.create ()
                 ; betas_suffix_in = Deque.create ()
                 ; optimal_proofs = Deque.create ()
                 } in
     MUntil (i, minit f, minit g, buf, Deque.create (), muaux)
  | _ -> failwith "This formula cannot be monitored"

let do_disj minimum2 expl_f1 expl_f2 =
  match expl_f1, expl_f2 with
  | S f1, S f2 -> minimum2 (S (SDisjL (f1))) (S (SDisjR(f2)))
  | S f1, V _ -> S (SDisjL (f1))
  | V _ , S f2 -> S (SDisjR (f2))
  | V f1, V f2 -> V (VDisj (f1, f2))

let do_conj minimum2 expl_f1 expl_f2 =
  match expl_f1, expl_f2 with
  | S f1, S f2 -> S (SConj (f1, f2))
  | S _ , V f2 -> V (VConjR (f2))
  | V f1, S _ -> V (VConjL (f1))
  | V f1, V f2 -> minimum2 (V (VConjL (f1))) (V (VConjR (f2)))

let meval' tp ts sap mform le minimuml =
  let minimum2 a b = minimuml [a; b] in
  (* TODO: This function should return (Deque.t, mformula) *)
  let rec meval tp ts sap mform =
    match mform with
    | MTT -> let d = Deque.create () in
             let _ = Deque.enqueue_back d (S (STT tp)) in
             (d, MTT)
    | MFF -> let d = Deque.create () in
             let _ = Deque.enqueue_back d (V (VFF tp)) in
             (d, MFF)
    | MP a ->
       let d = Deque.create () in
       let _ = if Util.SS.mem a sap then Deque.enqueue_back d (S (SAtom (tp, a)))
               else Deque.enqueue_back d (V (VAtom (tp, a))) in
       (d, MP a)
    | MNeg (mf) ->
       let (ps, mf') = meval tp ts sap mf in
       let ps' = Deque.fold ps ~init:(Deque.create ())
                   ~f:(fun d p ->
                     match p with
                     | S p' -> let _ = Deque.enqueue_back d (V (VNeg p')) in d
                     | V p' -> let _ = Deque.enqueue_back d (S (SNeg p')) in d) in
       (ps', MNeg(mf'))
    | MConj (mf1, mf2, buf) ->
       let op p1 p2 = do_conj minimum2 p1 p2 in
       let (p1s, mf1') = meval tp ts sap mf1 in
       let (p2s, mf2') = meval tp ts sap mf2 in
       let (ps, buf') = mbuf2_take op (mbuf2_add p1s p2s buf) in
       (ps, MConj (mf1', mf2', buf'))
    | MDisj (mf1, mf2, buf) ->
       let op p1 p2 = do_disj minimum2 p1 p2 in
       let (p1s, mf1') = meval tp ts sap mf1 in
       let (p2s, mf2') = meval tp ts sap mf2 in
       let (ps, buf') = mbuf2_take op (mbuf2_add p1s p2s buf) in
       (ps, MDisj (mf1', mf2', buf'))
    (* | MPrev (interval, mf, b, expl_lst, ts_d_lst) ->
     * | MNext (interval, mf, b, ts_a_lst) -> *)
    | MSince (interval, mf1, mf2, buf, tss_tps, msaux) ->
       let (p1s, mf1') = meval tp ts sap mf1 in
       let (p2s, mf2') = meval tp ts sap mf2 in
       let _ = Deque.enqueue_back tss_tps (ts, tp) in
       let ((ps, msaux'), buf', tss_tps') =
         mbuf2t_take
           (fun p1 p2 ts tp (ps, aux) ->
             let (cps, aux) = Past.update_since interval tp ts p1 p2 msaux le in
             let op = minimuml cps in
             let _ = Deque.enqueue_back ps op in
             (ps, aux))
           (Deque.create (), msaux) (mbuf2_add p1s p2s buf) tss_tps in
       let _ = Printf.fprintf stdout "---------------\n" in
       let _ = Printf.printf "mf = %s\n" (mformula_to_string (MSince (interval, mf1, mf2, buf, tss_tps, msaux))) in
       let _ = Printf.fprintf stdout "%s\n\n" (Past.msaux_to_string msaux') in
       let _ = Printf.fprintf stdout "Optimal proof:\n%s\n\n" (Expl.expl_to_string (Deque.peek_front_exn ps)) in
       (ps, MSince (interval, mf1', mf2', buf', tss_tps', msaux'))
    | MUntil (interval, mf1, mf2, buf, tss_tps, muaux) ->
       let (p1s, mf1') = meval tp ts sap mf1 in
       let (p2s, mf2') = meval tp ts sap mf2 in
       let _ = Printf.printf "---------------\n" in
       (* let _ = Printf.printf "mf = %s\n" (mformula_to_string (MUntil (interval, mf1, mf2, buf, tss_tps, muaux))) in *)
       let _ = Deque.enqueue_back tss_tps (ts, tp) in
       let _ = Printf.fprintf stdout "---------------\n%s\n\n" (Future.muaux_to_string muaux) in
       let (muaux', buf', ntss_ntps) =
         mbuf2t_take
           (fun p1 p2 ts tp aux -> Future.update_until interval ts tp p1 p2 muaux le minimuml)
           muaux (mbuf2_add p1s p2s buf) tss_tps in
       (* let _ = Printf.fprintf stdout "%s\n\n" (Future.muaux_to_string muaux') in *)
       let nts = match Deque.peek_front ntss_ntps with
         | None -> ts
         | Some(nts', _) -> nts' in
       let (ps, muaux'') = Future.eval_until (Deque.create ()) interval nts muaux in
       (ps, MUntil (interval, mf1', mf2', buf', ntss_ntps, muaux''))
    | _ -> failwith "This formula cannot be monitored" in
  meval tp ts sap mform

let monitor in_ch out_ch mode debug check test le f =
  let minimuml ps = minsize_list (get_mins le ps) in
  let rec loop f x = loop f (f x) in
  let mf = minit f in
  let mf_ap = relevant_ap mf in
  let _ = preamble out_ch mode f in
  let ctx = { tp = 0
            ; mf = mf
            ; events = [] } in
  let s (ctx, in_ch) =
    let ((sap, ts), in_ch) = input_event in_ch out_ch in
    let sap_filtered = filter_ap sap mf_ap in
    let events_updated = (sap_filtered, ts)::ctx.events in
    let (ps, mf_updated) = meval' ctx.tp ts sap_filtered ctx.mf le minimuml in
    (* let _ = Printf.fprintf stdout "|ps| outside = %d\n" (List.length ps) in *)
    let checker_ps = if check || debug || test then Some (check_ps events_updated f (Deque.to_list ps)) else None in
    let _ = print_ps out_ch mode ts ctx.tp (Deque.to_list ps) checker_ps debug test in
    let ctx_updated = { tp = ctx.tp+1
                      ; mf = mf_updated
                      ; events = events_updated } in
    (ctx_updated, in_ch) in
  loop s (ctx, in_ch)
