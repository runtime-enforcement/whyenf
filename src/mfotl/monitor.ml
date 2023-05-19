(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Etc
open Expl
open Pred

let min_list = Proof.Size.minsize_list
let min_elt = Proof.Size.minsize

let s_append_fdeque sp1 d =
  Fdeque.iteri d ~f:(fun i (ts, ssp) ->
      match ssp with
      | Proof.S sp -> Fdeque.set_exn d i (ts, S (Proof.s_append sp sp1))
      | V _ -> raise (Invalid_argument "found V proof in S deque")); d

let v_append_fdeque vp2 d =
  Fdeque.iteri d ~f:(fun i (ts, vvp) ->
      match vvp with
      | Proof.V vp -> Fdeque.set_exn d i (ts, V (Proof.v_append vp vp2))
      | S _ -> raise (Invalid_argument "found S proof in V deque")); d

let fst_lst_fdeque d =
  Fdeque.fold' d ~init:[] ~f:(fun acc (ts, p) -> p :: acc) `back_to_front

let remove_cond_front f d =
  let rec remove_cond_front_rec f d = match Fdeque.dequeue_front d with
    | None -> d
    | Some(el') -> if (f el') then remove_cond_front_rec f d
                   else Fdeque.fenqueue_front d el' in
  remove_cond_front_rec f d

let remove_cond_front_ne f d =
  let rec remove_cond_front_ne_rec f d =
    if (Fdeque.length d) > 1 then
      (match Fdeque.dequeue_front d with
       | None -> d
       | Some(el') -> if (f el') then remove_cond_front_ne_rec f d
                      else Fdeque.fenqueue_front d el')
    else d in
  remove_cond_front_ne_rec f d

let remove_cond_back f d =
  let rec remove_cond_back_rec f d =
    match Fdeque.dequeue_back d with
    | None -> d
    | Some(el') -> if (f el') then remove_cond_back_rec f d
                   else Fdeque.fenqueue_back d el' in
  remove_cond_back_rec f d

let sorted_append new_in d cmp =
  Fdeque.iter new_in ~f:(fun (ts, p) ->
      let _ = remove_cond_back (fun (ts', p') -> cmp p p') d in
      let _ = Fdeque.enqueue_back d (ts, p) in ()); d

let sorted_enqueue (ts, p) d cmp =
  let _ = remove_cond_back (fun (_, p') -> cmp p p') d in
  let _ = Fdeque.enqueue_back d (ts, p) in d

(* TODO: split_in_out and split_out_in should be rewritten as a single function *)
(* split_in_out considers a closed interval [l, r] *)
let split_in_out get_ts (l, r) d =
  let new_in = Fdeque.create () in
  let rec split_in_out_rec d =
    match Fdeque.dequeue_front d with
    | None -> d
    | Some(el) -> let ts = get_ts el in
                  if ts <= r then
                    if ts >= l then
                      let _ = Fdeque.enqueue_back new_in el in split_in_out_rec d
                    else Fdeque.fenqueue_front d el
                  else d in
  (split_in_out_rec d, new_in)

(* split_out_in considers an interval of the form [z, l) *)
let split_out_in get_ts (z, l) d =
  let new_out = Fdeque.create () in
  let rec split_out_in_rec d =
    match Fdeque.dequeue_front d with
    | None -> d
    | Some(el) -> let ts = get_ts el in
                  if ts < l then
                    if ts >= z then
                      let _ = Fdeque.enqueue_back new_out el in split_out_in_rec d
                    else Fdeque.fenqueue_front d el
                  else d in
  (split_out_in_rec d, new_out)

let etp tstps_in tstps_out tp =
  match Fdeque.peek_front tstps_in with
  | None -> (match Fdeque.peek_front tstps_out with
             | None -> tp
             | Some (_, tp') -> tp')
  | Some (_, tp') -> tp'

let ready_tstps b nts tstps_out tstps_in =
  let d = Fdeque.create () in
  Fdeque.iter tstps_out ~f:(fun (ts, tp) ->
      if ts + b < nts then Fdeque.enqueue_back d (ts, tp));
  Fdeque.iter tstps_in ~f:(fun (ts, tp) ->
      if ts + b < nts then Fdeque.enqueue_back d (ts, tp)); d

let first_ts_tp tstps_out tstps_in =
  match Fdeque.peek_front tstps_out with
  | None -> (match Fdeque.peek_front tstps_in with
             | None -> None
             | Some(ts, tp) -> Some(ts, tp))
  | Some(ts, tp) -> Some(ts, tp)

let add_tstp_future a b nts ntp tstps_out tstps_in =
  (* (ts, tp) update is performed differently if the queues are not empty *)
  (if (not (Fdeque.is_empty tstps_out)) || (not (Fdeque.is_empty tstps_in)) then
     let first_ts = match first_ts_tp tstps_out tstps_in with
       | None -> raise (Failure "tstps deques are empty")
       | Some(ts', _) -> ts' in
     if nts < first_ts + a then Fdeque.enqueue_back tstps_out (nts, ntp)
     else Fdeque.enqueue_back tstps_in (nts, ntp)
   else
     (if (nts >= a && nts <= b) || (a == 0) then
        Fdeque.enqueue_back tstps_in (nts, ntp)
      else Fdeque.enqueue_back tstps_out (nts, ntp)));
  (tstps_out, tstps_in)

let shift_tstps_future a first_ts ntp tstps_out tstps_in =
  Fdeque.iter tstps_in ~f:(fun (ts', tp') ->
      if (ts' < first_ts + a) && (tp' < ntp) then
        Fdeque.enqueue_back tstps_out (ts', tp'));
  let _ = remove_cond_front (fun (ts', tp') -> (ts' < first_ts) && (tp' < ntp)) tstps_out in
  let _ = remove_cond_front (fun (ts', tp') -> (ts' < first_ts + a) && (tp' < ntp)) tstps_in in
  (tstps_out, tstps_in)

let shift_tstps_past (l, r) a ts tp tstps_in tstps_out =
  if a = 0 then
    (Fdeque.enqueue_back tstps_in (ts, tp);
     (remove_cond_front (fun (ts', _) -> ts' < l) tstps_in, tstps_out))
  else
    (Fdeque.enqueue_back tstps_out (ts, tp);
     Fdeque.iter tstps_out ~f:(fun (ts', tp') ->
         if ts' <= r then Fdeque.enqueue_back tstps_in (ts', tp'));
     let ts_tp_out = remove_cond_front (fun (ts', _) -> ts' <= r) tstps_out in
     let ts_tp_in = remove_cond_front (fun (ts', _) -> ts' < l) tstps_in in
     (ts_tp_in, ts_tp_out))

module Buf2 = struct

  type t = Expl.t list * Expl.t list

  let add xs ys (l1, l2) = (l1 @ xs, l2 @ ys)

  let rec take f = function
    | [], ys -> ([], ([], ys))
    | xs, [] -> ([], (xs, []))
    | x::xs, y::ys -> let (zs, buf2') = take f (xs, ys) in
                      ((f x y)::zs, buf2')

end

module Buft = struct

  type t = Expl.t list * (timepoint * timestamp) list

  let rec take f z = function
    | [], ys -> (z, [], ys)
    | xs, [] -> (z, xs, [])
    | x::xs, (a,b)::ys -> take f (f x a b z) (xs, ys)

end

module Buf2t = struct

  type t = Expl.t list * Expl.t list * (timepoint * timestamp) list

  let rec take f w = function
    | [], ys, zs -> (w, ([], ys, zs))
    | xs, [], zs -> (w, (xs, [], zs))
    | xs, ys, [] -> (w, (xs, ys, []))
    | x::xs, y::ys, (a,b)::zs -> take f (f x y a b w) (xs, ys, zs)

end


module Once = struct

  type t = unit

end

module Eventually = struct

  type t = unit

end


module Historically = struct

  type t = unit

end

module Always = struct

  type t = unit

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
                ; tstps_in = Fdeque.create ()
                ; tstps_out = Fdeque.create ()
                ; s_beta_alphas_in = Fdeque.create ()
                ; s_beta_alphas_out = Fdeque.create ()
                ; v_alpha_betas_in = Fdeque.create ()
                ; v_alphas_out = Fdeque.create ()
                ; v_betas_in = Fdeque.create ()
                ; v_alphas_betas_out = Fdeque.create () }

end

module Until = struct

  type t = unit

end


module MFormula = struct

  type t =
    | MTT
    | MFF
    | MPredicate    of string * Term.t list
    | MNeg          of t
    | MAnd          of t * t * Buf2.t
    | MOr           of t * t * Buf2.t
    | MImp          of t * t * Buf2.t
    | MIff          of t * t * Buf2.t
    | MExists       of string * t
    | MForall       of string * t
    | MPrev         of Interval.t * t * bool * Expl.t list * timestamp list
    | MNext         of Interval.t * t * bool * timestamp list
    | MOnce         of Interval.t * t * (timestamp * timepoint) list * Once.t
    | MEventually   of Interval.t * t * Buft.t * Eventually.t
    | MHistorically of Interval.t * t * (timestamp * timepoint) list * Historically.t
    | MAlways       of Interval.t * t * Buft.t * Always.t
    | MSince        of Interval.t * t * t * Buf2t.t * Since.t
    | MUntil        of Interval.t * t * t * Buf2t.t * Until.t

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
    | Formula.Prev (i, f) -> MPrev (i, init f, true, [], [])
    | Formula.Next (i, f) -> MNext (i, init f, true, [])
    | Formula.Once (i, f) -> MOnce (i, init f, [], ())
    | Formula.Eventually (i, f) -> MEventually (i, init f, ([], []), ())
    | Formula.Historically (i, f) -> MHistorically (i, init f, [], ())
    | Formula.Always (i, f) -> MAlways (i, init f, ([], []), ())
    | Formula.Since (i, f, g) -> MSince (i, init f, init g, ([], [], []), Since.init ())
    | Formula.Until (i, f, g) -> MUntil (i, init f, init g, ([], [], []), ())

  let rec to_string_rec l = function
    | MTT -> Printf.sprintf "⊤"
    | MFF -> Printf.sprintf "⊥"
    | MPredicate (r, trms) -> Printf.sprintf "%step(%step)" r (Term.list_to_string trms)
    | MNeg f -> Printf.sprintf "¬%a" (fun x -> to_string_rec 5) f
    | MAnd (f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a ∧ %a") (fun x -> to_string_rec 4) f (fun x -> to_string_rec 4) g
    | MOr (f, g, _) -> Printf.sprintf (Etc.paren l 3 "%a ∨ %a") (fun x -> to_string_rec 3) f (fun x -> to_string_rec 4) g
    | MImp (f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a → %a") (fun x -> to_string_rec 4) f (fun x -> to_string_rec 4) g
    | MIff (f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a ↔ %a") (fun x -> to_string_rec 4) f (fun x -> to_string_rec 4) g
    | MExists (x, f) -> Printf.sprintf (Etc.paren l 5 "∃%step. %a") x (fun x -> to_string_rec 5) f
    | MForall (x, f) -> Printf.sprintf (Etc.paren l 5 "∀%step. %a") x (fun x -> to_string_rec 5) f
    | MPrev (i, f, _, _, _) -> Printf.sprintf (Etc.paren l 5 "●%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
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
  | MTT -> ([Leaf (Proof.S (STT tp))], MTT)
  | MFF -> ([Leaf (V (VFF tp))], MFF)
  | MPredicate (r, trms) ->
     let db' = Set.filter db (fun evt -> String.equal r (fst(evt))) in
     let maps = Set.fold db' ~init:[] ~f:(fun acc evt -> match_terms trms (snd evt) (Map.empty (module Term)) :: acc) in
     let maps' = List.map (List.filter maps ~f:(fun map_opt -> match map_opt with
                                                               | None -> false
                                                               | Some(map) -> not (Map.is_empty map)))
                   ~f:(fun map_opt -> Option.value_exn map_opt) in
     let fv = Formula.fv (Predicate (r, trms)) in
     let fv_vars = List.filter vars ~f:(fun var -> List.mem fv var ~equal:Pred.Term.equal) in
     let expl = pdt_of tp r trms fv_vars maps' in
     ([expl], MPredicate (r, trms))
  | MNeg (mf) ->
     let (expls, mf') = meval vars ts tp db mf in
     let f_expls = List.map expls ~f:(fun expl -> (Expl.apply1 vars (fun p -> do_neg p) expl)) in
     (f_expls, MNeg(mf'))
  | MAnd (mf1, mf2, buf2) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (f_expls, buf2') =
       Buf2.take
         (fun expl1 expl2 -> Expl.apply2 vars (fun p1 p2 -> min_list (do_and p1 p2)) expl1 expl2)
         (Buf2.add expls1 expls2 buf2) in
     (f_expls, MAnd (mf1', mf2', buf2'))
  | MOr (mf1, mf2, buf2) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (f_expls, buf2') =
       Buf2.take
         (fun expl1 expl2 -> Expl.apply2 vars (fun p1 p2 -> min_list (do_or p1 p2)) expl1 expl2)
         (Buf2.add expls1 expls2 buf2) in
     (f_expls, MOr (mf1', mf2', buf2'))
  | MImp (mf1, mf2, buf2) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (f_expls, buf2') =
       Buf2.take
         (fun expl1 expl2 -> Expl.apply2 vars (fun p1 p2 -> min_list (do_imp p1 p2)) expl1 expl2)
         (Buf2.add expls1 expls2 buf2) in
     (f_expls, MImp (mf1', mf2', buf2'))
  | MIff (mf1, mf2, buf2) ->
     let (expls1, mf1') = meval vars ts tp db mf1 in
     let (expls2, mf2') = meval vars ts tp db mf2 in
     let (f_expls, buf2') =
       Buf2.take
         (fun expl1 expl2 -> Expl.apply2 vars (fun p1 p2 -> do_iff p1 p2) expl1 expl2)
         (Buf2.add expls1 expls2 buf2) in
     (f_expls, MIff (mf1', mf2', buf2'))
  (* | MPrev (interval, mf, first, buf, tss) -> *)
  (*    let (ps, mf') = meval ts tp db mf in *)
  (*    let () = Deque.iter ps ~f:(fun p -> Deque.enqueue_back buf p) in *)
  (*    let () = Deque.enqueue_back tss ts in *)
  (*    let (ps', buf', tss') = Prev_Next.mprev_next Prev interval buf tss le in *)
  (*    (ts, (if first then (let () = Deque.enqueue_front ps' (V VPrev0) in ps') *)

  (*          else ps'), MPrev (interval, mf', false, buf', tss')) *)
  (* | MNext (interval, mf, first, tss) -> *)
  (*    let (_, ps, mf') = meval tp ts sap mf in *)
  (*    let () = Deque.enqueue_back tss ts in *)
  (*    let first = if first && (Deque.length ps) > 0 then (let () = Deque.drop_front ps in false) else first in *)
  (*    let (ps', _, tss') = Prev_Next.mprev_next Next interval ps tss le in *)
  (*    (ts, ps', MNext (interval, mf', first, tss')) *)
  (* | MOnce (interval, mf, ts_tps, moaux) -> *)
  (*    let (_, ps, mf') = meval tp ts sap mf in *)
  (*    let _ = Deque.enqueue_back ts_tps (ts, tp) in *)
  (*    let ((ps, moaux'), buf', ts_tps') = *)
  (*      mbuft_take *)
  (*          (fun p ts tp (ps, aux) -> *)
  (*            let (op, aux) = Once.update_once interval ts tp p aux le in *)
  (*            let () = Deque.enqueue_back ps op in *)
  (*            (ps, aux)) *)
  (*          (Deque.create (), moaux) ps ts_tps in *)
  (*      (ts, ps, MOnce (interval, mf', ts_tps', moaux')) *)
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
  (*   | MEventually (interval, mf, buf, nts_ntps, meaux) -> *)
  (*      let (_, ps, mf') = meval tp ts sap mf in *)
  (*      let () = Deque.enqueue_back nts_ntps (ts, tp) in *)
  (*      let () = Deque.iter ps ~f:(fun p -> Deque.enqueue_back buf p) in *)
  (*      let (meaux', buf', nts_ntps') = *)
  (*        mbuft_take *)
  (*          (fun p ts tp aux -> Eventually.update_eventually interval ts tp p le aux) *)
  (*          meaux buf nts_ntps in *)
  (*      let (nts, ntp) = match Deque.peek_front nts_ntps' with *)
  (*        | None -> (ts, tp) *)
  (*        | Some(nts', ntp') -> (nts', ntp') in *)
  (*      let (ts', ps, meaux'') = Eventually.eval_eventually (Deque.create ()) interval nts ntp le meaux' in *)
  (*      (ts', ps, MEventually (interval, mf', buf', nts_ntps', meaux'')) *)
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
           ; tstpdbs: (timestamp * timepoint * Db.t) Queue.t }

  let init mf = { mf = mf
                ; tp_out = -1
                ; ts_waiting = Queue.create ()
                ; tstpdbs = Queue.create () }

end

let tp = ref (-1)
let next_tp () = tp := !tp + 1; !tp

let mstep mode ts db (ms: MState.t) =
  let tp = next_tp () in
  let (expls, mf') = meval [] ts tp db ms.mf in
  let () = Queue.enqueue ms.ts_waiting ts in
  let tstps = List.zip_exn (List.range tp (tp + List.length expls)) (Queue.to_list ms.ts_waiting) in
  let tstpdbs = match mode with
    | Out.Plain.UNVERIFIED -> ms.tstpdbs
    | _ -> Queue.enqueue ms.tstpdbs (ts, tp, db); ms.tstpdbs in
  (List.zip_exn tstps expls,
   { ms with
     mf = mf'
   ; tp_out = ms.tp_out + (List.length expls)
   ; ts_waiting = queue_drop ms.ts_waiting (List.length expls)
   ; tstpdbs = tstpdbs })

let exec mode measure f inc =
  let rec step pb_opt ms =
    let (more, pb) = Other_parser.Trace.parse inc pb_opt in
    let (ts_tp_expls, ms') = mstep mode pb.ts pb.db ms in
    let () = Stdio.printf "%s\n" (Db.to_string pb.db) in
    Out.Plain.expls ts_tp_expls None mode;
    (match mode with
     | Out.Plain.UNVERIFIED -> ()
     | Out.Plain.VERIFIED -> ()
     | Out.Plain.DEBUG -> ());
    if more then step (Some(pb)) ms' in
  let mf = init f in
  let ms = MState.init mf in
  step None ms
