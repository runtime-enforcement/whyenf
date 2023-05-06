(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Import
open Pred
open Expl.Proof

module Buf2 = struct

  type t = Expl.Proof.t list * Expl.Proof.t list

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

  type t = unit

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
    | Formula.Since (i, f, g) -> MSince (i, init f, init g, ([], [], []), ())
    | Formula.Until (i, f, g) -> MSince (i, init f, init g, ([], [], []), ())

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
  | S sp -> V (VNeg sp)
  | V vp -> S (SNeg vp)

let do_and p1 p2 = match p1, p2 with
  | S sp1, S sp2 -> [S (SAnd (sp1, sp2))]
  | S _ , V vp2 -> [V (VAndR (vp2))]
  | V vp1, S _ -> [V (VAndL (vp1))]
  | V vp1, V vp2 -> [(V (VAndL (vp1))); (V (VAndR (vp2)))]

let do_or p1 p2 = match p1, p2 with
  | S sp1, S sp2 -> [(S (SOrL (sp1))); (S (SOrR(sp2)))]
  | S sp1, V _ -> [S (SOrL (sp1))]
  | V _ , S sp2 -> [S (SOrR (sp2))]
  | V vp1, V vp2 -> [V (VOr (vp1, vp2))]

let do_imp p1 p2 = match p1, p2 with
  | S _, S sp2 -> [S (SImpR sp2)]
  | S sp1, V vp2 -> [V (VImp (sp1, vp2))]
  | V vp1, S sp2 -> [S (SImpL vp1); S (SImpR sp2)]
  | V vp1, V _ -> [S (SImpL vp1)]

let do_iff p1 p2 = match p1, p2 with
  | S sp1, S sp2 -> S (SIffSS (sp1, sp2))
  | S sp1, V vp2 -> V (VIffSV (sp1, vp2))
  | V vp1, S sp2 -> V (VIffVS (vp1, sp2))
  | V vp1, V vp2 -> S (SIffVV (vp1, vp2))

let rec meval ts tp db = function
  | MTT -> ([S (STT tp)], MTT)
  | MFF -> ([V (VFF tp)], MFF)
  | MPredicate (r, trms) -> ([], MPredicate (r, trms))
  (* let d = Deque.create () in *)
  (* let _ = if SS.mem a sap then Deque.enqueue_back d (S (SAtom (tp, a))) *)
  (*         else Deque.enqueue_back d (V (VAtom (tp, a))) in *)
  (* (ts, d, MP a) *)
  | MNeg (mf) ->
     let (ps, mf') = meval ts tp db mf in
     let ps' = List.fold ps ~init:[] ~f:(fun acc p -> do_neg p :: acc) in
     (ps', MNeg(mf'))
  | MAnd (mf1, mf2, buf2) ->
     let (p1s, mf1') = meval ts tp db mf1 in
     let (p2s, mf2') = meval ts tp db mf2 in
     let (ps, buf2') = Buf2.take do_and (Buf2.add p1s p2s buf2) in
     (List.concat ps, MAnd (mf1', mf2', buf2'))
  | MOr (mf1, mf2, buf2) ->
     let (p1s, mf1') = meval ts tp db mf1 in
     let (p2s, mf2') = meval ts tp db mf2 in
     let (ps, buf2') = Buf2.take do_or (Buf2.add p1s p2s buf2) in
     (List.concat ps, MOr (mf1', mf2', buf2'))
  | MImp (mf1, mf2, buf2) ->
     let (p1s, mf1') = meval ts tp db mf1 in
     let (p2s, mf2') = meval ts tp db mf2 in
     let (ps, buf2') = Buf2.take do_imp (Buf2.add p1s p2s buf2) in
     (List.concat ps, MImp (mf1', mf2', buf2'))
  | MIff (mf1, mf2, buf2) ->
     let (p1s, mf1') = meval ts tp db mf1 in
     let (p2s, mf2') = meval ts tp db mf2 in
     let (ps, buf2') = Buf2.take do_iff (Buf2.add p1s p2s buf2) in
     (ps, MIff (mf1', mf2', buf2'))
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

type state =
  { tp: timepoint
  ; tss: timestamp list
  ; mf: MFormula.t
  ; events: (timestamp * Db.t) list }

let monitor_cli in_ch out_ch mode out_mode check le is_opt f =
  let mf = init f in
  let st = { tp = 0
           ; tss = []
           ; mf = mf
           ; events = [] } in
  (match out_mode with
   | PLAIN | DEBUG -> preamble_stdout out_ch mode f
   | JSON -> preamble_json out_ch f);
  let step (st, in_ch) =
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
  loop step (st, in_ch)

(* let monitor_vis obj_opt log le f = *)
(*   let events = parse_lines_from_string log in *)
(*   let (mf, st) = match obj_opt with *)
(*     | None -> let mf = init f in *)
(*               (mf, { tp = 0 *)
(*                    ; mf = mf *)
(*                    ; events = [] *)
(*                    ; tp_ts = Hashtbl.create 100 *)
(*               }) *)
(*     | Some (mf', st') -> (mf', st') in *)
(*   let mf_ap = relevant_ap mf in *)
(*   match events with *)
(*   | Ok es -> *)
(*      (let ((m, step), o) = List.fold_map es ~init:(mf, st) ~f:(fun (mf', st') (sap, ts) -> *)
(*                             let last_ts = match Hashtbl.find_opt st.tp_ts (st'.tp-1) with *)
(*                               | None -> ts *)
(*                               | Some(ts') -> ts' in *)
(*                             if last_ts <= ts then *)
(*                               (Hashtbl.add st.tp_ts st'.tp ts; *)
(*                                let sap_filtered = filter_ap sap mf_ap in *)
(*                                let (ts', ps, mf_updated) = meval' ts st'.tp sap_filtered mf' le in *)
(*                                let cbs_opt = None in *)
(*                                let expls = json_expls st.tp_ts f (Deque.to_list ps) cbs_opt in *)
(*                                let atoms = json_atoms f sap_filtered st'.tp ts in *)
(*                                let st_updated = { st with *)
(*                                                   tp = st'.tp+1 *)
(*                                                 ; mf = mf_updated } in *)
(*                                ((mf_updated, st_updated), (expls, atoms))) *)
(*                             else raise (INVALID_TIMESTAMP "Timestamp violates monotonicity constraint")) in *)
(*       let expls = List.map o (fun (e, _) -> e) in *)
(*       let expls' = String.concat ",\n" (List.filter expls (fun e -> not (String.equal e ""))) in *)
(*       let atoms = List.map o (fun (_, a) -> a) in *)
(*       let atoms' = String.concat ",\n" (List.filter atoms (fun a -> not (String.equal a ""))) in *)
(*       let ident = "    " in *)
(*       let json = (Printf.sprintf "{\n") ^ *)
(*                    (Printf.sprintf "%step\"expls\": [\n%step],\n" ident expls') ^ *)
(*                      (Printf.sprintf "%step\"atoms\": [\n%step]\n}" ident atoms') in *)
(*       (Some(m, step), json)) *)
(*   | Error err -> (None, json_error err) *)
