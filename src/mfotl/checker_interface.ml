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
open Formula
open Checker.MFOTL_Explanator2

module Deque = Core_kernel.Deque

type checker_proof = Inl of event_data sproof | Inr of event_data vproof
type checker_trace = (string set * nat) list
type trace_lst = (timestamp * (Db.Event.t, Db.Event.comparator_witness) Set.t) list

let int_of_nat n = Z.to_int (integer_of_nat n)
let nat_of_int i = nat_of_integer (Z.of_int i)
let enat_of_integer i = Enat (nat_of_integer i)

let convert_d (d: Domain.t) = match d with
  | Int v -> EInt (Z.of_int v)
  | Str v -> EString v
  | _ -> raise (Invalid_argument "type not yet supported")

let convert_term (t: Pred.Term.t) = match t with
  | Const c -> Const (convert_d c)
  | Var x -> Var x

let rec convert_part = function
  | Leaf pt -> (match pt with
                | Proof.S sp -> Inl (convert_sp sp)
                | V vp -> Inr (convert_vp vp))
  | Node (x, part) -> abs_part (convert_part)
and convert_sp (sp: Proof.sp) : (event_data sproof) = match sp with
  | STT tp -> STT (nat_of_int tp)
  | SPred (tp, s, trms) -> SPred (nat_of_int tp, s, List.map trms convert_term)
  | SNeg vp1 -> SNeg (convert_vp vp1)
  | SOrL sp1 -> SOrL (convert_sp sp1)
  | SOrR sp2 -> SOrR (convert_sp sp2)
  | SAnd (sp1, sp2) -> SAnd (convert_sp sp1, convert_sp sp2)
  | SImpL vp1 -> SImpL (convert_vp vp1)
  | SImpR sp2 -> SImpR (convert_sp sp2)
  | SIffSS (sp1, sp2) -> SIffSS (convert_sp sp1, convert_sp sp2)
  | SIffVV (vp1, vp2) -> SIffVV (convert_vp vp1, convert_vp vp2)
  | SExists (x, d, sp) -> SExists (Pred.Term.unvar x, convert_d d, convert_sp sp)
  | SForall (x, Abs_part part) -> SForall (Pred.Term.unvar x, convert_part part)
  | SPrev sp1 -> SPrev (convert_sp sp1)
  | SNext sp1 -> SNext (convert_sp sp1)
  | SOnce (tp, sp1) -> SOnce (nat_of_int tp, convert_sp sp1)
  | SHistorically (tp, etp, sp2s) ->
     let sp2s' = List.rev(Deque.fold sp2s ~init:[] ~f:(fun acc sp2 -> (convert_sp sp2)::acc)) in
     SHistorically (nat_of_int tp, nat_of_int etp, sp2s')
  | SHistoricallyOut tp -> SHistoricallyOut (nat_of_int tp)
  | SEventually (tp, sp1) -> SEventually (nat_of_int tp, convert_sp sp1)
  | SAlways (tp, ltp, sp2s) ->
     let sp2s' = List.rev(Deque.fold sp2s ~init:[] ~f:(fun acc sp2 -> (convert_sp sp2)::acc)) in
     SAlways (nat_of_int tp, nat_of_int ltp, sp2s')
  | SSince (sp2, sp1s) ->
     let sp1s' = List.rev(Deque.fold sp1s ~init:[] ~f:(fun acc sp1 -> (convert_sp sp1)::acc)) in
     SSince (convert_sp sp2, sp1s')
  | SUntil (sp2, sp1s) ->
     let sp1s' = List.rev(Deque.fold sp1s ~init:[] ~f:(fun acc sp1 -> (convert_sp sp1)::acc)) in
     SUntil (sp1s', convert_sp sp2)
and convert_vp (vp: Proof.vp) : (event_data vproof) = match vp with
  | VFF tp -> VFF (nat_of_int tp)
  | VPred (tp, s, trms) -> VPred (nat_of_int tp, s, List.map trms convert_term)
  | VNeg sp1 -> VNeg (convert_sp sp1)
  | VOr (vp1, vp2) -> VOr (convert_vp vp1, convert_vp vp2)
  | VAndL vp1 -> VAndL (convert_vp vp1)
  | VAndR vp2 -> VAndR (convert_vp vp2)
  | VImp (sp1, vp2) -> VImp (convert_sp sp1, convert_vp vp2)
  | VIffSV (sp1, vp2) -> VIffSV (convert_sp sp1, convert_vp vp2)
  | VIffVS (vp1, sp2) -> VIffVS (convert_vp vp1, convert_sp sp2)
  | VExists (x, Abs_part part) -> VExists (Pred.Term.unvar x, convert_part part)
  | VForall (x, d, vp) -> VForall (Pred.Term.unvar x, convert_d d, convert_vp vp)
  | VPrev vp1 -> VPrev (convert_vp vp1)
  | VPrev0 -> VPrevZ
  | VPrevOutL tp -> VPrevOutL (nat_of_int tp)
  | VPrevOutR tp -> VPrevOutR (nat_of_int tp)
  | VNext vp -> VNext (convert_vp vp)
  | VNextOutL tp -> VNextOutL (nat_of_int tp)
  | VNextOutR tp -> VNextOutR (nat_of_int tp)
  | VOnceOut tp -> VOnceOut (nat_of_int tp)
  | VOnce (tp, etp, vp1s) ->
     let vp1s' = List.rev(Deque.fold vp1s ~init:[] ~f:(fun acc vp1 -> (convert_vp vp1)::acc)) in
     VOnce (nat_of_int tp, nat_of_int etp, vp1s')
  | VHistorically (tp, vp1) -> VHistorically (nat_of_int tp, convert_vp vp1)
  | VEventually (tp, ltp, vp1s) ->
     let vp1s' = List.rev(Deque.fold vp1s ~init:[] ~f:(fun acc vp1 -> (convert_vp vp1)::acc)) in
     VEventually (nat_of_int tp, nat_of_int ltp, vp1s')
  | VAlways (tp, vp1) -> VAlways (nat_of_int tp, convert_vp vp1)
  | VSinceOut tp -> VSinceOut (nat_of_int tp)
  | VSince (tp, vp1, vp2s) ->
     let vp2s' = List.rev(Deque.fold vp2s ~init:[] ~f:(fun acc vp2 -> (convert_vp vp2)::acc)) in
     VSince (nat_of_int tp, convert_vp vp1, vp2s')
  | VSinceInf (tp, etp, vp2s) ->
     let vp2s' = List.rev(Deque.fold vp2s ~init:[] ~f:(fun acc vp2 -> (convert_vp vp2)::acc)) in
     VSinceInf (nat_of_int tp, nat_of_int etp, vp2s')
  | VUntil (tp, vp1, vp2s) ->
     let vp2s' = List.rev(Deque.fold vp2s ~init:[] ~f:(fun acc vp2 -> (convert_vp vp2)::acc)) in
     VUntil (nat_of_int tp, vp2s', convert_vp vp1)
  | VUntilInf (tp, ltp, vp2s) ->
     let vp2s' = List.rev(Deque.fold vp2s ~init:[] ~f:(fun acc vp2 -> (convert_vp vp2)::acc)) in
     VUntilInf (nat_of_int tp, nat_of_int ltp, vp2s')

let convert_p = function
  | Proof.S sp -> Inl (convert_sp sp)
  | V vp -> Inr (convert_vp vp)

let rec convert_expl = function
  | Expl.Leaf pt -> Leaf (convert_p pt)
  | Node (x, part) -> Node (Pred.Term.unvar x, convert_part part)

let convert_interval = function
  | Interval.B bi -> (match bi with
                      | BI (l, r) -> interval (nat_of_int l) (Enat (nat_of_int r)))
  | U ui -> (match ui with
             | UI l -> interval (nat_of_int l) Infinity_enat)

let rec convert_f = function
  | Formula.TT -> TT
  | FF -> FF
  | Predicate (x, trms) -> Pred (x, List.map trms ~f:convert_term)
  | Neg (f) -> Neg (convert_f f)
  | Or (f, g) -> Or (convert_f f, convert_f g)
  | And (f, g) -> And (convert_f f, convert_f g)
  | Imp (f, g) -> Imp (convert_f f, convert_f g)
  | Iff (f, g) -> Iff (convert_f f, convert_f g)
  | Exists (x, f) -> Exists (Pred.Term.unvar x, convert_f f)
  | Forall (x, f) -> Forall (Pred.Term.unvar x, convert_f f)
  | Prev (i, f) -> Prev (convert_interval i, convert_f f)
  | Next (i, f) -> Next (convert_interval i, convert_f f)
  | Once (i, f) -> Once (convert_interval i, convert_f f)
  | Eventually (i, f) -> Eventually (convert_interval i, convert_f f)
  | Historically (i, f) -> Historically (convert_interval i, convert_f f)
  | Always (i, f) -> Always (convert_interval i, convert_f f)
  | Since (i, f, g) -> Since (convert_f f, convert_interval i, convert_f g)
  | Until (i, f, g) -> Until (convert_f f, convert_interval i, convert_f g)

let convert_db db =
  specialized_set (Set.fold db ~init:[] ~f:(fun acc (name, ds) ->
                       (name, List.map ds ~f:convert_d)::acc))

let convert_trace trace_lst =
 trace_of_list_specialized (List.fold_left trace_lst ~init:[] ~f:(fun acc (ts, db) ->
                                (convert_db db, nat_of_int ts)::acc))

let check trace_lst f expls =
  let f' = convert_f f in
  let trace' = convert_trace trace_lst in
  List.rev(List.fold_left expls ~init:[] ~f:(fun acc expl ->
               let expl' = convert_expl expl in
               (check_all_specialized trace' f' expl', expl', trace')::acc))
