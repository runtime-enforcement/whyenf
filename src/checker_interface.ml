(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Z
open Mtl
open Expl
open Interval
open Util
open Checker.Explanator2

type checker_proof = CS of string sproof | CV of string vproof
type checker_trace = (string set * nat) list
type trace_t = (SS.t * int) list

let rec convert_sp sp =
  match sp with
  | SAtom (tp, s) -> let tp_nat = nat_of_integer (of_int tp) in
                     SAtm (s, tp_nat)
  | STT tp -> let tp_nat = nat_of_integer (of_int tp) in
              STT tp_nat
  | SNeg vp1 -> SNeg (convert_vp vp1)
  | SDisjL sp1 -> SDisjL (convert_sp sp1)
  | SDisjR sp2 -> SDisjR (convert_sp sp2)
  | SConj (sp1, sp2) -> SConj (convert_sp sp1, convert_sp sp2)
  | SImplL vp1 -> SImplL (convert_vp vp1)
  | SImplR sp2 -> SImplR (convert_sp sp2)
  | SIffSS (sp1, sp2) -> SIff_ss (convert_sp sp1, convert_sp sp2)
  | SIffVV (vp1, vp2) -> SIff_vv (convert_vp vp1, convert_vp vp2)
  | SPrev sp1 -> SPrev (convert_sp sp1)
  | SNext sp1 -> SNext (convert_sp sp1)
  | SOnce (tp, sp1) -> let tp_nat = nat_of_integer (of_int tp) in
                       SOnce (tp_nat, convert_sp sp1)
  | SHistorically (tp, etp, sp2s) -> let tp_nat = nat_of_integer (of_int tp) in
                                     let etp_nat = nat_of_integer (of_int etp) in
                                     let sp2s' = List.rev(List.fold_left (fun acc sp2 ->
                                                              (convert_sp sp2)::acc) [] sp2s) in
                                     SHistorically (tp_nat, etp_nat, sp2s')
  | SHistoricallyOutL tp -> let tp_nat = nat_of_integer (of_int tp) in
                            SHistorically_le tp_nat
  | SEventually (tp, sp1) -> let tp_nat = nat_of_integer (of_int tp) in
                             SEventually (tp_nat, convert_sp sp1)
  | SAlways (tp, ltp, sp2s) -> let tp_nat = nat_of_integer (of_int tp) in
                               let ltp_nat = nat_of_integer (of_int ltp) in
                               let sp2s' = List.rev(List.fold_left (fun acc sp2 ->
                                                        (convert_sp sp2)::acc) [] sp2s) in
                               SAlways (tp_nat, ltp_nat, sp2s')
  | SSince (sp2, sp1s) -> let sp1s' = List.rev(List.fold_left (fun acc sp1 ->
                                                   (convert_sp sp1)::acc) [] sp1s) in
                          SSince (convert_sp sp2, sp1s')
  | SUntil (sp2, sp1s) -> let sp1s' = List.rev(List.fold_left (fun acc sp1 ->
                                                   (convert_sp sp1)::acc) [] sp1s) in
                          SUntil (sp1s', convert_sp sp2)
and convert_vp vp =
  match vp with
  | VAtom (tp, s) -> let tp_nat = nat_of_integer (of_int tp) in
                     VAtm (s, tp_nat)
  | VFF tp -> let tp_nat = nat_of_integer (of_int tp) in
              VFF tp_nat
  | VNeg sp1 -> VNeg (convert_sp sp1)
  | VDisj (vp1, vp2) -> VDisj (convert_vp vp1, convert_vp vp2)
  | VConjL vp1 -> VConjL (convert_vp vp1)
  | VConjR vp2 -> VConjR (convert_vp vp2)
  | VImpl (sp1, vp2) -> VImpl (convert_sp sp1, convert_vp vp2)
  | VIffSV (sp1, vp2) -> VIff_sv (convert_sp sp1, convert_vp vp2)
  | VIffVS (vp1, sp2) -> VIff_vs (convert_vp vp1, convert_sp sp2)
  | VPrev vp1 -> VPrev (convert_vp vp1)
  | VPrevOutL tp -> let tp_nat = nat_of_integer (of_int tp) in
                    VPrev_le tp_nat
  | VPrevOutR tp -> let tp_nat = nat_of_integer (of_int tp) in
                    VPrev_ge tp_nat
  | VPrev0 -> VPrev_zero
  | VNext p1 -> VNext (convert_vp p1)
  | VNextOutL tp -> let tp_nat = nat_of_integer (of_int tp) in
                    VNext_le tp_nat
  | VNextOutR tp -> let tp_nat = nat_of_integer (of_int tp) in
                    VNext_ge tp_nat
  | VOnceOutL tp -> let tp_nat = nat_of_integer (of_int tp) in
                    VOnce_le tp_nat
  | VOnce (tp, etp, vp1s) -> let tp_nat = nat_of_integer (of_int tp) in
                             let etp_nat = nat_of_integer (of_int etp) in
                             let vp1s' = List.rev(List.fold_left (fun acc vp1 ->
                                                      (convert_vp vp1)::acc) [] vp1s) in
                             VOnce (tp_nat, etp_nat, vp1s')
  | VHistorically (tp, vp1) -> let tp_nat = nat_of_integer (of_int tp) in
                               VHistorically (tp_nat, convert_vp vp1)
  | VEventually (tp, ltp, vp1s) -> let tp_nat = nat_of_integer (of_int tp) in
                                   let ltp_nat = nat_of_integer (of_int ltp) in
                                   let vp1s' = List.rev(List.fold_left (fun acc vp1 ->
                                                            (convert_vp vp1)::acc) [] vp1s) in
                                   VEventually (tp_nat, ltp_nat, vp1s')
  | VAlways (tp, vp1) -> let tp_nat = nat_of_integer (of_int tp) in
                         VAlways (tp_nat, convert_vp vp1)
  | VSince (tp, vp1, vp2s) -> let tp_nat = nat_of_integer (of_int tp) in
                              let vp2s' = List.rev(List.fold_left (fun acc vp2 ->
                                                       (convert_vp vp2)::acc) [] vp2s) in
                              VSince (tp_nat, convert_vp vp1, vp2s')
  | VUntil (tp, vp1, vp2s) -> let tp_nat = nat_of_integer (of_int tp) in
                              let vp2s' = List.rev(List.fold_left (fun acc vp2 ->
                                                       (convert_vp vp2)::acc) [] vp2s) in
                              VUntil (tp_nat, vp2s', convert_vp vp1)
  | VSinceInf (tp, etp, vp2s) -> let tp_nat = nat_of_integer (of_int tp) in
                                 let etp_nat = nat_of_integer (of_int etp) in
                                 let vp2s' = List.rev(List.fold_left (fun acc vp2 ->
                                                          (convert_vp vp2)::acc) [] vp2s) in
                                 VSince_never (tp_nat, etp_nat, vp2s')
  | VUntilInf (tp, ltp, vp2s) -> let tp_nat = nat_of_integer (of_int tp) in
                                 let ltp_nat = nat_of_integer (of_int ltp) in
                                 let vp2s' = List.rev(List.fold_left (fun acc vp2 ->
                                                          (convert_vp vp2)::acc) [] vp2s) in
                                 VUntil_never (tp_nat, ltp_nat, vp2s')
  | VSinceOutL tp -> let tp_nat = nat_of_integer (of_int tp) in
                     VSince_le tp_nat

let convert_p = function
  | S sp -> CS (convert_sp sp)
  | V vp -> CV (convert_vp vp)

let convert_interval i =
  match i with
  | B bi ->
     (match bi with
      | BI (l, r) -> let l_nat = nat_of_integer (of_int l) in
                     let r_nat = nat_of_integer (of_int r) in
                     let e_nat = Enat r_nat in
                     interval l_nat e_nat)
  | U ui ->
     (match ui with
      | UI l -> let l_nat = nat_of_integer (of_int l) in
                interval l_nat Infinity_enat)

let rec convert_f f =
  match f with
  | P (x) -> Atom (x)
  | TT -> TT
  | FF -> FF
  | Neg (f) -> Neg (convert_f f)
  | Conj (f, g) -> Conj (convert_f f, convert_f g)
  | Disj (f, g) -> Disj (convert_f f, convert_f g)
  | Imp (f, g) -> Impl (convert_f f, convert_f g)
  | Iff (f, g) -> Iff (convert_f f, convert_f g)
  | Once (i, f) -> let i' = convert_interval i in
                   Once (i', convert_f f)
  | Historically (i, f) -> let i' = convert_interval i in
                           Historically (i', convert_f f)
  | Eventually (i, f) -> let i' = convert_interval i in
                         Eventually (i', convert_f f)
  | Always (i, f) -> let i' = convert_interval i in
                     Always (i', convert_f f)
  | Prev (i, f) -> let i' = convert_interval i in
                   Prev (i', convert_f f)
  | Next (i, f) -> let i' = convert_interval i in
                   Next (i', convert_f f)
  | Since (i, f, g) -> let i' = convert_interval i in
                       Since (convert_f f, i', convert_f g)
  | Until (i, f, g) -> let i' = convert_interval i in
                       Until (convert_f f, i', convert_f g)

let convert_event sap ts =
  let ts_nat = nat_of_integer (of_int ts) in
  let sap_lst = SS.elements sap in
  let set_check = strset sap_lst in
  (set_check, ts_nat)

let convert_trace trace =
  List.fold_left
    (fun acc (sap, ts) ->
      (convert_event sap ts)::acc) [] trace

let check_ps is_opt trace f ps =
  let checker_f = convert_f f in
  let trace_converted = convert_trace trace in
  let checker_trace = trace_of_list trace_converted in
  List.rev(List.fold_left (fun acc p ->
               let checker_p = convert_p p in
               let checker_p_sum = match checker_p with
                 | CS checker_sp -> Inl checker_sp
                 | CV checker_vp -> Inr checker_vp in
               let tp_nat = nat_of_integer (of_int (p_at p)) in
               let b = is_opt checker_trace tp_nat checker_f checker_p_sum in
               (b, checker_p, trace)::acc) [] ps)

let s_of_sum s_of_left s_of_right = function
  | Inl x -> "Inl (" ^ s_of_left x ^ ")"
  | Inr y -> "Inr (" ^ s_of_right y ^ ")"

let s_of_nat n = Z.to_string (integer_of_nat n)

let s_of_list s_of xs = "[" ^ String.concat ", " (List.map s_of xs) ^ "]"

let s_of_set sap = "[" ^ String.concat ", " (List.rev(SS.fold (fun s acc -> s::acc) sap [])) ^ "]"

let s_of_trace trace =
  String.concat "\n"
    (List.rev (List.map (fun (sap, ts) ->
         let s_of_sap = s_of_set sap in
         ("(" ^ (string_of_int ts) ^ ", " ^ s_of_sap ^ ")")) trace))

let rec s_of_sproof = function
  | STT tp -> "STT " ^ s_of_nat tp
  | SAtm (s, tp) -> "SAtm (" ^ s ^ ", " ^ s_of_nat tp ^ ")"
  | SNeg vp1 -> "SNeg (" ^ s_of_vproof vp1 ^ ")"
  | SDisjL sp1 -> "SDisjL (" ^ s_of_sproof sp1 ^ ")"
  | SDisjR sp2 -> "SDisjR (" ^ s_of_sproof sp2 ^ ")"
  | SConj (sp1, sp2) -> "SConj (" ^ s_of_sproof sp1 ^ ", " ^ s_of_sproof sp2 ^ ")"
  | SImplL vp1 -> "SImplL (" ^ s_of_vproof vp1 ^ ")"
  | SImplR sp2 -> "SImplR (" ^ s_of_sproof sp2 ^ ")"
  | SIff_ss (sp1, sp2) -> "SIff_ss (" ^ s_of_sproof sp1 ^ ", " ^ s_of_sproof sp2 ^ ")"
  | SIff_vv (vp1, vp2) -> "SIff_vv (" ^ s_of_vproof vp1 ^ ", " ^ s_of_vproof vp2 ^ ")"
  | SPrev sp1 -> "SPrev (" ^ s_of_sproof sp1 ^ ")"
  | SNext sp1 -> "SNext (" ^ s_of_sproof sp1 ^ ")"
  | SOnce (tp, sp1) -> "SOnce (" ^ s_of_nat tp ^ ", " ^ s_of_sproof sp1 ^ ")"
  | SHistorically (tp, etp, sp2s) -> "SHistorically (" ^ s_of_nat tp ^ ", " ^ s_of_nat etp ^ ", "
                                     ^ s_of_list s_of_sproof sp2s ^ ")"
  | SHistorically_le tp -> "SHistorically_le " ^ s_of_nat tp
  | SEventually (tp, sp1) -> "SEventually (" ^ s_of_nat tp ^ ", " ^ s_of_sproof sp1 ^ ")"
  | SAlways (tp, ltp, sp2s) -> "SAlways (" ^ s_of_nat tp ^ ", " ^ s_of_nat ltp ^ ", "
                               ^ s_of_list s_of_sproof sp2s ^ ")"
  | SSince (sp2, sp1s) -> "SSince (" ^ s_of_sproof sp2 ^ ", " ^ s_of_list s_of_sproof sp1s ^ ")"
  | SUntil (sp1s, sp2) -> "SUntil (" ^ s_of_list s_of_sproof sp1s ^ ", " ^ s_of_sproof sp2 ^ ")"
and s_of_vproof = function
  | VFF tp -> "VFF " ^ s_of_nat tp
  | VAtm (s, tp) -> "VAtm (" ^ s ^ ", " ^ s_of_nat tp ^ ")"
  | VNeg sp1 -> "VNeg (" ^ s_of_sproof sp1 ^ ")"
  | VDisj (vp1, vp2) -> "VDisj (" ^ s_of_vproof vp1 ^ ", " ^ s_of_vproof vp2 ^ ")"
  | VConjL vp1 -> "VConjL (" ^ s_of_vproof vp1 ^ ")"
  | VConjR vp2 -> "VConjR (" ^ s_of_vproof vp2 ^ ")"
  | VImpl (sp1, vp2) -> "VImpl (" ^ s_of_sproof sp1 ^ ", " ^ s_of_vproof vp2 ^ ")"
  | VIff_sv (sp1, vp2) -> "VIff_sv (" ^ s_of_sproof sp1 ^ ", " ^ s_of_vproof vp2 ^ ")"
  | VIff_vs (vp1, sp2) -> "VIff_vs (" ^ s_of_vproof vp1 ^ ", " ^ s_of_sproof sp2 ^ ")"
  | VPrev vp1 -> "VPrev (" ^ s_of_vproof vp1 ^ ")"
  | VPrev_ge tp -> "VPrev_ge " ^ s_of_nat tp
  | VPrev_le tp -> "VPrev_le " ^ s_of_nat tp
  | VPrev_zero -> "VPrev_zero"
  | VNext vp1 -> "VNext (" ^ s_of_vproof vp1 ^ ")"
  | VNext_ge tp -> "VNext_ge " ^ s_of_nat tp
  | VNext_le tp -> "VNext_le " ^ s_of_nat tp
  | VOnce_le tp -> "VOnce_le " ^ s_of_nat tp
  | VOnce (tp, etp, vp1s) -> "VOnce (" ^ s_of_nat tp ^ ", " ^ s_of_nat etp ^ ", "
                             ^ s_of_list s_of_vproof vp1s ^ ")"
  | VHistorically (tp, vp1) -> "VHistorically (" ^ s_of_nat tp ^ ", " ^ s_of_vproof vp1 ^ ")"
  | VEventually (tp, ltp, vp1s) -> "VEventually (" ^ s_of_nat tp ^ ", " ^ s_of_nat ltp ^ ", "
                                   ^ s_of_list s_of_vproof vp1s ^ ")"
  | VAlways (tp, vp1) -> "VAlways (" ^ s_of_nat tp ^ ", " ^ s_of_vproof vp1 ^ ")"
  | VSince (tp, vp1, vp2s) -> "VSince (" ^ s_of_nat tp ^ ", " ^ s_of_vproof vp1 ^ ", " ^ s_of_list s_of_vproof vp2s ^ ")"
  | VUntil (tp, vp2s, vp1) -> "VUntil (" ^ s_of_nat tp ^ ", " ^ s_of_list s_of_vproof vp2s ^ ", " ^ s_of_vproof vp1 ^ ")"
  | VSince_never (tp, etp, vp2s) -> "VSince_never (" ^ s_of_nat tp ^ ", " ^ s_of_nat etp ^ ", "
                                    ^ s_of_list s_of_vproof vp2s ^ ")"
  | VUntil_never (tp, ltp, vp2s) -> "VUntil_never (" ^ s_of_nat tp ^ ", " ^ s_of_nat ltp ^ ", "
                                    ^ s_of_list s_of_vproof vp2s ^ ")"
  | VSince_le tp -> "VSince_le " ^ s_of_nat tp

let s_of_proof = function
  | CS sp -> s_of_sproof sp
  | CV vp -> s_of_vproof vp

let of_int n = nat_of_integer (Z.of_int n)
