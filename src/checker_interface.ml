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
open Checker.Verified_checker

let rec convert_sp sp =
  match sp with
  | SAtom (i, s) -> let i_nat = nat_of_integer (of_int i) in
                    SAtm (s, i_nat)
  | SNeg p1 -> SNeg (convert_vp p1)
  | SDisjL p1 -> SDisjL (convert_sp p1)
  | SDisjR p2 -> SDisjR (convert_sp p2)
  | SConj (p1, p2) -> SConj (convert_sp p1, convert_sp p2)
  | SSince (p2, p1s) -> let p1s' = List.rev(List.fold_left (fun acc p1 ->
                                                (convert_sp p1)::acc) [] p1s) in
                        SSince (convert_sp p2, p1s')
  | SUntil (p2, p1s) -> let p1s' = List.rev(List.fold_left (fun acc p1 ->
                                                (convert_sp p1)::acc) [] p1s) in
                        SUntil (p1s', convert_sp p2)
  | SNext p1 -> SNext (convert_sp p1)
  | SPrev p1 -> SPrev (convert_sp p1)
  | _ -> failwith "This proof cannot be checked"
and convert_vp vp =
  match vp with
  | VAtom (i, s) -> let i_nat = nat_of_integer (of_int i) in
                    VAtm (s, i_nat)
  | VNeg p1 -> VNeg (convert_sp p1)
  | VDisj (p1, p2) -> VDisj (convert_vp p1, convert_vp p2)
  | VConjL p1 -> VConjL (convert_vp p1)
  | VConjR p2 -> VConjR (convert_vp p2)
  | VSince (i, p1, p2s) -> let i_nat = nat_of_integer (of_int i) in
                           let p2s' = List.rev(List.fold_left (fun acc p2 ->
                                                (convert_vp p2)::acc) [] p2s) in
                           VSince (i_nat, convert_vp p1, p2s')
  | VUntil (i, p1, p2s) -> let i_nat = nat_of_integer (of_int i) in
                           let p2s' = List.rev(List.fold_left (fun acc p2 ->
                                                (convert_vp p2)::acc) [] p2s) in
                           VUntil (i_nat, p2s', convert_vp p1)
  | VSinceInf (i, p2s) -> let i_nat = nat_of_integer (of_int i) in
                          let p2s' = List.rev(List.fold_left (fun acc p2 ->
                                                  (convert_vp p2)::acc) [] p2s) in
                          VSince_never (i_nat, p2s')
  | VUntilInf (i, p2s) -> let i_nat = nat_of_integer (of_int i) in
                          let p2s' = List.rev(List.fold_left (fun acc p2 ->
                                                  (convert_vp p2)::acc) [] p2s) in
                          VUntil_never (i_nat, p2s')
  | VSinceOutL i -> let i_nat = nat_of_integer (of_int i) in
                    VSince_le i_nat
  | VNext p1 -> VNext (convert_vp p1)
  | VNextOutL i -> let i_nat = nat_of_integer (of_int i) in
                   VNext_le i_nat
  | VNextOutR i -> let i_nat = nat_of_integer (of_int i) in
                   VNext_ge i_nat
  | VPrev vp1 -> VPrev (convert_vp vp1)
  | VPrevOutL i -> let i_nat = nat_of_integer (of_int i) in
                   VPrev_le i_nat
  | VPrevOutR i -> let i_nat = nat_of_integer (of_int i) in
                   VPrev_ge i_nat
  | VPrev0 -> VPrev_zero
  | _ -> failwith "This proof cannot be checked"

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
  match (value f) with
  | P (x) -> Atom (x)
  | Neg (f) -> Neg (convert_f f)
  | Disj (f, g) -> Disj (convert_f f, convert_f g)
    | Since (interval, f, g) -> let interval' = convert_interval interval in
                                Since (convert_f f, interval', convert_f g)
    | Until (interval, f, g) -> let interval' = convert_interval interval in
                         Until (convert_f f, interval', convert_f g)
    | _ -> failwith "This formula cannot be checked"

let convert_event sap ts =
  let ts_nat = nat_of_integer (of_int ts) in
  let sap_lst = SS.elements sap in
  let set_check = Set sap_lst in
  (set_check, ts_nat)

let convert_events events =
  List.rev (List.fold_left
              (fun acc (sap, ts) ->
                (convert_event sap ts)::acc) [] events)

let check_proof events f p =
  let f_check = convert_f f in
  let events_check = to_trace (convert_events events) in
  match p with
  | S sp -> let sp_check = convert_sp sp in
            strs_check events_check f_check sp_check
  | V vp -> let vp_check = convert_vp vp in
            strv_check events_check f_check vp_check
