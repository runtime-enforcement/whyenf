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

let convert_trace trace =
  List.rev (List.fold_left
              (fun acc (sap, ts) ->
                (convert_event sap ts)::acc) [] trace)

let check_ps trace f ps =
  let checker_f = convert_f f in
  let trace_converted = convert_trace trace in
  let checker_trace = to_trace trace_converted in
  List.rev(List.fold_left (fun acc p ->
               let checker_p = convert_p p in
               match checker_p with
               | CS checker_sp -> let b = strs_check checker_trace checker_f checker_sp in
                                  (b, checker_p, trace_converted)::acc
               | CV checker_vp -> let b = strv_check checker_trace checker_f checker_vp in
                                  (b, checker_p, trace_converted)::acc) [] ps)

let s_of_sum s_of_left s_of_right = function
  | Inl x -> "Inl (" ^ s_of_left x ^ ")"
  | Inr y -> "Inr (" ^ s_of_right y ^ ")"

let s_of_nat n = Z.to_string (integer_of_nat n)

let s_of_list s_of xs = "[" ^ String.concat ", " (List.map s_of xs) ^ "]"

let s_of_trace trace =
  List.fold_right (fun (checker_sap, checker_nat) acc ->
      let s_of_checker_sap =
        match checker_sap with
        | Set lst -> s_of_list (fun s -> s) lst
        | Coset lst -> s_of_list (fun s -> s) lst in
      ("(" ^ s_of_nat checker_nat ^ ", " ^ s_of_checker_sap ^ ") " ^ acc)) (List.rev trace) ""

let rec s_of_sproof = function
  | STT n -> "STT " ^ s_of_nat n
  | SAtm (s, n) -> "SAtm (" ^ s ^ ", " ^ s_of_nat n ^ ")"
  | SNeg p -> "SNeg (" ^ s_of_vproof p ^ ")"
  | SDisjL p -> "SDisjL (" ^ s_of_sproof p ^ ")"
  | SDisjR p -> "SDisjR (" ^ s_of_sproof p ^ ")"
  | SConj (p, q) -> "SConj (" ^ s_of_sproof p ^ ", " ^ s_of_sproof q ^ ")"
  | SSince (p, qs) -> "SSince (" ^ s_of_sproof p ^ ", " ^ s_of_list s_of_sproof qs ^ ")"
  | SUntil (qs, p) -> "SUntil (" ^ s_of_list s_of_sproof qs ^ ", " ^ s_of_sproof p ^ ")"
  | SNext p -> "SNext (" ^ s_of_sproof p ^ ")"
  | SPrev p -> "SPrev (" ^ s_of_sproof p ^ ")"
and s_of_vproof = function
  | VFF n -> "VFF " ^ s_of_nat n
  | VAtm (s, n) -> "VAtm (" ^ s ^ ", " ^ s_of_nat n ^ ")"
  | VNeg p -> "VNeg (" ^ s_of_sproof p ^ ")"
  | VDisj (p, q) -> "VDisj (" ^ s_of_vproof p ^ ", " ^ s_of_vproof q ^ ")"
  | VConjL p -> "VConjL (" ^ s_of_vproof p ^ ")"
  | VConjR p -> "VConjR (" ^ s_of_vproof p ^ ")"
  | VSince (n, p, qs) -> "VSince (" ^ s_of_nat n ^ ", " ^ s_of_vproof p ^ ", " ^ s_of_list s_of_vproof qs ^ ")"
  | VUntil (n, qs, p) -> "VUntil (" ^ s_of_nat n ^ ", " ^ s_of_list s_of_vproof qs ^ ", " ^ s_of_vproof p ^ ")"
  | VSince_never (n, qs) -> "VSince_never (" ^ s_of_nat n ^ ", " ^ s_of_list s_of_vproof qs ^ ")"
  | VUntil_never (n, qs) -> "VUntil_never (" ^ s_of_nat n ^ ", " ^ s_of_list s_of_vproof qs ^ ")"
  | VSince_le n -> "VSince_le " ^ s_of_nat n
  | VNext p -> "VNext (" ^ s_of_vproof p ^ ")"
  | VNext_ge n -> "VNext_ge " ^ s_of_nat n
  | VNext_le n -> "VNext_le " ^ s_of_nat n
  | VPrev p -> "VPrev (" ^ s_of_vproof p ^ ")"
  | VPrev_ge n -> "VPrev_ge " ^ s_of_nat n
  | VPrev_le n -> "VPrev_le " ^ s_of_nat n
  | VPrev_zero -> "VPrev_zero"

let s_of_proof = function
  | CS sp -> s_of_sproof sp
  | CV vp -> s_of_vproof vp

let of_int n = nat_of_integer (Z.of_int n)
