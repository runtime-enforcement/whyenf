(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2022:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl
open Expl

let list_to_json l =
  let els_str = String.concat "" (List.map (fun el -> "\"" ^ el ^ "\",")  l) in
  "[" ^ (String.sub els_str 0 ((String.length els_str)-1)) ^ "]\n"

let preamble f subf tps_in =
  let indent = "  " in
  Printf.sprintf "{\n%s\"formula\": %s\n%s\"subformulas\": [%s]\n" indent (formula_to_string f) indent (list_to_json subf)
  (* \"tps_in\": [" ^ (list_to_json (List.map (fun el -> string_of_int el) tps_in)) ^ "\n" *)

let rec s_to_json indent p =
  let indent' = "  " ^ indent in
  match p with
  | STT i -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"true\"\n%s\"tp\": %d\n%s}"
               indent indent' indent' i indent
  | SAtom (i, a) -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"SAtom\"\n%s\"atom\": \"%s\"\n%s\"tp\": %d\n%s}"
                      indent indent' indent' a indent' i indent
  | SNeg vphi -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"SNeg\"\n%s\"tp\": %d\n%s%s\n%s}"
                   indent indent' indent' (s_at p) indent' (v_to_string indent' vphi) indent
  | SDisjL sphi -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"SDisjL\"\n%s\"tp\": %d\n%s%s\n%s}"
                     indent indent' indent' (s_at p) indent' (s_to_string indent' sphi) indent
  | SDisjR spsi -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"SDisjR\"\n%s\"tp\": %d\n%s%s\n%s}"
                     indent indent' indent' (s_at p) indent' (s_to_string indent' spsi) indent
  | SConj (sphi, spsi) -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"SConj\"\n%s\"tp\": %d\n%s%s\n%s%s\n%s}"
                            indent indent' indent' (s_at p) indent' (s_to_string indent' sphi) indent' (s_to_string indent' spsi) indent
  | SPrev sphi -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"SPrev\"\n%s\"tp\": %d\n%s%s\n%s}"
                    indent indent' indent' (s_at p) indent' (s_to_string indent' sphi) indent
  | SNext sphi -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"SNext\"\n%s\"tp\": %d\n%s%s\n%s}"
                    indent indent' indent' (s_at p) indent' (s_to_string indent' sphi) indent
  | SSince (spsi, sphis) -> let sphis_str = list_to_json (List.map (fun el -> s_to_string indent' el) sphis) in
                            Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"SSince\"\n%s\"tp\": %d\n%s%s\n%s%s\n%s}"
                              indent indent' indent' (s_at p) indent' (s_to_string indent' spsi) indent' sphis_str indent
  | SUntil (spsi, sphis) -> let sphis_str = list_to_json (List.map (fun el -> s_to_string indent' el) sphis) in
                            Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"SUntil\"\n%s\"tp\": %d\n%s%s\n%s%s\n%s}"
                              indent indent' indent' (s_at p) indent' sphis_str  indent' (s_to_string indent' spsi) indent
  | _ -> ""
and v_to_json indent p =
  let indent' = "  " ^ indent in
  match p with
  | VFF i -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"false\"\n%s\"tp\": %d\n%s}"
               indent indent' indent' i indent
  | VAtom (i, a) -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VAtom\"\n%s\"atom\": \"%s\"\n%s\"tp\": %d\n%s}"
                      indent indent' indent' a indent' i indent
  | VNeg sphi -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VNeg\"\n%s\"tp\": %d\n%s%s\n%s}"
                   indent indent' indent' (v_at p) indent' (s_to_string indent' sphi) indent
  | VDisj (vphi, vpsi) -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VDisj\"\n%s\"tp\": %d\n%s%s\n%s%s\n%s}"
                            indent indent' indent' (v_at p) indent' (v_to_string indent' vphi) indent' (v_to_string indent' vpsi) indent
  | VConjL vphi -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VConjL\"\n%s\"tp\": %d\n%s%s\n%s}"
                     indent indent' indent' (v_at p) indent' (v_to_string indent' vphi) indent
  | VConjR vpsi -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VConjR\"\n%s\"tp\": %d\n%s%s\n%s}"
                     indent indent' indent' (v_at p) indent' (v_to_string indent' vpsi) indent
  | VPrev0 -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VPrev0\"\n%s\"tp\": 0\n%s}"
               indent indent' indent' indent
  | VPrevOutL i -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VPrevOutL\"\n%s\"tp\": %d\n%s}"
                     indent indent' indent' i indent
  | VPrevOutR i -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VPrevOutR\"\n%s\"tp\": %d\n%s}"
                     indent indent' indent' i indent
  | VPrev vphi -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VPrev\"\n%s\"tp\": %d\n%s%s\n%s}"
                    indent indent' indent' (v_at p) indent' (v_to_string indent' vphi) indent
  | VNextOutL i -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VNextOutL\"\n%s\"tp\": %d\n%s}"
                     indent indent' indent' i indent
  | VNextOutR i -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VNextOutR\"\n%s\"tp\": %d\n%s}"
                     indent indent' indent' i indent
  | VNext vphi -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VNext\"\n%s\"tp\": %d\n%s%s\n%s}"
                    indent indent' indent' (v_at p) indent' (v_to_string indent' vphi) indent
  | VSince (_, vphi, vpsis) -> let vpsis_str = list_to_json (List.map (fun el -> v_to_string indent' el) vpsis) in
                               Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VSince\"\n%s\"tp\": %d\n%s%s\n%s%s\n%s}"
                                 indent indent' indent' (v_at p) indent' (v_to_string indent' vphi) indent' vpsis_str indent
  | VSinceInf (_, _, vpsis) -> let vpsis_str = list_to_json (List.map (fun el -> v_to_string indent' el) vpsis) in
                               Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VSince\"\n%s\"tp\": %d\n%s%s\n%s}"
                                 indent indent' indent' (v_at p) indent' vpsis_str indent
  | VSinceOutL i -> Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VSinceOutL\"\n%s\"tp\": %d\n%s}"
                     indent indent' indent' i indent
  | VUntil (_, vphi, vpsis) -> let vpsis_str = list_to_json (List.map (fun el -> v_to_string indent' el) vpsis) in
                               Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VUntil\"\n%s\"tp\": %d\n%s%s\n%s%s\n%s}"
                                 indent indent' indent' (v_at p) indent' vpsis_str indent' (v_to_string indent' vphi) indent
  | VUntilInf (_, _, vpsis) -> let vpsis_str = list_to_json (List.map (fun el -> v_to_string indent' el) vpsis) in
                               Printf.sprintf "%s\"explanation\": {\n%s\"type\": \"VUntilInf\"\n%s\"tp\": %d\n%s%s\n%s}"
                                 indent indent' indent' (v_at p) indent' vpsis_str indent
  | _ -> ""

let expl_to_json = function
  | S p -> s_to_json "  " p
  | V p -> v_to_json "  " p
