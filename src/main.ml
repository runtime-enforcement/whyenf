(*******************************************************************)
(*     This is part of Aerial, it is distributed under the         *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util
open Monitor
open Mtl_parser
open Mtl_lexer

exception EXIT

(* let measure_ref = ref None *)
(* let fmla_ref = ref (disj (always (eventually (p "p"))) (eventually (conj (p "p") (next (p "q"))))) *)
(* let fmla_ref = ref None *)
let log_ref = ref stdin
let out_ref = ref stdout
let full_ref = ref true
let filter_atoms = ref false

let usage () = Format.eprintf
"Example usage: explanator2 -measure size -fmla test.fmla -log test.log -out test.out
Arguments:
\t -ap      - output only the \"responsible atomic proposition\" view
\t -O
\t\t size   - optimize proof size (default)
\t\t high   - optimize highest time-point occuring in a proof (lower is better)
\t\t pred   - optimize multiset cardinality of atomic predicates
\t\t none   - give any proof
\t -fmla
\t\t <file> or <string> - formula to be explained (if none given some default formula will be used)\n
\t -log
\t\t <file> - log file (default: stdin)
\t -out
\t\t <file> - output file where the explanation is printed to (default: stdout)\n%!"; raise EXIT

let measure_error () =
  Format.eprintf "mode should be either of \"size\", \"high\", \"pred\", or \"none\" (without quotes)\n%!";
  raise EXIT

let process_args =
  let rec go = function
    | ("-ap" :: args) ->
        full_ref := false;
        go args
    (* | ("-O" :: mode :: args) ->
     *     let mode =
     *       match mode with
     *       | "size" | "SIZE" | "Size" -> size_le
     *       | "high" | "HIGH" | "High" -> high_le
     *       | "pred" | "PRED" | "Pred" -> predicates_le
     *       | "none" | "NONE" | "None" -> (fun _ _ -> true)
     *       | _ -> measure_error () in
     *     measure_ref := (match !measure_ref with
     *       | None -> Some mode
     *       | Some mode' -> Some (prod_le mode mode'));
     *     go args *)
    (* | ("-Olex" :: mode :: args) ->
     *     let mode =
     *       match mode with
     *       | "size" | "SIZE" | "Size" -> size_le
     *       | "high" | "HIGH" | "High" -> high_le
     *       | "pred" | "PRED" | "Pred" -> predicates_le
     *       | "none" | "NONE" | "None" -> (fun _ _ -> true)
     *       | _ -> measure_error () in
     *     measure_ref := (match !measure_ref with
     *       | None -> Some mode
     *       | Some mode' -> Some (lex_le mode mode'));
     *     go args *)
    | ("-log" :: logfile :: args) ->
        log_ref := open_in logfile;
        go args
    (* | ("-fmla" :: fmlafile :: args) ->
     *     (try
     *       let in_ch = open_in fmlafile in
     *       fmla_ref := Mtl_parser.formula Mtl_lexer.token (Lexing.from_channel in_ch);
     *       close_in in_ch
     *     with
     *       _ -> fmla_ref := Mtl_parser.formula Mtl_lexer.token (Lexing.from_string fmlafile));
     *     go args *)
    | ("-out" :: outfile :: args) ->
        out_ref := open_out outfile;
        go args
    | [] -> ()
    | _ -> usage () in
  go

(* let _ =
 *   try
 *     process_args (List.tl (Array.to_list Sys.argv));
 *     let f, l = if !nusmv then parse_nusmv_output !log_ref else !fmla_ref, parse_lasso !log_ref in
 *     let p = optimal_proof l (match !measure_ref with None -> size_le | Some mode -> mode) f in
 *     let (ulen, vlen) = length_pair_lasso l in
 *     if !full_ref then
 *       let _ = Printf.fprintf !out_ref "Formula: %s\n" (formula_to_string f) in
 *       let _ = Printf.fprintf !out_ref "Word:\n%s\n" (lasso_to_string l) in
 *       let _ = Printf.fprintf !out_ref "Lasso Length: |u| = %d , |v| = %d \n" ulen vlen in
 *       let _ = Printf.fprintf !out_ref "Past height: %d , Future height: %d \n" (hp f) (hf f) in
 *       let _ = Printf.fprintf !out_ref "Proof Statistics: Size = %d, High = %d, Low = %d, Predicates = %d\n" (size p) (high p) (low p) (predicates p) in
 *       let _ = Printf.fprintf !out_ref "Proof: \n%s\n" (to_string p) in
 *       let pos = p_at p in
 *       if check_proof l f p then
 *         if pos = 0 then Printf.fprintf !out_ref "Checked proof at 0. Everything is fine.\n"
 *         else Printf.fprintf !out_ref
 *           "This proof isn't a proof at 0 but at %d. You have discovered a bug.\n" pos
 *       else Printf.fprintf !out_ref "This proof isn't a proof. You have discovered a bug.\n"
 *     else
 *       let _ = Printf.fprintf !out_ref "Formula: %s\n%s\n" (formula_to_string f) (visualize l f p) in
 *       ()
 *   with
 *     | End_of_file -> let _ = Printf.fprintf !out_ref "Bye.\n" in close_out !out_ref; exit 0
 *     | EXIT -> close_out !out_ref; exit 1 *)
