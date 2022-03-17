(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl
open Util
open Expl
open Interval
open Vis
open Checker.Explanator2
open Checker_interface

module String = Base.String

type output =
  | Explanation of (timestamp * timepoint) * expl * bool option
  | ExplanationDebug of (timestamp * timepoint) * expl * bool * checker_proof * trace_t
  | ExplanationToJSON of (timestamp * timepoint) * timepoint list * formula * expl * bool option
  | Info of string

let parse_line s =
  let s = String.strip s in
  if String.length s > 1 && (String.get s 0) = '@' then
    match String.split_on_chars (String.sub s 1 (String.length s - 1)) [' '] with
    | [] -> None
    | raw_t :: preds ->
       try Some (SS.of_list (List.map
                               (fun p ->
                                 String.strip (String.map p (fun c ->
                                                  if c = '(' || c = ')' then ' '
                                                  else c)))
                               (List.filter (fun x -> x <> "()") preds)),
                 int_of_string raw_t)
       with Failure _ -> None
  else None

(* in/out_channel related *)
let rec parse_lines line in_ch out_ch =
  match parse_line line with
  | Some s -> (s, in_ch)
  | None -> parse_lines (input_line in_ch) in_ch out_ch

let input_event in_ch out_ch =
  parse_lines (input_line in_ch) in_ch out_ch

let output_event out_ch event = Printf.fprintf out_ch "%s" event

let output_explanation out_ch expl =
  match expl with
  | Explanation ((ts, tp), p, b_opt) ->
     Printf.fprintf out_ch "%d:%d\nProof: \n%s\n" ts tp (expl_to_string p);
     (match b_opt with
      | None -> ()
      | Some b -> Printf.fprintf out_ch "\nChecker output: %B\n\n" b);
  | ExplanationDebug ((ts, tp), p, b, cp, trace) ->
     Printf.printf "%d:%d\nProof: \n%s\n" ts tp (expl_to_string p);
     Printf.printf "\nChecker output: %B\n" b;
     Printf.printf "\nTrace: \n%s\n\n" (s_of_trace trace);
     Printf.printf "\nChecker proof: \n%s\n\n" (s_of_proof cp)
  | ExplanationToJSON ((ts, tp), tps_in, f, p, cb_opt) ->
     let ident = "    " in
     let tps_in_json = list_to_json (List.map (fun el -> string_of_int el) tps_in) in
     Printf.fprintf out_ch "{\n";
     Printf.fprintf out_ch "%s\"ts\": %d,\n" ident ts;
     Printf.fprintf out_ch "%s\"tp\": %d,\n" ident tp;
     Printf.fprintf out_ch "%s\"tps_in\": %s,\n" ident tps_in_json;
     (match cb_opt with
      | None -> ()
      | Some cb -> Printf.fprintf out_ch "%s\"checker\": \"%B\",\n" ident cb);
     Printf.printf "%s\n" (expl_to_json f p);
     Printf.fprintf out_ch "}\n";
  | Info s -> Printf.fprintf out_ch "\nInfo: %s\n" s

let preamble_stdout out_ch mode f =
  let m = match mode with
    | SAT -> "SAT"
    | VIOL -> "VIOL"
    | ALL -> "ALL" in
  Printf.fprintf out_ch "Monitoring %s in mode %s\n\n" (formula_to_string f) m

let closing_stdout out_ch =
  output_event out_ch "Bye.\n"

let preamble_json out_ch f =
  Printf.fprintf out_ch "{\n  \"columns\": %s\n}\n" (list_to_json (List.map formula_to_string (subfs_dfs f)))

let output_ps out_ch mode out_mode ts tp tps_in f ps checker_ps_opt =
  let ps' = match mode with
    | SAT -> List.filter (fun p -> match p with
                                   | S _ -> true
                                   | V _ -> false) ps
    | VIOL -> List.filter (fun p -> match p with
                                    | S _ -> false
                                    | V _ -> true) ps
    | ALL -> ps in
  match checker_ps_opt with
  | None -> (List.iter (fun p -> match out_mode with
                                 | PLAIN -> let expl = Explanation ((ts, tp), p, None) in
                                            output_explanation out_ch expl
                                 | JSON -> let expl = ExplanationToJSON ((ts, tp), tps_in, f, p, None) in
                                           output_explanation out_ch expl
                                 | _ -> ()) ps')
  | Some checker_ps -> (List.iter2 (fun p (b, checker_p, trace) ->
                            match out_mode with
                            | PLAIN -> let expl = Explanation ((ts, tp), p, Some(b)) in
                                       output_explanation out_ch expl
                            | JSON -> let expl = ExplanationToJSON ((ts, tp), tps_in, f, p, Some(b)) in
                                      output_explanation out_ch expl
                            | DEBUG -> let expl = ExplanationDebug ((ts, tp), p, b, checker_p, trace) in
                                       output_explanation out_ch expl) ps' checker_ps)

(* from/to_string related *)
let parse_lines_from_string s =
  let events = String.split_lines s in
  List.map (fun e -> match parse_line e with
                     | Some s -> s
                     | None -> failwith "") events

let input_event in_ch out_ch =
  parse_lines (input_line in_ch) in_ch out_ch
