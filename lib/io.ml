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
open Checker.Explanator2
open Checker_interface

type output =
  | Explanation of (timestamp * timepoint) * expl * bool option
  | ExplanationJSON of (timestamp * timepoint) * timepoint list * expl * bool option
  | ExplanationDebug of (timestamp * timepoint) * expl * bool * checker_proof * trace_t
  | Info of string

let parse_line s =
  let s = String.trim s in
  if String.length s > 1 && (String.get s 0) = '@' then
    match String.split_on_char ' ' (String.sub s 1 (String.length s - 1)) with
    | [] -> None
    | raw_t :: preds ->
       try Some (SS.of_list (List.map
                               (fun p ->
                                 String.trim (String.map (fun c ->
                                                  if c = '(' || c = ')' then ' '
                                                  else c) p))
                               (List.filter (fun x -> x <> "()") preds)),
                 int_of_string raw_t)
       with Failure _ -> None
  else None

let rec parse_lines line in_ch out_ch =
  match parse_line line with
  | Some s -> (s, in_ch)
  | None -> parse_lines (input_line in_ch) in_ch out_ch

let input_event in_ch out_ch =
  parse_lines (input_line in_ch) in_ch out_ch

let output_event out_ch event = Printf.fprintf out_ch "%s" event

let output_result out_ch res =
  match res with
  | Explanation ((ts, tp), p, b_opt) ->
     Printf.fprintf out_ch "%d:%d\nProof: \n%s\n" ts tp (expl_to_string p);
     (match b_opt with
      | None -> ()
      | Some b -> Printf.fprintf out_ch "\nChecker output: %B\n\n" b);
  | ExplanationJSON ((ts, tp), tps_in, p, b_opt) ->
     let tps_in_str = list_to_json (List.map (fun el -> string_of_int el) tps_in) in
     Printf.printf "    \"ts\": %d,\n" ts;
     Printf.printf "    \"tp\": %d,\n" tp;
     let () = match b_opt with
       | None -> ()
       | Some b -> Printf.printf "    \"checker\": \"%B\",\n" b in
     Printf.printf "    \"tps_in\": %s,\n" tps_in_str;
     Printf.printf "%s\n" (expl_to_json p);
  | ExplanationDebug ((ts, tp), p, b, cp, trace) ->
     Printf.printf "%d:%d\nProof: \n%s\n" ts tp (expl_to_string p);
     Printf.printf "\nChecker output: %B\n" b;
     Printf.printf "\nTrace: \n%s\n\n" (s_of_trace trace);
     Printf.printf "\nChecker proof: \n%s\n\n" (s_of_proof cp)
  | Info s -> Printf.fprintf out_ch "\nInfo: %s\n" s

let output_interval out_ch i = output_event out_ch (interval_to_string i)

let output_preamble out_ch mode out_mode f =
  let preamble_cl mode f =
    let mode_str = match mode with
      | SAT -> "SAT"
      | VIOL -> "VIOL"
      | ALL -> "ALL" in
    "Monitoring " ^ (formula_to_string f) ^ " in mode " ^ mode_str ^ "\n\n" in
  let preamble_json mode f =
    let subformulas = subfs_bfs [f] in
    let subformulas_json = String.concat "\n  },\n  {\n" (List.map formula_to_json subformulas) in
    Printf.sprintf "{\n  \"formula\": \"%s\",\n  \"columns\": %s,\n  \"subformulas\": [\n  {\n%s\n  }],\n  \"explanations\": [\n"
      (formula_to_string f) (list_to_json (List.map formula_to_string subformulas)) subformulas_json in
  match out_mode with
  | PLAIN -> output_event out_ch (preamble_cl mode f)
  | JSON -> output_event out_ch  (preamble_json mode f)
  | DEBUG -> output_event out_ch (preamble_cl mode f)

let output_closing out_ch out_mode =
  match out_mode with
  | PLAIN -> output_event out_ch "Bye.\n"
  | JSON -> output_event out_ch "  ]\n}"
  | DEBUG -> ()

let print_ps out_ch mode out_mode ts tp ps tps_in checker_ps_opt last_tp =
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
                                 | PLAIN -> let out = Explanation ((ts, tp), p, None) in
                                            output_result out_ch out
                                 | JSON -> let out = ExplanationJSON ((ts, tp), tps_in, p, None) in
                                           let () = output_event out_ch "  {\n" in
                                           let () = output_result out_ch out in
                                           if last_tp then output_event out_ch "  }\n"
                                           else output_event out_ch "  },\n"
                                 | _ -> ()) ps')
  | Some checker_ps -> (List.iter2 (fun p (b, checker_p, trace) ->
                            match out_mode with
                            | PLAIN -> let out = Explanation ((ts, tp), p, Some(b)) in
                                       output_result out_ch out
                            | JSON -> let out = ExplanationJSON ((ts, tp), tps_in, p, Some(b)) in
                                      let () = output_event out_ch "  {\n" in
                                      let () = output_result out_ch out in
                                      if last_tp then output_event out_ch "  }\n"
                                      else output_event out_ch "  },\n"
                            | DEBUG -> let out = ExplanationDebug ((ts, tp), p, b, checker_p, trace) in
                                       output_result out_ch out) ps' checker_ps)
