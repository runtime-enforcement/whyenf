(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Formula
open Util
open Expl
open Interval
open Vis
open Checker.VerifiedExplanator2
open Checker_interface

module List = Base.List
module String = Base.String
module Error = Base.Error
module Or_error = Base.Or_error

type output =
  | Explanation of (timestamp * timepoint) * expl * bool option
  | ExplanationDebug of (timestamp * timepoint) * expl * bool * checker_proof * trace_t
  | ExplanationToJSON of (timestamp * timepoint) * timepoint list * formula * expl * bool option
  | Info of string

(* Trace *)
let parse_trace_line s =
  let s = String.strip s in
  if String.length s > 1 && (String.get s 0) = '@' then
    match String.split_on_chars (String.sub s 1 (String.length s - 1)) [' '] with
    | [] -> None
    | raw_t :: preds ->
       try Some (SS.of_list (List.map (List.filter preds (fun x -> x <> "()"))
                               (fun p ->
                                 String.strip (String.map p (fun c ->
                                                   if c = '(' || c = ')' then ' '
                                                   else c)))),
                 int_of_string raw_t)
       with Failure _ -> None
  else None

(* in/out_channel related *)
let rec parse_trace_lines line in_ch out_ch =
  match parse_trace_line line with
  | Some s -> (s, in_ch)
  | None -> parse_trace_lines (input_line in_ch) in_ch out_ch

let input_event in_ch out_ch =
  parse_trace_lines (input_line in_ch) in_ch out_ch

let output_event out_ch event = Printf.fprintf out_ch "%s" event

(* Weights *)
let parse_weight_line s =
  let s = String.strip s in
  if String.length s > 1 then
    (match String.split_on_chars s [':'] with
     | [] -> None
     | raw_atm :: [raw_weight] ->
        try Some (String.strip raw_atm, int_of_string (String.strip raw_weight))
        with Failure _ -> None
     | _ -> None)
  else None

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
     let tps_in_json = list_to_json (List.map tps_in (fun el -> string_of_int el)) in
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
  Printf.fprintf out_ch "{\n  \"columns\": %s\n}\n" (list_to_json (List.map (subfs_dfs f) formula_to_string))

let output_ps out_ch mode out_mode ts tps_in f ps checker_ps_opt =
  let ps' = match mode with
    | SAT -> List.filter ps (fun p -> match p with
                                      | S _ -> true
                                      | V _ -> false)
    | VIOL -> List.filter ps (fun p -> match p with
                                       | S _ -> false
                                       | V _ -> true)
    | ALL -> ps in
  match checker_ps_opt with
  | None -> (List.iter ps' (fun p -> match out_mode with
                                     | PLAIN -> let expl = Explanation ((ts, (p_at p)), p, None) in
                                                output_explanation out_ch expl
                                     | JSON -> let expl = ExplanationToJSON ((ts, (p_at p)), tps_in, f, p, None) in
                                               output_explanation out_ch expl
                                     | _ -> ()))
  | Some checker_ps -> (List.iter2_exn ps' checker_ps (fun p (b, checker_p, trace) ->
                            match out_mode with
                            | PLAIN -> let expl = Explanation ((ts, (p_at p)), p, Some(b)) in
                                       output_explanation out_ch expl
                            | JSON -> let expl = ExplanationToJSON ((ts, (p_at p)), tps_in, f, p, Some(b)) in
                                      output_explanation out_ch expl
                            | DEBUG -> let expl = ExplanationDebug ((ts, (p_at p)), p, b, checker_p, trace) in
                                       output_explanation out_ch expl))

(* from/to_string related *)
(* Here, instead of using exceptions, errors are handled
 * using error-aware return types. This is particularly
 * useful for returning errors to the visualization. *)
let trace_error = "Events are specified in the format: @1 a b"

let parse_lines_from_string s =
  let events = String.split_lines s in
  List.fold_until events ~init:[] ~finish:(fun acc -> Ok (List.rev acc))
    ~f:(fun acc e -> match parse_trace_line e with
                     | None -> Stop (Or_error.error_string trace_error)
                     | Some s -> Continue (s::acc))

let json_table_columns f =
  let aps_columns = Formula.atoms f in
  let subfs_columns = List.map (subfs_dfs f) op_to_string in
  let subfs = List.map (subfs_dfs f) formula_to_string in
  Printf.sprintf "{\n  \"apsColumns\": %s,\n  \"subfsColumns\": %s,\n  \"subformulas\": %s}\n"
    (list_to_json aps_columns) (list_to_json subfs_columns) (list_to_json subfs)

let json_expls tp_ts f ps cbs_opt =
  let ident = "    " in
  let ident2 = "    " ^ ident in
  match cbs_opt with
  | None -> String.concat ~sep:",\n" (List.map ps ~f:(fun p ->
                                          let tp = (p_at p) in
                                          let ts = Hashtbl.find tp_ts tp in
                                          Printf.sprintf "%s{\n" ident ^
                                          Printf.sprintf "%s\"ts\": %d,\n" ident2 ts ^
                                          Printf.sprintf "%s\"tp\": %d,\n" ident2 tp ^
                                          Printf.sprintf "%s\n" (expl_to_json f p) ^
                                          Printf.sprintf "%s}" ident))
  | Some cbs -> String.concat ~sep:",\n" (List.map2_exn ps cbs ~f:(fun p cb ->
                                              let tp = (p_at p) in
                                              let ts = Hashtbl.find tp_ts tp in
                                              Printf.sprintf "%s{\n" ident ^
                                              Printf.sprintf "%s\"ts\": %d,\n" ident2 ts ^
                                              Printf.sprintf "%s\"tp\": %d,\n" ident2 tp ^
                                              Printf.sprintf "%s\"checker\": \"%B\",\n" ident2 cb ^
                                              Printf.sprintf "%s\n" (expl_to_json f p) ^
                                              Printf.sprintf "%s}" ident))

let json_error err =
  Printf.sprintf "ERROR: %s" (Error.to_string_hum err)

let json_atoms f sap tp ts =
  let ident = "    " in
  let ident2 = "    " ^ ident in
  Printf.sprintf "%s{\n" ident ^
  Printf.sprintf "%s\"ts\": %d,\n" ident2 ts ^
  Printf.sprintf "%s\"tp\": %d,\n" ident2 tp ^
  Printf.sprintf "%s\n" (atoms_to_json f sap tp) ^
  Printf.sprintf "%s}" ident
