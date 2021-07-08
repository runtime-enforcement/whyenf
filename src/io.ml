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
open Ocolor_format

type output =
  | Boolean of (timestamp * timepoint) * bool
  | BooleanCheck of (timestamp * timepoint) * bool * bool
  | Explanation of (timestamp * timepoint) * expl
  | ExplanationCheck of (timestamp * timepoint)  * expl * bool
  | ExplanationDebug of (timestamp * timepoint)  * expl * bool * checker_proof * checker_trace
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
  | Boolean ((ts, tp), b) ->
     Printf.fprintf out_ch "%d:%d %B\n" ts tp b
  | BooleanCheck ((ts, tp), b, cb) ->
     Printf.fprintf out_ch "%d:%d %B\n" ts tp b;
     Printf.fprintf out_ch "\nChecker output: \n%B\n" cb
  | Explanation ((ts, tp), p) ->
     Printf.fprintf out_ch "%d:%d\nProof: \n%s\n" ts tp (expl_to_string p)
  | ExplanationCheck ((ts, tp), p, b) ->
     Printf.fprintf out_ch "%d:%d\nProof: \n%s\n" ts tp (expl_to_string p);
     Printf.fprintf out_ch "\nChecker output: %B\n\n" b
  | ExplanationDebug ((ts, tp), p, b, cp, ctrace) ->
     Ocolor_format.printf "@{<yellow;bold>%d:%d@}\nProof: \n%s\n" ts tp (expl_to_string p);
     (if b then Ocolor_format.printf "\nChecker output: %B\n" b
      else Ocolor_format.printf "\nChecker output: @{<red;bold>%B@}\n" b);
     Ocolor_format.printf "\nTrace: \n%s\n\n" (s_of_trace ctrace);
     Ocolor_format.printf "\nChecker proof: \n%s\n\n" (s_of_proof cp)
  | Info s ->
     Printf.fprintf out_ch "\nInfo: %s\n" s

let output_interval out_ch i = output_event out_ch (interval_to_string i)

let preamble out_ch mode f =
  output_event out_ch "Monitoring ";
  output_event out_ch (formula_to_string f);
  output_event out_ch (" in mode " ^
                         (match mode with
                          | SAT -> "SAT"
                          | VIOL -> "VIOL"
                          | ALL -> "ALL"
                          | BOOL -> "BOOL")
                         ^ "\n\n")

let print_ps out_ch mode ts tp ps checker_ps_opt debug =
  let checker_ps =
    match checker_ps_opt with
    | None -> []
    | Some checker_ps -> checker_ps in
  match mode with
  | SAT -> if (List.length checker_ps) > 0 then
             List.iter2 (fun p (b, checker_p, trace) ->
                 match p with
                 | S _ -> if debug then
                            let out = ExplanationDebug ((ts, tp), p, b, checker_p, trace) in
                            output_result out_ch out
                          else
                            let out = ExplanationCheck ((ts, tp), p, b) in
                            output_result out_ch out
                 | V _ -> ()) ps checker_ps
           else
             List.iter (fun p ->
                 match p with
                 | S _ -> let out = Explanation ((ts, tp), p) in
                          output_result out_ch out
                 | V _ -> ()) ps
  | VIOL -> if (List.length checker_ps) > 0 then
              List.iter2 (fun p (b, checker_p, trace) ->
                  match p with
                  | S _ -> ()
                  | V _ -> if debug then
                             let out = ExplanationDebug ((ts, tp), p, b, checker_p, trace) in
                             output_result out_ch out
                           else
                             let out = ExplanationCheck ((ts, tp), p, b) in
                             output_result out_ch out) ps checker_ps
            else
              List.iter (fun p ->
                  match p with
                  | S _ -> ()
                  | V _ -> let out = Explanation ((ts, tp), p) in
                           output_result out_ch out) ps
  | ALL -> if (List.length checker_ps) > 0 then
             List.iter2 (fun p (b, checker_p, trace) ->
                 if debug then
                   let out = ExplanationDebug ((ts, tp), p, b, checker_p, trace) in
                   output_result out_ch out
                 else
                   let out = ExplanationCheck ((ts, tp), p, b) in
                   output_result out_ch out) ps checker_ps
            else
              List.iter (fun p ->
                  let out = Explanation ((ts, tp), p) in
                  output_result out_ch out) ps
  | BOOL -> if (List.length checker_ps) > 0 then
              List.iter2 (fun p (b, _, _) ->
                  match p with
                  | S _ -> let out = BooleanCheck ((ts, tp), true, b) in
                           output_result out_ch out
                  | V _ -> let out = BooleanCheck ((ts, tp), false, b) in
                           output_result out_ch out) ps checker_ps
            else
              List.iter (fun p ->
                  match p with
                  | S _ -> let out = Boolean ((ts, tp), true) in
                           output_result out_ch out
                  | V _ -> let out = Boolean ((ts, tp), false) in
                           output_result out_ch out) ps
