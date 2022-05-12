(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Lib.Util
open Lib.Expl
open Lib.Mtl
open Lib.Io
open Lib.Mtl_parser
open Lib.Mtl_lexer
open Lib.Monitor
open Lib.Checker.Explanator2

module Explanator2 = struct

  exception UNEXPECTED_EXIT

  let check_ref = ref false
  let debug_ref = ref false
  let json_ref = ref false
  let mode_ref = ref ALL
  let out_mode_ref = ref PLAIN
  let measure_le_ref = ref None
  let is_opt_ref = ref None
  let fmla_ref = ref None
  let log_ref = ref stdin
  let out_ref = ref stdout
  let vis_ref = ref false
  let log_str_ref = ref ""

  let usage () =
    Format.eprintf
      "Usage: ./explanator2.exe [ARGUMENTS]
       Example: ./explanator2.exe -check -O size -fmla ex.mtl -log ex.log
       Arguments:
       \t -check   - execute verified checker
       \t -mode
       \t\t all    - output both satisfaction and violation explanations (default)
       \t\t sat    - output only satisfaction explanations
       \t\t viol   - output only violation explanations
       \t -O (measure)
       \t\t size   - optimize proof size
       \t\t wsize  - optimize weighted proof size (less is better)
       \t\t none   - pick any proof
       \t -fmla
       \t\t <file> or <string> - formula to be explained
       \t -log
       \t\t <file> - log file (default: stdin)
       \t -out_mode
       \t\t plain  - plain output (default)
       \t\t json   - JSON output (only useful for the visualization)
       \t\t debug  - plain verbose output (only useful for debugging)
       \t -out
       \t\t <file> - output file where the explanation is printed to (default: stdout)\n%!";
    exit 0

  let mode_error () =
    Format.eprintf "mode should be either \"sat\", \"viol\" or \"all\" (without quotes)\n%!";
    raise UNEXPECTED_EXIT

  let out_mode_error () =
    Format.eprintf "out_mode should be either \"plain\", \"json\" or \"debug\" (without quotes)\n%!";
    raise UNEXPECTED_EXIT

  let measure_error () =
    Format.eprintf "measure should be either \"size\", \"wsize\" or \"none\" (without quotes)\n%!";
    raise UNEXPECTED_EXIT

  let process_args =
    let rec go = function
      | ("-check" :: args) ->
         check_ref := true;
         go args
      | ("-out_mode" :: out_mode :: args) ->
         out_mode_ref :=
           (match out_mode with
            | "plain" | "PLAIN" | "Plain" -> PLAIN
            | "json" | "JSON" | "Json" -> JSON
            | "debug" | "DEBUG" | "Debug" -> DEBUG
            | _ -> mode_error ());
         go args
      | ("-mode" :: mode :: args) ->
         mode_ref :=
           (match mode with
            | "all" | "ALL" | "All" -> ALL
            | "sat" | "SAT" | "Sat" -> SAT
            | "viol" | "VIOL" | "Viol" -> VIOL
            | _ -> mode_error ());
         go args
      | ("-O" :: measure :: args) ->
         let measure_le =
           match measure with
           | "size" | "SIZE" | "Size" -> size_le
           | "high" | "HIGH" | "High" -> high_le
           | "none" | "NONE" | "None" -> (fun _ _ -> true)
           | _ -> measure_error () in
         measure_le_ref := Some measure_le;
         let is_opt =
           match measure with
           | "size" | "SIZE" | "Size" -> is_opt_atm (fun s -> nat_of_integer (Z.of_int 1))
           | "high" | "HIGH" | "High" -> is_opt_minmaxreach
           | "none" | "NONE" | "None" -> (fun _ _ _ _ -> true)
           | _ -> measure_error () in
         is_opt_ref := Some is_opt;
         go args
      | ("-log" :: logfile :: args) ->
         log_ref := open_in logfile;
         go args
      | ("-fmla" :: fmlafile :: args) ->
         (try
            let in_ch = open_in fmlafile in
            fmla_ref := Some(Lib.Mtl_parser.formula Lib.Mtl_lexer.token (Lexing.from_channel in_ch));
            close_in in_ch
          with
            _ -> fmla_ref := Some(Lib.Mtl_parser.formula Lib.Mtl_lexer.token (Lexing.from_string fmlafile)));
         go args
      | ("-out" :: outfile :: args) ->
         out_ref := open_out outfile;
         go args
      | ("-vis" :: fmlafile :: args) ->
         (* Quick sanity check (visualization related) *)
         let in_ch = open_in fmlafile in
         fmla_ref := Some(Lib.Mtl_parser.formula Lib.Mtl_lexer.token (Lexing.from_channel in_ch));
         log_str_ref := "@0 q\n@1 p\n@2 r\n@3 q";
         is_opt_ref := Some(is_opt_atm (fun s -> nat_of_integer (Z.of_int 1)));
         vis_ref := true;
         check_ref := false;
         measure_le_ref := Some(size_le);
         go args
      | [] -> ()
      | _ -> usage () in
    go

  let _ =
    try
      process_args (List.tl (Array.to_list Sys.argv));
      let measure_le = Option.get !measure_le_ref in
      let is_opt = Option.get !is_opt_ref in
      let formula = Option.get !fmla_ref in
      if !vis_ref then
        let () = Printf.printf "%s" (json_table_columns formula) in
        let (_, out) = monitor2 None !log_str_ref !check_ref measure_le formula in
        Printf.printf "%s" out
      else
        let _ = monitor !log_ref !out_ref !mode_ref !out_mode_ref !check_ref measure_le is_opt formula in ()
    with
    | End_of_file -> (if !out_mode_ref = PLAIN then
                        closing_stdout !out_ref);
                     close_out !out_ref; exit 0
    | UNEXPECTED_EXIT -> close_out !out_ref; exit 1

end
