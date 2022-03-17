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

module Explanator2 = struct

  exception EXIT

  let check_ref = ref false
  let debug_ref = ref false
  let json_ref = ref false
  let mode_ref = ref ALL
  let out_mode_ref = ref PLAIN
  let measure_le_ref = ref None
  let fmla_ref = ref None
  let log_ref = ref stdin
  let out_ref = ref stdout
  let last_tp = ref 0

  let usage () =
    Format.eprintf
      "Usage: ./explanator2.exe [ARGUMENTS]
       Example: ./explanator2.exe -check -O size -fmla ex.mtl -log ex.log -out_mode plain
       Arguments:
       \t -check   - execute verified checker
       \t -mode
       \t\t all    - output both satisfaction and violation explanations (default)
       \t\t sat    - output only satisfaction explanations
       \t\t viol   - output only violation explanations
       \t -O (measure)
       \t\t size   - optimize proof size (default)
       \t\t high   - optimize highest time-point occuring in a proof (lower is better)
       \t\t pred   - optimize multiset cardinality of atomic predicates
       \t\t none   - give any proof
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
    raise EXIT

  let mode_error () =
    Format.eprintf "mode should be either \"sat\", \"viol\" or \"all\" (without quotes)\n%!";
    raise EXIT

  let out_mode_error () =
    Format.eprintf "out_mode should be either \"plain\", \"json\" or \"debug\" (without quotes)\n%!";
    raise EXIT

  let measure_error () =
    Format.eprintf "measure should be either \"size\", \"high\", \"pred\", or \"none\" (without quotes)\n%!";
    raise EXIT

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
           | "pred" | "PRED" | "Pred" -> predicates_le
           | "none" | "NONE" | "None" -> (fun _ _ -> true)
           | _ -> measure_error () in
         measure_le_ref :=
           (match !measure_le_ref with
            | None -> Some measure_le
            | Some measure_le' -> Some(prod measure_le measure_le'));
         go args
      | ("-Olex" :: measure :: args) ->
         let measure_le =
           match measure with
           | "size" | "SIZE" | "Size" -> size_le
           | "high" | "HIGH" | "High" -> high_le
           | "pred" | "PRED" | "Pred" -> predicates_le
           | "none" | "NONE" | "None" -> (fun _ _ -> true)
           | _ -> measure_error () in
         measure_le_ref :=
           (match !measure_le_ref with
            | None -> Some measure_le
            | Some measure_le' -> Some(lex measure_le measure_le'));
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
      | [] -> ()
      | _ -> usage () in
    go

  let _ =
    try
      process_args (List.tl (Array.to_list Sys.argv));
      match !fmla_ref with
      | None -> ()
      | Some(f) -> let measure_le =
                     match !measure_le_ref with
                     | None -> size_le
                     | Some measure_le' -> measure_le' in
                   let _ = monitor !log_ref !out_ref !mode_ref !out_mode_ref !check_ref measure_le f in ()
    with
    | End_of_file -> (if !out_mode_ref = PLAIN then
                        closing_stdout !out_ref);
                     close_out !out_ref; exit 0
    | EXIT -> close_out !out_ref; exit 1

end
