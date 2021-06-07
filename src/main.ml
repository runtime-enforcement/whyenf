(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util
open Expl
open Mtl
open Channel
open Mtl_parser
open Mtl_lexer
open Monitor

exception EXIT

let full_ref = ref true
let mode_ref = ref ALL
let measure_ref = ref None
let fmla_ref = ref None
let log_ref = ref (Input stdin)
let out_ref = ref (Output stdout)

let usage () =
  Format.eprintf
    "Example usage: explanator2 -O size -mode sat -fmla test.fmla -log test.log -out test.out
     Arguments:
     \t -ap      - output only the \"responsible atomic proposition\" view
     \t -mode
     \t\t all    - output all satisfaction and violation proofs (default)
     \t\t sat    - output only satisfaction proofs 
     \t\t viol   - output only violation proofs
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
     \t\t <file> - output file where the explanation is printed to (default: stdout)\n%!";
  raise EXIT

let mode_error () =
  Format.eprintf "mode should be either \"sat\", \"viol\" or \"all\" (without quotes)\n%!";
  raise EXIT

let measure_error () =
  Format.eprintf "measure should be either \"size\", \"high\", \"pred\", or \"none\" (without quotes)\n%!";
  raise EXIT

let process_args =
  let rec go = function
    | ("-ap" :: args) ->
       full_ref := false;
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
       let measure =
         match measure with
         | "size" | "SIZE" | "Size" -> size_le
         | "high" | "HIGH" | "High" -> high_le
         | "pred" | "PRED" | "Pred" -> predicates_le
         | "none" | "NONE" | "None" -> (fun _ _ -> true)
         | _ -> measure_error () in
       measure_ref :=
         (match !measure_ref with
          | None -> Some measure
          | Some measure' -> Some(prod_le measure measure'));
       go args
    | ("-Olex" :: measure :: args) ->
       let measure =
         match measure with
         | "size" | "SIZE" | "Size" -> size_le
         | "high" | "HIGH" | "High" -> high_le
         | "pred" | "PRED" | "Pred" -> predicates_le
         | "none" | "NONE" | "None" -> (fun _ _ -> true)
         | _ -> measure_error () in
       measure_ref :=
         (match !measure_ref with
          | None -> Some measure
          | Some measure' -> Some(lex_le measure measure'));
       go args
    | ("-log" :: logfile :: args) ->
       log_ref := Input (open_in logfile);
       go args
    | ("-fmla" :: fmlafile :: args) ->
       (try
          let in_ch = open_in fmlafile in
          fmla_ref := Some(Mtl_parser.formula Mtl_lexer.token (Lexing.from_channel in_ch));
          close_in in_ch
        with
          _ -> fmla_ref := Some(Mtl_parser.formula Mtl_lexer.token (Lexing.from_string fmlafile)));
       go args
    | ("-out" :: outfile :: args) ->
       out_ref := Output (open_out outfile);
       go args
    | [] -> ()
    | _ -> usage () in
  go

let close out = match out with Output x | OutputDebug (_, x) -> close_out x | OutputMock x -> ()

let _ =
  try
    process_args (List.tl (Array.to_list Sys.argv));
    match !fmla_ref with
    | None -> ()
    | Some(f) -> let measure = match !measure_ref with
                   | None -> size_le
                   | Some measure' -> measure' in
                 let in_ch, out_ch, mode = !log_ref, !out_ref, !mode_ref in
                 if !full_ref then
                   let _ = monitor in_ch out_ch mode measure f in ()
                 else ()
  with
  | End_of_file -> let _ = Printf.fprintf stdout "Bye.\n" in close !out_ref; exit 0
  | EXIT -> close !out_ref; exit 1
