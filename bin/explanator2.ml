(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Mfotl

(* TODO: This module must be rewritten using the Command module from Core *)
module Explanator2 = struct

  let mode_ref = ref Io.Stdout.UNVERIFIED
  let measure_ref = ref ""
  let formula_ref = ref None
  let trace_ref = ref Stdio.In_channel.stdin
  let outc_ref = ref Stdio.Out_channel.stdout

  let usage () =
    Caml.Format.eprintf
      "usage: ./explanator2.exe [-mode] [-measure] [-formula] [-log] [-out]
       arguments:
       \t -mode
       \t\t unverified         - (default)
       \t\t verified           - check output with formally verified checker
       \t -measure
       \t\t size               - optimize proof size (default)
       \t\t none               - pick any proof
       \t -formula
       \t\t <file> or <string> - MFOTL formula
       \t -log
       \t\t <file>             - specify log file as trace (default: stdin)
       \t -out
       \t\t <file>             - output file (default: stdout)\n%!";
    exit 0

  let mode_error () =
    Caml.Format.eprintf "modes: unverified, verified or debug\n%!";
    raise (Invalid_argument "undefined mode")

  let measure_error () =
    Caml.Format.eprintf "measures: size and none\n%!";
    raise (Invalid_argument "undefined measure")

  let process_args =
    let rec process_args_rec = function
      | ("-mode" :: m :: args) ->
         mode_ref :=
           (match m with
            | "unverified" -> Io.Stdout.UNVERIFIED
            | "verified" -> Io.Stdout.VERIFIED
            | "debug" -> Io.Stdout.DEBUG
            | _ -> mode_error ());
         process_args_rec args
      | ("-measure" :: m :: args) ->
         measure_ref :=
           (match m with
            | "size" -> m
            | "none" -> m
            | _ -> measure_error ());
         process_args_rec args
      | ("-log" :: logf :: args) ->
         trace_ref := open_in logf;
         process_args_rec args
      | ("-formula" :: f :: args) ->
         (try
            let inc = open_in f in
            formula_ref := Some(Formula_parser.formula Formula_lexer.token (Lexing.from_channel inc));
            close_in inc
          with _ -> formula_ref := Some(Formula_parser.formula Formula_lexer.token (Lexing.from_string f)));
         process_args_rec args
      | ("-out" :: outf :: args) ->
         outc_ref := open_out outf;
         process_args_rec args
      | _ -> usage () in process_args_rec

  let _ =
    try
      process_args (List.tl_exn (Array.to_list Sys.argv));
      let formula = Option.value !formula_ref in ()
    with
    | Invalid_argument _ -> Stdio.Out_channel.close !outc_ref; exit 1
    | End_of_file -> Stdio.Out_channel.close !outc_ref; exit 0

end
