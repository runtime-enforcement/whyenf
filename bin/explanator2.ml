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
open Stdio
open Mfotl

(* TODO: This module must be rewritten using the Command module from Core *)
module Explanator2 = struct

  let mode_ref = ref Io.Stdout.UNVERIFIED
  let measure_ref = ref ""
  let formula_ref = ref None
  let trace_ref = ref In_channel.stdin
  let sig_ref = ref In_channel.stdin
  let outc_ref = ref Out_channel.stdout

  let n_args = ref 0

  let usage () =
    Caml.Format.eprintf
      "usage: ./explanator2.exe [-mode] [-measure] [-sig] [-formula] [-log] [-out]
       arguments:
       \t -mode
       \t\t unverified         - (default)
       \t\t verified           - check output with formally verified checker
       \t -measure
       \t\t size               - optimize proof size (default)
       \t\t none               - pick any proof
       \t -sig
       \t\t <file>             - signature
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
            | "debug" -> Etc.debug := true; Io.Stdout.DEBUG
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
         trace_ref := In_channel.create logf;
         process_args_rec args
      | ("-sig" :: sf :: args) ->
         n_args := !n_args + 1;
         Other_parser.Sig.parse sf;
         process_args_rec args
      | ("-formula" :: f :: args) ->
         n_args := !n_args + 1;
         In_channel.with_file f ~f:(fun inc ->
             let lexbuf = Lexing.from_channel inc in
             formula_ref := try Some(Formula_parser.formula Formula_lexer.token lexbuf)
                            with Formula_parser.Error -> Stdio.printf "%s\n" (Etc.lexbuf_error_msg lexbuf); None);
         process_args_rec args
      | ("-out" :: outf :: args) ->
         outc_ref := Out_channel.create outf;
         process_args_rec args
      | [] -> if !n_args >= 2 then () else usage ()
      | _ -> usage () in
    process_args_rec

  let _ =
    try
      process_args (List.tl_exn (Array.to_list Sys.argv));
      let formula = Option.value_exn !formula_ref in
      Monitor.exec !mode_ref !measure_ref formula !trace_ref
    with
    | Invalid_argument _ -> Out_channel.close !outc_ref; exit 1
    | End_of_file -> Out_channel.close !outc_ref; exit 0

end
