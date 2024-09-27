(*******************************************************************)
(*     This is part of WhyEnf, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Base
open Stdio
open Monitor_lib

(* TODO: This module must be rewritten using the Command module from Core *)
module Whyenf = struct

  let formula_ref = ref None
  let sig_ref = ref In_channel.stdin
  let logstr_ref = ref ""
  let b_ref = ref Time.Span.zero

  let n_args = ref 0

  let usage () =
    Caml.Format.eprintf
      "usage: ./whyenf.exe [-sig] [-formula] [-func] [-log] [-out] [-b]
       arguments:
       \t -sig
       \t\t <file>             - signature
       \t -formula
       \t\t <file> or <string> - MFOTL formula
       \t -func
       \t\t <file>             - Python file containing function definitions
       \t -log
       \t\t <file>             - specify log file as trace (default: stdin)
       \t -out
       \t\t <file>             - output file (default: stdout)
       \t -b int                     - default bound for future operators (default: 0)\n%!";
    exit 0

  let process_args =
    let rec process_args_rec = function
      | ("-debug" :: args) ->
         Etc.debug := true;
         process_args_rec args
      | ("-log" :: logf :: args) ->
         Etc.inc_ref := In_channel.create logf;
         process_args_rec args
      | ("-logstr" :: logs :: args) ->
         logstr_ref := logs;
         process_args_rec args
      | ("-sig" :: sf :: args) ->
         n_args := !n_args + 1;
         Other_parser.Sig.parse_from_channel sf;
         process_args_rec args
      | ("-formula" :: f :: args) ->
         n_args := !n_args + 1;
         In_channel.with_file f ~f:(fun inc ->
             let lexbuf = Lexing.from_channel inc in
             formula_ref := try Some (Formula_parser.formula Formula_lexer.token lexbuf)
                            with Formula_parser.Error as e ->
                              Stdio.printf "%s\n" (Etc.lexbuf_error_msg lexbuf);
                              Stdlib.flush_all (); None);
         process_args_rec args
      | ("-func":: f :: args) ->
         n_args := !n_args + 1;
         Funcs.Python.load f
      | ("-out" :: outf :: args) ->
         Etc.outc_ref := Out_channel.create outf;
         process_args_rec args
      | ("-b" :: bound :: args) ->
         b_ref := Time.Span.of_string bound;
         process_args_rec args
      | [] -> if !n_args >= 2 then () else usage ()
      | _ -> usage () in
    process_args_rec

  let _ =
    try
      process_args (List.tl_exn (Array.to_list Sys.argv));
      let formula = Option.value_exn !formula_ref in
      let (module CI: Checker_interface.Checker_interfaceT) =
        (module Checker_interface.LightChecker_interface) in
      let module Enforcer = Enforcer.Make (CI) in
      let _ = Enforcer.exec formula !Etc.inc_ref !b_ref in ()
    with End_of_file -> Out_channel.close !Etc.outc_ref; exit 0

end
