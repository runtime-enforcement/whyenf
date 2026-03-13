open Core
open Stdio
open Enfguard_lib
open Enfguard_lib.Global

module Enfguard = struct

  let lexbuf_error_msg (lexbuf: Lexing.lexbuf) =
    Printf.sprintf "a problem was found at line %d character %d"
      (lexbuf.lex_curr_p.pos_lnum) (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol)

  let formula_ref = ref None
  let sig_ref = ref In_channel.stdin

  let run debug enfflash sig_file formula_file =
    if debug then Global.debug := true;
    (match sig_file with
     | Some sf -> Other_parser.Sig.parse_from_channel sf
     | None -> ());
    (match formula_file with
     | Some f ->
         In_channel.with_file f ~f:(fun inc ->
           let lexbuf = Lexing.from_channel inc in
           formula_ref := (try Some (Formula_parser.formula Formula_lexer.token lexbuf)
                           with Formula_parser.Error ->
                             printf "%s\n" (lexbuf_error_msg lexbuf);
                             Out_channel.flush stdout;
                             None))
     | None -> ());
    match !formula_ref with
    | Some sformula ->
       let _ =
         let formula = Formula.init sformula in
         let open Tyformula.MFOTL_Enforceability(Sig) in
         let f = Formula.convert_vars formula in
         let f = Tyformula.of_formula' f in
         let f = do_type ~moderate:(not !Global.unroll_all) f !b_ref in
         printf "%s\n" (Tyformula.to_string_typed f)
       in
         ()
    | None ->
        printf "Error: No valid formula provided.\n";
        exit 1

  let command =
    Command.basic
      ~summary:"EnfFlash: A tool for monitoring and enforcing MFOTL formulas"
      (let%map_open.Command debug = flag "-debug" no_arg ~doc:" Enable debug mode"
       and enfflash = flag "-enfflash" no_arg ~doc:" Quantify free variables universally"
       and sig_file = flag "-sig" (optional string) ~doc:"FILE Signature file"
       and formula_file = flag "-formula" (optional string) ~doc:"FILE MFOTL formula file"
       in
       fun () ->
       run debug enfflash sig_file formula_file)

end

let () = Command_unix.run Enfguard.command
