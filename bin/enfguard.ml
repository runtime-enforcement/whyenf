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
  let logstr_ref = ref ""

  let run debug forall monitoring log_file logstr sig_file formula_file func_file out_file json bound time_zone step statistics latex label simplify no_filter no_memo =
    if debug then Global.debug := true;
    if forall then Global.forall := true;
    if monitoring then Global.monitoring := true;
    if label then Global.label := true;
    if simplify then Global.simplify := true;
    if no_filter then Global.filter := false;
    if no_memo then Global.memo := false;
    (match log_file with
     | Some logf -> inc_ref := In_channel.create logf
     | None -> ());
    logstr_ref := Option.value logstr ~default:"";
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
    (match func_file with
     | Some f -> Funcs.Python.load f
     | None -> ());
    (match out_file with
     | Some outf -> outc_ref := Out_channel.create outf
     | None -> ());
    if json then Global.json := true;
    (match bound with
     | Some b -> b_ref := MFOTL_lib.Time.Span.of_string b
     | None -> ());
    (match time_zone with
     | Some tz ->
         let tz_setting = if String.(=) tz "local" then
                            CalendarLib.Time_Zone.Local
                          else
                            CalendarLib.Time_Zone.UTC_Plus (Int.of_string tz)
         in
         CalendarLib.Time_Zone.change tz_setting
     | None -> ());
    (match step with
     | Some s -> s_ref := MFOTL_lib.Time.Span.of_string s
     | None -> ());
    match !formula_ref with
    | Some sformula ->
       let _ =
         let xs = Set.elements (Sformula.fv sformula) in
         let sformula =
           if forall
           then Sformula.SExists (xs, sformula)
           else sformula in
         let formula = Formula.init sformula in
         let formula =
           if label
           then formula
           else Formula.erase_label formula in
         if statistics then
           Formula.print_statistics formula
         else if latex then
           Stdio.printf "%s\n" (Formula.to_latex formula)
         else
           Enforcer.exec formula
       in
         ()
    | None ->
        printf "Error: No valid formula provided.\n";
        exit 1

  let command =
    Command.basic
      ~summary:"EnfGuard: A tool for monitoring and enforcing MFOTL formulas"
      ~readme:(fun () -> "Processes log files against MFOTL formulas with various options.")
      (let%map_open.Command debug = flag "-debug" no_arg ~doc:" Enable debug mode"
       and forall = flag "-forall" no_arg ~doc:" Quantify free variables universally"
       and monitoring = flag "-monitoring" no_arg ~doc:" Monitoring mode"
       and log_file = flag "-log" (optional string) ~doc:"FILE Log file as trace (default: stdin)"
       and logstr = flag "-logstr" (optional string) ~doc:"STRING Log string"
       and sig_file = flag "-sig" (optional string) ~doc:"FILE Signature file"
       and formula_file = flag "-formula" (optional string) ~doc:"FILE MFOTL formula file"
       and func_file = flag "-func" (optional string) ~doc:"FILE Python file containing function definitions"
       and out_file = flag "-out" (optional string) ~doc:"FILE Output file (default: stdout)"
       and json = flag "-json" no_arg ~doc:" Enable JSON output"
       and bound = flag "-b" (optional string) ~doc:"INT[smhdMy] Default bound for future operators (default: 0)"
       and time_zone = flag "-tz" (optional string) ~doc:"local|INT Time zone (default: local, otherwise UTC+x)"
       and step = flag "-s" (optional string) ~doc:"INT[smhdMy] Enforcement step (default: 1s)"
       and statistics = flag "-statistics" no_arg ~doc:" Print statistics about the formula"
       and latex = flag "-latex" no_arg ~doc:" Print latex code of the formula"
       and label = flag "-label" no_arg ~doc:" Report labels of enforcement actions"
       and simplify = flag "-simplify" no_arg ~doc:" Simplify the formula"
       and no_filter = flag "-no-filter" no_arg ~doc:" Do not use filter optimization"
       and no_memo = flag "-no-memo" no_arg ~doc:" Do not use memo optimization"
       in
       fun () ->
       run debug forall monitoring log_file logstr sig_file formula_file func_file out_file json bound time_zone step statistics latex label simplify no_filter no_memo)

end

let () = Command_unix.run Enfguard.command
