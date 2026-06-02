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

  (* Locate the enfflash binary: check relative to the executable's real
     location (resolving symlinks), then walk up from cwd, then fall back to PATH *)
  let find_enfflash () =
    (* Resolve the real directory of the running executable *)
    let exe_dir =
      try Filename.dirname (Core_unix.readlink "/proc/self/exe")
      with _ ->
        (* Fallback: resolve argv[0] against cwd *)
        let argv0 = (Sys.get_argv ()).(0) in
        if Filename.is_relative argv0 then
          Filename.dirname (Filename.concat (Sys_unix.getcwd ()) argv0)
        else
          Filename.dirname argv0
    in
    (* Walk up from a directory looking for enfflash/target/release/enfflash *)
    let rec try_parents dir depth =
      if depth > 5 then None
      else
        let candidate = Filename.concat (Filename.concat dir "enfflash/target/release") "enfflash" in
        match Sys_unix.file_exists candidate with
        | `Yes -> Some candidate
        | _ -> try_parents (Filename.dirname dir) (depth + 1)
    in
    (* 1. sibling of executable *)
    let sibling = Filename.concat exe_dir "enfflash" in
    match Sys_unix.file_exists sibling with
    | `Yes -> sibling
    | _ ->
      (* 2. walk up from exe_dir *)
      match try_parents exe_dir 0 with
      | Some p -> p
      | None ->
        (* 3. walk up from cwd *)
        match try_parents (Sys_unix.getcwd ()) 0 with
        | Some p -> p
        | None -> "enfflash" (* hope it's on PATH *)

  let run debug sig_file formula_file functions_file output_file no_run log_file
        label json stats (verbose : int) state_file =
    let run_enfflash = not no_run in
    if debug then Global.debug := true;
    if json then Global.json := true;
    (match sig_file with
     | Some sf -> Other_parser.Sig.parse_from_channel sf
     | None -> ());
    (match functions_file with
     | Some f -> Funcs.Python.load f
     | None -> ());
    let py_source = match functions_file with
      | Some f -> Some (In_channel.input_all (In_channel.create f))
      | None -> None in
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
         if stats then Formula.print_stats formula;
         let f = Formula.convert_vars formula in
         let f = Tyformula.of_formula' f in
         let lets, clauses, let_map, f = Enforceability.do_type_and_compile ~moderate:(not !Global.unroll_all) f !b_ref in
         let ef_file = match output_file with
           | Some filename ->
             ignore (Compiler.compile_and_write ~filename ~py_source ~let_map ~lets ~clauses);
             Some filename
           | None ->
             if run_enfflash then begin
               let tmp = Stdlib.Filename.temp_file "enfflash_" ".ef" in
               ignore (Compiler.compile_and_write ~filename:tmp ~py_source ~let_map ~lets ~clauses);
               Some tmp
             end else begin
               printf "%s\n" (Tyformula.to_string_typed f);
               None
             end
         in
         if run_enfflash then begin
           match ef_file with
           | Some ef ->
             let enfflash_bin = find_enfflash () in
             let args = [enfflash_bin; "--program"; ef]
               @ (match log_file with Some l -> ["--log"; l] | None -> [])
               @ (if label then ["--label"] else [])
               @ (if json then ["--json"] else [])
               @ (if verbose > 0 then ["--verbose"; string_of_int verbose] else [])
               @ (match state_file with Some s -> ["--state"; s] | None -> [])
             in
             eprintf "[enfguard] Running: %s\n" (String.concat ~sep:" " args);
             let argv = Array.of_list args in
             (* Replace current process with enfflash *)
             never_returns (Core_unix.exec ~prog:enfflash_bin ~argv:(Array.to_list argv) ())
           | None -> ()
         end
       in
         ()
    | None ->
        printf "Error: No valid formula provided.\n";
        exit 1

  let command =
    Command.basic
      ~summary:"EnfFlash: A tool for monitoring and enforcing MFOTL formulas"
      (let%map_open.Command debug = flag "-debug" no_arg ~doc:" Enable debug mode"
       and sig_file = flag "-sig" (optional string) ~doc:"FILE Signature file"
       and formula_file = flag "-formula" (optional string) ~doc:"FILE MFOTL formula file"
       and functions_file = flag "-func" (optional string) ~doc:"FILE Python file containing function definitions"
       and output_file = flag "-output" (optional string) ~doc:"FILE Enfflash file"
       and no_run = flag "-no-run" no_arg ~doc:" Only compile, do not run enfflash"
       and log_file = flag "-log" (optional string) ~doc:"FILE Log file (reads stdin if omitted)"
       and label = flag "-label" no_arg ~doc:" Print rule labels in enforcement output"
       and json = flag "-json" no_arg ~doc:" Output enforcement actions in JSON format"
       and stats = flag "-stats" no_arg ~doc:" Return statistics about the formula"
       and verbose = flag "-verbose" (optional_with_default 0 int) ~doc:"LEVEL Verbosity level (0=off, 1=basic, 2=full detail)"
       and state_file = flag "-state" (optional string) ~doc:"FILE State file for saving/restoring engine state"
       in
       fun () ->
       run debug sig_file formula_file functions_file output_file no_run log_file
         label json stats verbose state_file)

end

let () = Command_unix.run Enfguard.command
