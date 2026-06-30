open Core
open Stdio
open Enfflash_lib
open Enfflash_lib.Global

module Enfflash = struct

  let lexbuf_error_msg (lexbuf: Lexing.lexbuf) =
    Printf.sprintf "a problem was found at line %d character %d"
      (lexbuf.lex_curr_p.pos_lnum) (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol)

  let formula_ref = ref None
  let sig_ref = ref In_channel.stdin

  (* Find a binary by name: check sibling of this executable, then walk up
     the directory tree looking for enfflash/target/release/<name>, then
     fall back to PATH. *)
  let find_binary name =
    let exe_dir =
      try Filename.dirname (Core_unix.readlink "/proc/self/exe")
      with _ ->
        let argv0 = (Sys.get_argv ()).(0) in
        if Filename.is_relative argv0 then
          Filename.dirname (Filename.concat (Sys_unix.getcwd ()) argv0)
        else
          Filename.dirname argv0
    in
    let rec try_parents dir depth =
      if depth > 5 then None
      else
        let candidate =
          Filename.concat (Filename.concat dir "enfflash/target/release") name in
        match Sys_unix.file_exists candidate with
        | `Yes -> Some candidate
        | _    -> try_parents (Filename.dirname dir) (depth + 1)
    in
    let sibling = Filename.concat exe_dir name in
    match Sys_unix.file_exists sibling with
    | `Yes -> sibling
    | _ ->
      match try_parents exe_dir 0 with
      | Some p -> p
      | None ->
        match try_parents (Sys_unix.getcwd ()) 0 with
        | Some p -> p
        | None   -> name   (* hope it is on PATH *)

  let find_enfflash ()          = find_binary "enfflash"
  let find_enfflash_parallel () = find_binary "enfflash-parallel"

  (* Strip a trailing .ef extension if present, return the basename. *)
  let base_name_of_path p =
    let bn = Filename.basename p in
    if String.is_suffix bn ~suffix:".ef"
    then String.drop_suffix bn 3
    else bn

  (* Parse a "-data-groups" spec: comma-separated "Event.field:N" entries. *)
  let parse_data_groups (s : string) : (string * int) list =
    String.split s ~on:','
    |> List.filter_map ~f:(fun entry ->
        let entry = String.strip entry in
        if String.is_empty entry then None
        else match String.rsplit2 entry ~on:':' with
          | Some (field, n) ->
            (match Option.try_with (fun () -> Int.of_string (String.strip n)) with
             | Some k -> Some (String.strip field, k)
             | None -> failwith (Printf.sprintf "invalid bucket count in '%s'" entry))
          | None -> failwith (Printf.sprintf "malformed -data-groups entry '%s' (expected Event.field:N)" entry))

  let run debug sig_file formula_file functions_file output_file no_run log_file
        label json stats (verbose : int) state_file
        parallel filtered (aggressivity : int) (num_groups : int) data_analyze data_groups_spec
        edg_dot_file edg_dir drop_monotone complexity =
    let run_enfflash = not no_run in
    if debug then Global.debug := true;
    if json  then Global.json  := true;
    (match sig_file with
     | Some sf -> Other_parser.Sig.parse_from_channel sf
     | None    -> ());
    (match functions_file with
     | Some f -> Funcs.Python.load f
     | None   -> ());
    let py_source = match functions_file with
      | Some f -> Some (In_channel.input_all (In_channel.create f))
      | None   -> None in
    (match formula_file with
     | Some f ->
       In_channel.with_file f ~f:(fun inc ->
         let lexbuf = Lexing.from_channel inc in
         formula_ref :=
           (try Some (Formula_parser.formula Formula_lexer.token lexbuf)
            with Formula_parser.Error ->
              printf "%s\n" (lexbuf_error_msg lexbuf);
              Out_channel.flush stdout;
              None))
     | None -> ());
    match !formula_ref with
    | None ->
      printf "Error: No valid formula provided.\n";
      exit 1
    | Some sformula ->
      if stats then Formula.print_stats (Formula.init sformula);
      if complexity then begin
        (* Compile the policy and print only its estimated per-time-point
           complexity (the .ef itself is discarded). *)
        let tmp = Stdlib.Filename.temp_file "enfflash_" ".ef" in
        let program =
          Compiler.run ~py_source ~b:!b_ref ~verbose:false ~drop_monotone
            ~moderate:(not !Global.unroll_all) ~filename:tmp sformula in
        (try Stdlib.Sys.remove tmp with _ -> ());
        Stdio.print_endline (Enfflash.program_complexity_to_string program);
        let defs = Enfflash.relevant_definitions_to_string program in
        if not (String.is_empty defs) then begin
          Stdio.print_endline "\n── Relevant definitions (what each |·| accumulates, with dependencies unfolded) ──\n";
          Stdio.print_endline defs
        end
      end
      else if data_analyze then
        Compiler.analyze_data sformula
      else if Option.is_some edg_dir then
        Compiler.edg_dir ~py_source ~drop_monotone ~b:!b_ref sformula (Option.value_exn edg_dir)
      else if Option.is_some edg_dot_file then begin
        let path = Option.value_exn edg_dot_file in
        Out_channel.write_all path ~data:(Compiler.edg_dot ~b:!b_ref sformula);
        eprintf "[enfflash] EDG written to %s\n" path
      end
      else if parallel then begin
        (* ── Parallel path ───────────────────────────────────────────── *)
        let output_dir, base =
          match output_file with
          | Some f -> Filename.dirname f, base_name_of_path f
          | None   ->
            let tmp = Core_unix.mkdtemp "enfflash_parallel_" in
            tmp, "policy"
        in
        let data_groups =
          match data_groups_spec with Some s -> parse_data_groups s | None -> [] in
        let manifest, _groups =
          Compiler.run_parallel
            ~filtered ~aggressivity ~num_groups ~data_groups ~py_source
            ~b:!b_ref ~moderate:(not !Global.unroll_all)
            ~output_dir ~base_name:base
            sformula
        in
        eprintf "[enfflash] Manifest written to %s\n" manifest;
        if run_enfflash then begin
          let bin  = find_enfflash_parallel () in
          let args =
            [ bin; "--manifest"; manifest ]
            @ (match log_file with Some l -> ["--log"; l] | None -> [])
            @ (if json then ["--json"] else [])
            @ (match state_file with Some s -> ["--state"; s] | None -> [])
          in
          eprintf "[enfflash] Running: %s\n" (String.concat ~sep:" " args);
          never_returns (Core_unix.exec ~prog:bin ~argv:args ())
        end
      end else begin
        (* ── Single-enforcer path (original) ─────────────────────────── *)
        let ef_file =
          match output_file with
          | Some filename ->
            ignore (Compiler.run ~py_source ~b:!b_ref ~drop_monotone
                      ~moderate:(not !Global.unroll_all)
                      ~filename sformula);
            Some filename
          | None ->
            if run_enfflash then begin
              let tmp = Stdlib.Filename.temp_file "enfflash_" ".ef" in
              ignore (Compiler.run ~py_source ~b:!b_ref ~drop_monotone
                        ~moderate:(not !Global.unroll_all)
                        ~filename:tmp sformula);
              Some tmp
            end else begin
              let r =
                Extraction.do_type_and_extract
                  ~moderate:(not !Global.unroll_all)
                  (Tyformula.of_formula'
                     (Formula.convert_vars (Formula.init sformula)))
                  !b_ref in
              printf "%s\n" (Tyformula.to_string_typed r.Tnformula.formula);
              None
            end
        in
        if run_enfflash then
          match ef_file with
          | Some ef ->
            let bin  = find_enfflash () in
            let args =
              [ bin; "--program"; ef ]
              @ (match log_file with Some l -> ["--log"; l] | None -> [])
              @ (if label   then ["--label"]                        else [])
              @ (if json    then ["--json"]                         else [])
              @ (if verbose > 0 then ["--verbose"; string_of_int verbose] else [])
              @ (match state_file with Some s -> ["--state"; s] | None -> [])
            in
            if verbose > 0 then
              eprintf "[enfflash] Running: %s\n" (String.concat ~sep:" " args);
            never_returns (Core_unix.exec ~prog:bin ~argv:args ())
          | None -> ()
      end

  let command =
    Command.basic
      ~summary:"Enfflash: compile and run MFOTL enforcement policies"
      (let%map_open.Command
         debug        = flag "-debug"       no_arg               ~doc:" Enable debug mode"
       and sig_file   = flag "-sig"         (optional string)    ~doc:"FILE Signature file"
       and formula_file = flag "-formula"   (optional string)    ~doc:"FILE MFOTL formula file"
       and functions_file = flag "-func"    (optional string)    ~doc:"FILE Python file with function definitions"
       and output_file = flag "-output"     (optional string)    ~doc:"FILE Output .ef file (single) or base path (parallel)"
       and no_run     = flag "-no-run"      no_arg               ~doc:" Compile only; do not launch enforcer"
       and log_file   = flag "-log"         (optional string)    ~doc:"FILE Log file (reads stdin if omitted)"
       and label      = flag "-label"       no_arg               ~doc:" Print rule labels in enforcement output"
       and json       = flag "-json"        no_arg               ~doc:" Output enforcement actions in JSON format"
       and stats      = flag "-stats"       no_arg               ~doc:" Print formula statistics"
       and verbose    = flag "-verbose"     (optional_with_default 0 int)
                          ~doc:"LEVEL Verbosity level (0=off, 1=basic, 2=full)"
       and state_file = flag "-state"       (optional string)    ~doc:"FILE State file for save/restore"
       and parallel   = flag "-parallel"    no_arg
                          ~doc:" Split the policy and run one enforcer per group in parallel"
       and filtered   = flag "-filtered"    no_arg
                          ~doc:" Use monotonicity-aware CDG* edge filtering when splitting"
       and aggressivity = flag "-aggressivity" (optional_with_default 0 int)
                          ~doc:"N Merge heuristic aggressivity (0 = largest covering, k = merge batches of k)"
       and num_groups = flag "-num-groups" (optional_with_default 0 int)
                          ~doc:"K Balance components into at most K clause-homogeneous groups (overrides -aggressivity)"
       and data_analyze = flag "-data-analyze" no_arg
                          ~doc:" Print the data-split field-interaction components (analysis only) and exit"
       and data_groups = flag "-data-groups" (optional string)
                          ~doc:"SPEC Data-split selections, e.g. \"Read.user:2,Read.activity:3\" (with -parallel)"
       and edg_dot = flag "-edg-dot" (optional string)
                          ~doc:"FILE Write the Event Dependency Graph (SCC-clustered) as Graphviz DOT and exit"
       and edg_dir = flag "-edg-dir" (optional string)
                          ~doc:"DIR Write full + focused + per-SCC EDG graphs (DOT, rendered to SVG if graphviz present) into DIR and exit"
       and drop_monotone = flag "-drop-monotone-deps" no_arg
                          ~doc:" Drop monotone-harmless dependency edges (CDG* filtering) from the rule graph: fewer/smaller fixpoint sections, more parallelism, at the cost of transparency"
       and complexity = flag "-complexity" no_arg
                          ~doc:" Print the estimated per-time-point complexity of the compiled policy and exit"
       in
       fun () ->
         (* Library-level errors carry a human-readable explanation that the
            producing code has already printed (e.g. the "The formula ... is not
            enforceable: ..." block).  Catch them here so the process exits with a
            non-zero status without dumping an OCaml stack trace. *)
         try
           run debug sig_file formula_file functions_file output_file no_run log_file
             label json stats verbose state_file
             parallel filtered aggressivity num_groups data_analyze data_groups
             edg_dot edg_dir drop_monotone complexity
         with
         | Errors.FormulaError _ ->
           (* Detailed, formula-specific message already printed above. *)
           Stdlib.exit 1
         | Errors.TermError m | Errors.FunctionError m | Errors.MonitoringError m
         | Errors.EnforcementError m | Errors.SigError m | Errors.LogError m
         | Errors.InternalError m ->
           printf "%s\n" m;
           Stdlib.exit 1)

end

let () = Command_unix.run Enfflash.command
