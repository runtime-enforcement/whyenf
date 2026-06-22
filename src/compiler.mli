open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

(** [compile r ~py_source] translates an [Extraction.result] into an
    Enfflash program (the IR consumed by the Rust enforcement engine).
    [py_source] is an optional path to a Python helper file for UDFs. *)
val compile :
  ?drop_monotone:bool ->
  py_source:string option ->
  Tnformula.t ->
  Enfflash.program

(** [compile_and_write r ~py_source ~filename] calls [compile] and
    additionally serialises the program to [filename] in Enfflash text format. *)
val compile_and_write :
  filename:string ->
  py_source:string option ->
  Tnformula.t ->
  Enfflash.program

(** [run ~py_source ~b ?verbose ?moderate ~filename sformula] runs the full
    pipeline in sequence:
      1. Init + alpha conversion    (Formula.init, Formula.convert_vars)
      2. Basic term typing          (Tyformula.of_formula')
      3. Normalization + typing     (Enforceability.enforce — includes let-pulling)
      4. Extraction of a solution   (Extraction.extract)
      5. Compilation to Enfflash IR (compile)
      6. Linearization              (Enfflash.write_program_to_file → [filename])
    Returns the compiled [Enfflash.program]. *)
val run :
  py_source:string option ->
  b:Time.Span.s ->
  ?verbose:bool ->
  ?moderate:bool ->
  ?drop_monotone:bool ->
  filename:string ->
  Sformula.t ->
  Enfflash.program

(** Info about one compiled sub-group produced by [split_and_compile] /
    [run_parallel]. *)
type split_group_info = {
  sgi_program_file   : string;
  sgi_trigger_events : string list;
}

(** [run_parallel ~output_dir ~base_name sformula] runs the full pipeline,
    splits the extracted [Tnformula.t] using [Splitting.split], writes one
    [base_name_subN.ef] per group plus [base_name_manifest.json] into
    [output_dir], and returns [(manifest_path, group_infos)].

    [~filtered] enables CDG* (monotonicity-aware) edge filtering.
    [~aggressivity] controls the merge heuristic (0 = largest covering).
    [~num_groups] (> 0) overrides [aggressivity] and balances the components
    into at most that many clause-count-homogeneous groups.
    [~data_groups] is a list of [(field_name, num_buckets)] selections (e.g.
    [("Read.user", 2)]); each picks the data-split component containing that
    field and shards it into that many hash buckets. The manifest then contains
    (event groups × data shards) sub-enforcers, each running the same program on
    a data slice. When [data_groups] is non-empty and no event split is
    requested, the whole policy is kept as a single event group. *)
val run_parallel :
  ?filtered:bool ->
  ?aggressivity:int ->
  ?num_groups:int ->
  ?data_groups:(string * int) list ->
  py_source:string option ->
  b:Time.Span.s ->
  ?verbose:bool ->
  ?moderate:bool ->
  output_dir:string ->
  base_name:string ->
  Sformula.t ->
  string * split_group_info list

(** [analyze_data sformula] builds the base-event field-interaction graph
    (data-splitting analysis) and prints its connected components — the
    available data-parallel axes — and the un-partitionable (tainted)
    fields. Does not compile or enforce. *)
val analyze_data : Sformula.t -> unit

(** [edg_dot ~b sformula] runs the enforceability front-end and returns the
    Event Dependency Graph of the accepted policy as Graphviz DOT (one cluster
    per SCC). Prints a short SCC summary to stderr. *)
val edg_dot : ?moderate:bool -> b:Time.Span.s -> Sformula.t -> string

(** [edg_dir ~b sformula dir] writes a bundle into [dir]: the full graph
    ([edg.dot]), the focused condensation ([focus.dot]), one graph per recursive
    SCC ([scc_<k>.dot]), and the compiled enforcement program ([policy.ef]).
    Each [.dot] is also rendered to [.svg] via Graphviz [dot] when available. *)
val edg_dir :
  ?moderate:bool -> ?py_source:string option -> ?drop_monotone:bool ->
  b:Time.Span.s -> Sformula.t -> string -> unit
