open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

(** [compile r ~py_source] translates an [Extraction.result] into an
    EnfFlash program (the IR consumed by the Rust enforcement engine).
    [py_source] is an optional path to a Python helper file for UDFs. *)
val compile :
  ?drop_monotone:bool ->
  py_source:string option ->
  Tnformula.t ->
  Enfflash.program

(** [compile_and_write r ~py_source ~filename] calls [compile] and
    additionally serialises the program to [filename] in EnfFlash text format. *)
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
      5. Compilation to EnfFlash IR (compile)
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
