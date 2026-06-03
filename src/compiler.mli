open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

(** [compile r ~py_source] translates an [Extraction.result] into an
    Enfflash program (the IR consumed by the Rust enforcement engine).
    [py_source] is an optional path to a Python helper file for UDFs. *)
val compile :
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
  filename:string ->
  Sformula.t ->
  Enfflash.program
(** [run] orchestrates all 8 pipeline phases in sequence:
    1. Init + alpha conversion  (Formula.init, Formula.convert_vars)
    2. Basic term typing        (Tyformula.of_formula')
    3. Normalization            (Normalize.normalize)
    4. Enforceability typing    (Enforceability.enforce)
    5. Extraction of solution   (Extraction.extract)
    6. Compilation to IR        (compile)
    7. Linearization            (Enfflash.write_program_to_file → [filename]) *)
