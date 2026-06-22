open Base
open MFOTL_lib
open Tyformula
open Nformula

(** Phase 6: constraint solving and enforcement strategy selection.

    Takes an {!Enforceability.typing_result} and produces concrete
    Enfflash-ready artifacts by:

    1. Solving the constraint system to pick an enforcement strategy.
    2. Compiling each let body to a pair of typed formulas (positive and,
       if needed, negative polarity).
    3. Collecting all enforcement clauses.
    4. Assembling the final typed formula with let bindings.

    The output {!result} feeds directly into {!Compiler.compile}.
*)

(** Phase 6: solve constraints and select an enforcement strategy.
    Raises [Errors.FormulaError] if no satisfying constraint assignment exists. *)
val extract : ?orig:Tyformula.t -> Nformula.t -> Tnformula.t

(** Phases 5+6: enforceability type inference then solution extraction. *)
val do_type_and_extract :
  ?verbose:bool ->
  ?moderate:bool ->
  Tyformula.t -> Time.Span.s -> Tnformula.t
