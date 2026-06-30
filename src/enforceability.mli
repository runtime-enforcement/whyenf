(** Phase 5: enforceability type checking.

    Input:  [Normalize.result] — normalized formula with let-bound predicates extracted.
    Output: [typing_result]    — enforcement strategies before constraint solving.
*)

open Base
open MFOTL_lib
open Tyformula
open Nformula

module Var  : module type of Tterm.TypedVar
module Term : module type of Tterm



(** [enforce ?verbose norm b] runs enforceability type checking.
    Input:  [Normalize.result] (Phase 4 output).
    Output: [typing_result]    (Phase 6 input). *)
val enforce :
  ?verbose:bool ->
  Lformula.t -> Time.Span.s -> Nformula.t

(** [last_table_guard_warnings ()] returns the (table-name, body) pairs for the
    unbounded tables pulled as guards during the most recent [enforce] call.
    This is an over-approximation — it includes tables whose guard is only used
    to characterise filter-only let definitions and is therefore never scanned
    at run time.  Filter it against the compiled program's complexity before
    reporting to the user. *)
val last_table_guard_warnings : unit -> (string * string) list
