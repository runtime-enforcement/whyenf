open Base
open MFOTL_lib
open Tyformula

module Var  : module type of Tterm.TypedVar
module Term : module type of Tterm

(** Result of extracting a single let-bound predicate. *)
type let_def = {
  le_name    : string;
  le_enftype : Enftype.t option;
  le_args    : (Tterm.TypedVar.t * Dom.tt option) list;
  le_body    : Tyformula.t;
  le_origin  : Tyformula.t;
}

val let_def_to_string: let_def -> string

(** Formula helpers. *)
val strip_exists    : Tyformula.t -> Tyformula.t
val add_back_exists : Tyformula.t -> Tterm.TypedVar.t list -> Tyformula.t list -> Tyformula.t

(** [do_pull_lets f] extracts all let-bound predicates from [f] and returns
    [(extractions, residual_formula)].  Each extraction records the name,
    optional enforcement type, arguments, simplified body, and original node. *)
val do_pull_lets : Tyformula.t -> let_def list * Tyformula.t

(** Phase 4 output type. *)
type t = {
  lets    : let_def list;
  formula : Tyformula.t;
  origin  : Tyformula.t;   (* original typed formula, before normalization *)
}

val to_string: t -> string

(** [normalize ?moderate f] runs the full normalization pipeline:
    push_negs → convert_vars → convert_lets → unroll_let → simplify →
    push_quants → do_pull_lets → ac_simplify.
    Input:  [Tyformula.t] (output of Phase 3, basic term typing).
    Output: [result] ready for Phase 5 (enforceability type checking). *)
val make : ?moderate:bool -> Tyformula.t -> t
