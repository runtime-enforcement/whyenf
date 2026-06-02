open Base
open MFOTL_lib
open Tyformula

module Var  : module type of Tterm.TypedVar
module Term : module type of Tterm

(** Formula rank (sum of predicate ranks weighted by their positions). *)
val rank : t -> int

(** Constraint system ------------------------------------------------------- *)

module Constraints : sig
  type constr =
    | CTT
    | CFF
    | CGeq of string * Enftype.t
    | CLeq of string * Enftype.t
    | CConj of constr list
    | CDisj of constr list [@@deriving equal, compare, sexp_of]

  val ac_simplify : constr -> constr
  val to_string   : constr -> string

  (** [solve c] returns the list of satisfying variable assignments. *)
  val solve :
    constr ->
    (string, Enftype.Constraint.t, String.comparator_witness) Map.t list
end

(** Enforcement solutions: a list of (clauses, constraint) pairs,
    or an error explaining why enforcement is impossible. *)
type enf_sols =
  (Normalize.clause list * Constraints.constr) Normalize.Verdict.v

(** Let definitions --------------------------------------------------------- *)

type let_def = {
  name              : string;
  args              : (Tterm.TypedVar.t * Dom.tt option) list;
  body              : t;
  cau_sols          : enf_sols;
  sup_sols          : enf_sols;
  switch_pos_opt    : Normalize.switch option;
  switch_neg_opt    : Normalize.switch option;
  filter_trigger_opt: Normalize.trigger option;
}

type let_map = (string, let_def, String.comparator_witness) Map.t

(** A compiled let binding ready for the Enfflash backend:
    [(name, enftype, args, body_pos, body_neg_opt, clauses_opt, filter_trigger_opt)] *)
type compiled_let =
  string
  * Enftype.t option
  * (Tterm.TypedVar.t * Dom.tt option) list
  * typed_t
  * typed_t option
  * Normalize.clause list option
  * Normalize.trigger option

(** Main entry points ------------------------------------------------------- *)

(** [do_type f b] enforceability-types formula [f] with right-bound [b].
    Returns the typed formula.  Raises [Errors.FormulaError] on failure. *)
val do_type :
  ?verbose:bool ->
  ?moderate:bool ->
  t -> Time.Span.s -> typed_t

(** [do_type_and_compile f b] additionally returns the intermediate
    enforcement data needed by the Enfflash compiler:
    [(compiled_lets, raw_clauses, let_map, typed_formula)] *)
val do_type_and_compile :
  ?verbose:bool ->
  ?moderate:bool ->
  t -> Time.Span.s ->
  compiled_let list * Normalize.clause list * let_map * typed_t
