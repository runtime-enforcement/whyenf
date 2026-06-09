open Base
open MFOTL_lib
open Tyformula

module Var  : module type of Tterm.TypedVar
module Term : module type of Tterm

(** Enforcement IR types (shared with Extraction and Compiler). *)

module Trigger : sig
  type t = { guards : Tyformula.t list list; filter : Tyformula.t } [@@deriving equal]
  val make       : Tyformula.t -> t
  val to_string  : t -> string
  val to_formula : bool -> t -> Tyformula.t
  val predicates :
    ?lets:(string, (string, String.comparator_witness) Set.t,
           String.comparator_witness) Map.t ->
    t -> (string, String.comparator_witness) Set.t
  val non_monotone_predicates :
    ?let_ctxt_mon:(string, (string, String.comparator_witness) Set.t,
                   String.comparator_witness) Map.t ->
    ?let_ctxt_anti_mon:(string, (string, String.comparator_witness) Set.t,
                        String.comparator_witness) Map.t ->
    t -> (string, String.comparator_witness) Set.t
       * (string, String.comparator_witness) Set.t
end

module Effect : sig
  type t =
    | Cau of string * Tterm.t list
    | Sup of string * Tterm.t list
    | EventuallyCau of Interval.t * string * Tterm.t list
    | EventuallySup of Interval.t * string * Tterm.t list
    | NextCau of Interval.t list * string * Tterm.t list
    | NextTT of Interval.t list
    | NextSup of Interval.t list * string * Tterm.t list
  val eventualize : Interval.t -> t -> t
  val nextize : Interval.t list -> t -> t
  val to_string : t -> string
  val to_typed : t -> typed_t
  val map_predicate : f:(bool -> string -> string) -> t -> t
  val fvs : t list -> (Var.t, Var.comparator_witness) Set.t
  val predicates : t -> (string, String.comparator_witness) Set.t
end

module Clause : sig
  type t = { trigger : Trigger.t; effects : Effect.t list }
  val to_string : t -> string
  val trigger_predicates :
    ?lets:(string, (string, String.comparator_witness) Set.t,
           String.comparator_witness) Map.t ->
    t -> (string, String.comparator_witness) Set.t
  val trigger_non_monotone_predicates :
    ?let_ctxt_mon:(string, (string, String.comparator_witness) Set.t,
                   String.comparator_witness) Map.t ->
    ?let_ctxt_anti_mon:(string, (string, String.comparator_witness) Set.t,
                        String.comparator_witness) Map.t ->
    t -> (string, String.comparator_witness) Set.t
       * (string, String.comparator_witness) Set.t
  val effect_predicates : t -> (string, String.comparator_witness) Set.t
  val predicates : t -> (string, String.comparator_witness) Set.t
end

module Switch : sig
  type t =
    | Once  of Trigger.t
    | Prev  of Trigger.t
    | Since of Trigger.t * Trigger.t
    | Now   of Trigger.t
  val to_string  : t -> string
  val to_formula : bool -> t -> Tyformula.t
end

module GuardInfo : sig
  type t = {
    switch_pos_opt : Switch.t option;
    body_str       : string;
  }
  type map = (string, t, String.comparator_witness) Map.t
end

module Verdict : module type of Verdict.Make(Tyformula)

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
  val solve :
    constr ->
    (string, Enftype.Constraint.t, String.comparator_witness) Map.t list
  val try_merge :
    (string, Enftype.Constraint.t, String.comparator_witness) Map.t *
    (string, Enftype.Constraint.t, String.comparator_witness) Map.t ->
    (string, Enftype.Constraint.t, String.comparator_witness) Map.t option
end
    
type enf_sols = (Clause.t list * Constraints.constr) Verdict.v

type let_def = {
  name               : string;
  enftype_opt        : Enftype.t option;
  args               : (Tterm.TypedVar.t * Dom.tt option) list;
  body               : t;
  origin             : t;
  cau_sols           : enf_sols;
  sup_sols           : enf_sols;
  switch_pos_opt     : Switch.t option;
  switch_neg_opt     : Switch.t option;
  filter_trigger_opt : Trigger.t option;
}

type let_map = (string, let_def, String.comparator_witness) Map.t

type t = {
  let_names : string list;
  let_map   : let_map;
  sols      : enf_sols;
}


