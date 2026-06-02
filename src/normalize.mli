open Base
open MFOTL_lib
open Tyformula

module Var  : module type of Tterm.TypedVar
module Term : module type of Tterm

(** Shared enforcement types ------------------------------------------------ *)

type trigger = {
  guards : t list list;  (** DNF of guard conjuncts *)
  filter : t;
} [@@deriving equal]

type clause = {
  trigger : trigger;
  effects : t list;
}

type switch =
  | SOnce  of trigger
  | SPrev  of trigger
  | SSince of trigger * trigger
  | SNow   of trigger

(** Adapter used by [pull_guard]: only the fields it needs from [let_def]. *)
type let_guard_info = {
  switch_pos_opt : switch option;
  body_str       : string;
}
type guard_map = (string, let_guard_info, String.comparator_witness) Map.t

(** Verdict monad (success / failure + error messages) --------------------- *)

module Verdict : module type of Verdict.Make(Tyformula)

(** Trigger helpers --------------------------------------------------------- *)

val trigger_to_string : trigger -> string
val of_trigger        : bool -> trigger -> t
val init_trigger      : t -> trigger
val of_switch         : bool -> switch -> t

(** Formula helpers --------------------------------------------------------- *)

val strip_exists     : t -> t
val add_back_exists  : t -> Tterm.TypedVar.t list -> t list -> t

(** Enforcement-specific let-extraction.
    Returns [(lets, residual_formula)] where each let entry is
    [(name, enftype_opt, args, body)]. *)
val do_pull_lets :
  t ->
  (string * Enftype.t option * (Tterm.TypedVar.t * Dom.tt option) list * t) list
  * t

(** Monotonicity analysis on triggers. *)
val non_monotone_predicates_of_trigger :
  let_ctxt_mon:(string, (string, String.comparator_witness) Set.t,
                String.comparator_witness) Map.t ->
  let_ctxt_anti_mon:(string, (string, String.comparator_witness) Set.t,
                     String.comparator_witness) Map.t ->
  bool ->
  trigger ->
  (string, String.comparator_witness) Set.t *
  (string, String.comparator_witness) Set.t

(** Two-tier guard control flags. *)
val allow_table_guards   : bool ref
val table_guard_warnings : (string * string) list ref

(** Guardedness checking ---------------------------------------------------- *)

(** [pull_guard m x p trig] tries to find (or widen) a guard for variable [x]
    in trigger [trig] under polarity [p].  Returns [None] if impossible. *)
val pull_guard :
  guard_map -> Tterm.TypedVar.t -> bool -> trigger -> trigger option

(** [normalize_trigger ?vars m trig p orig] ensures every variable in [vars]
    (default: all free variables of the trigger) is guarded.
    Returns [Verdict.Impossible _] if any variable cannot be guarded. *)
val normalize_trigger :
  ?vars:Tterm.TypedVar.t list option ->
  guard_map -> trigger -> bool -> t ->
  trigger Verdict.v

(** Best-effort version: skips variables that cannot be guarded rather than
    failing. *)
val normalize_trigger_best_effort :
  ?vars:Tterm.TypedVar.t list option ->
  guard_map -> trigger -> bool -> t ->
  trigger

(** Predicate maps for a list of let definitions.
    Returns [(pred_map, mon_map, anti_mon_map)]. *)
val maps_of_lets :
  (string * 'a * 'b * t) list ->
  (string, (string, String.comparator_witness) Set.t, String.comparator_witness) Map.t *
  (string, (string, String.comparator_witness) Set.t, String.comparator_witness) Map.t *
  (string, (string, String.comparator_witness) Set.t, String.comparator_witness) Map.t
