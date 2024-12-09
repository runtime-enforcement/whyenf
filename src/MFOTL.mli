(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*           (see file LICENSE for more details)                   *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

open MFOTL_Base

module Filter : sig

  type t = An of string | AllOf of t list | OneOf of t list [@@deriving equal, compare, hash, sexp_of]

  val tt : t
  val ff : t

  val eval : Db.t -> t -> bool

  val to_string : t -> string

  val simplify : t -> t

  val conj : t -> t -> t
  val disj : t -> t -> t
  
end

module Make
  (Info : I)
  (Var  : V)
  (Dom  : D)
  (Term : MFOTL_Term.T with type v = Var.t) : sig

  type ('i, 'v, 'd, 't) _core_t =
    | TT
    | FF
    | EqConst of 't * 'd
    | Predicate of string * 't list
    | Predicate' of string * 't list * ('i, 'v, 'd, 't) _t
    | Let of string * Enftype.t option * 'v list * ('i, 'v, 'd, 't) _t * ('i, 'v, 'd, 't) _t
    | Let' of string * 'v list * ('i, 'v, 'd, 't) _t * ('i, 'v, 'd, 't) _t
    | Agg of 'v * Aggregation.op *  't * 'v list * ('i, 'v, 'd, 't) _t
    | Top of 'v list * string * 't list * 'v list * ('i, 'v, 'd, 't) _t
    | Neg of ('i, 'v, 'd, 't) _t
    | And of Side.t * ('i, 'v, 'd, 't) _t list
    | Or of Side.t * ('i, 'v, 'd, 't) _t list
    | Imp of Side.t * ('i, 'v, 'd, 't) _t * ('i, 'v, 'd, 't) _t
    | Exists of 'v * ('i, 'v, 'd, 't) _t
    | Forall of 'v * ('i, 'v, 'd, 't) _t
    | Prev of Interval.t * ('i, 'v, 'd, 't) _t
    | Next of Interval.t * ('i, 'v, 'd, 't) _t
    | Once of Interval.t * ('i, 'v, 'd, 't) _t
    | Eventually of Interval.t * ('i, 'v, 'd, 't) _t
    | Historically of Interval.t * ('i, 'v, 'd, 't) _t
    | Always of Interval.t * ('i, 'v, 'd, 't) _t
    | Since of Side.t * Interval.t * ('i, 'v, 'd, 't) _t * ('i, 'v, 'd, 't) _t
    | Until of Side.t * Interval.t * ('i, 'v, 'd, 't) _t * ('i, 'v, 'd, 't) _t
    | Type of ('i, 'v, 'd, 't) _t * Enftype.t
                                      [@@deriving compare, sexp_of, hash, equal]

  and ('i, 'v, 'd, 't) _t = { form : ('i, 'v, 'd, 't) _core_t; info : 'i}
                              [@@deriving compare, sexp_of, hash, equal]

  type core_t = (Info.t, Var.t, Dom.t, Term.t) _core_t [@@deriving compare, sexp_of, hash, equal]
  type t      = (Info.t, Var.t, Dom.t, Term.t) _t      [@@deriving compare, sexp_of, hash, equal]

  type typed_info = {
      info : Info.t;
      enftype : Enftype.t;
      filter : Filter.t;
      flag : bool
    } [@@deriving compare, sexp_of, hash, equal]

  module TypedInfo : MFOTL_Base.I with type t = typed_info

  type core_typed_t = (TypedInfo.t, Var.t, Dom.t, Term.t) _core_t
  type typed_t      = (TypedInfo.t, Var.t, Dom.t, Term.t) _t

  val map_info: f:('a -> 'b) -> ('a, Var.t, Dom.t, Term.t) _t -> ('b, Var.t, Dom.t, Term.t) _t
  val untyped: typed_t -> t

  val tt: core_t
  val ff: core_t
  val eqconst: Term.t -> Dom.t -> core_t
  val agg: Var.t -> Aggregation.op -> Term.t -> Var.t list -> t -> core_t
  val top: Var.t list -> string -> Term.t list -> Var.t list -> t -> core_t
  val predicate: string -> Term.t list -> core_t
  val flet: string -> Enftype.t option -> Var.t list -> t -> t -> core_t
  val neg: t -> core_t
  val conj: Side.t -> t -> t -> core_t
  val disj: Side.t -> t -> t -> core_t
  val conjs: Side.t -> t list -> core_t
  val disjs: Side.t -> t list -> core_t
  val imp: Side.t -> t -> t -> core_t
  val exists: Var.t -> t -> core_t
  val forall: Var.t -> t -> core_t
  val prev: Interval.t -> t -> core_t
  val next: Interval.t -> t -> core_t
  val once: Interval.t -> t -> core_t
  val eventually: Interval.t -> t -> core_t
  val historically: Interval.t -> t -> core_t
  val always: Interval.t -> t -> core_t
  val since: Side.t -> Interval.t -> t -> t -> core_t
  val until: Side.t -> Interval.t -> t -> t -> core_t
  val ftype: t -> Enftype.t -> core_t
  
  val exists_of_agg: Var.t list -> t -> (Var.t -> t -> Info.t) -> t

  val term: Term.t -> core_t
  val trigger: Side.t -> Interval.t -> t -> t -> Info.t -> Info.t -> Info.t -> core_t
  val release: Side.t -> Interval.t -> t -> t -> Info.t -> Info.t -> Info.t -> core_t
  val iff: Side.t -> Side.t -> t -> t -> Info.t -> Info.t -> core_t

  val make : core_t -> Info.t -> t 
  val make_dummy : core_t -> t

  val fv : ('i, Var.t, Dom.t, Term.t) _t -> (Var.t, Var.comparator_witness) Base.Set.t
  val fvs : ('i, Var.t, Dom.t, Term.t) _t list -> (Var.t, Var.comparator_witness) Base.Set.t
  val list_fv : t -> Var.t list
  val terms : ('i, Var.t, Dom.t, Term.t) _t -> (Term.t, Term.comparator_witness) Base.Set.t
  val deg : ('i, Var.t, Dom.t, Term.t) _t -> int
  val predicates : t -> (string * Term.t list) list

  val subst : (Var.t, Term.t, Var.comparator_witness) Base.Map.t -> t -> t

  val op_to_string : t -> string
  val to_string : t -> string
  val to_string_typed : typed_t -> string

  val convert_vars : t -> t
  val convert_lets : t -> t
  val unroll_let : t -> t
  val ac_simplify : t -> t

  val relative_interval : ?itl_itvs:(string, Zinterval.t, Base.String.comparator_witness) Base.Map.t -> t -> Zinterval.t
  val relative_intervals : ?itl_itvs:(string, Zinterval.t, Base.String.comparator_witness) Base.Map.t -> t list -> Zinterval.t
  val relative_past : ?itl_itvs:(string, Zinterval.t, Base.String.comparator_witness) Base.Map.t -> t -> bool
  val strict : ?itl_strict:(string, bool, Base.String.comparator_witness) Base.Map.t -> ?itv:Zinterval.t -> ?fut:bool -> t -> bool
  val stricts : ?itl_strict:(string, bool, Base.String.comparator_witness) Base.Map.t -> ?itv:Zinterval.t -> ?fut:bool -> t list -> bool

  module MFOTL_Enforceability (_ : MFOTL_Base.S) : sig

    val rank : t -> int

    val present_filter : ?b:bool -> t -> Filter.t

    module Errors : sig

      type error =
        | ECast of string * Enftype.t * Enftype.t
        | EFormula of string option * t * Enftype.t
        | EConj of error list
        | EDisj of error list
        | ERule of string [@@deriving equal]

      val to_string : ?n:int -> error -> string

    end
        
    module Constraints : sig

      type constr =
        | CTT
        | CFF
        | CGeq of string * Enftype.t
        | CLeq of string * Enftype.t
        | CConj of constr list
        | CDisj of constr list [@@deriving equal, compare, sexp_of]

      type verdict = Possible of constr | Impossible of Errors.error

      val conj : verdict -> verdict -> verdict
      val disj : verdict -> verdict -> verdict

      val conjs : verdict list -> verdict
      val disjs : verdict list -> verdict

      val solve : constr -> (string, Enftype.Constraint.t, String.comparator_witness) Map.t list

    end

    type pg_map = (Var.t, Etc.string_set_list, Var.comparator_witness) Map.t
    type t_map  = (string, Enftype.t * int list, String.comparator_witness) Map.t

    val solve_past_guarded : pg_map -> Var.t -> bool -> ('i, Var.t, Dom.t, Term.t) _t -> Etc.string_set_list
    val solve_past_guarded_multiple_vars : pg_map -> Var.t list -> string -> ('i, Var.t, Dom.t, Term.t) _t -> pg_map
    val solve_past_guarded_multiple : pg_map -> Var.t -> bool -> ('i, Var.t, Dom.t, Term.t) _t list -> Etc.string_set_list
    val is_past_guarded : ?ts:pg_map -> Var.t -> bool -> ('i, Var.t, Dom.t, Term.t) _t -> bool
    val is_past_guarded_multiple : ?ts:pg_map -> Var.t -> bool -> ('i, Var.t, Dom.t, Term.t) _t list -> bool
    val observable: ?itl_observable:(string, bool, String.comparator_witness) Map.t -> ('i, Var.t, Dom.t, Term.t) _t -> bool
    val observable_multiple: ?itl_observable:(string, bool, String.comparator_witness) Map.t -> ('i, Var.t, Dom.t, Term.t) _t list -> bool

    val types : ?itl_itvs:(string, Zinterval.t, String.comparator_witness) Map.t -> ?itl_strict:(string, bool, String.comparator_witness) Map.t -> ?itl_observable:(string, bool, String.comparator_witness) Map.t -> Enftype.t -> pg_map -> t -> Constraints.verdict
    val convert : Interval.v -> Enftype.t -> t -> typed_t option
    val do_type : t -> Time.Span.s -> typed_t
    val strictly_relative_past : ?itl_itvs:(string, Zinterval.t, String.comparator_witness) Map.t -> ?itl_strict:(string, bool, String.comparator_witness) Map.t -> ?itl_observable:(string, bool, String.comparator_witness) Map.t -> ('i, Var.t, Dom.t, Term.t) _t -> bool
    val is_transparent: typed_t -> bool

  end

end

