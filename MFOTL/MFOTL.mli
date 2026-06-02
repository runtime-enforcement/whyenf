open Base

open Modules

module Make
  (Info : I)
  (Var  : V)
  (Dom  : D)
  (Term : Term.T with type v = Var.t and type d = Dom.t) : sig

  type ('i, 'v, 'd, 't) _core_t =
    | TT
    | FF
    | EqConst of 't * 'd
    | Predicate of string * 't list
    | Predicate' of string * 't list * ('i, 'v, 'd, 't) _t
    | Let of string * Enftype.t * ('v * Dom.tt option) list * ('i, 'v, 'd, 't) _t * ('i, 'v, 'd, 't) _t
    | Let' of string * Enftype.t * ('v * Dom.tt option) list * ('i, 'v, 'd, 't) _t * ('i, 'v, 'd, 't) _t
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
    | Label of string * ('i, 'v, 'd, 't) _t
                          [@@deriving compare, sexp_of, hash, equal]

  and ('i, 'v, 'd, 't) _t = { form : ('i, 'v, 'd, 't) _core_t; info : 'i}
                              [@@deriving compare, sexp_of, hash, equal]

  type core_t = (Info.t, Var.t, Dom.t, Term.t) _core_t [@@deriving compare, sexp_of, hash, equal]
  type t      = (Info.t, Var.t, Dom.t, Term.t) _t      [@@deriving compare, sexp_of, hash, equal]

  val core_equal : t -> t -> bool

  type typed_info = {
      info : Info.t;
      enftype : Enftype.t;
      filter : Filter.t;
      flag : bool;
      tabular: bool;
    } [@@deriving compare, sexp_of, hash, equal]

  module TypedInfo : Modules.I with type t = typed_info

  type core_typed_t = (TypedInfo.t, Var.t, Dom.t, Term.t) _core_t
  type typed_t      = (TypedInfo.t, Var.t, Dom.t, Term.t) _t

  val map_info: f:('a -> 'b) -> ('a, Var.t, Dom.t, Term.t) _t -> ('b, Var.t, Dom.t, Term.t) _t
  val untyped: typed_t -> t

  val tt: core_t
  val ff: core_t
  val eqconst: Term.t -> Dom.t -> core_t
  val agg: Var.t -> Aggregation.op -> Term.t -> Var.t list -> t -> core_t
  val assign: Var.t -> Term.t -> t -> core_t
  val top: Var.t list -> string -> Term.t list -> Var.t list -> t -> core_t
  val predicate: string -> Term.t list -> core_t
  val flet: string -> Enftype.t option -> (Var.t * Dom.tt option) list -> t -> t -> core_t
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
  val label: string -> t -> core_t
  
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
  val size : ('i, Var.t, Dom.t, Term.t) _t -> int
  val height : ('i, Var.t, Dom.t, Term.t) _t -> int
  val print_stats : ('i, Var.t, Dom.t, Term.t) _t -> unit
  val exists_subformula :
    f_term:(Term.t -> bool) -> f_fun:(('i, Var.t, Dom.t, Term.t) _t -> bool) -> ('i, Var.t, Dom.t, Term.t) _t -> bool
  val predicates :
    ?lets:((string, (string, String.comparator_witness) Set.t, String.comparator_witness) Map.t) ->
    ('i, Var.t, Dom.t, Term.t) _t -> (string, String.comparator_witness) Set.t


  val subst : (Var.t, Term.t, Var.comparator_witness) Base.Map.t -> t -> t
  val map_predicate : f:(bool -> string -> string) -> ?pol:bool -> ('i, Var.t, Dom.t, Term.t) _t -> ('i, Var.t, Dom.t, Term.t) _t
  val map_consts : f:(Term.d -> Term.d) -> t -> t

  val op_to_string : t -> string
  val to_string : t -> string
  val to_string_typed : typed_t -> string
  val to_string_value : ('i, Var.t, Dom.t, Term.t) _t -> string
  val to_latex : t -> string
  val to_json : t -> string
  val string_of_opt_typed_var : (Var.t * Dom.tt option) -> string

  val convert_vars : t -> t
  val convert_lets : t -> t
  val unroll_let : ?moderate:bool -> t -> t
  val unprime : t -> t
  val erase_label : t -> t
  val ac_simplify : ('i, Var.t, Dom.t, Term.t) _t -> ('i, Var.t, Dom.t, Term.t) _t

  val push_negs   : t -> t
  val push_quants : t -> t
  val simplify    : t -> t

  val all_exists     : t -> Var.t list * t list
  val destruct_nexts : t -> Interval.t list * t list
  val construct_nexts : Interval.t list -> t list -> core_t -> core_t

  val relative_interval : ?itl_itvs:(string, Zinterval.t, Base.String.comparator_witness) Base.Map.t -> t -> Zinterval.t
  val relative_intervals : ?itl_itvs:(string, Zinterval.t, Base.String.comparator_witness) Base.Map.t -> t list -> Zinterval.t
  val relative_past : ?itl_itvs:(string, Zinterval.t, Base.String.comparator_witness) Base.Map.t -> t -> bool
  val is_right_bounded : ('i, Var.t, Dom.t, Term.t) _t  -> bool
    
  val strict : ?itl_strict:(string, bool, Base.String.comparator_witness) Base.Map.t -> ?itv:Zinterval.t -> ?fut:bool -> t -> bool
  val stricts : ?itl_strict:(string, bool, Base.String.comparator_witness) Base.Map.t -> ?itv:Zinterval.t -> ?fut:bool -> t list -> bool

  val non_monotone_predicates :
    ?let_ctxt_mon:(string, (string, Base.String.comparator_witness) Base.Set.t, Base.String.comparator_witness) Base.Map.t ->
    ?let_ctxt_anti_mon:(string, (string, Base.String.comparator_witness) Base.Set.t, Base.String.comparator_witness) Base.Map.t ->
    ?init_mon:(string, Base.String.comparator_witness) Base.Set.t ->
    ?init_anti_mon:(string, Base.String.comparator_witness) Base.Set.t ->
    ('i, Var.t, Dom.t, Term.t) _t ->
    (string, Base.String.comparator_witness) Base.Set.t *
    (string, Base.String.comparator_witness) Base.Set.t

end
