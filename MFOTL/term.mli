open Base

open Modules

module type T = sig

  type t [@@deriving compare, sexp_of, hash, equal]
  type v [@@deriving compare, sexp_of, hash, equal]
  type d [@@deriving compare, sexp_of, hash, equal]

  type comparator_witness
  val core_equal : t -> t -> bool
  val comparator : (t, comparator_witness) Comparator.t

  val dummy_var : v -> t
  val dummy_app : string -> t list -> t
  val dummy_int : int -> t

  val unvar_opt : t -> v option
  val unconst_opt : t -> d option

  val fv_list : t list -> v list
  val fn_list : t list -> string list
  val size : t -> int
  val exists_subterm : f:(t -> bool) -> t -> bool
  val equal : t -> t -> bool

  val to_string : t -> string
  val value_to_string : ?l:int -> t -> string
  val value_to_latex : ?l:int -> t -> string
  val list_to_string : t list -> string
  val list_to_latex : t list -> string

  val subst : (v, t, 'a) Map.t -> t -> t
  val substs : (v, t, 'a) Map.t -> t list -> t list

  val map_consts: f:(d -> d) -> t -> t

end


module Make (Var : V) (Dom : D) (Uop : O) (Bop : O) (Info : I) : sig

  type core_t =
    | Var of Var.t
    | Const of Dom.t
    | App of string * t list
    | Unop of Uop.t * t
    | Binop of t * Bop.t * t
    | Proj of t * string
    | Record of (string * t) list
     [@@deriving compare, sexp_of, hash, equal]
  and t = { trm : core_t; info : Info.t }
  
  type v = Var.t [@@deriving compare, sexp_of, hash, equal]
  type d = Dom.t [@@deriving compare, sexp_of, hash, equal]

  type comparator_witness

  val core_equal: t -> t -> bool

  val var: v -> core_t
  val const: d -> core_t
  val app: string -> t list -> core_t
  val unop: Uop.t -> t -> core_t
  val binop: t -> Bop.t -> t -> core_t
  val proj: t -> string -> core_t
  val record: (string * t) list -> core_t

  val make : core_t -> Info.t -> t
  val make_dummy : core_t -> t

  val dummy_var : v -> t
  val dummy_app : string -> t list -> t
  val dummy_int : int -> t

  val is_var: t -> bool
  val is_const: t -> bool

  val unvar_opt : t -> v option
  val unconst_opt : t -> d option

  val unvar: t -> v

  val unconst: t -> d

  val comparator: (t, comparator_witness) Comparator.t

  val fv_list: t list -> v list
  val fn_list: t list -> string list
  val size: t -> int
  val exists_subterm: f:(t -> bool) -> t -> bool

  val to_string: t -> string

  val value_to_string: ?l:int -> t -> string
  val value_to_latex : ?l:int -> t -> string

  val list_to_string: t list -> string
  val list_to_latex: t list -> string
  val list_to_string_core: core_t list -> string

  val filter_vars: t list -> v list

  val reorder: t list -> t list -> t list

  val subst: (v, t, 'a) Map.t -> t -> t
  val substs: (v, t, 'a) Map.t -> t list -> t list

  val map_consts: f:(d -> d) -> t -> t
  
end

module Index : T with type t = int
