open Base

type t = Var of string | Const of Dom.t | App of string * t list [@@deriving compare, sexp_of, hash]

type comparator_witness

val var: string -> t
val const: Dom.t -> t
val app: string -> t list -> t

val is_var: t -> bool
val is_const: t -> bool

val unvar: t -> string

val unconst: t -> Dom.t

val comparator: (t, comparator_witness) Comparator.t

val fv_list: t list -> string list
val fn_list: t list -> string list

val equal: t -> t -> bool

val to_string: t -> string

val value_to_string: t -> string

val list_to_string: t list -> string

val filter_vars: t list -> string list

val reorder: t list -> string list -> t list

val subst: (String.t, t, String.comparator_witness) Map.t -> t -> t
val substs: (String.t, t, String.comparator_witness) Map.t -> t list -> t list

val init: Sformula.t -> t
