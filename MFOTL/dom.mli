open Base

type tt = TInt | TStr | TFloat [@@deriving compare, sexp_of, hash, equal]

type t = Int of int | Str of string | Float of float [@@deriving compare, sexp_of, hash, equal]

type comparator_witness

val comparator : (t, comparator_witness) Comparator.t

val lt: t -> t -> bool
val gt: t -> t -> bool
val leq: t -> t -> bool
val geq: t -> t -> bool

val bool_tt : t

val equal_tt: tt -> tt -> bool

val tt_of_string: string -> tt

val tt_of_domain: t -> tt

val tt_to_string: tt -> string

val tt_default: tt -> t

val string_to_t: string -> tt -> t

val to_string: t -> string

val list_to_string: t list -> string

val to_int_exn: t -> int
val to_float_exn: t -> float
val to_string_exn: t -> string

