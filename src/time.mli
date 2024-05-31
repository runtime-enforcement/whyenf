open Core

type t = Second of int | Minute of int | Hour of int [@@deriving compare, sexp_of, hash, equal]

val (+) : t -> t -> t
val inc : t -> t
val dec : t -> t

val (-) : t -> t -> t
val (|-) : t -> t -> t

val (<=) : t -> t -> bool
val (<) : t -> t -> bool

val min : t -> t -> t
val max : t -> t -> t

val is_zero : t -> bool
val inv: t -> t

val zero : t
val max_time : t

val to_zero : t -> t

val to_string : t -> string
val to_int : t -> int

val make : int -> string -> t

val of_timestamp : Etc.timestamp -> t
