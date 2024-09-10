open Core

type t

module Span : sig

  type t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val sexp_of_t : t -> Sexp.t
  val hash_fold_t : Base_internalhash_types.state -> t -> Base_internalhash_types.state

  val inc : t -> t
  val dec : t -> t
  val inv : t -> t

  val (+) : t -> t -> t
  val (-) : t -> t -> t

  val (<=) : t -> t -> bool
  val (<) : t -> t -> bool

  val min : t -> t -> t
  val max : t -> t -> t

  val max_span : t

  val is_zero : t -> bool
  val zero : t

  val make : int -> string -> t

  val to_int : t -> int
  
  val of_string : string -> t
  val to_string : t -> string
  
end

val equal : t -> t -> bool
val compare : t -> t -> int
val sexp_of_t : t -> Sexp.t
val hash_fold_t : Base_internalhash_types.state -> t -> Base_internalhash_types.state

val of_float : float -> t
val of_int : int -> t

val (+) : t -> Span.t -> t
val (-) : t -> t -> Span.t
val (--) : t -> Span.t -> t

val (<=) : t -> t -> bool
val (<) : t -> t -> bool

val min : t -> t -> t
val max : t -> t -> t

val zero : t

val to_string : t -> string
