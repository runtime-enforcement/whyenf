open Core

type t

val equal : t -> t -> bool
val compare : t -> t -> int
val sexp_of_t : t -> Sexp.t
val hash_fold_t : Base_internalhash_types.state -> t -> Base_internalhash_types.state

module type U = sig
  
  type u [@@deriving equal, compare, sexp_of, hash]
  
  val min_seconds : u -> int
  val max_seconds : u -> int
  val (+) : t -> u -> t
  val neg : u -> u
  val inc : u -> u
  val dec : u -> u
  val is_zero : u -> bool
  val is_one : u -> bool
  val of_string : string -> u
  val to_string : u -> string
  
end

module type S = sig
  
  type v

  val equal_v : v -> v -> bool
  val compare_v : v -> v -> int
  val sexp_of_v : v -> Sexp.t
  val hash_fold_v : Base_internalhash_types.state -> v -> Base_internalhash_types.state

  val min_seconds : v -> int
  val max_seconds : v -> int
  val leq : v -> v -> bool
  val (+) : t -> v -> t
  val inc : v -> v
  val dec : v -> v
  val is_zero : v -> bool
  val zero : v
  val to_string : v -> string
  
end

module Span : sig

  module Second : U
  module Minute : U
  module Hour   : U
  module Day    : U
  module Month  : U
  module Year   : U

  type s =
    | Second of Second.u
    | Minute of Minute.u
    | Hour   of Hour.u
    | Day    of Day.u
    | Month  of Month.u
    | Year   of Year.u
  [@@deriving equal, compare, sexp_of, hash]
  
  val (+) : t -> s -> t
  val neg : s -> s
  val inc : s -> s
  val dec : s -> s
  val is_zero : s -> bool
  val make : string -> string -> s
  val of_string : string -> s
  val to_string : s -> string

  val (-) : t -> s -> t

  val zero : s
  val infty : s

  val min_seconds : s -> int
  val max_seconds : s -> int
  val leq : s -> s -> bool

  module S : S with type v = s
  
end

val of_int : int -> t
val to_int : t -> int

val (+) : t -> Span.s -> t
val (-) : t -> Span.s -> t

val (<=) : t -> t -> bool
val (<) : t -> t -> bool
val (==) : t -> t -> bool

val min : t -> t -> t
val max : t -> t -> t

val zero : t

val to_string : t -> string
val to_epoch_string : t -> string

val of_string : string -> t
