open Core

open Modules

module type T = sig

  type v
  type c
  type t = (v, Dom.t, c) Map.t

  val compare: t -> t -> int
  val equal: t -> t -> bool
  val empty: t
  val sexp_of: t -> Sexp.t
  val extend: t -> t -> t
  val hash: t -> int

  val to_string: t -> string

  val of_alist_exn : v list -> Dom.t list -> t

end

module Make (Var : V) : T with type v = Var.t and type c = Var.comparator_witness
