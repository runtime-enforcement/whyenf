open Base

open Modules

module type C = sig

  type d
  type tt
  
  type ttt =
    | TConst of tt
    | TVar of string [@@deriving compare, sexp_of, hash]

  type t

  val unconst : ttt -> tt

  val empty : t
  val mem : t -> string -> bool
  val remove : t -> string -> t
  val fresh_var : t -> t * string
  val fresh_ttt : t -> t * ttt
  val convert_with_fresh_ttts : t -> ttt list -> t * ttt list
  val get_ttt : string -> t -> default:ttt -> ttt
  val get_ttt_exn : string -> t -> ttt
  val get_tt : string -> t -> default:tt -> tt
  val get_tt_exn : string -> t -> tt
  val type_const : d -> ttt -> t -> t * ttt
  val type_var : string -> ttt -> t -> t * ttt

  val ttt_to_string : ttt -> string

end


module Make (Dom : D) : C with type d = Dom.t and type tt = Dom.tt
