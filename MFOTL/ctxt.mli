open Base

open Modules

module type C = sig

  type d

  type tt
  
  type ttt =
    | TConst of tt
    | TNamed of string
    | TVar of string
    | TSum of (string * ttt) list [@@deriving compare, sexp_of, hash, equal]

  type t

  type meet = ttt -> ttt -> ttt option

  exception CtxtError of string

  val unconst : ttt -> tt

  val empty : t
  val empty_meet : meet
  val of_meet : meet -> t
  val of_alist : ?meet:meet -> (string * ttt) list -> t
  val mem : t -> string -> bool
  val remove : t -> string -> t
  val fresh_var : t -> t * string
  val fresh_ttt : t -> t * ttt
  val add_tv : string -> t -> t
  val convert_with_fresh_ttts : t -> ttt list -> t * ttt list
  val merge : t -> t -> t
  val get_ttt : string -> t -> default:ttt -> ttt
  val get_ttt_exn : string -> t -> ttt
  val get_tt : string -> t -> default:tt -> tt
  val get_tt_exn : string -> t -> tt
  val get_concrete_exn : string -> t -> ttt
  val eval : ttt -> t -> ttt
  val type_const : d -> ttt -> t -> t * ttt
  val type_var : string -> ttt -> t -> t * ttt
  val unify : ttt -> ttt -> t -> t * ttt
  val vars : t -> string list
  val tvs : t -> string list

  val ttt_to_string : ttt -> string
  val to_string : t -> string

end


module Make (Dom : D) : C with type d = Dom.t and type tt = Dom.tt