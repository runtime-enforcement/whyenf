open Dom

type ttt =
  | TConst of Dom.tt
  | TVar of string [@@deriving compare, sexp_of, hash]

type t

val unconst : ttt -> Dom.tt

val empty : t
val fresh_var : t -> t * string
val fresh_ttt : t -> t * ttt
val convert_with_fresh_ttts : t -> ttt list -> t * ttt list
val get_tt_exn : string -> t -> tt
val type_const : Dom.t -> ttt -> t -> t * ttt
val type_var : string -> ttt -> t -> t * ttt

val ttt_to_string : ttt -> string
