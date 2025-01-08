type t [@@deriving compare, sexp_of, hash, equal]

val neg : t -> t

val to_string : t -> string
val to_string_let : t -> string

val meet : t -> t -> t
val join : t -> t -> t

val leq : t -> t -> bool
val geq : t -> t -> bool

val is_causable : t -> bool
val is_suppressable : t -> bool
val is_observable : t -> bool
val is_only_observable : t -> bool
val is_absent : t -> bool
val is_internal : t -> bool
val is_error : t -> bool
val is_strict : t -> bool
val is_non_strict : t -> bool
val is_transparent : t -> bool

val bot : t
val cau : t
val ncau : t
val sup : t
val causup : t
val caubot : t
val ncaubot : t
val obs : t
val sct : t
val abs : t
val itl : t

val causable : t
val suppressable : t
val tcausable : t
val tsuppressable : t

module Constraint : sig

    type enftype_t = t
  
    type t = { lower: enftype_t option; upper: enftype_t option }

    val lower : enftype_t -> t
    val upper : enftype_t -> t

    exception CannotMerge

    val merge : key:'a -> [< `Both of t * t | `Left of t | `Right of t ] -> t option
    val solve : t -> enftype_t

    val to_string : t -> string
  
end
