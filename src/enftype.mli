type t [@@deriving compare, sexp_of, hash, equal]

val neg : t -> t

val to_string : t -> string

val meet : t -> t -> t
val join : t -> t -> t

val leq : t -> t -> bool
val geq : t -> t -> bool

val is_causable : t -> bool
val is_suppressable : t -> bool
val is_observable : t -> bool
val is_only_observable : t -> bool
val is_error : t -> bool

val bot : t
val cau : t
val ncau : t
val scau : t
val obs : t
val sup : t
val nsup : t
val ssup : t
val causup : t
val caubot : t
val sct : t
val noncau : t
