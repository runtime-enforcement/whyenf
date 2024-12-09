type t = N | L | R | LR [@@deriving compare, sexp_of, hash]

val equal: t -> t -> bool

val to_string: t -> string
val to_string2: t * t -> string
val of_string: string -> t
  
val value: t option -> t
val value2: (t * t) option -> t * t
