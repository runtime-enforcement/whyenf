type t = Cau | NCau | SCau | Sup | CauSup | Obs [@@deriving compare, sexp_of, hash, equal]

val neg : t -> t

val to_int : t -> int

val to_string : t -> string

val meet : t -> t -> t

val join : t -> t -> t

val leq : t -> t -> bool

val geq : t -> t -> bool

val is_causable : t -> bool
val is_suppressable : t -> bool
