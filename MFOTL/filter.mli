type t = An of string | AllOf of t list | OneOf of t list [@@deriving equal, compare, hash, sexp_of]

val tt : t
val ff : t

(*val eval : Db.t -> t -> bool*)

val to_string : t -> string

val simplify : t -> t

val conj : t -> t -> t
val disj : t -> t -> t

val conjs : t list -> t
val disjs : t list -> t

