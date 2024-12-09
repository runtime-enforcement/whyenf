open Base

module type LinT = sig

  type t [@@deriving compare, sexp_of, hash, equal]

  val value : t -> int
  val to_string : t -> string

end

module type PreL = sig

  type t [@@deriving compare, sexp_of, hash, equal]

  val join : t -> t -> t
  val meet : t -> t -> t

  val to_string : t -> string

end

module type L = sig

  type t [@@deriving compare, sexp_of, hash, equal]
 
  module P : PreL

  val join : t -> t -> t
  val meet : t -> t -> t

  val leq : t -> t -> bool
  val geq : t -> t -> bool
  
  val to_string : t -> string

end

module Linear (L : LinT) : PreL with type t = L.t

module Make  (P : PreL)                                      : L with type t = P.t
module Make2 (P1 : PreL) (P2 : PreL)                         : L with type t = P1.t * P2.t
module Make3 (P1 : PreL) (P2 : PreL) (P3 : PreL)             : L with type t = P1.t * P2.t * P3.t
module Make4 (P1 : PreL) (P2 : PreL) (P3 : PreL) (P4 : PreL) : L with type t = P1.t * P2.t * P3.t * P4.t
