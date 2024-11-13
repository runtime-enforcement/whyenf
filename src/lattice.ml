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

module Linear (L : LinT) : PreL with type t = L.t = struct

  type t = L.t [@@deriving compare, sexp_of, hash, equal]

  let join a b = if L.value a <= L.value b then a else b
  let meet a b = if L.value a <= L.value b then b else a

  let to_string = L.to_string

end

module Make (P : PreL) : L with type t = P.t = struct

  module P = P
    
  include P

  let leq a b = equal (meet a b) a
  let geq a b = equal (join a b) a

end

module PreMake2 (P1 : PreL) (P2 : PreL) : PreL with type t = P1.t * P2.t = struct

  type t = P1.t * P2.t [@@deriving compare, sexp_of, hash, equal]

  let join (a1, a2) (b1, b2) = (P1.join a1 b1, P2.join a2 b2)
  let meet (a1, a2) (b1, b2) = (P1.meet a1 b1, P2.meet a2 b2)

  let to_string (a1, a2) = P1.to_string a1 ^ ", " ^ P2.to_string a2

end

module Make2 (P1 : PreL) (P2 : PreL) : L with type t = P1.t * P2.t = Make (PreMake2 (P1) (P2))

module PreMake3 (P1 : PreL) (P2 : PreL) (P3 : PreL) : PreL with type t = P1.t * P2.t * P3.t = struct

  type t = P1.t * P2.t * P3.t [@@deriving compare, sexp_of, hash, equal]

  let join (a1, a2, a3) (b1, b2, b3) = (P1.join a1 b1, P2.join a2 b2, P3.join a3 b3)
  let meet (a1, a2, a3) (b1, b2, b3) = (P1.meet a1 b1, P2.meet a2 b2, P3.meet a3 b3)

  let to_string (a1, a2, a3) = P1.to_string a1 ^ ", " ^ P2.to_string a2 ^ ", " ^ P3.to_string a3

end

module Make3 (P1 : PreL) (P2 : PreL) (P3 : PreL) : L with type t = P1.t * P2.t * P3.t = Make (PreMake3 (P1) (P2) (P3))


