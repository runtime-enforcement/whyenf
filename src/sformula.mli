open Base

module Const : sig

  type t =
    | CBool  of bool
    | CInt   of int
    | CFloat of float
    | CStr   of string
    [@@deriving compare, sexp_of, hash]

  val to_dom: t -> Dom.t

end

module Aop : sig

  type t = ASum | AAvg | AMed | ACnt | AMin | AMax | AStd
           [@@deriving compare, sexp_of, hash, equal]

end

module Bop2 : sig

  type t = BIff [@@deriving compare, sexp_of, hash]

end

module Bop : sig

  type t =
    | BAnd | BOr | BImp
    | BAdd | BSub | BMul | BDiv | BPow
    | BFAdd | BFSub | BFMul | BFDiv | BFPow
    | BEq | BNeq | BLt | BLeq | BGt | BGeq
    | BConc
    [@@deriving compare, sexp_of, hash]

  val is_relational: t -> bool
  
end

module Uop : sig

  type t = USub | UFSub | UNot
           [@@deriving compare, sexp_of, hash]

end

module Btop : sig

  type t = BSince | BUntil | BRelease | BTrigger
           [@@deriving compare, sexp_of, hash]

end

module Utop : sig

  type t = UNext | UPrev | UAlways | UHistorically | UEventually | UOnce
           [@@deriving compare, sexp_of, hash]

end

type t =
  | SConst of Const.t
  | SVar of string
  | SApp of string * t list
  | SLet of string * Enftype.t option * string list * t * t
  | SAgg of string * Aop.t * t * string list * t
  | STop of string list * string * t list * string list * t
  | SAssign of t * string * t
  | SBop of Side.t option * t * Bop.t * t
  | SBop2 of (Side.t * Side.t) option * t * Bop2.t * t
  | SUop of Uop.t * t
  | SExists of string list * t
  | SForall of string list * t
  | SBtop of Side.t option * Interval.t * t * Btop.t * t
  | SUtop of Interval.t * Utop.t * t
  [@@deriving compare, sexp_of, hash]
