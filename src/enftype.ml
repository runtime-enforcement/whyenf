open Base

module Sup = struct

  type t = Sup | Obs | NonObs [@@deriving compare, sexp_of, hash, equal]

  let value = function
    | NonObs -> 0
    | Obs    -> 1
    | Sup    -> 2

  let to_string = function
    | NonObs -> "NonObs"
    | Obs    -> "Obs"
    | Sup    -> "Sup"

end

module Cau = struct

  type t = Cau | NonCau [@@deriving compare, sexp_of, hash, equal]

  let value = function
    | NonCau -> 0
    | Cau    -> 1

  let to_string = function
    | NonCau -> "NonCau"
    | Cau    -> "Cau"

end

module Sct = struct

  type t = Sct | NonSct | AnySct | ErrSct [@@deriving compare, sexp_of, hash, equal]

  let to_string = function
    | NonSct -> "NonSct"
    | Sct    -> "Sct"
    | AnySct -> "AnySct"
    | ErrSct -> "ErrSct"

end

module Suppressability = Lattice.Linear(Sup)
module Causability     = Lattice.Linear(Cau)

module Strictness = struct

  type t = Sct.t [@@deriving compare, sexp_of, hash, equal]

  let join a b = match a, b with
    | Sct.ErrSct, _ | _, Sct.ErrSct
      | NonSct, Sct | Sct, NonSct -> Sct.ErrSct
    | _, AnySct -> a
    | AnySct, _ -> b
    | _, _ -> a

  let meet a b = match a, b with
    | Sct.AnySct, _ | _, Sct.AnySct
      | NonSct, Sct | Sct, NonSct -> Sct.AnySct
    | _, ErrSct -> a
    | ErrSct, _ -> b
    | _, _ -> a

  let to_string = Sct.to_string

end

include Lattice.Make3 (Suppressability) (Causability) (Strictness)

let bot    = (Sup.NonObs, Cau.NonCau, Sct.AnySct)
let cau    = (Sup.Obs, Cau.Cau, Sct.AnySct)
let ncau   = (Sup.Obs, Cau.Cau, Sct.NonSct)
let scau   = (Sup.Obs, Cau.Cau, Sct.Sct)
let obs    = (Sup.Obs, Cau.NonCau, Sct.AnySct)
let sup    = (Sup.Sup, Cau.NonCau, Sct.AnySct)
let nsup   = (Sup.Sup, Cau.Cau, Sct.NonSct)
let ssup   = (Sup.Sup, Cau.Cau, Sct.Sct)
let causup = (Sup.Sup, Cau.Cau, Sct.AnySct)
let caubot = (Sup.NonObs, Cau.Cau, Sct.AnySct)
let sct    = (Sup.Sup, Cau.Cau, Sct.Sct)
let noncau = (Sup.Sup, Cau.NonCau, Sct.AnySct)

let get_sup (a, b, c) = a
let get_cau (a, b, c) = b
let get_sct (a, b, c) = c

let neg_sup = function
  | Sup.Sup -> Cau.Cau
  | _       -> NonCau

let neg_cau a b = match a, b with
  | Cau.Cau, _          -> Sup.Sup
  | NonCau , Sup.NonObs -> NonObs
  | _      , _          -> Obs

let neg (a, b, c) : t = (neg_cau b a, neg_sup a, c)

let is_causable        a = Cau.(equal (get_cau a) Cau)
let is_suppressable    a = Sup.(equal (get_sup a) Sup)
let is_observable      a = Sup.(equal (get_sup a) Sup || equal (get_sup a) Obs)
let is_only_observable a = not (is_causable a) && not (is_suppressable a) && is_observable a
let is_error           a = Sct.(equal (get_sct a) ErrSct)

let to_string ((a, b, c) as d) =
  match a, b, c with
  | Sup.NonObs, Cau.NonCau, _          -> "Bot"
  | Sup.Obs   , Cau.NonCau, _          -> "Obs"
  | Sup.Sup   , Cau.NonCau, Sct.AnySct -> "Sup"
  | Sup.Obs   , Cau.Cau   , Sct.AnySct -> "Cau"
  | Sup.Obs   , Cau.Cau   , Sct.NonSct -> "NCau"
  | Sup.Obs   , Cau.Cau   , Sct.Sct    -> "SCau"
  | Sup.Sup   , Cau.NonCau, Sct.NonSct -> "NSup"
  | Sup.Sup   , Cau.NonCau, Sct.Sct    -> "SSup"   
  | _         ,    _         , _       -> to_string d
