open Base

type t = Cau | NCau | SCau | Sup | NSup | SSup | CauSup | Obs [@@deriving compare, sexp_of, hash, equal]

let neg = function
  | Cau    -> Sup
  | NCau   -> NSup
  | SCau   -> SSup
  | Sup    -> Cau
  | NSup   -> NCau
  | SSup   -> SCau 
  | CauSup -> CauSup
  | Obs    -> Obs

let to_int = function
  | Cau    -> 1
  | NCau   -> 2
  | SCau   -> 3
  | Sup    -> 4
  | NSup   -> 5
  | SSup   -> 6
  | CauSup -> 7
  | Obs    -> 0

let to_string = function
  | Cau    -> "Cau"
  | NCau   -> "NCau"
  | SCau   -> "SCau"
  | Sup    -> "Sup"
  | NSup   -> "NSup"
  | SSup   -> "SSup"
  | CauSup -> "CauSup"
  | Obs    -> "Obs"

let meet a b = match a, b with
  | _, _ when a == b -> a
  | Obs, x | x, Obs -> x
  | Cau, NCau | NCau, Cau
    | Cau, SCau | SCau, Cau -> Cau
  | Sup, NSup | NSup, Sup
    | Sup, SSup | SSup, Sup -> Sup
  | _, _ -> CauSup

let join a b = match a, b with
  | _, _ when a == b -> a
  | CauSup, x | x, CauSup -> x
  | Cau, NCau | NCau, Cau -> NCau
  | Cau, SCau | SCau, Cau -> SCau
  | Sup, NSup | NSup, Sup -> NSup
  | Sup, SSup | SSup, Sup -> SSup
  | _, _ -> Obs

let leq a b = (meet a b) == a
let geq a b = (join a b) == a

let is_causable = function
  | CauSup | Cau | NCau | SCau -> true
  | _ -> false

let is_suppressable = function
  | CauSup | Sup | NSup | SSup -> true
  | _ -> false
