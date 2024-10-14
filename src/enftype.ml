open Base

type t = Cau | NCau | SCau | Sup | CauSup | Obs [@@deriving compare, sexp_of, hash, equal]

let neg = function
  | Cau
    | NCau
    | SCau -> Sup
  | Sup    -> Cau 
  | CauSup -> CauSup
  | Obs    -> Obs

let to_int = function
  | Cau    -> 1
  | NCau   -> 2
  | SCau   -> 3
  | Sup    -> 4
  | CauSup -> 5
  | Obs    -> 0

let to_string = function
  | Cau    -> "Cau"
  | NCau   -> "NCau"
  | SCau   -> "SCau"
  | Sup    -> "Sup"
  | CauSup -> "CauSup"
  | Obs    -> "Obs"

let meet a b = match a, b with
  | _, _ when a == b -> a
  | Obs, x | x, Obs -> x
  | Cau, NCau | NCau, Cau
    | Cau, SCau | SCau, Cau -> Cau
  | _, _ -> CauSup

let join a b = match a, b with
  | _, _ when a == b -> a
  | CauSup, x | x, CauSup -> x
  | Cau, NCau | NCau, Cau -> NCau
  | Cau, SCau | SCau, Cau -> SCau
  | _, _ -> Obs

let leq a b = (meet a b) == a
let geq a b = (join a b) == a

let is_causable = function
  | CauSup | Cau | NCau | SCau -> true
  | _ -> false

let is_suppressable = function
  | CauSup | Sup -> true
  | _ -> false
