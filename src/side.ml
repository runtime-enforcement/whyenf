type t = N | L | R | LR [@@deriving compare, sexp_of, hash]

let equal s s' = match s, s' with
  | N, N
    | L, L
    | R, R
    | LR, LR -> true
  | _ -> false

let to_string = function
  | N  -> ""
  | L  -> ":L"
  | R  -> ":R"
  | LR -> ":LR"

let to_string2 =
  let aux = function N  -> "N" | L  -> "L" | R  -> "R" | LR -> "LR"
  in function (N, N) -> "" | (a, b) -> ":" ^ aux a ^ "," ^ aux b

let of_string = function
  | "L"  -> L
  | "R"  -> R
  | "LR" -> LR
