open Base

module T = struct

  type tt = TInt | TStr | TFloat [@@deriving compare, sexp_of, hash, equal]

  type t = Int of Int.t | Str of String.t | Float of Float.t [@@deriving compare, sexp_of, hash, equal]

  exception DomError of string

  let lt d d' = match d, d' with
    | Int v, Int v' -> Int.(v < v')
    | Str v, Str v' -> String.(v < v')
    | Float v, Float v' -> Float.(v < v')
    | _ -> false

  let gt d d' = match d, d' with
    | Int v, Int v' -> Int.(v > v')
    | Str v, Str v' -> String.(v > v')
    | Float v, Float v' -> Float.(v > v')
    | _ -> false

  let leq d d' = match d, d' with
    | Int v, Int v' -> Int.(v <= v')
    | Str v, Str v' -> String.(v <= v')
    | Float v, Float v' -> Float.(v <= v')
    | _ -> false

  let geq d d' = match d, d' with
    | Int v, Int v' -> Int.(v >= v')
    | Str v, Str v' -> String.(v >= v')
    | Float v, Float v' -> Float.(v >= v')
    | _ -> false

  let bool_tt = Int 1

  let tt_of_string = function
    | "int" -> TInt
    | "string" -> TStr
    | "float" -> TFloat
    | t -> raise (DomError (Printf.sprintf "type %s is not supported" t))

  let tt_of_domain = function
    | Int _ -> TInt
    | Str _ -> TStr
    | Float _ -> TFloat

  let tt_to_string = function
    | TInt -> "int"
    | TStr -> "string"
    | TFloat -> "float"

  let tt_default = function
    | TInt -> Int 0
    | TStr -> Str ""
    | TFloat -> Float 0.0

  let string_to_t s tt = match tt with
    | TInt -> (try Int (Int.of_string s)
               with Failure _ -> raise (DomError (Printf.sprintf "%s is not an int" s)))
    | TStr -> Str s
    | TFloat -> (try Float (Float.of_string s)
                 with Failure _ -> raise (DomError (Printf.sprintf "%s is not a float" s)))

  let to_string = function
    | Int v -> Int.to_string v
    | Str v -> Printf.sprintf "\"%s\"" v
    | Float v -> Float.to_string v

  let to_latex = function
    | Int v -> Int.to_string v
    | Str v -> Printf.sprintf "\\texttt{\"%s\"}" v
    | Float v -> Float.to_string v

  let to_json = function
    | Int v -> Printf.sprintf "{ \"constructor\": \"Int\", \"value\": %d }" v
    | Str v -> Printf.sprintf "{ \"constructor\": \"Str\", \"value\": \"%s\" }"
                 (String.concat_map v ~f:(fun x -> if Char.equal x '"' then "\\\"" else String.of_char x))
    | Float v -> Printf.sprintf "{ \"constructor\": \"Float\", \"value\": %f }" v

  let list_to_string ds =
    String.drop_suffix (List.fold ds ~init:"" ~f:(fun acc d -> acc ^ (to_string d) ^ ", ")) 2

  let to_int_exn = function
    | Int v -> v
    | d -> raise (DomError (Printf.sprintf "type %s is not supported" (tt_to_string (tt_of_domain d))))

  let to_float_exn = function
    | Float v -> v
    | d -> raise (DomError (Printf.sprintf "type %s is not supported" (tt_to_string (tt_of_domain d))))

  let to_string_exn = function
    | Str v -> v
    | d -> raise (DomError (Printf.sprintf "type %s is not supported" (tt_to_string (tt_of_domain d))))

  let of_int i = Int i

end

include T
include Comparator.Make(T)

