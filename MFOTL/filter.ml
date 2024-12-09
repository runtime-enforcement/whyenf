open Base

type t = An of string | AllOf of t list | OneOf of t list [@@deriving equal, compare, hash, sexp_of]

let tt = AllOf []
let ff = OneOf []

let is_an = function An _ -> true | _ -> false
let is_allof = function AllOf _ -> true | _ -> false
let is_oneof = function OneOf _ -> true | _ -> false

let rec to_string_rec l = function
  | An e -> e
  | AllOf [] -> "⊤"
  | OneOf [] -> "⊥"
  | AllOf fis -> Printf.sprintf (Etc.paren l 4 "%s") (String.concat ~sep:"∧" (List.map fis ~f:(to_string_rec 4)))
  | OneOf fis -> Printf.sprintf (Etc.paren l 3 "%s") (String.concat ~sep:"∨" (List.map fis ~f:(to_string_rec 3)))

let to_string = to_string_rec 0

let rec simplify = function
  | An e -> An e
  | AllOf [] -> AllOf []
  | OneOf [] -> OneOf []
  | AllOf fis ->
     let fis        = List.map fis ~f:simplify in
     let all_of_fis = List.concat_map fis ~f:(function AllOf fis -> fis | _ -> []) in
     let one_ofs    = List.filter fis ~f:is_oneof in
     let ans        = List.filter fis ~f:is_an in
     let one_of_bad = List.exists one_ofs ~f:(equal ff) in
     if one_of_bad then
       ff
     else
       AllOf (all_of_fis @ one_ofs @ ans)
  | OneOf fis ->
     let fis        = List.map fis ~f:simplify in
     let one_of_fis = List.concat_map fis ~f:(function OneOf fis -> fis | _ -> []) in
     let all_ofs    = List.filter fis ~f:is_allof in
     let ans        = List.filter fis ~f:is_an in
     let all_of_bad = List.exists all_ofs ~f:(equal tt) in
     if all_of_bad then
       tt
     else
       OneOf (one_of_fis @ all_ofs @ ans)

let conj fi1 fi2 = simplify (AllOf [fi1; fi2])
let disj fi1 fi2 = simplify (OneOf [fi1; fi2])
let conjs fis    = simplify (AllOf fis)
let disjs fis    = simplify (OneOf fis)

