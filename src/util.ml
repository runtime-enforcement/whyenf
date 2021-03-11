(*******************************************************************)
(*     This is part of Aerial, it is distributed under the         *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2017:                                                *)
(*  Dmitriy Traytel (ETH Zürich)                                   *)
(*******************************************************************)

(*make the list [from, from + 1, ..., to]*)
let rec ( -- ) i j =
  if i > j then [] else i :: (i + 1 -- j)

let paren h k x = if h>k then "("^^x^^")" else x

(*sets are defined using a functional interface given a type*)
module SS = Set.Make(String)
type timestamp = int
type trace = (SS.t * timestamp) list

(*intervals bounded by +∞, i.e., [i,+∞)*)
type uinterval = UI of int
(*intervals of the form [i,j]*)
type binterval = BI of int * int
type interval = B of binterval | U of uinterval

let case_I f1 f2 = function
  | B i -> f1 i
  | U i -> f2 i
let map_I f1 f2 = case_I (fun i -> B (f1 i)) (fun i -> U (f2 i))

let subtract n i = if i < n then 0 else i - n

let lclosed_UI i = U (UI i)
let lopen_UI i = U (UI (i + 1))
let nonempty_BI l r = if l <= r then BI (l, r) else raise (Failure "empty interval")
let lclosed_rclosed_BI i j = B (nonempty_BI i j)
let lopen_rclosed_BI i j = B (nonempty_BI (i + 1) j)
let lclosed_ropen_BI i j = B (nonempty_BI i (j - 1))
let lopen_ropen_BI i j = B (nonempty_BI (i + 1) (j - 1))
let left_UI (UI i) = i
(*let left_BI (BI (i, _)) = i*)
let right_BI (BI (_, j)) = j
(*val left_I = case_I left_BI left_UI*)
let right_I = case_I right_BI left_UI
let full = U (UI 0)

let subtract_UI n (UI i) = UI (subtract n i)
let subtract_BI n (BI (i, j)) = BI (subtract n i, subtract n j)
let subtract_I n = map_I (subtract_BI n) (subtract_UI n)

let multiply_UI n (UI i) = UI (i*n)
let multiply_BI n (BI (i, j)) = BI(i*n,j*n)
let multiply_I n = map_I (multiply_BI n) (multiply_UI n)

let mem_UI t (UI l) = l <= t
let mem_BI t (BI (l, r)) = l <= t && t <= r
let mem_I t = case_I (mem_BI t) (mem_UI t)

let binterval_to_string = function
  | BI (i, j) -> Printf.sprintf "[%d,%d]" i j

let interval_to_string = function
  | U (UI i) -> Printf.sprintf "[%d,∞)" i
  | B i -> Printf.sprintf "%a" (fun x -> binterval_to_string) i


type mode = NAIVE | COMPRESS_LOCAL | COMPRESS_GLOBAL

let lex_interval error l i j r =
  (match j with
    | "INFINITY" | "∞" ->
      (match l with
      | '[' -> lclosed_UI (int_of_string i)
      | '(' -> lopen_UI (int_of_string i)
      | _ -> error ())
    | _ ->
      (match l, r with
      | '[',']' -> lclosed_rclosed_BI (int_of_string i) (int_of_string j)
      | '(',']' -> lopen_rclosed_BI (int_of_string i) (int_of_string j)
      | '[',')' -> lclosed_ropen_BI (int_of_string i) (int_of_string j)
      | '(',')' -> lopen_ropen_BI (int_of_string i) (int_of_string j)
      | _ -> error ()))

