(*******************************************************************)
(*     This is part of Aerial, it is distributed under the         *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util

(* Intervals bounded by +∞, i.e., [i,+∞) *)
type uinterval = UI of int

(* Intervals of the form [i,j] *)
type binterval = BI of int * int 
type interval = B of binterval | U of uinterval

(* Given a ts and an interval, check if 
   ts < i OR ts \in i OR ts > i 
 *)
type rel = Below | Inside | Above

let case_I f1 f2 = function
  | B i -> f1 i
  | U i -> f2 i
let map_I f1 f2 = case_I (fun i -> B (f1 i)) (fun i -> U (f2 i))

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

(* Interval operations *)
let subtract n i = if i < n then 0 else i - n
let subtract_UI n (UI i) = UI (subtract n i)
let subtract_BI n (BI (i, j)) = BI (subtract n i, subtract n j)
let subtract_I n = map_I (subtract_BI n) (subtract_UI n)

let multiply_UI n (UI i) = UI (i*n)
let multiply_BI n (BI (i, j)) = BI(i*n,j*n)
let multiply_I n = map_I (multiply_BI n) (multiply_UI n)

(* Check if t \in interval *)
let mem_UI t (UI l) = l <= t
let mem_BI t (BI (l, r)) = l <= t && t <= r
let mem_I t = case_I (mem_BI t) (mem_UI t)

(* Check if t < interval *)
let below_UI t (UI l) = t < l
let below_BI t (BI (l, r)) = t < l
let below_I t = case_I (below_BI t) (below_UI t)

(* Check if t > interval *)
let above_UI t (UI l) = false
let above_BI t (BI (l, r)) = t > r
let above_I t = case_I (above_BI t) (above_UI t)

let where_UI t (UI l) =
  let b = below_UI t (UI l) in
  let a = above_UI t (UI l) in
  match b, a with
  | true, false -> Below 
  | false, false -> Inside
  | _ , _ -> failwith "There is a problem with intervals"

let where_BI t (BI (l, r)) =
  let b = below_BI t (BI (l, r)) in
  let a = above_BI t (BI (l, r)) in
  match b, a with
  | true, false -> Below
  | false, true -> Above
  | false, false -> Inside
  | _ , _ -> failwith "There is a problem with intervals"

let where_I t = case_I (where_BI t) (where_UI t)

let get_b_UI t (UI l) = None
let get_b_BI t (BI (l, r)) = Some(r)
let get_b_I t = case_I (get_b_BI t) (get_b_UI t)

(* TODO: This might not be the best 
   place for these functions 
 *)

(* ETP: earliest \tau_i s.t. \tau_i >= \tau 
   We assume ts_asc_list is in ascending order
 *)
let rec etp tau ts_asc_list =
  match ts_asc_list with
  | [] -> failwith "Empty time-stamp list"
  | h::[] -> h
  | h::t when h >= tau -> h
  | h::t -> etp tau t

(* LTP: latest \tau_i s.t. \tau_i <= \tau 
   We assume ts_desc_list is in descending order
 *)
let rec ltp tau ts_desc_list =
  match ts_desc_list with
  | [] -> failwith "Empty time-stamp list"
  | h::[] -> h
  | h::t when h <= tau -> h
  | h::t -> ltp tau t

let binterval_to_string = function
  | BI (i, j) -> Printf.sprintf "[%d,%d]" i j

let interval_to_string = function
  | U (UI i) -> Printf.sprintf "[%d,∞)" i
  | B i -> Printf.sprintf "%a" (fun x -> binterval_to_string) i

(* Intervals to String *)
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
