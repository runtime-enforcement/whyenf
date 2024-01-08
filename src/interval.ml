(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

(* Unbounded [i,+∞) *)
type ut = UI of int

(* Bounded [i,j] *)
type bt = BI of int * int

type t = B of bt | U of ut

let equal i i' = match i, i' with
  | B (BI (a, b)), B (BI (a', b')) -> Int.equal a a' && Int.equal b b'
  | U (UI a), U (UI a') -> Int.equal a a'
  | _ -> false

let lclosed_UI i = U (UI i)
let lopen_UI i = U (UI (i + 1))

let nonempty_BI l r = if l <= r then BI (l, r) else raise (Invalid_argument "empty interval")
let lopen_ropen_BI i j = B (nonempty_BI (i + 1) (j - 1))
let lopen_rclosed_BI i j = B (nonempty_BI (i + 1) j)
let lclosed_ropen_BI i j = B (nonempty_BI i (j - 1))
let lclosed_rclosed_BI i j = B (nonempty_BI i j)

let singleton i = lclosed_rclosed_BI i i

let full = U (UI 0)

let case f1 f2 = function
  | B i -> f1 i
  | U i -> f2 i

let is_bounded_exn op = function
  | B _ -> ()
  | U _ -> raise (Invalid_argument (Printf.sprintf "unbounded future operator: %s" op))

let sub i t = match i with
  | B (BI (a, b)) -> B (BI (a, b - t))
  | U _ -> raise (Invalid_argument (Printf.sprintf "unbounded future operator"))

let sub2 i t = match i with
  | B (BI (a, b)) -> B (BI (max 0 (a - t), max 0 (b - t)))
  | U (UI a) -> U (UI (max 0 (a - t)))

let boundaries = function
  | B (BI (a, b)) -> (a, b)
  | U _ -> raise (Invalid_argument (Printf.sprintf "unbounded future operator"))

let map f1 f2 = case (fun i -> B (f1 i)) (fun i -> U (f2 i))

let mem t =
  let mem_UI t (UI l) = l <= t in
  let mem_BI t (BI (l, r)) = l <= t && t <= r in
  case (mem_BI t) (mem_UI t)

let left =
  let left_UI (UI l) = l in
  let left_BI (BI (l, r)) = l in
  case left_BI left_UI

let right =
  let right_UI (UI l) = None in
  let right_BI (BI (l, r)) = Some(r) in
  case right_BI right_UI

let lub i i' =
  let l = min (left i) (left i') in
  match right i, right i' with
  | Some r, Some r' -> lclosed_rclosed_BI l (max r r')
  | _ -> lclosed_UI l

let below_UI t (UI l) = t < l
let below_BI t (BI (l, r)) = t < l
let below t = case (below_BI t) (below_UI t)

(* Check if t > interval *)
let above_UI t (UI l) = false
let above_BI t (BI (l, r)) = t > r
let above t = case (above_BI t) (above_UI t)

let to_string_BI = function
  | BI (i, j) -> Printf.sprintf "[%d,%d]" i j

let to_string = function
  | U (UI i) -> Printf.sprintf "[%d,∞)" i
  | B i -> Printf.sprintf "%a" (fun x -> to_string_BI) i

let to_latex = function
  | U (UI i) -> Printf.sprintf "[%d,\\infty)" i
  | B i -> Printf.sprintf "%a" (fun x -> to_string_BI) i

let lex error l i j r =
  (match j with
   | "INFINITY" | "∞" | "*" ->
      (match l with
       | '[' -> lclosed_UI (Int.of_string i)
       | '(' -> lopen_UI (Int.of_string i)
       | _ -> error ())
   | _ ->
      (match l, r with
       | '[',']' -> lclosed_rclosed_BI (Int.of_string i) (Int.of_string j)
       | '(',']' -> lopen_rclosed_BI (Int.of_string i) (Int.of_string j)
       | '[',')' -> lclosed_ropen_BI (Int.of_string i) (Int.of_string j)
       | '(',')' -> lopen_ropen_BI (Int.of_string i) (Int.of_string j)
       | _ -> error ()))
