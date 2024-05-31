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
type ut = UI of Time.t [@@deriving compare, sexp_of, hash, equal]

(* Bounded [i,j] *)
type bt = BI of Time.t * Time.t [@@deriving compare, sexp_of, hash, equal]

type t = B of bt | U of ut [@@deriving compare, sexp_of, hash, equal]

let lclosed_UI i = U (UI i)
let lopen_UI i = U (UI (Time.inc i))

let nonempty_BI l r = if Time.(l <= r) then BI (l, r) else raise (Invalid_argument "empty interval")
let lopen_ropen_BI i j = B (nonempty_BI (Time.inc i) (Time.dec j))
let lopen_rclosed_BI i j = B (nonempty_BI (Time.inc i) j)
let lclosed_ropen_BI i j = B (nonempty_BI i (Time.dec j))
let lclosed_rclosed_BI i j = B (nonempty_BI i j)

let singleton i = lclosed_rclosed_BI i i

let is_zero = function
  | U _ -> false
  | B (BI (i, j)) -> Time.is_zero i && Time.equal i j

let has_zero = function
  | U (UI i) -> Time.is_zero i
  | B (BI (i, j)) -> Time.is_zero i

let is_full = function
  | U (UI i) -> Time.is_zero i
  | B _ -> false

let full = U (UI Time.zero)

let case f1 f2 = function
  | B i -> f1 i
  | U i -> f2 i

let is_bounded = function
  | B _ -> true
  | U _ -> false

let is_bounded_exn op = function
  | B _ -> ()
  | U _ -> raise (Invalid_argument (Printf.sprintf "unbounded future operator: %s" op))

let sub i t = match i with
  | B (BI (a, b)) -> B (BI (a, Time.(b - t)))
  | U _ -> raise (Invalid_argument (Printf.sprintf "unbounded future operator"))

let sub2 i t = match i with
  | B (BI (a, b)) -> B (BI (Time.(a |- t), Time.(b |- t)))
  | U (UI a) -> U (UI (Time.(a |- t)))

let boundaries = function
  | B (BI (a, b)) -> (a, b)
  | U _ -> raise (Invalid_argument (Printf.sprintf "unbounded future operator"))

let map f1 f2 = case (fun i -> B (f1 i)) (fun i -> U (f2 i))

let mem t =
  let mem_UI t (UI l) = Time.(l <= t) in
  let mem_BI t (BI (l, r)) = Time.(l <= t) && Time.(t <= r) in
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
  let l = Time.min (left i) (left i') in
  match right i, right i' with
  | Some r, Some r' -> lclosed_rclosed_BI l (Time.max r r')
  | _ -> lclosed_UI l

let below_UI t (UI l) = Time.(t < l)
let below_BI t (BI (l, r)) = Time.(t < l)
let below t = case (below_BI t) (below_UI t)

(* Check if t > interval *)
let above_UI t (UI l) = false
let above_BI t (BI (l, r)) = Time.(r < t)
let above t = case (above_BI t) (above_UI t)

let to_string_BI = function
  | BI (i, j) -> Printf.sprintf "[%s,%s]" (Time.to_string i) (Time.to_string j)

let to_string = function
  | U (UI i) -> Printf.sprintf "[%s,∞)" (Time.to_string i)
  | B i -> Printf.sprintf "%a" (fun x -> to_string_BI) i

let to_latex = function
  | U (UI i) -> Printf.sprintf "[%s,\\infty)" (Time.to_string i)
  | B i -> Printf.sprintf "%a" (fun x -> to_string_BI) i

let lex error l i u j v r =
  let i = Int.of_string i in
  match j with
   | "INFINITY" | "∞" | "*" ->
      (match l with
       | '[' -> lclosed_UI (Time.make i u)
       | '(' -> lopen_UI (Time.make i u)
       | _ -> error ())
   | _ ->
      (let j = Int.of_string j in
       match l, r with
       | '[',']' -> lclosed_rclosed_BI (Time.make i u) (Time.make j v)
       | '(',']' -> lopen_rclosed_BI (Time.make i u) (Time.make j v)
       | '[',')' -> lclosed_ropen_BI (Time.make i u) (Time.make j v)
       | '(',')' -> lopen_ropen_BI (Time.make i u) (Time.make j v)
       | _ -> error ())


  
