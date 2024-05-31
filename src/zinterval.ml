(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Base
open Interval

type t = ZB of bt | ZUL of ut | ZUR of ut | ZU [@@deriving equal]

let lclosed_UI i = ZUR (UI i)
let lopen_UI i = ZUR (UI (Time.inc i))
let rclosed_UI i = ZUL (UI i)
let ropen_UI i = ZUL (UI (Time.inc i))

let nonempty_BI l r = if Time.(l <= r) then BI (l, r) else raise (Invalid_argument "empty interval")
let lopen_ropen_BI i j = ZB (nonempty_BI (Time.inc i) (Time.dec j))
let lopen_rclosed_BI i j = ZB (nonempty_BI (Time.inc i) j)
let lclosed_ropen_BI i j = ZB (nonempty_BI i (Time.dec j))
let lclosed_rclosed_BI i j = ZB (nonempty_BI i j)

let singleton i = lclosed_rclosed_BI i i
let of_interval = function
  | B (BI (a, b)) -> ZB (BI (a, b))
  | U (UI a) -> ZUR (UI a)

let full = ZU

let case f1 f2 f3 f4 = function
  | ZB i -> f1 i
  | ZUL i -> f2 i
  | ZUR i -> f3 i
  | ZU -> f4

let map f1 f2 f3 f4 = case (fun i -> ZB (f1 i)) (fun i -> ZUL (f2 i))
                        (fun i -> ZUL (f3 i)) f4

let mem t =
  let mem_UIL (UI r) = Time.(t <= r) in
  let mem_UIR (UI l) = Time.(l <= t) in
  let mem_BI (BI (l, r)) = Time.(l <= t) && Time.(t <= r) in
  case mem_BI mem_UIL mem_UIR true

let left =
  let left_UIL (UI _) = None in
  let left_UIR (UI l) = Some l in
  let left_BI (BI (l, r)) = Some l in
  case left_BI left_UIL left_UIR None

let right =
  let right_UIL (UI r) = Some r in
  let right_UIR (UI _) = None in
  let right_BI (BI (l, r)) = Some r in
  case right_BI right_UIL right_UIR None

let lub i i' = 
  match left i, left i' with
  | Some l, Some l' -> begin
      match right i, right i' with
      | Some r, Some r' -> lclosed_rclosed_BI (Time.min l l') (Time.max r r')
      | _ -> lclosed_UI (Time.min l l')
    end
  | _, _ ->
     match right i, right i' with
     | Some r, Some r' -> rclosed_UI (Time.max r r')
     | _ -> full

let has_zero = function
  | ZB (BI (l, r)) -> Time.(l <= Time.zero) && Time.(Time.zero <= r)
  | ZUL (UI r) -> Time.(Time.zero <= r)
  | ZUR (UI l) -> Time.(l <= Time.zero)
  | ZU -> true

let to_zero i = lub (singleton Time.zero) i

let is_nonpositive =
  let isnp_BI (BI (_, r)) = Time.(r <= Time.zero) in
  let isnp_UIL (UI r) = Time.(r <= Time.zero) in
  let isnp_UIR _ = false in
  case isnp_BI isnp_UIL isnp_UIR false

let add x =
  let add_UI (UI r) = UI Time.(r+x) in
  let add_BI (BI (l, r)) = BI (Time.(l + x), Time.(r + x)) in
  map add_BI add_UI add_UI ZU

let sum i i' =
  match left i, left i' with
  | Some l, Some l' -> begin
      match right i, right i' with
      | Some r, Some r' -> lclosed_rclosed_BI (Time.(l + l')) (Time.(r + r'))
      | _ -> lclosed_UI (Time.(l + l'))
    end
  | _, _ ->
     match right i, right i' with
     | Some r, Some r' -> rclosed_UI (Time.(r + r'))
     | _ -> full

let inv =
  let inv_UIL (UI r) = ZUR (UI (Time.inv r)) in
  let inv_UIR (UI l) = ZUL (UI (Time.inv l)) in
  let inv_BI (BI (l, r)) = ZB (BI (Time.inv r, Time.inv l)) in
  case inv_BI inv_UIL inv_UIR ZU

let to_string_BI = function
  | BI (i, j) -> Printf.sprintf "[%s,%s]" (Time.to_string i) (Time.to_string j)

let to_string = function
  | ZB i -> Printf.sprintf "%a" (fun x -> to_string_BI) i
  | ZUL (UI i) -> Printf.sprintf "(-∞,%s]" (Time.to_string i)
  | ZUR (UI i) -> Printf.sprintf "[%s,∞)" (Time.to_string i)
  | ZU -> Printf.sprintf "(-∞,∞)"

let to_latex = function
  | ZB i -> Printf.sprintf "%a" (fun x -> to_string_BI) i
  | ZUL (UI i) -> Printf.sprintf "(-\\infty,%s]" (Time.to_string i)
  | ZUR (UI i) -> Printf.sprintf "[%s,\\infty)" (Time.to_string i)
  | ZU -> Printf.sprintf "(-\\infty,\\infty)" 
