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
open Time

type t = ZB of bt | ZUL of ut | ZUR of ut | ZU [@@deriving equal]

let lclosed_UI i = ZUR (UI i)
let lopen_UI i = ZUR (UI (Span.inc i))
let rclosed_UI i = ZUL (UI i)
let ropen_UI i = ZUL (UI (Span.inc i))

let nonempty_BI l r = if Span.(l <= r) then BI (l, r) else raise (Invalid_argument "empty interval")
let lopen_ropen_BI i j = ZB (nonempty_BI (Span.inc i) (Span.dec j))
let lopen_rclosed_BI i j = ZB (nonempty_BI (Span.inc i) j)
let lclosed_ropen_BI i j = ZB (nonempty_BI i (Span.dec j))
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
  let mem_UIL (UI r) = Span.(t <= r) in
  let mem_UIR (UI l) = Span.(l <= t) in
  let mem_BI (BI (l, r)) = Span.(l <= t) && Span.(t <= r) in
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
      | Some r, Some r' -> lclosed_rclosed_BI (Span.min l l') (Span.max r r')
      | _ -> lclosed_UI (Span.min l l')
    end
  | _, _ ->
     match right i, right i' with
     | Some r, Some r' -> rclosed_UI (Span.max r r')
     | _ -> full

let has_zero = function
  | ZB (BI (l, r)) -> Span.(l <= Span.zero) && Span.(Span.zero <= r)
  | ZUL (UI r) -> Span.(Span.zero <= r)
  | ZUR (UI l) -> Span.(l <= Span.zero)
  | ZU -> true

let to_zero i = lub (singleton Span.zero) i

let is_nonpositive =
  let isnp_BI (BI (_, r)) = Span.(r <= Span.zero) in
  let isnp_UIL (UI r) = Span.(r <= Span.zero) in
  let isnp_UIR _ = false in
  case isnp_BI isnp_UIL isnp_UIR false

let add x =
  let add_UI (UI r) = UI Span.(r + x) in
  let add_BI (BI (l, r)) = BI (Span.(l + x), Span.(r + x)) in
  map add_BI add_UI add_UI ZU

let sum i i' =
  match left i, left i' with
  | Some l, Some l' -> begin
      match right i, right i' with
      | Some r, Some r' -> lclosed_rclosed_BI (Time.Span.(l + l')) (Time.Span.(r + r'))
      | _ -> lclosed_UI (Time.Span.(l + l'))
    end
  | _, _ ->
     match right i, right i' with
     | Some r, Some r' -> rclosed_UI (Time.Span.(r + r'))
     | _ -> full

let inv =
  let inv_UIL (UI r) = ZUR (UI (Span.inv r)) in
  let inv_UIR (UI l) = ZUL (UI (Span.inv l)) in
  let inv_BI (BI (l, r)) = ZB (BI (Span.inv r, Span.inv l)) in
  case inv_BI inv_UIL inv_UIR ZU

let to_string_BI = function
  | BI (i, j) -> Printf.sprintf "[%s,%s]" (Span.to_string i) (Span.to_string j)

let to_string = function
  | ZB i -> Printf.sprintf "%a" (fun x -> to_string_BI) i
  | ZUL (UI i) -> Printf.sprintf "(-∞,%s]" (Span.to_string i)
  | ZUR (UI i) -> Printf.sprintf "[%s,∞)" (Span.to_string i)
  | ZU -> Printf.sprintf "(-∞,∞)"

let to_latex = function
  | ZB i -> Printf.sprintf "%a" (fun x -> to_string_BI) i
  | ZUL (UI i) -> Printf.sprintf "(-\\infty,%s]" (Span.to_string i)
  | ZUR (UI i) -> Printf.sprintf "[%s,\\infty)" (Span.to_string i)
  | ZU -> Printf.sprintf "(-\\infty,\\infty)" 
