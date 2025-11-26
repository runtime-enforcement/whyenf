open Base
open Interval
open Time

module Z = struct

  type v = int

  let equal_v = Int.equal
  let compare_v = Int.compare
  let sexp_of_v = Int.sexp_of_t
  let hash_fold_v = Int.hash_fold_t

  let min_seconds i = i
  let max_seconds i = i
  let leq = Int.(<=)
  let (+) t _ = t
  let inc i = Int.(i + 1)
  let dec i = Int.(i - 1)
  let is_zero i = Int.(i = 0)
  let zero = 0
  let to_string = Int.to_string
  let to_json = to_string

end
  
module MakeZinterval (S : S) = struct

  type v = Z.v

  module UI = MakeUI(Z)
  module NUI = MakeNUI(Z)
  module BI = MakeBI(Z)
  module UUI = MakeUUI(Z)

  module SInterval = MakeInterval(S)
  
  type t = ZB of BI.t | ZUL of NUI.t | ZUR of UI.t | ZU of UUI.t [@@deriving equal]

  let case f1 f2 f3 f4 = function
    | ZB i -> f1 i
    | ZUL i -> f2 i
    | ZUR i -> f3 i
    | ZU i -> f4 i

  let lclosed_UI i = ZUR i
  let lopen_UI i = ZUR (Z.inc i)
  let rclosed_UI i = ZUL i
  let ropen_UI i = ZUL (Z.inc i)

  let lopen_ropen_BI i j = ZB (BI.make_exn (Z.inc i, Z.dec j))
  let lopen_rclosed_BI i j = ZB (BI.make_exn (Z.inc i, j))
  let lclosed_ropen_BI i j = ZB (BI.make_exn (i, Z.dec j))
  let lclosed_rclosed_BI i j = ZB (BI.make_exn (i, j))
  let singleton i = lclosed_rclosed_BI i i

  let is_zero = case BI.is_zero NUI.is_zero UI.is_zero UUI.is_zero
  let has_zero = case BI.has_zero NUI.has_zero UI.has_zero UUI.has_zero
  let is_full = function
    | ZU _ -> true
    | _ -> false

  let full = ZU ()

  let is_bounded = case BI.is_bounded NUI.is_bounded UI.is_bounded UUI.is_bounded
  let is_nonpositive = case BI.is_nonpositive NUI.is_nonpositive UI.is_nonpositive UUI.is_nonpositive

  let left = case BI.left NUI.left UI.left UUI.left
  let right = case BI.right NUI.right UI.right UUI.right 

  let lub i i' = 
    match left i, left i' with
    | Some l, Some l' -> begin
        match right i, right i' with
        | Some r, Some r' -> lclosed_rclosed_BI (Int.min l l') (Int.max r r')
        | _ -> lclosed_UI (Int.min l l')
      end
    | _, _ ->
       match right i, right i' with
       | Some r, Some r' -> rclosed_UI (Int.max r r')
       | _ -> full

  let sum i i' =
    match left i, left i' with
    | Some l, Some l' -> begin
        match right i, right i' with
        | Some r, Some r' -> lclosed_rclosed_BI (Int.(l + l')) (Int.(r + r'))
        | _ -> lclosed_UI (Int.(l + l'))
      end
    | _, _ ->
       match right i, right i' with
       | Some r, Some r' -> rclosed_UI (Int.(r + r'))
       | _ -> full

  let inv = function
    | ZB (l, r) -> ZB (Int.(- r), Int.(- l))
    | ZUL l -> ZUR Int.(- l)
    | ZUR l -> ZUL Int.(- l)
    | ZU () -> ZU ()

  let mem t =
    let mem_BI (l, r) = Int.(l <= t) && Int.(t <= r) in
    let mem_UIL r = Int.(t <= r) in
    let mem_UIR l = Int.(l <= t) in
    let mem_UUI () = true in
    case mem_BI mem_UIL mem_UIR mem_UUI

  let to_zero i = lub (singleton 0) i
  
  let of_interval = function
    | (B (a, b) : SInterval.t) -> ZB (S.min_seconds a, S.max_seconds b)
    | U a -> ZUR (S.min_seconds a)

  let to_string = case BI.to_string NUI.to_string UI.to_string UUI.to_string
  let to_latex = case BI.to_latex NUI.to_latex UI.to_latex UUI.to_latex
  let to_json = case BI.to_json NUI.to_json UI.to_json UUI.to_json


end

include MakeZinterval(Span.S)
