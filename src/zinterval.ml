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

module Z = struct

  type v = float

  let equal_v = Float.equal
  let compare_v = Float.compare
  let sexp_of_v = Float.sexp_of_t
  let hash_fold_v = Float.hash_fold_t

  let min_seconds i = i
  let max_seconds i = i
  let leq = Float.(<=)
  let (+) t u = assert false
  let inc i = Float.(i + 1.)
  let dec i = Float.(i - 1.)
  let is_zero i = Float.(i = 0.)
  let zero = 0.
  let to_string = string_of_float

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
        | Some r, Some r' -> lclosed_rclosed_BI (Float.min l l') (Float.max r r')
        | _ -> lclosed_UI (Float.min l l')
      end
    | _, _ ->
       match right i, right i' with
       | Some r, Some r' -> rclosed_UI (Float.max r r')
       | _ -> full

  let sum i i' =
    match left i, left i' with
    | Some l, Some l' -> begin
        match right i, right i' with
        | Some r, Some r' -> lclosed_rclosed_BI (Float.(l + l')) (Float.(r + r'))
        | _ -> lclosed_UI (Float.(l + l'))
      end
    | _, _ ->
       match right i, right i' with
       | Some r, Some r' -> rclosed_UI (Float.(r + r'))
       | _ -> full

  let inv = function
    | ZB (l, r) -> ZB (Float.(- r), Float.(- l))
    | ZUL l -> ZUR Float.(- l)
    | ZUR l -> ZUL Float.(- l)
    | ZU () -> ZU ()

  let to_zero i = lub (singleton 0.) i
  
  let of_interval = function
    | (B (a, b) : SInterval.t) -> ZB (S.min_seconds a, S.max_seconds b)
    | U a -> ZUR (S.min_seconds a)

  let to_string = case BI.to_string NUI.to_string UI.to_string UUI.to_string
  let to_latex = case BI.to_latex NUI.to_latex UI.to_latex UUI.to_latex


end

include MakeZinterval(Span.S)
