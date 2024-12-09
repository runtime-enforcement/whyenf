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
open Time

module type B = sig

  type v
  type t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val sexp_of_t : t -> Sexp.t
  val hash_fold_t : Base_internalhash_types.state -> t -> Base_internalhash_types.state

  val has_zero : t -> bool
  val is_zero : t -> bool
  val is_full : t -> bool
  val is_bounded : t -> bool
  val is_nonpositive : t -> bool
  val left : t -> v option
  val right : t -> v option
  val to_string : t -> string
  val to_latex : t -> string
  val make_exn : t -> t

end

module MakeUI (S : S) : B with type v = S.v and type t = S.v = struct

  (* Unbounded [i,+∞) *)
  type v = S.v
  type t = S.v
  
  let compare = S.compare_v
  let sexp_of_t = S.sexp_of_v
  let hash_fold_t = S.hash_fold_v
  let equal = S.equal_v

  let has_zero i = S.is_zero i
  let is_zero _ = false
  let is_full i = S.is_zero i
  let is_bounded _ = false
  let is_nonpositive _ = false
  let left i = Some i
  let right _ = None
  let to_string i = Printf.sprintf "[%s,∞)" (S.to_string i)
  let to_latex i = Printf.sprintf "[%s,\\infty)" (S.to_string i)
  let make_exn i = i

end

module MakeNUI (S : S) : B with type v = S.v and type t = S.v = struct

  (* Unbounded [i,+∞) *)
  type v = S.v
  type t = S.v
  
  let compare = S.compare_v
  let sexp_of_t = S.sexp_of_v
  let hash_fold_t = S.hash_fold_v
  let equal = S.equal_v

  let has_zero i = S.leq S.zero i
  let is_zero _ = false
  let is_full _ = false
  let is_bounded _ = false
  let is_nonpositive i = S.leq i S.zero
  let left _ = None
  let right i = Some i
  let to_string i = Printf.sprintf "(-∞,%s]" (S.to_string i)
  let to_latex i = Printf.sprintf "(-\\infty,%s]" (S.to_string i)
  let make_exn i = i

end

module MakeBI (S : S) : B with type v = S.v and type t = S.v * S.v = struct

  (* Bounded [i,j] *)
  type v = S.v
  type t = S.v * S.v [@@deriving compare, sexp_of, hash, equal]

  let has_zero (i, _) = S.is_zero i
  let is_zero (i, j) = S.is_zero i && S.is_zero j
  let is_full _ = false
  let is_bounded _ = true
  let is_nonpositive (_, j) = S.leq j S.zero
  let left (i, _) = Some i
  let right (_, j) = Some j
  let to_string (i, j) = Printf.sprintf "[%s,%s]" (S.to_string i) (S.to_string j)
  let to_latex = to_string
  let make_exn (l, r) = if S.leq l r then (l, r) else raise (Invalid_argument "empty interval")
  
end

module MakeUUI (S : S) : B with type v = S.v and type t = unit = struct

  (* Bounded [i,j] *)
  type v = S.v
  type t = unit [@@deriving compare, sexp_of, hash, equal]

  let has_zero _ = true
  let is_zero _ = false
  let is_full _ = true
  let is_bounded _ = false
  let is_nonpositive _ = false
  let left _ = None
  let right _ = None
  let to_string _ = "(-∞,∞)"
  let to_latex = to_string
  let make_exn _ = ()
  
end

module MakeInterval (S : S) = struct

  type v = S.v

  module UI = MakeUI(S)
  module BI = MakeBI(S)

  type t = B of BI.t | U of UI.t [@@deriving compare, sexp_of, hash, equal]

  let case f1 f2 = function
    | B bt -> f1 bt
    | U ut -> f2 ut

  let lclosed_UI i = U i
  let lopen_UI i = U (S.inc i)

  let lopen_ropen_BI i j = B (BI.make_exn (S.inc i, S.dec j))
  let lopen_rclosed_BI i j = B (BI.make_exn (S.inc i, j))
  let lclosed_ropen_BI i j = B (BI.make_exn (i, S.dec j))
  let lclosed_rclosed_BI i j = B (BI.make_exn (i, j))

  let singleton i = lclosed_rclosed_BI i i

  let is_zero = case BI.is_zero UI.is_zero
  let has_zero = case BI.has_zero UI.has_zero
  let is_full = case BI.is_full UI.is_full

  let full = U (S.zero)

  let is_bounded = case BI.is_bounded UI.is_bounded
  
  let left i = Option.value_exn (case BI.left UI.left i)
  let right = case BI.right UI.right

  let to_string = case BI.to_string UI.to_string
  let to_latex = case BI.to_latex UI.to_latex

  let diff_right_of ts ts' i =
    match right i with
    | Some b -> S.(ts + b) < ts'
    | None -> false

  let diff_left_of ts ts' i =
    ts' < S.(ts + left i)

  let diff_is_in ts ts' i =
    not (diff_right_of ts ts' i || diff_left_of ts ts' i)


end

include MakeInterval(Span.S)

let lex error l i u j v r =
  match j with
   | "INFINITY" | "∞" | "*" ->
      (match l with
       | '[' -> lclosed_UI (Span.make i u)
       | '(' -> lopen_UI (Span.make i u)
       | _ -> error ())
   | _ ->
      (match l, r with
       | '[',']' -> lclosed_rclosed_BI (Span.make i u) (Span.make j v)
       | '(',']' -> lopen_rclosed_BI (Span.make i u) (Span.make j v)
       | '[',')' -> lclosed_ropen_BI (Span.make i u) (Span.make j v)
       | '(',')' -> lopen_ropen_BI (Span.make i u) (Span.make j v)
       | _ -> error ())


 
