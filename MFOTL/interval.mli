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

module MakeUI (S : S) : B with type v = S.v and type t = S.v
module MakeNUI (S : S) : B with type v = S.v and type t = S.v
module MakeBI (S : S) : B with type v = S.v and type t = S.v * S.v
module MakeUUI (S : S) : B with type v = S.v and type t = unit

module MakeInterval (S : S) : sig

  type v = S.v

  module UI : B with type v = S.v and type t = S.v
  module BI : B with type v = S.v and type t = S.v * S.v
  
  type t = B of BI.t | U of UI.t [@@deriving compare, sexp_of, hash, equal]

  val equal: t -> t -> bool
  
  val lclosed_UI: v -> t
  val lopen_UI: v -> t

  val lopen_ropen_BI: v -> v -> t
  val lopen_rclosed_BI: v -> v -> t
  val lclosed_ropen_BI: v -> v -> t
  val lclosed_rclosed_BI: v -> v -> t
  val singleton: v -> t

  val is_zero: t -> bool
  val has_zero: t -> bool
  val is_full: t -> bool

  val full: t

  val is_bounded: t -> bool

  val left: t -> v
  val right: t -> v option

  val diff_right_of: Time.t -> Time.t -> t -> bool
  val diff_left_of: Time.t -> Time.t -> t -> bool
  val diff_is_in: Time.t -> Time.t -> t -> bool

  val to_string: t -> string
  val to_latex: t -> string

end

include module type of MakeInterval(Time.Span.S) with type v = Time.Span.s

val lex: (unit -> t) -> char -> string -> string -> string -> string -> char -> t

