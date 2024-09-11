(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

type ut = UI of Time.Span.t [@@deriving compare, sexp_of, hash, equal]
type bt = BI of Time.Span.t * Time.Span.t [@@deriving compare, sexp_of, hash, equal]
type t = B of bt | U of ut [@@deriving compare, sexp_of, hash, equal]

val equal: t -> t -> bool

val lclosed_UI: Time.Span.t -> t
val lopen_UI: Time.Span.t -> t

val lopen_ropen_BI: Time.Span.t -> Time.Span.t -> t
val lopen_rclosed_BI: Time.Span.t -> Time.Span.t -> t
val lclosed_ropen_BI: Time.Span.t -> Time.Span.t -> t
val lclosed_rclosed_BI: Time.Span.t -> Time.Span.t -> t
val singleton: Time.Span.t -> t
val is_zero: t -> bool

val full: t

val is_bounded_exn: string -> t -> unit
val is_bounded: t -> bool

val sub: t -> Time.Span.t -> t
val boundaries: t -> Time.Span.t * Time.Span.t

val mem: Time.Span.t -> t -> bool

val left: t -> Time.Span.t
val right: t -> Time.Span.t option

val diff_right_of: Time.t -> Time.t -> t -> bool

val lub: t -> t -> t

val below: Time.Span.t -> t -> bool
val above: Time.Span.t -> t -> bool

val to_string: t -> string
val to_latex: t -> string
val lex: (unit -> t) -> char -> string -> string -> string -> string -> char -> t

val has_zero: t -> bool
val is_zero: t -> bool
val is_full: t -> bool
