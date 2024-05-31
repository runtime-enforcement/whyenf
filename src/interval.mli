(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

type ut = UI of Time.t [@@deriving compare, sexp_of, hash, equal]
type bt = BI of Time.t * Time.t [@@deriving compare, sexp_of, hash, equal]
type t = B of bt | U of ut [@@deriving compare, sexp_of, hash, equal]

val equal: t -> t -> bool

val lclosed_UI: Time.t -> t
val lopen_UI: Time.t -> t

val lopen_ropen_BI: Time.t -> Time.t -> t
val lopen_rclosed_BI: Time.t -> Time.t -> t
val lclosed_ropen_BI: Time.t -> Time.t -> t
val lclosed_rclosed_BI: Time.t -> Time.t -> t
val singleton: Time.t -> t
val is_zero: t -> bool

val full: t

val is_bounded_exn: string -> t -> unit
val is_bounded: t -> bool

val sub: t -> Time.t -> t
val sub2: t -> Time.t -> t
val boundaries: t -> Time.t * Time.t

val mem: Time.t -> t -> bool

val left: t -> Time.t
val right: t -> Time.t option

val lub: t -> t -> t

val below: Time.t -> t -> bool
val above: Time.t -> t -> bool

val to_string: t -> string
val to_latex: t -> string
val lex: (unit -> t) -> char -> string -> string -> string -> string -> char -> t

val has_zero: t -> bool
val is_zero: t -> bool
val is_full: t -> bool
