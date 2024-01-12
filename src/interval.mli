(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

type ut = UI of int [@@deriving compare, sexp_of, hash]
type bt = BI of int * int [@@deriving compare, sexp_of, hash]
type t = B of bt | U of ut [@@deriving compare, sexp_of, hash]

val equal: t -> t -> bool

val lclosed_UI: int -> t
val lopen_UI: int -> t

val lopen_ropen_BI: int -> int -> t
val lopen_rclosed_BI: int -> int -> t
val lclosed_ropen_BI: int -> int -> t
val lclosed_rclosed_BI: int -> int -> t
val singleton: int -> t
val is_zero: t -> bool

val full: t

val is_bounded_exn: string -> t -> unit

val sub: t -> int -> t
val sub2: t -> int -> t
val boundaries: t -> int * int

val mem: int -> t -> bool

val left: t -> int
val right: t -> int option

val lub: t -> t -> t

val below: int -> t -> bool
val above: int -> t -> bool

val to_string: t -> string
val to_latex: t -> string
val lex: (unit -> t) -> char -> string -> string -> char -> t
