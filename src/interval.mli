(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

type ut = UI of int
type bt = BI of int * int
type t = B of bt | U of ut

val lclosed_UI: int -> t
val lopen_UI: int -> t

val lopen_ropen_BI: int -> int -> t
val lopen_rclosed_BI: int -> int -> t
val lclosed_ropen_BI: int -> int -> t
val lclosed_rclosed_BI: int -> int -> t

val full: t

val mem: int -> t -> bool

val left: t -> int
val right: t -> int option

val below: int -> t -> bool
val above: int -> t -> bool

val to_string: t -> string
val to_latex: t -> string
val lex: (unit -> t) -> char -> string -> string -> char -> t
