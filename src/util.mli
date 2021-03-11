(*******************************************************************)
(*     This is part of Aerial, it is distributed under the         *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2017:                                                *)
(*  Dmitriy Traytel (ETH Zürich)                                   *)
(*******************************************************************)


val ( -- ): int -> int -> int list
val paren: int -> int -> ('b, 'c, 'd, 'e, 'f, 'g) format6 -> ('b, 'c, 'd, 'e, 'f, 'g) format6

module SS: Set.S with type elt = string
type timestamp = int
type trace = (SS.t * timestamp) list

type binterval
type uinterval
type interval

val lclosed_UI: int -> interval
val lclosed_rclosed_BI: int -> int -> interval
val lclosed_ropen_BI: int -> int -> interval
val lopen_UI: int -> interval
val lopen_rclosed_BI: int -> int -> interval
val lopen_ropen_BI: int -> int -> interval
val mem_I: int -> interval -> bool
val right_BI: binterval -> int
val right_I: interval -> int
val full: interval
val subtract_I: int -> interval -> interval
val multiply_I: int -> interval -> interval
val case_I: (binterval -> 'a) -> (uinterval -> 'a) -> interval -> 'a
val interval_to_string: interval -> string


type mode = NAIVE | COMPRESS_LOCAL | COMPRESS_GLOBAL

val lex_interval: (unit -> interval) -> char -> string -> string -> char -> interval