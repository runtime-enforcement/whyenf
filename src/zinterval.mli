(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Interval

type t = ZB of bt | ZUL of ut | ZUR of ut | ZU

val equal: t -> t -> bool

val lclosed_UI: int -> t
val lopen_UI: int -> t

val lopen_ropen_BI: int -> int -> t
val lopen_rclosed_BI: int -> int -> t
val lclosed_ropen_BI: int -> int -> t
val lclosed_rclosed_BI: int -> int -> t
val singleton: int -> t
val of_interval: Interval.t -> t

val full: t

val mem: int -> t -> bool

val left: t -> int option
val right: t -> int option

val lub: t -> t -> t
val to_zero: t -> t
val is_nonpositive: t -> bool
val add: int -> t -> t
val sum: t -> t -> t
val inv: t -> t

val to_string: t -> string
val to_latex: t -> string
