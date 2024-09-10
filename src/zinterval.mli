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

open Interval
open Time

type t = ZB of bt | ZUL of ut | ZUR of ut | ZU

val equal: t -> t -> bool

val lclosed_UI: Span.t -> t
val lopen_UI: Span.t -> t

val lopen_ropen_BI: Span.t -> Span.t -> t
val lopen_rclosed_BI: Span.t -> Span.t -> t
val lclosed_ropen_BI: Span.t -> Span.t -> t
val lclosed_rclosed_BI: Span.t -> Span.t -> t
val singleton: Span.t -> t
val of_interval: Interval.t -> t

val full: t

val mem: Span.t -> t -> bool

val left: t -> Span.t option
val right: t -> Span.t option

val lub: t -> t -> t
val has_zero: t -> bool
val to_zero: t -> t
val is_nonpositive: t -> bool
val add: Span.t -> t -> t
val sum: t -> t -> t
val inv: t -> t

val to_string: t -> string
val to_latex: t -> string
