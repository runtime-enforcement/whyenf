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

type t = ZB of bt | ZUL of ut | ZUR of ut | ZU

val equal: t -> t -> bool

val lclosed_UI: Time.t -> t
val lopen_UI: Time.t -> t

val lopen_ropen_BI: Time.t -> Time.t -> t
val lopen_rclosed_BI: Time.t -> Time.t -> t
val lclosed_ropen_BI: Time.t -> Time.t -> t
val lclosed_rclosed_BI: Time.t -> Time.t -> t
val singleton: Time.t -> t
val of_interval: Interval.t -> t

val full: t

val mem: Time.t -> t -> bool

val left: t -> Time.t option
val right: t -> Time.t option

val lub: t -> t -> t
val has_zero: t -> bool
val to_zero: t -> t
val is_nonpositive: t -> bool
val add: Time.t -> t -> t
val sum: t -> t -> t
val inv: t -> t

val to_string: t -> string
val to_latex: t -> string
