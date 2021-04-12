(*******************************************************************)
(*     This is part of Aerial, it is distributed under the         *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2017:                                                *)
(*  Dmitriy Traytel (ETH Zürich)                                   *)
(*******************************************************************)

type mode = NAIVE | COMPRESS_LOCAL | COMPRESS_GLOBAL

module SS: Set.S with type elt = string
type ts = int
type tp = int
type ts_asc_list = ts list
type ts_desc_list = ts list
type trace = (SS.t * ts) list

val ( -- ): int -> int -> int list
val paren: int -> int -> ('b, 'c, 'd, 'e, 'f, 'g) format6 -> ('b, 'c, 'd, 'e, 'f, 'g) format6
val sum: ('a -> int) -> 'a list -> int
val mk_le: ('a -> int) -> 'a -> 'a -> bool
val prod_le: ('a -> 'a -> bool) -> ('a -> 'a -> bool) -> 'a -> 'a -> bool
