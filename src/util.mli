(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2017:                                                *)
(*  Dmitriy Traytel (ETH Zürich)                                   *)
(*******************************************************************)

exception EMPTY_LIST

module SS: Set.S with type elt = string
type timestamp = int
type timepoint = int
type event = SS.t * timestamp
type trace = event list
type mode = SAT | VIOL | ALL | BOOL

val max_list: int list -> int
val min_list: int list -> int
val ( -- ): int -> int -> int list
val thd: ('a * 'b * 'c) -> 'c
val last: 'a list -> 'a
val paren: int -> int -> ('b, 'c, 'd, 'e, 'f, 'g) format6 -> ('b, 'c, 'd, 'e, 'f, 'g) format6
val sum: ('a -> int) -> 'a list -> int
val prod: ('a -> 'a -> bool) -> ('a -> 'a -> bool) -> 'a -> 'a -> bool
val lex: ('a -> 'a -> bool) -> ('a -> 'a -> bool) -> 'a -> 'a -> bool
val mk_le: ('a -> int) -> 'a -> 'a -> bool
val sl_le: 'a -> 'a -> ('a -> 'a -> bool) -> bool
val list_to_string: string -> (string -> 'a -> string) -> 'a list -> string
val get_mins: ('a -> 'a -> bool) -> 'a list -> 'a list
val drop_front: 'a list -> 'a list
