(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2017:                                                *)
(*  Dmitriy Traytel (ETH Zürich)                                   *)
(*******************************************************************)

module SS: Set.S with type elt = string
type timestamp = int
type timepoint = int
type event = SS.t * timestamp
type trace = event list
type mode = SAT | VIOL | ALL

val max_list: int list -> int
val min_list: int list -> int
val ( -- ): int -> int -> int list
val last: 'a list -> 'a
val paren: int -> int -> ('b, 'c, 'd, 'e, 'f, 'g) format6 -> ('b, 'c, 'd, 'e, 'f, 'g) format6
val sum: ('a -> int) -> 'a list -> int
val prod_le: ('a -> 'a -> bool) -> ('a -> 'a -> bool) -> 'a -> 'a -> bool
val lex_le: ('a -> 'a -> bool) -> ('a -> 'a -> bool) -> 'a -> 'a -> bool
val mk_le: ('a -> int) -> 'a -> 'a -> bool
val mk_sl: ('a -> int) -> 'a -> 'a -> bool
val list_to_string: string -> (string -> 'a -> string) -> 'a list -> string
val get_mins: ('a -> 'a -> bool) -> 'a list -> 'a list
