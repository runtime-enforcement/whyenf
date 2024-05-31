(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Core

type timepoint = int
type timestamp = int

val debug: bool ref
val inc_ref: Stdio.In_channel.t ref
val outc_ref: Stdio.Out_channel.t ref

val eat: string -> string -> string
val paren: int -> int -> ('b, 'c, 'd, 'e, 'f, 'g) format6 -> ('b, 'c, 'd, 'e, 'f, 'g) format6
val is_digit: char -> bool

exception Parsing_error of Lexing.position*Lexing.position*string
val parsing_error: Lexing.position -> Lexing.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val lexing_error: Lexing.lexbuf -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val lexbuf_error_msg: Lexing.lexbuf -> string

exception Empty_deque of string
val deque_to_string: string -> (string -> 'a -> string) -> 'a Core.Fdeque.t -> string

val queue_drop: 'a Base.Queue.t -> int -> 'a Base.Queue.t

val list_to_string: string -> (string -> 'a -> string) -> 'a list -> string

val string_list_to_string: string list -> string

val some_string: unit -> string

val string_list_to_json: string list -> string

type valuation = (string, Dom.t, String.comparator_witness) Map.t

val compare_valuation: valuation -> valuation -> int
val empty_valuation: valuation

val dom_map_to_string: (string, Dom.t, String.comparator_witness) Map.t -> string
val valuation_to_string: (string, Dom.t, String.comparator_witness) Map.t -> string

val int_list_to_json: int list -> string

val unquote: string -> string

val escape_underscores: string -> string

val fdeque_for_all2_exn: 'a Fdeque.t -> 'b Fdeque.t -> f:('a -> 'b -> bool) -> bool

val spaces: int -> string

val lexicographic2: ('a -> 'a -> int) -> ('b -> 'b -> int) -> ('a * 'b) -> ('a * 'b) -> int
val lexicographic3: ('a -> 'a -> int) -> ('b -> 'b -> int) -> ('c -> 'c -> int) -> ('a * 'b * 'c) -> ('a * 'b * 'c) -> int
val lexicographic4: ('a -> 'a -> int) -> ('b -> 'b -> int) -> ('c -> 'c -> int) -> ('d -> 'd -> int) -> ('a * 'b * 'c * 'd) -> ('a * 'b * 'c * 'd) -> int
val lexicographic5: ('a -> 'a -> int) -> ('b -> 'b -> int) -> ('c -> 'c -> int) -> ('d -> 'd -> int) -> ('e -> 'e -> int) -> ('a * 'b * 'c * 'd * 'e) -> ('a * 'b * 'c * 'd * 'e) -> int


(* For debugging only *)
val _print: string -> ('a -> string) -> 'a -> 'a

val reorder: ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
