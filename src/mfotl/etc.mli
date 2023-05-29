(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

type timepoint = int
type timestamp = int

val debug: bool ref
val inc_ref: Stdio.In_channel.t ref
val outc_ref: Stdio.Out_channel.t ref

val eat: string -> string -> string
val paren: int -> int -> ('b, 'c, 'd, 'e, 'f, 'g) format6 -> ('b, 'c, 'd, 'e, 'f, 'g) format6

exception Parsing_error of Lexing.position*Lexing.position*string
val parsing_error: Lexing.position -> Lexing.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val lexing_error: Lexing.lexbuf -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val lexbuf_error_msg: Lexing.lexbuf -> string

exception Empty_deque of string
val deque_to_string: string -> (string -> 'a -> string) -> 'a Core_kernel.Fdeque.t -> string

val queue_drop: 'a Base.Queue.t -> int -> 'a Base.Queue.t

val list_to_string: string -> (string -> 'a -> string) -> 'a list -> string

val string_list_to_string: string list -> string

val some_string: unit -> string

val list_to_json: string list -> string
