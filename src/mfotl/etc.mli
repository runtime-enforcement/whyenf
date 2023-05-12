(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

val eat: string -> string -> string
val paren: int -> int -> ('b, 'c, 'd, 'e, 'f, 'g) format6 -> ('b, 'c, 'd, 'e, 'f, 'g) format6

exception Parsing_error of Lexing.position*Lexing.position*string
val parsing_error: Lexing.position -> Lexing.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val lexing_error: Lexing.lexbuf -> ('a, Format.formatter, unit, 'b) format4 -> 'a
