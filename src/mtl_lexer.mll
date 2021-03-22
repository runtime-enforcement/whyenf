{
(*******************************************************************)
(*     This is part of Aerial, it is distributed under the         *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2017:                                                *)
(*  Dmitriy Traytel (ETH Zürich)                                   *)
(*******************************************************************)

open Interval
open Mtl_parser
open Mtl

(* lexing/parsing errors *)
open Lexing
exception ParsingError_ of position*position*string
exception ParsingError of string

let parsing_error i j fmt = Format.kasprintf (fun s -> raise (ParsingError_(i,j,s))) fmt
let lexing_error lexbuf fmt = parsing_error (lexeme_start_p lexbuf) (lexeme_end_p lexbuf) fmt

let interval lexbuf = lex_interval (fun () -> lexing_error lexbuf "bad interval")
}

let blank = [' ' '\t' ]+
let newline = ['\r' '\n' ] | "\r\n"
let num = ['0'-'9' ]+
let alpha = ['a'-'z' 'A'-'Z' '$']
let alphanums = ['a'-'z' 'A'-'Z' '$' '0'-'9' '_' '\'' '"' ]*

rule token = parse
  | newline                                       { Lexing.new_line lexbuf; token lexbuf }
  | blank                                         { token lexbuf }
  | "false" | "⊥"                                 { FALSE }
  | "true" | "⊤" 		                  { TRUE }
  | '!' | "¬" | "NOT"                             { NEG }
  | '&' | "∧" | "AND"                             { CONJ }
  | '|' | "∨" | "OR"                              { DISJ }
  | "=>" | "->" | "→"                             { IMPL }
  | "<=>"  | "<->" | "↔"                          { IFF }
  | "SINCE" | "S" | "U⁻"                          { SINCE }
  | "UNTIL" |	"U"                               { UNTIL }
  | "WEAK_UNTIL" | "W"                            { WUNTIL }
  | "RELEASE" | "R" 		                  { RELEASE }
  | "TRIGGER" |	"T"	| "R⁻"                    { TRIGGER }
  | "NEXT" | "X" | "○"	                          { NEXT }
  | "PREV" | "PREVIOUS" | "Y" | "X⁻" | "●" 	  { PREV }
  | "GLOBALLY" | "ALWAYS" | "G" | "□" 	          { ALWAYS }
  | "FINALLY" | "EVENTUALLY" | "F" | "◊"          { EVENTUALLY }
  | "GLOBALLY_PAST" | "HISTORICALLY" | "G⁻" | "■" { HISTORICALLY }
  | "FINALLY_PAST" | "ONCE" | "F⁻" | "⧫"          { ONCE }
  | "("                                           { LOPEN }
  | ")"                                           { ROPEN }
  | (alpha alphanums)	as name "()"?             { ATOM name }
  | (['(' '['] as l) blank* (num as i) blank* "," blank* ((num | "INFINITY" | "∞") as j) blank* ([')' ']'] as r)
                                                  { INTERVAL (interval lexbuf l i j r) }
  | "/*"                                          { skip 1 lexbuf }
  | '#'                                           { skip_line lexbuf }
  | _ as c                                        { lexing_error lexbuf "unexpected character: `%c'" c }
  | eof                                           { EOF }

and skip n = parse
  | newline                           { Lexing.new_line lexbuf; skip n lexbuf }
  | "*/"                              { if n=1 then token lexbuf else skip (n-1) lexbuf }
  | "/*"                              { skip (n+1) lexbuf }
  | _                                 { skip n lexbuf }
  | eof                               { lexing_error lexbuf "unterminated comment" }

and skip_line = parse
  | newline                           { Lexing.new_line lexbuf; token lexbuf }
  | _                                 { skip_line lexbuf }
  | eof                               { EOF }
