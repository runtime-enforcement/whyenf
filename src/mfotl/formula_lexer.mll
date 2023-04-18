{
(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Formula
open Formula_parser
open Lexing

exception Parsing_Error of position*position*string

let parsing_error i j fmt = Format.kasprintf (fun s -> raise (Parsing_Error(i,j,s))) fmt
let lexing_error lexbuf fmt = parsing_error (lexeme_start_p lexbuf) (lexeme_end_p lexbuf) fmt

let make_interval lexbuf = Interval.lex (fun () -> lexing_error lexbuf "Couldn't lex one of the intervals")

}

let blank = [' ' '\t']+
let newline = ['\r' '\n' ] | "\r\n"

let lc = ['a'-'z']
let uc = ['A'-'Z']
let letter = uc | lc
let digit = ['0'-'9']

let digits = ['0'-'9']+
let string = (letter | digit | '_' | '[' | ']' | '/' | '-' | '.' | '!')+

rule token = parse
  | newline                                       { Lexing.new_line lexbuf; token lexbuf }
  | blank                                         { token lexbuf }
  | "false" | "⊥"                                 { FALSE }
  | "true" | "⊤"                                  { TRUE }
  | '!' | "¬" | "NOT"                             { NEG }
  | '&' | "∧" | "AND"                             { CONJ }
  | '|' | "∨" | "OR"                              { DISJ }
  | "=>" | "->" | "→" | "IMPLIES"                 { IMP }
  | "<=>"  | "<->" | "↔" | "IFF"                  { IFF }
  | "∃"  | "EXISTS"                               { EXISTS }
  | "∀"  | "FORALL"                               { FORALL }
  | "SINCE" | "S" | "U⁻"                          { SINCE }
  | "UNTIL" |	"U"                               { UNTIL }
  | "RELEASE" | "R"                               { RELEASE }
  | "TRIGGER" |	"T"	| "R⁻"                    { TRIGGER }
  | "NEXT" | "X" | "○"                            { NEXT }
  | "PREV" | "PREVIOUS" | "Y" | "X⁻" | "●"        { PREV }
  | "GLOBALLY" | "ALWAYS" | "G" | "□"             { ALWAYS }
  | "FINALLY" | "EVENTUALLY" | "F" | "◊"          { EVENTUALLY }
  | "GLOBALLY_PAST" | "HISTORICALLY" | "G⁻" | "■" { HISTORICALLY }
  | "FINALLY_PAST" | "ONCE" | "F⁻" | "⧫"          { ONCE }
  | "("                                           { LOPEN }
  | ")"                                           { ROPEN }
  | string as s                                   { STRING s }
  | (['(' '['] as l) blank* (digits as i) blank* "," blank* ((digits | "INFINITY" | "∞") as j) blank* ([')' ']'] as r)
                                                  { INTERVAL (make_interval lexbuf l i j r) }
  | "/*"                                          { skip 1 lexbuf }
  | '#'                                           { skip_line lexbuf }
  | eof                                           { EOF }
  | _ as c                                        { lexing_error lexbuf "Unexpected character: `%c'" c }

and skip n = parse
  | newline                                       { Lexing.new_line lexbuf; skip n lexbuf }
  | "*/"                                          { if n=1 then token lexbuf else skip (n-1) lexbuf }
  | "/*"                                          { skip (n+1) lexbuf }
  | _                                             { skip n lexbuf }
  | eof                                           { lexing_error lexbuf "Unterminated comment" }

and skip_line = parse
  | newline                                       { Lexing.new_line lexbuf; token lexbuf }
  | eof                                           { EOF }
  | _                                             { skip_line lexbuf }
