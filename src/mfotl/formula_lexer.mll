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

exception Parsing_Error of Lexing.position*Lexing.position*string

let parsing_error i j fmt = Format.kasprintf (fun s -> raise (Parsing_Error(i,j,s))) fmt
let lexing_error lexbuf fmt = parsing_error (Lexing.lexeme_start_p lexbuf) (Lexing.lexeme_end_p lexbuf) fmt

let make_interval lexbuf = Interval.lex (fun () -> lexing_error lexbuf "interval lexing did not succeed")

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
  | ','                                           { COMMA }
  | '.'                                           { DOT }
  | "false" | "⊥"                                 { FALSE }
  | "true" | "⊤"                                  { TRUE }
  | '!' | "¬" | "NOT"                             { NEG }
  | '&' | "∧" | "AND"                             { AND }
  | '|' | "∨" | "OR"                              { OR }
  | "=>" | "->" | "→" | "IMPLIES"                 { IMP }
  | "<=>"  | "<->" | "↔" | "IFF"                  { IFF }
  | "∃"  | "EXISTS"                               { EXISTS }
  | "∀"  | "FORALL"                               { FORALL }
  | "SINCE" | "S"                                 { SINCE }
  | "UNTIL" |	"U"                               { UNTIL }
  | "RELEASE" | "R"                               { RELEASE }
  | "TRIGGER" |	"T"                               { TRIGGER }
  | "NEXT" | "X" | "○"                            { NEXT }
  | "PREV" | "PREVIOUS" | "Y" | "●"               { PREV }
  | "GLOBALLY" | "ALWAYS" | "G" | "□"             { ALWAYS }
  | "FINALLY" | "EVENTUALLY" | "F" | "◊"          { EVENTUALLY }
  | "GLOBALLY_PAST" | "HISTORICALLY" | "■"        { HISTORICALLY }
  | "FINALLY_PAST" | "ONCE" | "⧫"                 { ONCE }
  | "("                                           { LPA }
  | ")"                                           { RPA }
  | string as s                                   { STR s }
  | (['(' '['] as l) blank* (digits as i) blank* "," blank* ((digits | "INFINITY" | "∞") as j) blank* ([')' ']'] as r)
                                                  { INTERVAL (make_interval lexbuf l i j r) }
  | '#'                                           { skip_line lexbuf }
  | eof                                           { EOF }
  | _ as c                                        { lexing_error lexbuf "unexpected character: `%c'" c }

and skip_line = parse
  | "\n" | "\r" | "\r\n"                          { Lexing.new_line lexbuf; token lexbuf }
  | eof                                           { EOF }
  | _                                             { skip_line lexbuf }
