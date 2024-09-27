{
(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Etc
open Formula
open Formula_parser

let make_interval lexbuf = Interval.lex (fun () -> lexing_error lexbuf "interval lexing did not succeed")

let debug m = if !debug then Stdio.print_endline ("[debug] formula_lexer: " ^ m)

}

let blank = [' ' '\t']+
let newline = ['\r' '\n' ] | "\r\n"

let lc = ['a'-'z']
let uc = ['A'-'Z']
let letter = uc | lc
let digit = ['0'-'9']

let digits = ['0'-'9']+
let string = (letter | digit | '_' | '-' | '!')+
let quoted_string = '"' ([^ '"' '\\'] | '\\' _)* '"'

rule token = parse
  | newline                                       { Lexing.new_line lexbuf; token lexbuf }
  | blank                                         { token lexbuf }
  | "(*"                                          { comment lexbuf; token lexbuf }
  | '#'                                           { debug "skip_line"; skip_line lexbuf }
  | ','                                           { debug "COMMA"; COMMA }
  | ';'                                           { debug "SEMICOLON"; SEMICOLON }
  | '.'                                           { debug "DOT"; DOT }
  | ':'                                           { debug "COL"; COL }
  | '+'                                           { debug "ADD"; ADD }
  | '-'                                           { debug "SUB"; SUB }
  | '*'                                           { debug "MUL"; MUL }
  | '/'                                           { debug "DIV"; DIV }
  | '^'                                           { debug "CONC"; CONC }
  | "LET"                                         { debug "LET"; LET }
  | "IN"                                          { debug "IN"; IN }
  | "FALSE" | "⊥"                                { debug "FALSE"; FALSE }
  | "TRUE" | "⊤"                                 { debug "TRUE"; TRUE }
  | "=="                                          { debug "EQEQ"; EQEQ }
  | '='                                           { debug "EQCONST"; EQCONST }
  | "<-"                                          { debug "GETS"; GETS }
  | "<="                                           { debug "LEQ"; LEQ }
  | "<>"                                           { debug "NEQ"; NEQ }
  | '<'                                           { debug "LT"; LT }
  | ">="                                           { debug "GEQ"; GEQ }
  | '>'                                           { debug "GT"; GT }
  | "¬" | "NOT"                                   { debug "NEG"; NEG }
  | "∧" | "AND"                                  { debug "AND"; AND }
  | "∨" | "OR"                                   { debug "OR"; OR }
  | "→" | "IMPLIES"                               { debug "IMP"; IMP }
  | "↔" | "IFF"                                   { debug "IFF"; IFF }
  | "∃"  | "EXISTS"                               { debug "EXISTS"; EXISTS }
  | "∀"  | "FORALL"                               { debug "FORALL"; FORALL }
  | "SINCE" | "S"                                 { debug "SINCE"; SINCE }
  | "UNTIL" | "U"                                 { debug "UNTIL"; UNTIL }
  | "RELEASE" | "R"                               { debug "RELEASE"; RELEASE }
  | "TRIGGER" |	"T"                               { debug "TRIGGER"; TRIGGER }
  | "NEXT" | "X" | "○"                            { debug "NEXT"; NEXT }
  | "PREV" | "PREVIOUS" | "Y" | "●"               { debug "PREV"; PREV }
  | "GLOBALLY" | "ALWAYS" | "G" | "□"             { debug "ALWAYS"; ALWAYS }
  | "EVENTUALLY" | "F" | "◊"                      { debug "EVENTUALLY"; EVENTUALLY }
  | "GLOBALLY_PAST" | "HISTORICALLY" | "■"       { debug "HISTORICALLY"; HISTORICALLY }
  | "ONCE" | "⧫"                                  { debug "ONCE"; ONCE }
  | "SUM"                                         { debug "SUM"; SUM }
  | "AVG"                                         { debug "AVG"; AVG }
  | "MED"                                         { debug "MED"; MED }
  | "CNT"                                         { debug "CNT"; CNT }
  | "MIN"                                         { debug "MIN"; MIN }
  | "MAX"                                         { debug "MAX"; MAX }
  | (['(' '['] as l) blank* (digits as i) blank* (string? as u) blank* ',' blank* ((digits | "INFINITY" | "∞" | "*") as j) blank* (string? as v) blank* ([')' ']'] as r)
                                                  { debug "INTERVAL"; INTERVAL (make_interval lexbuf l i u j v r) }
  | "("                                           { debug "LPA"; LPA }
  | ")"                                           { debug "RPA"; RPA }
  | digits as d                                   { debug ("INT " ^ d); INT (Base.Int.of_string d) }
  | string as s                                   { debug ("STR " ^ s); STR s }
  | quoted_string as qs                           { debug ("QSTR " ^ qs); QSTR qs }
  | _ as c                                        { lexing_error lexbuf "unexpected character: `%c'" c }
  | eof                                           { debug "EOF"; EOF }

and skip_line = parse
  | "\n" | "\r" | "\r\n"                          { Lexing.new_line lexbuf; token lexbuf }
  | eof                                           { debug "EOF"; EOF }
  | _                                             { skip_line lexbuf }

and comment = parse
  | "*)" { () }
  | "(*" { comment lexbuf; comment lexbuf }
  | eof { failwith "Unterminated comment" }
  | newline { Lexing.new_line lexbuf; comment lexbuf }
  | _ { comment lexbuf }
