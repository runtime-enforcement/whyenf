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
let string = (letter | digit | '_' | '/' | '-' | '!')+

rule token = parse
  | newline                                       { Lexing.new_line lexbuf; token lexbuf }
  | blank                                         { token lexbuf }
  | '#'                                           { debug "skip_line"; skip_line lexbuf }
  | ','                                           { debug "COMMA"; COMMA }
  | '.'                                           { debug "DOT"; DOT }
  | "false" | "⊥"                                 { debug "FALSE"; FALSE }
  | "true" | "⊤"                                  { debug "TRUE"; TRUE }
  | '!' | "¬" | "NOT"                             { debug "NEG"; NEG }
  | '&' | "∧" | "AND"                             { debug "AND"; AND }
  | '|' | "∨" | "OR"                              { debug "OR"; OR }
  | "=>" | "->" | "→" | "IMPLIES"                 { debug "IMP"; IMP }
  | "<=>"  | "<->" | "↔" | "IFF"                  { debug "IFF"; IFF }
  | "∃"  | "EXISTS"                               { debug "EXISTS"; EXISTS }
  | "∀"  | "FORALL"                               { debug "FORALL"; FORALL }
  | "SINCE" | "S"                                 { debug "SINCE"; SINCE }
  | "UNTIL" |	"U"                               { debug "UNTIL"; UNTIL }
  | "RELEASE" | "R"                               { debug "RELEASE"; RELEASE }
  | "TRIGGER" |	"T"                               { debug "TRIGGER"; TRIGGER }
  | "NEXT" | "X" | "○"                            { debug "NEXT"; NEXT }
  | "PREV" | "PREVIOUS" | "Y" | "●"               { debug "PREV"; PREV }
  | "GLOBALLY" | "ALWAYS" | "G" | "□"             { debug "ALWAYS"; ALWAYS }
  | "FINALLY" | "EVENTUALLY" | "F" | "◊"          { debug "EVENTUALLY"; EVENTUALLY }
  | "GLOBALLY_PAST" | "HISTORICALLY" | "■"        { debug "HISTORICALLY"; HISTORICALLY }
  | "FINALLY_PAST" | "ONCE" | "⧫"                 { debug "ONCE"; ONCE }
  | (['(' '['] as l) blank* (digits as i) blank* ',' blank* ((digits | "INFINITY" | "∞") as j) blank* ([')' ']'] as r)
                                                  { debug "INTERVAL"; INTERVAL (make_interval lexbuf l i j r) }
  | "("                                           { debug "LPA"; LPA }
  | ")"                                           { debug "RPA"; RPA }
  | string as s                                   { debug ("STR " ^ s); STR s }
  | _ as c                                        { lexing_error lexbuf "unexpected character: `%c'" c }
  | eof                                           { debug "EOF"; EOF }

and skip_line = parse
  | "\n" | "\r" | "\r\n"                          { Lexing.new_line lexbuf; token lexbuf }
  | eof                                           { debug "EOF"; EOF }
  | _                                             { skip_line lexbuf }
