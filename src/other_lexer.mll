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

type token = AT | FUN | SFUN | PRD | EXT | LPA | RPA | LAN | RAN | COM | SEP | COL | EOF | PLS | MNS | QU | STR of string

}

let blank = [' ' '\t']+
let newline = ['\r' '\n' ] | "\r\n"

let lc = ['a'-'z']
let uc = ['A'-'Z']
let letter = uc | lc
let digit = ['0'-'9']

let digits = ['0'-'9']+
let string = (letter | digit | '_' | '[' | ']' | '/' | '-' | '.' | '!' | ':' | '"')+
let quoted_string = ([^ '"' '\\'] | '\\' _)*

rule token = parse
  | newline                        { Lexing.new_line lexbuf; token lexbuf }
  | blank                          { token lexbuf }
  | "@"                            { AT }
  | "fun"                          { FUN }
  | "sfun"                         { SFUN }
  | "pred"                         { PRD }
  | "ext"                          { EXT }
  | "("                            { LPA }
  | ")"                            { RPA }
  | ">"                            { LAN }
  | "<"                            { RAN }
  | ","                            { COM }
  | ";"                            { SEP }
  | "#"                            { skip_line lexbuf }
  | ":"                            { COL }
  | "+"                            { PLS }
  | "-"                            { MNS }
  | "?"                            { QU }
  | '"' (quoted_string as s) '"'   { STR s }
  | string as s                    { STR s }
  | eof                            { EOF }
  | _ as c                         { lexing_error lexbuf "unexpected character: `%c'" c }

and skip_line = parse
  | "\n" | "\r" | "\r\n"           { Lexing.new_line lexbuf; token lexbuf }
  | eof                            { EOF }
  | _                              { skip_line lexbuf }
