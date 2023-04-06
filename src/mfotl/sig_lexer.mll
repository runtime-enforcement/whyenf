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

open Sig_parser
open Lexing

exception Parsing_Error of position*position*string

let parsing_error i j fmt = Format.kasprintf (fun s -> raise (Parsing_Error(i,j,s))) fmt
let lexing_error lexbuf fmt = parsing_error (lexeme_start_p lexbuf) (lexeme_end_p lexbuf) fmt

}

let blank = [' ' '\t']+
let newline = ['\r' '\n' ] | "\r\n"

let lc = ['a'-'z']
let uc = ['A'-'Z']
let letter = uc | lc
let digit = ['0'-'9']

let string = (letter | digit | '_' | '[' | ']' | '/' | ':' | '-' | '.' | '!')+

rule token = parse
  | newline                        { Lexing.new_line lexbuf; token lexbuf }
  | blank                          { token lexbuf }
  | "("                            { LOPEN }
  | ")"                            { ROPEN }
  | ","                            { COMMA }
  | ":"                            { COLON }
  | "/*"                           { skip 1 lexbuf }
  | "#"                            { skip_line lexbuf }
  | eof                            { EOF }
  | string as s                    { STRING s }
  | _ as c                         { lexing_error lexbuf "Unexpected character: `%c'" c }

and skip n = parse
  | newline                        { Lexing.new_line lexbuf; skip n lexbuf }
  | "*/"                           { if n=1 then token lexbuf else skip (n-1) lexbuf }
  | "/*"                           { skip (n+1) lexbuf }
  | _                              { skip n lexbuf }
  | eof                            { lexing_error lexbuf "Unterminated comment" }

and skip_line = parse
  | newline                        { Lexing.new_line lexbuf; token lexbuf }
  | eof                            { EOF }
  | _                              { skip_line lexbuf }
