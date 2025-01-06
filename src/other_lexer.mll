{
  type token = AT | FUN | SFUN | TFUN | PRD | EXT | LPA | RPA | LAN | RAN | COM | SEP | COL | EOF | ADD | SUB | QST | EXC | STR of string


let lexing_error lexbuf s =
  raise (Errors.ParserError (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf, s))

let lexbuf_error_msg (lexbuf: Lexing.lexbuf) =
  Printf.sprintf "a problem was found at line %d character %d"
    (lexbuf.lex_curr_p.pos_lnum) (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol) 

}

let blank = [' ' '\t']+
let newline = ['\r' '\n' ] | "\r\n"

let lc = ['a'-'z']
let uc = ['A'-'Z']
let letter = uc | lc
let digit = ['0'-'9']

let digits = ['0'-'9']+
let string = (letter | digit | '_' | '!' | '.' | '-')+
(*let string = (letter | digit | '_' | '[' | ']' | '/' | '-' | '.' | '!' | ':' | '"')+ *)
let quoted_string = ([^ '"' '\\'] | '\\' _)*

rule token = parse
  | newline                        { Lexing.new_line lexbuf; token lexbuf }
  | blank                          { token lexbuf }
  | "@"                            { AT }
  | "fun"                          { FUN }
  | "sfun"                         { SFUN }
  | "afun"                         { TFUN }
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
  | "+"                            { ADD }
  | "-"                            { SUB }
  | "?"                            { QST }
  | "!"                            { EXC }
  | '"' (quoted_string as s) '"'   { STR s }
  | string as s                    { STR s }
  | _                              { lexing_error lexbuf
                                       (Printf.sprintf "unexpected character: `%s'"
                                          (Lexing.lexeme lexbuf)) }
  | eof                            { EOF }


and skip_line = parse
  | "\n" | "\r" | "\r\n"           { Lexing.new_line lexbuf; token lexbuf }
  | eof                            { EOF }
  | _                              { skip_line lexbuf }
