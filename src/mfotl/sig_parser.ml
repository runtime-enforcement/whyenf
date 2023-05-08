(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for parse_ntconst_rec details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Stdio

type parsebuf = { pb_lexbuf: Lexing.lexbuf ; mutable pb_token: Trace_lexer.token }

let init_parsebuf lexbuf = { pb_lexbuf = lexbuf; pb_token = Trace_lexer.token lexbuf }

let next pb = pb.pb_token <- Trace_lexer.token pb.pb_lexbuf

let string_of_token (t: Trace_lexer.token) =
  match t with
  | AT -> "'@'"
  | LPA -> "'('"
  | RPA -> "')'"
  | COM -> "','"
  | SEP -> "';'"
  | STR s -> "\"" ^ String.escaped s ^ "\""
  | EOF -> "<EOF>"

let token_equal (t1: Trace_lexer.token) (t2: Trace_lexer.token) =
  match t1, t2 with
  | AT, AT
    | LPA, LPA
    | RPA, RPA
    | COM, COM
    | SEP, SEP
    | EOF, EOF -> true
  | STR s1, STR s2 -> String.equal s1 s2
  | _ -> false

let parse_string pb =
  match pb.pb_token with
  | STR s -> next pb; s
  | t -> raise (Failure ("expected a string but found " ^ string_of_token t))

let parse_int pb =
  let s = parse_string pb in
  try Int.of_string s
  with Failure _ -> raise (Failure ("expected an integer but found \"" ^ String.escaped s ^ "\""))

let parse_ntconst pb =
  let expect pb t =
    if token_equal pb.pb_token t then next pb
    else raise (Failure ("expected " ^ string_of_token t ^ " but found " ^ string_of_token pb.pb_token)) in
  let rec parse_ntconst_rec l =
    match pb.pb_token with
    | COM -> next pb;
             let s = parse_string pb in
             parse_ntconst_rec (s::l)
    | RPA -> next pb; List.rev l
    | t -> raise (Failure ("expected ',' or ')' but found " ^ string_of_token t)) in
  expect pb LPA;
  match pb.pb_token with
  | RPA -> next pb; []
  | STR s -> next pb; parse_ntconst_rec [s]
  | t -> raise (Failure ("expected a string or ')' but found " ^ string_of_token t))

let convert_types sl =
  List.map sl (fun s -> match String.split s ':' with
                        | [] -> raise (Failure ("unable to parse the variable signature string " ^ s))
                        | name :: ttype :: [] -> (name, Domain.tt_of_string ttype)
                        | _ -> raise (Failure ("unable to parse the variable signature string " ^ s)))

let rec parse_ntconsts pb =
  match pb.pb_token with
  | EOF -> ()
  | STR s -> next pb;
             Pred.Sig.add s (convert_types (parse_ntconst pb));
             parse_ntconsts pb
  | t -> raise (Failure ("unexpected character: " ^ string_of_token t))

let parse f =
  let inc = In_channel.create f in
  let lexbuf = Lexing.from_channel inc in
  let pb = init_parsebuf lexbuf in
  let () = Lexing.set_filename lexbuf f in
  try parse_ntconsts pb
  with Failure s -> failwith ("error while parsing signature\n " ^ s)
