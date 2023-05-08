(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Stdio

let string_of_token (t: Other_lexer.token) =
  match t with
  | AT -> "'@'"
  | LPA -> "'('"
  | RPA -> "')'"
  | COM -> "','"
  | SEP -> "';'"
  | STR s -> "\"" ^ String.escaped s ^ "\""
  | EOF -> "<EOF>"

module Parsebuf = struct

  type t = { lexbuf: Lexing.lexbuf; mutable token: Other_lexer.token }

  let init lexbuf = { lexbuf = lexbuf; token = Other_lexer.token lexbuf }

  let next pb = pb.token <- Other_lexer.token pb.lexbuf

end

module Sig = struct

  let token_equal (t1: Other_lexer.token) (t2: Other_lexer.token) =
    match t1, t2 with
    | AT, AT
      | LPA, LPA
      | RPA, RPA
      | COM, COM
      | SEP, SEP
      | EOF, EOF -> true
    | STR s1, STR s2 -> String.equal s1 s2
    | _ -> false

  let parse_string (pb: Parsebuf.t) =
    match pb.token with
    | STR s -> Parsebuf.next pb; s
    | t -> raise (Failure ("expected a string but found " ^ string_of_token t))

  let parse_int pb =
    let s = parse_string pb in
    try Int.of_string s
    with Failure _ -> raise (Failure ("expected an integer but found \"" ^ String.escaped s ^ "\""))

  let parse_ntconst (pb: Parsebuf.t) =
    let expect (pb: Parsebuf.t) t =
      if token_equal pb.token t then Parsebuf.next pb
      else raise (Failure ("expected " ^ string_of_token t ^ " but found " ^ string_of_token pb.token)) in
    let rec parse_ntconst_rec l =
      match pb.token with
      | COM -> Parsebuf.next pb;
               let s = parse_string pb in
               parse_ntconst_rec (s::l)
      | RPA -> Parsebuf.next pb; List.rev l
      | t -> raise (Failure ("expected ',' or ')' but found " ^ string_of_token t)) in
    expect pb LPA;
    match pb.token with
    | RPA -> Parsebuf.next pb; []
    | STR s -> Parsebuf.next pb; parse_ntconst_rec [s]
    | t -> raise (Failure ("expected a string or ')' but found " ^ string_of_token t))

  let convert_types sl =
    List.map sl (fun s -> match String.split s ':' with
                          | [] -> raise (Failure ("unable to parse the variable signature string " ^ s))
                          | name :: ttype :: [] -> (name, Domain.tt_of_string ttype)
                          | _ -> raise (Failure ("unable to parse the variable signature string " ^ s)))

  let rec parse_ntconsts (pb: Parsebuf.t) =
    match pb.token with
    | EOF -> ()
    | STR s -> Parsebuf.next pb;
               Pred.Sig.add s (convert_types (parse_ntconst pb));
               parse_ntconsts pb
    | t -> raise (Failure ("unexpected character: " ^ string_of_token t))

  let parse f =
    let inc = In_channel.create f in
    let lexbuf = Lexing.from_channel inc in
    let pb = Parsebuf.init lexbuf in
    let () = Lexing.set_filename lexbuf f in
    try parse_ntconsts pb
    with Failure s -> failwith ("error while parsing signature\n " ^ s)


end

module Trace = struct

exception Stop_parser

let parse db_schema lexbuf ctxt =
  let pb = init lexbuf in
  let debug msg =
    if Misc.debugging Misc.Dbg_log then
      Printf.eprintf "[Log_parser] state %s with token=%s\n" msg
        (string_of_token pb.pb_token)
    else ()
  in
  let rec parse_init () =
    debug "init";
    match pb.pb_token with
    | EOF -> ()
    | AT -> next pb; parse_ts ()
    | CMD -> next pb; parse_command ()
    | t -> fail ("Expected '@' or '>' but saw " ^ string_of_token t)
  and parse_ts () =
    debug "ts";
    match pb.pb_token with
    | STR s ->
       let ts =
         try Some (MFOTL.ts_of_string s)
         with Failure _ -> None
       in
       (match ts with
        | Some ts ->
           C.begin_tp ctxt ts;
           next pb;
           parse_db ()
        | None -> fail ("Cannot convert " ^ s ^ " into a timestamp"))
    | t -> fail ("Expected a time-stamp but saw " ^ string_of_token t)
  and parse_db () =
    debug "db";
    match pb.pb_token with
    | STR s ->
       (match List.assoc_opt s db_schema with
        | Some tl ->
           pb.pb_schema <- (s, tl);
           next pb;
           (match pb.pb_token with
            | LPA -> next pb; parse_tuple ()
            | _ -> C.tuple ctxt pb.pb_schema []; parse_db ())
        | None -> fail ("Predicate " ^ s
                        ^ " was not defined in the signature."))
    | AT ->
       C.end_tp ctxt;
       next pb;
       parse_ts ()
    | SEP ->
       C.end_tp ctxt;
       next pb;
       parse_init ()
    | CMD ->
       C.end_tp ctxt;
       next pb;
       parse_command ()
    | EOF -> C.end_tp ctxt
    | t -> fail ("Expected a predicate, '@', ';', or '>' but saw "
                 ^ string_of_token t)
  and parse_tuple () =
    debug "tuple";
    match pb.pb_token with
    | RPA ->
       parse_tuple_cont []
    | STR s ->
       next pb;
       parse_tuple_cont [s]
    | t -> fail ("Expected a tuple field or ')' but saw " ^ string_of_token t)
  and parse_tuple_cont l =
    debug "tuple_cont";
    match pb.pb_token with
    | RPA ->
       next pb;
       C.tuple ctxt pb.pb_schema (List.rev l);
       (match pb.pb_token with
        | LPA -> next pb; parse_tuple ()
        | _ -> parse_db ())
    | COM ->
       next pb;
       (match pb.pb_token with
        | STR s ->
           next pb;
           parse_tuple_cont (s::l)
        | t -> fail ("Expected a tuple field but saw " ^ string_of_token t))
    | t -> fail ("Expected ',' or ')' but saw " ^ string_of_token t)
  and parse_command () =
    debug "command";
    match pb.pb_token with
    | STR name ->
       next pb;
       let err, params =
         try None, parse_command_params pb
         with Local_error msg -> Some msg, None
       in
       (match err with
        | None -> C.command ctxt name params; parse_init ()
        | Some msg -> fail msg)
    | t -> fail ("Expected a command name but saw " ^ string_of_token t)
  and fail msg =
    C.parse_error ctxt pb.pb_lexbuf.Lexing.lex_start_p msg;
    recover ()
  and recover () =
    debug "recover";
    next pb;
    match pb.pb_token with
    | AT -> next pb; parse_ts ()
    | SEP -> next pb; parse_init ()
    | CMD -> next pb; parse_command ()
    | EOF -> ()
    | _ -> next pb; recover ()
  in
  try
    parse_init ();
    C.end_log ctxt;
    true
  with Stop_parser -> false

let parse f_opt =
  let inc = match f_opt with
    | None ->  stdin
    | Some f -> In_channel.create f in
  let lexbuf = Lexing.from_channel inc in
  Lexing.set_filename lexbuf (Option.value_exn f_opt);
  parse dbschema lexbuf ctxt

end
