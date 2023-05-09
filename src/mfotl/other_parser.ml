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

  type t = { lexbuf: Lexing.lexbuf; mutable token: Other_lexer.token; mutable predsig: (string * Pred.Sig.props) list }

  let init lexbuf = { lexbuf = lexbuf; token = Other_lexer.token lexbuf; predsig = []  }

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

  let tp = ref (-1)
  let next_tp () = tp := !tp + 1; !tp

  (* TODO: This should return a Db.t *)
  let parse lexbuf db_schema ctxt =
    let pb = Parsebuf.init lexbuf in
    let rec parse_init () =
      match pb.token with
      | EOF -> ()
      | AT -> Parsebuf.next pb; parse_ts ()
      | t -> fail ("expected '@' but found " ^ string_of_token t)
    and parse_ts () =
      match pb.token with
      | STR s -> let ts = try Some (Int.of_string s)
                          with _ -> None in
                 (match ts with
                  | Some ts -> Parsebuf.next pb;
                               parse_db ()
                  | None -> fail ("expected a time-stamp but found " ^ s))
      | t -> fail ("expected a time-stamp but found " ^ string_of_token t)
    and parse_db () =
      match pb.token with
      | STR s -> (match Hashtbl.find Pred.Sig.table s with
                  | Some props -> (pb.predsig <- [(s, props)];
                                   Parsebuf.next pb;
                                   (match pb.token with
                                    | LPA -> Parsebuf.next pb;
                                             parse_tuple ()
                                    | t -> fail ("expected '(' but found " ^ string_of_token t)))
                  | None -> fail ("predicate " ^ s ^ " was not specified"))
      | AT -> Parsebuf.next pb;
              parse_ts ()
      | EOF -> C.end_tp ctxt
      | t -> fail ("expected a predicate or '@' but found " ^ string_of_token t)
    and parse_tuple () =
      match pb.token with
      | RPA -> parse_tuple_cont []
      | STR s -> Parsebuf.next pb;
                 parse_tuple_cont [s]
      | t -> fail ("expected a tuple or ')' but found " ^ string_of_token t)
    and parse_tuple_cont l =
      match pb.token with
      | RPA -> Parsebuf.next pb;
               C.tuple ctxt pb.pb_schema (List.rev l);
               (match pb.token with
                | LPA -> Parsebuf.next pb; parse_tuple ()
                | _ -> parse_db ())
      | COM -> Parsebuf.next pb;
               (match pb.token with
                | STR s -> Parsebuf.next pb;
                           parse_tuple_cont (s::l)
                | t -> fail ("expected a tuple but found " ^ string_of_token t))
      | t -> fail ("expected ',' or ')' but found " ^ string_of_token t)
    and recover () =
      Parsebuf.next pb;
      match pb.token with
      | AT -> Parsebuf.next pb; parse_ts ()
      | EOF -> ()
      | _ -> Parsebuf.next pb; recover ()
    and fail msg =
      C.parse_error ctxt pb.pb_lexbuf.Lexing.lex_start_p msg;
      recover () in
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
