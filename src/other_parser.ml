open Base
open Stdio

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

module TheSig = Sig

let string_of_token (t: Other_lexer.token) =
  match t with
  | AT -> "'@'"
  | LPA -> "'('"
  | RPA -> "')'"
  | COM -> "','"
  | SEP -> "';'"
  | COL -> "':'"
  | STR s -> "\"" ^ String.escaped s ^ "\""
  | EOF -> "<EOF>"
  | FUN -> "\"fun\""
  | SFUN -> "\"sfun\""
  | TFUN -> "\"tfun\""
  | PRD -> "\"pred\""
  | EXT -> "\"ext\""
  | LAN -> "'>'"
  | RAN -> "'<'"
  | ADD -> "'+'"
  | SUB -> "'-'"
  | QST -> "'?'"
  | EXC -> "'!'"


module Stats = struct

  type t = { mutable ev_done: int
           ; mutable tp_done: int
           ; mutable ev_cau: int
           ; mutable ev_sup: int
           ; mutable tp_ins: int
           }

  let init () = { ev_done = 0
                ; tp_done = 0
                ; ev_cau = 0
                ; ev_sup = 0
                ; tp_ins = 0
                }

  let reset stats =
    stats.ev_done <- 0;
    stats.tp_done <- 0;
    stats.ev_cau <- 0;
    stats.ev_sup <- 0;
    stats.tp_ins <- 0

  let inc_ev stats =
    stats.ev_done <- stats.ev_done + 1

  let inc_tp stats =
    stats.tp_done <- stats.tp_done + 1

  let add_cau i ?(ins=false) stats =
    stats.ev_cau <- stats.ev_cau + i;
    if ins then stats.tp_ins <- stats.tp_ins + 1

  let add_sup i stats =
    stats.ev_sup <- stats.ev_sup + i

  let to_string stats =
    Printf.sprintf "%d %d %d %d %d"
      stats.ev_done stats.tp_done stats.ev_cau stats.ev_sup stats.tp_ins

end

module Parsebuf = struct

  type t = { lexbuf: Lexing.lexbuf
           ; mutable token: Other_lexer.token
           ; mutable pred_sig: Sig.elt option
           ; mutable tp: int
           ; mutable ts: int
           ; mutable db: Db.t
           ; mutable check: bool
           ; stats: Stats.t
           }

  let init lexbuf = { lexbuf = lexbuf
                    ; token = Other_lexer.token lexbuf
                    ; pred_sig = None
                    ; tp = -1
                    ; ts = -1
                    ; db = Db.create []
                    ; check = false
                    ; stats = Stats.init ()
                    }

  let next pb = pb.token <- Other_lexer.token pb.lexbuf

  let reset_stats pb = Stats.reset pb.stats

  let arity pb = (Sig.arity (snd (Option.value_exn pb.pred_sig)))

  let pred pb = fst (Option.value_exn pb.pred_sig)

  let clean pb = { pb with pred_sig = None
                         ; tp = -1
                         ; ts = -1
                         ; db = Db.create [] }

  let add_event evt pb =
    pb.db <- Db.add_event pb.db evt;
    if not (Db.Event.equal evt Db.Event._tick) then
      Stats.inc_ev pb.stats

  let count_tp pb =
    Stats.inc_tp pb.stats

  let print_stats comment pb = 
    Stdio.printf ">%s %s %d <\n" comment (Stats.to_string pb.stats)
      (Float.to_int (1000. *. Unix.gettimeofday ()));
    Stdlib.flush_all();
    reset_stats pb

end

module Sig = struct

  let token_equal (t1: Other_lexer.token) (t2: Other_lexer.token) =
    match t1, t2 with
    | AT, AT
      | LPA, LPA
      | RPA, RPA
      | COM, COM
      | SEP, SEP
      | EOF, EOF
      | FUN, FUN
      | COL, COL
      | QST, QST
      | EXC, EXC -> true
    | STR s1, STR s2 -> String.equal s1 s2
    | _ -> false

  let parse_string (pb: Parsebuf.t) =
    match pb.token with
    | STR s -> Parsebuf.next pb; s
    | t -> raise (Failure ("expected a string but found " ^ string_of_token t))

  let expect_token (pb: Parsebuf.t) t =
    if token_equal pb.token t then Parsebuf.next pb
    else raise (Failure ("expected " ^ string_of_token t ^ " but found " ^ string_of_token pb.token))

  let parse_arg_tts (pb: Parsebuf.t) =
    let rec parse_arg_tts_rec l =
      match pb.token with
      | COM -> Parsebuf.next pb;
               let s = parse_string pb in
               parse_arg_tts_rec (s::l)
      | RPA -> Parsebuf.next pb; List.rev l
      | t -> raise (Failure ("expected ',' or ')' but found " ^ string_of_token t)) in
    expect_token pb LPA;
    match pb.token with
    | RPA -> Parsebuf.next pb; []
    | STR s -> Parsebuf.next pb; parse_arg_tts_rec [s]
    | t -> raise (Failure ("expected a string or ')' but found " ^ string_of_token t))

  let parse_ret_tt (pb: Parsebuf.t) =
    expect_token pb COL;
    match pb.token with
    | STR s -> Parsebuf.next pb; s
    | t -> raise (Failure ("expected a string but found " ^ string_of_token t))

  let parse_ret_tts (pb: Parsebuf.t) =
    let rec parse_ret_tts_rec l =
      match pb.token with
      | COM -> Parsebuf.next pb;
               parse_ret_tts_rec ((parse_string pb)::l)
      | RPA -> Parsebuf.next pb; List.rev l
      | t -> raise (Failure ("expected ',' or ')' but found " ^ string_of_token t)) in
    expect_token pb COL;
    expect_token pb LPA;
    match pb.token with
    | RPA -> Parsebuf.next pb; []
    | STR s -> Parsebuf.next pb; parse_ret_tts_rec [s]
    | t -> raise (Failure ("expected a string or ')' but found " ^ string_of_token t))

  let convert_types sl =
    List.map sl ~f:(fun s -> match String.split s ~on:':' with
                             | [] -> raise (Failure ("unable to parse the variable signature string " ^ s))
                             | name :: ttype :: [] -> (name, Dom.tt_of_string ttype)
                             | _ -> raise (Failure ("unable to parse the variable signature string " ^ s)))

  let parse_enftype (pb: Parsebuf.t) =
    match pb.token with
    | ADD -> begin Parsebuf.next pb;
                   match pb.token with
                   | SUB -> Parsebuf.next pb;
                            Enftype.causup
                   | QST -> Parsebuf.next pb;
                            Enftype.caubot
                   | _   -> Enftype.cau
             end
    | SUB -> begin Parsebuf.next pb;
                   match pb.token with
                   | ADD -> Parsebuf.next pb;
                            Enftype.causup
                   | _   -> Enftype.sup
             end
    | QST -> begin Parsebuf.next pb;
                   match pb.token with
                   | ADD -> Parsebuf.next pb;
                            Enftype.caubot
                   | _   -> Enftype.bot
             end
    | _ -> Enftype.obs

  let rec parse_pred_sigs (pb: Parsebuf.t) rank_ref =
    match pb.token with
    | EOF -> ()
    | FUN | SFUN as kw -> begin
        Parsebuf.next pb;
        match pb.token with
         | STR s -> Parsebuf.next pb;
                    let arg_tts = convert_types (parse_arg_tts pb) in
                    let ret_tt = Dom.tt_of_string (parse_ret_tt pb) in
                    let strict = match kw with SFUN -> true | _ -> false in
                    Sig.add_func s arg_tts ret_tt External strict;
                    parse_pred_sigs pb rank_ref
         | t -> raise (Failure ("unexpected character: " ^ string_of_token t))
      end
    | TFUN -> begin
        Parsebuf.next pb;
        match pb.token with
         | STR s -> Parsebuf.next pb;
                    let arg_tts = convert_types (parse_arg_tts pb) in
                    let ret_tts = List.map ~f:Dom.tt_of_string (parse_ret_tts pb) in
                    Sig.add_tfunc s arg_tts ret_tts;
                    parse_pred_sigs pb rank_ref
         | t -> raise (Failure ("unexpected character: " ^ string_of_token t))
      end
    | PRD | EXT as tok -> begin
        Parsebuf.next pb;
        match pb.token with
         | STR s -> Parsebuf.next pb;
                    let arg_tts = convert_types (parse_arg_tts pb) in
                    Sig.add_pred s arg_tts Enftype.obs 0
                      (match tok with
                       | PRD -> Predicate
                       | EXT -> External
                       | _ -> raise (Failure ("unexpected character: " ^ string_of_token tok)));
                    parse_pred_sigs pb rank_ref
         | t -> raise (Failure ("unexpected character: " ^ string_of_token t))
      end
    | STR s -> begin
        Parsebuf.next pb;
        let arg_tts = convert_types (parse_arg_tts pb) in
        let enftype  = parse_enftype pb in
        let rank = if Enftype.is_observable enftype then 0 else rank_ref in
        let next_rank_ref = if Int.equal rank 0 then
                              rank_ref + 1
                            else
                              rank_ref in
        Sig.add_pred s arg_tts enftype rank Trace;
        parse_pred_sigs pb (next_rank_ref)
      end
    | t -> raise (Failure ("unexpected character: " ^ string_of_token t))

  let parse_from_channel fn =
    let inc = In_channel.create fn in
    let lexbuf = Lexing.from_channel inc in
    let pb = Parsebuf.init lexbuf in
    let () = Lexing.set_filename lexbuf fn in
    try parse_pred_sigs pb 0
    with Failure s -> failwith ("error while parsing signature\n " ^ s)

  let parse_from_string ssig =
    let lexbuf = Lexing.from_string ssig in
    let pb = Parsebuf.init lexbuf in
    try parse_pred_sigs pb 0
    with Failure s -> failwith ("error while parsing signature\n " ^ s)

end

module Trace = struct

  let parse_aux (pb: Parsebuf.t) =
    let rec parse_init () =
      match pb.token with
      | SEP | RAN -> Parsebuf.next pb; parse_init ()
      | AT -> Parsebuf.next pb; parse_ts ()
      | EOF -> None
      | LAN -> Parsebuf.next pb;
               Parsebuf.print_stats (parse_comment "") pb;
               parse_init ()
      | t -> raise (Failure ("expected '@' but found " ^ string_of_token t))
    and parse_comment acc =
      match pb.token with
      | RAN -> acc
      | STR s -> Parsebuf.next pb; parse_comment (acc ^ " " ^ s)
      | _   -> Parsebuf.next pb; parse_comment acc
    and parse_ts () =
      match pb.token with
      | STR s -> let ts = try Some (Int.of_string s)
                          with _ -> None in
                 (match ts with
                  | Some ts -> Parsebuf.next pb;
                               pb.ts <- ts;
                               pb.check <- false;
                               parse_db ()
                  | None -> raise (Failure ("expected a time-stamp but found " ^ s)))
      | t -> raise (Failure ("expected a time-stamp but found " ^ string_of_token t))
    and parse_db () =
      Parsebuf.count_tp pb;
      match pb.token with
      | STR s -> (match Hashtbl.find TheSig.table s with
                  | Some props -> (pb.pred_sig <- Some(s, props);
                                   Parsebuf.next pb;
                                   (match pb.token with
                                    | LPA -> Parsebuf.next pb;
                                             parse_tuple ()
                                    | t -> raise (Failure ("expected '(' but found " ^ string_of_token t))))
                  | None -> raise (Failure ("predicate " ^ s ^ " was not specified")))
      | AT -> Some (true, pb)
      | EOF -> Some (false, pb)
      | SEP -> Some (true, pb)
      | QST -> pb.check <- true; Some (true, pb)
      | t -> raise (Failure ("expected a predicate or '@' but found " ^ string_of_token t))
    and parse_tuple () =
      match pb.token with
      | RPA -> parse_tuple_cont (Queue.create ())
      | STR s -> Parsebuf.next pb;
                 parse_tuple_cont (Queue.of_list [s])
      | t -> raise (Failure ("expected a tuple or ')' but found " ^ string_of_token t))
    and parse_tuple_cont q =
      match pb.token with
      | RPA -> Parsebuf.next pb;
               (if Int.equal (Queue.length q) (Parsebuf.arity pb) then
                  let evt = Db.event (Parsebuf.pred pb) (Queue.to_list q) in
                  Parsebuf.add_event evt pb
                else raise (Failure (Printf.sprintf "expected a tuple of arity %d but found %d arguments"
                                       (Parsebuf.arity pb) (Queue.length q))));
               (match pb.token with
                | LPA -> Parsebuf.next pb; parse_tuple ()
                | _ -> parse_db ())
      | COM -> Parsebuf.next pb;
               (match pb.token with
                | STR s -> Parsebuf.next pb;
                           Queue.enqueue q s;
                           parse_tuple_cont q
                | t -> raise (Failure ("expected a tuple but found " ^ string_of_token t)))
      | t -> raise (Failure ("expected ',' or ')' but found " ^ string_of_token t)) in
    parse_init ()

  let parse_from_channel inc pb_opt =
    if Option.is_none pb_opt then
      let lexbuf = Lexing.from_channel inc in
      parse_aux (Parsebuf.init lexbuf)
    else parse_aux (Parsebuf.clean (Option.value_exn pb_opt))

  let parse_from_string log =
    let lexbuf = Lexing.from_string log in
    parse_aux (Parsebuf.init lexbuf)

end
