(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Stdio
open Etc

let string_of_token (t: Other_lexer.token) =
  match t with
  | AT -> "'@'"
  | LPA -> "'('"
  | RPA -> "')'"
  | COM -> "','"
  | SEP -> "';'"
  | STR s -> "\"" ^ String.escaped s ^ "\""
  | EOF -> "<EOF>"


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
           ; mutable pred_sig: Pred.Sig.t option
           ; mutable ts: int
           ; mutable db: Db.t
           ; stats: Stats.t
           }

  let init lexbuf = { lexbuf = lexbuf
                    ; token = Other_lexer.token lexbuf
                    ; pred_sig = None
                    ; ts = -1
                    ; db = Db.create []
                    ; stats = Stats.init ()
                    }

  let next pb = pb.token <- Other_lexer.token pb.lexbuf

  let reset_stats pb = Stats.reset pb.stats

  let arity pb = (snd (Option.value_exn pb.pred_sig)).arity

  let pred pb = fst (Option.value_exn pb.pred_sig)

  let clean pb = { pb with pred_sig = None
                         ; ts = -1
                         ; db = Db.create [] }

  let add_event evt pb =
    pb.db <- Db.add_event pb.db evt;
    if not (Db.Event.equal evt Db.Event._tick) then
      Stats.inc_ev pb.stats

  let count_tp pb =
    Stats.inc_tp pb.stats

  let clear pb = pb

  let print_stats comment pb = 
    Stdio.printf ">%s %s %d <\n" comment (Stats.to_string pb.stats)
      (int_of_float (1000. *. Unix.gettimeofday ()));
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
    List.map sl ~f:(fun s -> match String.split s ~on:':' with
                             | [] -> raise (Failure ("unable to parse the variable signature string " ^ s))
                             | name :: ttype :: [] -> (name, Dom.tt_of_string ttype)
                             | _ -> raise (Failure ("unable to parse the variable signature string " ^ s)))

  let parse_enftype (pb: Parsebuf.t) =
    match pb.token with
    | PLS -> begin Parsebuf.next pb;
                   match pb.token with
                   | MNS -> Parsebuf.next pb;
                            Pred.EnfType.CauSup
                   | _   -> Pred.EnfType.Cau
             end
    | MNS -> begin Parsebuf.next pb;
        match pb.token with
        | PLS -> Parsebuf.next pb;
                 Pred.EnfType.CauSup
        | _   -> Pred.EnfType.Sup
             end
    | _ -> Pred.EnfType.Obs

  let rec parse_pred_sigs (pb: Parsebuf.t) rank_ref =
    match pb.token with
    | EOF -> ()
    | STR s -> Parsebuf.next pb;
               let ntconsts = convert_types (parse_ntconst pb) in
               let enftype  = parse_enftype pb in
               let rank = match enftype with
                 | Pred.EnfType.Obs -> 0
                 | _ -> rank_ref in
               let next_rank_ref = if Int.equal rank 0 then
                                     rank_ref + 1
                                   else
                                     rank_ref in
               Pred.Sig.add s ntconsts enftype rank;
               parse_pred_sigs pb (next_rank_ref)
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
      | AT -> Parsebuf.next pb; parse_ts ()
      | EOF -> None
      | LAN -> Parsebuf.next pb;
               Parsebuf.print_stats (parse_comment "") pb;
               parse_init ()
      | t -> raise (Failure ("expected '@' but found " ^ string_of_token t))
    and parse_comment acc =
      match pb.token with
      | RAN -> Parsebuf.next pb; acc
      | STR s -> Parsebuf.next pb; parse_comment (acc ^ " " ^ s)
      | _   -> Parsebuf.next pb; parse_comment acc
    and parse_ts () =
      match pb.token with
      | STR s -> let ts = try Some (Int.of_string s)
                          with _ -> None in
                 (match ts with
                  | Some ts -> Parsebuf.next pb;
                               pb.ts <- ts;
                               parse_db ()
                  | None -> raise (Failure ("expected a time-stamp but found " ^ s)))
      | t -> raise (Failure ("expected a time-stamp but found " ^ string_of_token t))
    and parse_db () =
      Parsebuf.count_tp pb;
      match pb.token with
      | STR s -> (match Hashtbl.find Pred.Sig.table s with
                  | Some props -> (pb.pred_sig <- Some(s, props);
                                   Parsebuf.next pb;
                                   (match pb.token with
                                    | LPA -> Parsebuf.next pb;
                                             parse_tuple ()
                                    | t -> raise (Failure ("expected '(' but found " ^ string_of_token t))))
                  | None -> raise (Failure ("predicate " ^ s ^ " was not specified")))
      | AT -> Some (true, pb)
      | EOF -> Some (false, pb)
      | SEP -> Parsebuf.next pb; Some (true, pb)
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
