(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

module Deque = Core_kernel.Deque

type timepoint = int
type timestamp = int

let debug = ref false
let inc_ref = ref Stdio.In_channel.stdin
let outc_ref = ref Stdio.Out_channel.stdout

let eat s t = s ^ (String.strip t)
let paren h k x = if h>k then "("^^x^^")" else x

exception Parsing_error of Lexing.position*Lexing.position*string
let parsing_error i j fmt = Format.kasprintf (fun s -> raise (Parsing_error(i,j,s))) fmt
let lexing_error lexbuf fmt = parsing_error (Lexing.lexeme_start_p lexbuf) (Lexing.lexeme_end_p lexbuf) fmt
let lexbuf_error_msg (lexbuf: Lexing.lexbuf) =
  Printf.sprintf "a problem was found at line %d character %d"
    (lexbuf.lex_curr_p.pos_lnum) (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol)

exception Empty_deque of string
let deque_to_string indent f d =
  if Deque.is_empty d then indent ^ "[]"
  else
    (if Int.equal (Deque.length d) 1 then
       indent ^ eat "[" (f indent (Deque.peek_front_exn d) ^ "]")
     else
       Deque.fold ~f:(fun s el -> eat (s ^ "\n" ^ indent ^ "; ") (f indent el))
         ~init:(indent ^ eat "[ " (f indent (Deque.peek_front_exn d))) (Deque.drop_front d; d) ^ " ]")

let rec queue_drop q n =
  if Int.equal n 0 then q
  else (let _ = Queue.dequeue_exn q in queue_drop q (n-1))

let list_to_string indent f = function
  | [] -> indent ^ "[]"
  | [x] -> indent ^ eat "[" (f indent x ^ "]")
  | x :: xs ->
     List.fold_left xs ~init:(indent ^ eat "[ " (f indent x))
       ~f:(fun s el -> eat (s ^ "\n" ^ indent ^ "; ") (f indent el)) ^ " ]"

let rec transpose lst = match lst with
  | [] -> []
  | [] :: xs -> transpose xs
  | (x :: xs) :: xss -> (x :: List.map xss ~f:List.hd_exn) :: transpose (xs :: List.map xss ~f:List.tl_exn)
