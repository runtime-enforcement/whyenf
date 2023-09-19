(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

module Fdeque = Core_kernel.Fdeque

type timepoint = int
type timestamp = int

let debug = ref false
let inc_ref = ref Stdio.In_channel.stdin
let outc_ref = ref Stdio.Out_channel.stdout

let eat s t = s ^ (String.strip t)
let paren h k x = if h>k then "("^^x^^")" else x
let is_digit = function
  | '0' .. '9' -> true
  | _ -> false

exception Parsing_error of Lexing.position*Lexing.position*string
let parsing_error i j fmt = Format.kasprintf (fun s -> raise (Parsing_error(i,j,s))) fmt
let lexing_error lexbuf fmt = parsing_error (Lexing.lexeme_start_p lexbuf) (Lexing.lexeme_end_p lexbuf) fmt
let lexbuf_error_msg (lexbuf: Lexing.lexbuf) =
  Printf.sprintf "a problem was found at line %d character %d"
    (lexbuf.lex_curr_p.pos_lnum) (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol)

exception Empty_deque of string
let deque_to_string indent f d =
  if Fdeque.is_empty d then indent ^ "[]"
  else
    (if Int.equal (Fdeque.length d) 1 then
       indent ^ eat "[" (f indent (Fdeque.peek_front_exn d) ^ "]")
     else
       Fdeque.fold ~f:(fun s el -> eat (s ^ "\n" ^ indent ^ "; ") (f indent el))
         ~init:(indent ^ eat "[ " (f indent (Fdeque.peek_front_exn d))) (Fdeque.drop_front_exn d) ^ " ]")

let rec queue_drop q n =
  if Int.equal n 0 then q
  else (let _ = Queue.dequeue_exn q in queue_drop q (n-1))

let list_to_string indent f = function
  | [] -> indent ^ "[]"
  | [x] -> indent ^ eat "[" (f indent x ^ "]")
  | x :: xs ->
     List.fold_left xs ~init:(indent ^ eat "[ " (f indent x))
       ~f:(fun s el -> eat (s ^ "\n" ^ indent ^ "; ") (f indent el)) ^ " ]"

let rec string_list_to_string = function
  | [] -> ""
  | x :: xs -> if List.is_empty xs then x
               else Printf.sprintf "%s, %s" x (string_list_to_string xs)

let some_string () = (String.of_char (Random.ascii ())) ^ (String.of_char (Random.ascii ())) ^
                       (String.of_char (Random.ascii ())) ^ (String.of_char (Random.ascii ()))

let string_list_to_json l =
  match l with
  | [] -> "[]"
  | _ -> let els_str = String.concat ~sep:"" (List.map l ~f:(fun el -> "\"" ^ el ^ "\",")) in
         "[" ^ (String.sub els_str 0 ((String.length els_str)-1)) ^ "]"

let int_list_to_json l =
  match l with
  | [] -> "[]"
  | _ -> let els_str = String.concat ~sep:"" (List.map l ~f:(fun el -> (Int.to_string el) ^ ",")) in
         "[" ^ (String.sub els_str 0 ((String.length els_str)-1)) ^ "]"

let unquote s =
    let len = String.length s in
    if Char.equal s.[0] '\"' && Char.equal s.[len-1] '\"' then
      String.sub s 1 (len-2)
    else s

let escape_underscores s =
  String.fold s ~init:"" ~f:(fun acc c -> if Char.equal c '_' then acc ^ "\\_" else acc ^ (Char.to_string c))
