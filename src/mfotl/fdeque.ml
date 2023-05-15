(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Core_kernel
open Etc

type 'a t = 'a Deque.t

let enqueue_front d e = Deque.enqueue_front d e; d

let enqueue_back d e = Deque.enqueue_back d e; d

let drop_front d = Deque.drop_front d; d

let is_empty d = Deque.is_empty d

let peek_back_exn d = Deque.peek_back_exn d

let peek_front_exn d = Deque.peek_back_exn d

let fold d = Deque.fold d

let iter d = Deque.iter d

let create () = Deque.create ()

let length d = Deque.length d

let dequeue_front_exn d = Deque.dequeue_front_exn d

let dequeue_back_exn d = Deque.dequeue_back_exn d

let to_string indent f d =
  if is_empty d then indent ^ "[]"
  else
    (if Int.equal (length d) 1 then
       indent ^ Etc.eat "[" (f indent (peek_front_exn d) ^ "]")
     else
       fold ~f:(fun s el -> Etc.eat (s ^ "\n" ^ indent ^ "; ") (f indent el))
         ~init:(indent ^ Etc.eat "[ " (f indent (peek_front_exn d))) (drop_front d) ^ " ]")
