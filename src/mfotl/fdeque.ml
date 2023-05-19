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

exception Empty of string

let fenqueue_front d e = Deque.enqueue_front d e; d

let fenqueue_back d e = Deque.enqueue_back d e; d

let enqueue_front d e = Deque.enqueue_front d e

let enqueue_back d e = Deque.enqueue_back d e

let fdrop_front d = Deque.drop_front d; d

let drop_front d = Deque.drop_front d

let drop_back d = Deque.drop_back d

let is_empty d = Deque.is_empty d

let peek_back_exn d = Deque.peek_back_exn d

let peek_back d = Deque.peek_back d

let peek_front_exn d = Deque.peek_back_exn d

let peek_front d = Deque.peek_front d

let fold d = Deque.fold d

let fold' d = Deque.fold' d

let foldi d = Deque.foldi d

let iter d = Deque.iter d

let iteri d = Deque.iteri d

let set_exn d = Deque.set_exn d

let create () = Deque.create ()

let clear d = Deque.clear d

let length d = Deque.length d

let dequeue_front_exn d = Deque.dequeue_front_exn d

let dequeue_front d = Deque.dequeue_front d

let dequeue_back_exn d = Deque.dequeue_back_exn d

let dequeue_back d = Deque.dequeue_back d

let find d = Deque.find d

let front_index_exn d = Deque.front_index_exn d

let to_list d = Deque.to_list d

let to_string indent f d =
  if is_empty d then indent ^ "[]"
  else
    (if Int.equal (length d) 1 then
       indent ^ Etc.eat "[" (f indent (peek_front_exn d) ^ "]")
     else
       fold ~f:(fun s el -> Etc.eat (s ^ "\n" ^ indent ^ "; ") (f indent el))
         ~init:(indent ^ Etc.eat "[ " (f indent (peek_front_exn d))) (fdrop_front d) ^ " ]")
