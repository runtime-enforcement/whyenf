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

type 'a t = 'a Deque.t

val fenqueue_front: 'a t -> 'a -> 'a t

val enqueue_front: 'a t -> 'a -> unit

val fenqueue_back: 'a t -> 'a -> 'a t

val enqueue_back: 'a t -> 'a -> unit

val fdrop_front: 'a t -> 'a t

val drop_front: 'a t -> unit

val is_empty: 'a t -> bool

val peek_back_exn: 'a t -> 'a

val peek_back: 'a t -> 'a option

val peek_front_exn: 'a t -> 'a

val peek_front: 'a t -> 'a option

val fold: 'a t -> init: 'b -> f:('b -> 'a -> 'b) -> 'b

val fold': 'a t -> [ `back_to_front | `front_to_back ] -> init:'b -> f:('b -> 'a -> 'b) -> 'b

val iter: 'a t -> f:('a -> unit) -> unit

val iteri: 'a t -> f:(int -> 'a -> unit) -> unit

val set_exn: 'a t -> int -> 'a -> unit

val length: 'a t -> int

val to_string: string -> (string -> 'a -> string) -> 'a t -> string

val create: unit -> 'a t

val dequeue_front_exn: 'a t -> 'a

val dequeue_front: 'a t -> 'a option

val dequeue_back_exn: 'a t -> 'a

val dequeue_back: 'a t -> 'a option

val to_list: 'a t -> 'a list
