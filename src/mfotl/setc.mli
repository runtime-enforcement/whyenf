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

type ('a, 'b) t = Finite of ('a, 'b) Set.t | Complement of ('a, 'b) Set.t

val length: ('a, 'b) t -> int
val univ: ('a, 'b) Comparator.Module.t -> ('a, 'b) t
val equal: ('a, 'b) t -> ('a, 'b) t -> bool
val add: ('a, 'b) t -> 'a -> ('a, 'b) t
val is_empty: ('a, 'b) t -> bool
val inter: ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
val diff: ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
val some_elt: Domain.tt -> (Domain.t, 'a) t -> Domain.t
val is_finite: ('a, 'b) t -> bool

val to_list: ('a, 'b) t -> 'a list
val to_json: (Domain.t, 'a) t -> string
val to_string: (Domain.t, 'a) t -> string
val to_latex: (Domain.t, 'a) t -> string
