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

val is_empty: ('a, 'b) t -> bool
val inter: ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
val diff: ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
