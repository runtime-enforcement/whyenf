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
open Pred

module Event : sig
  type t = string * const list [@@deriving compare, sexp_of]
  include Comparable.S with type t := t
end

type t = int * (Event.t, Event.comparator_witness) Set.t

val db: string -> Event.t list -> t

val event: string -> string list -> Event.t
