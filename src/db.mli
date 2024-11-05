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
open Etc

module Event : sig
  type t = string * Dom.t list [@@deriving compare, sexp_of]

  val equal: t -> t -> bool

  val to_string: t -> string
  val name : t -> string

  include Comparable.S with type t := t

  val _tp: t
  val _tick: t
end

type t

val events: t -> (Event.t, Event.comparator_witness) Set.t

val mem_trace: t -> string -> bool

val create: Event.t list -> t

val diff: t -> t -> t
val union: t -> t -> t

val empty: t
val singleton : Event.t -> t

val equal: t -> t -> bool

val mem: t -> Event.t -> bool
val is_empty: t -> bool
val remove: t -> Event.t -> t
val size: t -> int
val filter: t -> f:(Event.t -> bool) -> t

val event: string -> string list -> Event.t

val add_event: t -> Event.t -> t
val is_tick: t -> bool

val to_string: t -> string

val to_json: t -> string

val retrieve_external: string -> t
val retrieve_builtin: timestamp -> timepoint -> string -> t
