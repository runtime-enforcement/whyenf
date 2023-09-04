(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Etc
open Checker_interface

module Plain : sig

  type mode = UNVERIFIED | VERIFIED | DEBUG | DEBUGVIS

  val expls: timepoint -> ((timestamp * timepoint) * Expl.t) list -> (bool * Checker_pdt.t * Checker_trace.t) list option ->
             ((Domain.t, Domain.comparator_witness) Setc.t list list option list) option -> mode -> unit

end

module Json : sig

  val table_columns: Formula.t -> string

  val db: timestamp -> timepoint -> Db.t -> Formula.t -> string

  val expls: (timepoint, timestamp) Hashtbl.t -> Formula.t -> Expl.t list -> string list

  val aggregate: string list -> string list -> string

end
