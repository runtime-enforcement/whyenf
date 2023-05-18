(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Etc

module Plain : sig

  type mode = UNVERIFIED | VERIFIED | DEBUG

  val expls: ((timestamp * timepoint) * Expl.t) list -> (bool * 'a * 'b) list option -> mode -> unit

end
