(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

module MFormula : sig

  type t

end

module MState : sig

  type t

end

val exec: Out.Plain.mode -> string -> Formula.t -> in_channel -> unit

val exec_vis: MState.t option -> Formula.t -> string -> (MState.t * (string * string))
