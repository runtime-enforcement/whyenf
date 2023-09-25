(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

module Dbs : sig

  val to_json: Etc.timepoint -> Db.t -> Formula.t -> string

end

module Expl : sig

  val to_json: Formula.t -> Expl.t -> string

end
