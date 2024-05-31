(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  François Hublet (ETH Zurich)                                   *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

module type EnforcerT = sig
  
  val exec: Formula.t -> in_channel -> Time.t -> unit

end

module Make (C: Checker_interface.Checker_interfaceT) : EnforcerT
