(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl
open Expl
open Util
open Checker.Explanator2

type checker_proof = CS of string sproof | CV of string vproof
type checker_trace = (string set * nat) list

val s_of_proof: checker_proof -> string
(* val s_of_trace: (string set * nat) list -> string *)
val check_ps: (Util.SS.t * int) list -> formula -> expl list -> (bool * checker_proof * checker_trace) list
