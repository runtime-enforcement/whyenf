(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Etc
open Monitor
open MFormula

type polarity = POS | NEG

type kind =
  | FFormula of MFormula.t                       (* fun _ -> f *)
  | FInterval of int * Interval.t * MFormula.t   (* fun t -> if mem t i then f else Formula.TT *)
  | FUntil of int * Formula.Side.t * Interval.t * MFormula.t * MFormula.t * buf2_info * until_info
                                                 (* fun t -> Until (s, sub2 i (t-t0), f1, f2) *)
  | FAlways of int * Interval.t * MFormula.t * buf_info * always_info
                                                 (* fun t -> Always (sub2 i (t-t0), f1) *)
  | FEventually of int * Interval.t * MFormula.t * buf_info * eventually_info
                                                 (* fun t -> Eventually (sub2 i (t-t0), f1) *)

type t = kind * Expl.Proof.valuation * polarity

val eval: int -> t -> MFormula.t
val to_string: t -> string
