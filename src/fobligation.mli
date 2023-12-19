(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Etc

type take_formula = timestamp -> Formula.t
type polarity = POS | NEG
type kind = NextCau | NextSup | UntilCau | UntilSup | Other

type t = kind * take_formula * Expl.Proof.valuation * polarity

val to_string: t -> string
