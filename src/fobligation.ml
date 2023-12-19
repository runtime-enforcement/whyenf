(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Etc

type take_formula = timestamp -> Formula.t
type polarity = POS | NEG
type kind = NextCau | NextSup | UntilCau | UntilSup | Other

(* TODO: kind and polarity are redundant *)
type t = kind * take_formula * Expl.Proof.valuation * polarity

let polarity_to_string = function
  | POS -> "+"
  | NEG -> "-"

let kind_to_string = function
  | NextCau -> "NextCau"
  | NextSup -> "NextSup"
  | UntilCau -> "UntilCau"
  | UntilSup -> "UntilSup"
  | Other -> "Other"

let to_string ((kind, _, valuation, pol) : t) =
  Printf.sprintf "Kind: %s\n" (kind_to_string kind) ^
    Printf.sprintf "Valuation: %s\n" (Etc.dom_map_to_string valuation) ^
      Printf.sprintf "Polarity: %s\n" (polarity_to_string pol)
