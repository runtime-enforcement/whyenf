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
open Monitor

open MFormula

type take_formula = timestamp -> MFormula.t
type polarity = POS | NEG

type kind =
  | FFormula of MFormula.t                  (* fun _ -> f *)
  | FInterval of int * Interval.t * MFormula.t
                                            (* fun t -> if mem (t-t0) i then f else Formula.TT *)
  | FUntil of int * Formula.Side.t * Interval.t * MFormula.t * MFormula.t * buf2_info * until_info
                                            (* fun t -> Until (s, sub2 i (t-t0), f, g) *)
  | FAlways of int * Interval.t * MFormula.t * buf_info * always_info
                                            (* fun t -> Always (sub2 i (t-t0), f) *)
  | FEventually of int * Interval.t * MFormula.t * buf_info * eventually_info
                                            (* fun t -> Eventually (sub2 i (t-t0), f) *)

type t = kind * Expl.Proof.valuation * polarity

let eval_kind ts' k p = match k with
  | FFormula f -> f
  | FInterval (ts, i, f) ->
     if Interval.mem (ts' - ts) i then
       f
     else
       MTT
  | FUntil (ts, side, i, f, g, bi, ui) ->
     if not (Interval.above (ts' - ts) i) then
       (* TODO: adapt bi and ui *)
       MUntil (side, Interval.sub2 i (ts' - ts), f, g, bi, ui)
     else
       MFF
  | FAlways (ts, i, f, bi, ai) ->
     if not (Interval.above (ts' - ts) i) then
       (* TODO: adapt bi and ai *)
       MAlways (Interval.sub2 i (ts' - ts), f, bi, ai)
     else
       MTT
  | FEventually (ts, i, f, bi, ei) ->
     if not (Interval.above (ts' - ts) i) then
       MEventually (Interval.sub2 i (ts' - ts), f, bi, ei)
     else
       MFF

let eval ts (k, v, p) =
  let f = apply_valuation v (eval_kind ts k p) in
  match p with
  | POS -> f
  | NEG -> MNeg f 

let polarity_to_string = function
  | POS -> "+"
  | NEG -> "-"

let rec kind_to_string = function
  | FFormula f -> Printf.sprintf "Fformula(%s)" (to_string f)
  | FInterval (t, i, f) -> Printf.sprintf "FInterval(%d, %s, %s)" t (Interval.to_string i) (to_string f)
  | FUntil (t, s, i, f, g, _, _) -> Printf.sprintf "FUntil(%d, %s, %s, %s, %s)" t (Formula.Side.to_string s) (Interval.to_string i) (to_string f) (to_string g)
  | FAlways (t, i, f, _, _) -> Printf.sprintf "FAlways(%d, %s, %s)" t (Interval.to_string i) (to_string f)
  | FEventually (t, i, f, _, _) -> Printf.sprintf "FEventually(%d, %s, %s)" t (Interval.to_string i) (to_string f)

let to_string ((kind, valuation, pol) : t) =
  Printf.sprintf "Kind: %s\n" (kind_to_string kind) ^
    Printf.sprintf "Valuation: %s\n" (Etc.dom_map_to_string valuation) ^
      Printf.sprintf "Polarity: %s\n" (polarity_to_string pol)
