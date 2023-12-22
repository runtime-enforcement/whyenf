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
open Tformula

type take_formula = timestamp -> Tformula.t
type polarity = POS | NEG

type kind =
  | FFormula of Tformula.t                  (* fun _ -> f *)
  | FInterval of int * Interval.t * Tformula.t
                                            (* fun t -> if mem (t-t0) i then f else Formula.TT *)
  | FUntil of int * Formula.Side.t * Interval.t * Tformula.t * Tformula.t
                                            (* fun t -> Until (s, sub2 i (t-t0), f, g) *)
  | FAlways of int * Interval.t * Tformula.t
                                            (* fun t -> Always (sub2 i (t-t0), f) *)
  | FEventually of int * Interval.t * Tformula.t
                                            (* fun t -> Eventually (sub2 i (t-t0), f) *)

type t = kind * Expl.Proof.valuation * polarity

let eval_kind ts' k p = match k with
  | FFormula f -> f
  | FInterval (ts, i, f) ->
     if Interval.mem (ts' - ts) i then
       f
     else
       ttrue
  | FUntil (ts, side, i, f, g) ->
     if not (Interval.above (ts' - ts) i) then
       { f = TUntil (side, Interval.sub2 i (ts' - ts), f, g);
         enftype = match p with POS -> Cau | NEG -> Sup }
     else
       tfalse
  | FAlways (ts, i, f) ->
     if not (Interval.above (ts' - ts) i) then
       { f = TAlways (Interval.sub2 i (ts' - ts), f);
         enftype = match p with POS -> Cau | NEG -> Sup }
     else
       ttrue
  | FEventually (ts, i, f) ->
     if not (Interval.above (ts' - ts) i) then
       { f = TEventually (Interval.sub2 i (ts' - ts), f);
         enftype = match p with POS -> Cau | NEG -> Sup }
     else
       tfalse

let eval ts (k, v, p) =
  let f = apply_valuation v (eval_kind ts k p) in
  match p with
  | POS -> f
  | NEG -> Tformula.neg f Cau

let polarity_to_string = function
  | POS -> "+"
  | NEG -> "-"

let rec kind_to_string = function
  | FFormula f -> Printf.sprintf "Fformula(%s)" (to_string f)
  | FInterval (t, i, f) -> Printf.sprintf "FInterval(%d, %s, %s)" t (Interval.to_string i) (to_string f)
  | FUntil (t, s, i, f, g) -> Printf.sprintf "FUntil(%d, %s, %s, %s, %s)" t (Formula.Side.to_string s) (Interval.to_string i) (to_string f) (to_string g)
  | FAlways (t, i, f) -> Printf.sprintf "FAlways(%d, %s, %s)" t (Interval.to_string i) (to_string f)
  | FEventually (t, i, f) -> Printf.sprintf "FEventually(%d, %s, %s)" t (Interval.to_string i) (to_string f)

let to_string ((kind, valuation, pol) : t) =
  Printf.sprintf "Kind: %s\n" (kind_to_string kind) ^
    Printf.sprintf "Valuation: %s\n" (Etc.dom_map_to_string valuation) ^
      Printf.sprintf "Polarity: %s\n" (polarity_to_string pol)
