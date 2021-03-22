(*******************************************************************)
(*    This is part of Explanator2, it is distributed under the     *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl
open Height

(* explanations *)
type sexpl =
  | STT of int
  | SAtom of int * string
  | SNeg of vexpl
  | SDisjL of sexpl
  | SDisjR of sexpl
  | SConj of sexpl * sexpl
  | SImplL of vexpl
  | SImplR of sexpl
  | SIffS of sexpl * sexpl
  | SIffV of vexpl * vexpl
  | SPrev of sexpl
  | SOnce of int * sexpl
  | SHistorically of sexpl list
  | SNext of sexpl
  | SEventually of int * sexpl
  | SAlways of sexpl list
  | SSince of sexpl * sexpl list
  | SUntil of sexpl * sexpl list
and vexpl =
  | VFF of int
  | VAtom of int * string
  | VNeg of sexpl
  | VDisj of vexpl * vexpl
  | VConjL of vexpl
  | VConjR of vexpl
  | VImpl of sexpl * vexpl
  | VIffL of sexpl * vexpl
  | VIffR of vexpl * sexpl
  | VPrev0
  | VPrev of vexpl
  | VOnce of vexpl list
  | VHistorically of int * vexpl
  | VNext of vexpl
  | VEventually of vexpl list
  | VAlways of int * vexpl
  | VSince of vexpl * vexpl list
  | VSincew of vexpl list
  | VUntil of vexpl * vexpl list
  | VUntilw of vexpl list

type expl = S of sexpl | V of vexpl

exception VEXPL
exception SEXPL

let unS = function S p -> p | _ -> raise VEXPL
let unV = function V p -> p | _ -> raise SEXPL

let expl_to_bool = function
  | S _ -> true
  | V _ -> false

(* let sappend sp' sp_f1 = match sp' with
 *   | SSince (sp_f2, sp_f1s) -> SSince (sp_f2, List.append sp_f1s [sp_f1])
 *   | SHistorically sp_f1s -> SHistorically (List.append sp_f1s [sp_f1])
 *   | SUntil (sp_f2, sp_f1s) -> SUntil (sp_f2, sp_f1 :: sp_f1s)
 *   | SAlways sp_f1s -> SAlways (sp_f1 :: sp_f1s)
 *   | _ -> failwith "bad arguments for sappend"
 * 
 * let slift = function
 *   | SOnce (i, sp) -> SOnce (i + 1, sp)
 *   | SEventually (i, sp) -> SEventually (i - 1, sp)
 *   | _ -> failwith "bad arguments for slift"
 * 
 * let vlift = function
 *   | VHistorically (i, vp) -> VHistorically (i + 1, vp)
 *   | VAlways (i, vp) -> VAlways (i - 1, vp)
 *   | _ -> failwith "bad arguments for vlift"
 * 
 * let vappend vp' vp_f2 = match vp' with
 *   | VSince (vp_f1, vp_f2s) -> VSince (vp_f1, List.append vp_f2s [vp_f2])
 *   | VSincew vp_f2s -> VSincew (List.append vp_f2s [vp_f2])
 *   | VOnce vp_f2s -> VOnce (List.append vp_f2s [vp_f2])
 *   | VUntil (vp_f1, vp_f2s) -> VUntil (vp_f1, vp_f2 :: vp_f2s)
 *   | VUntilw vp_f2s -> VUntilw (vp_f2 :: vp_f2s)
 *   | VEventually vp_f2s -> VEventually (vp_f2 :: vp_f2s)
 *   | _ -> failwith "bad arguments for vappend" *)
