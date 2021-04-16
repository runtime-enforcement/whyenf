(*******************************************************************)
(*    This is part of Explanator2, it is distributed under the     *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

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
  | VPrevB of int
  | VPrevA of int
  | VPrev of vexpl
  | VOnce of vexpl list
  | VHistorically of int * vexpl
  | VNextB of int
  | VNextA of int
  | VNext of vexpl
  | VEventually of vexpl list
  | VAlways of int * vexpl
  | VSince of int * vexpl * vexpl list
  | VSinceInf of int * vexpl list
  | VSinceOut of int
  | VUntil of int * vexpl * vexpl list
  | VUntilInf of int * vexpl list

type expl = S of sexpl | V of vexpl

exception VEXPL
exception SEXPL

let unS = function S p -> p | _ -> raise VEXPL
let unV = function V p -> p | _ -> raise SEXPL

let expl_to_bool = function
  | S _ -> true
  | V _ -> false

let sappend sp' sp_f1 = match sp' with
  | SSince (sp_f2, sp_f1s) -> SSince (sp_f2, List.append sp_f1s [sp_f1])
  | SUntil (sp_f2, sp_f1s) -> SUntil (sp_f2, sp_f1 :: sp_f1s)
  (* | SHistorically sp_f1s -> SHistorically (List.append sp_f1s [sp_f1])
   * | SAlways sp_f1s -> SAlways (sp_f1 :: sp_f1s) *)
  | _ -> failwith "Bad arguments for sappend"

let vappend vp' vp_f2 = match vp' with
  | VSince (i, vp_f1, vp_f2s) -> VSince (i+1, vp_f1, List.append vp_f2s [vp_f2])
  | VSinceInf (i, vp_f2s) -> VSinceInf (i+1, List.append vp_f2s [vp_f2])
  | VUntil (i, vp_f1, vp_f2s) -> VUntil (i, vp_f1, vp_f2 :: vp_f2s)
  | VUntilInf (i, vp_f2s) -> VUntilInf (i, vp_f2 :: vp_f2s)
  (* | VOnce vp_f2s -> VOnce (List.append vp_f2s [vp_f2])
   * | VEventually vp_f2s -> VEventually (vp_f2 :: vp_f2s) *)
  | _ -> failwith "Bad arguments for vappend"

let slift = function
  | SOnce (i, sp) -> SOnce (i + 1, sp)
  | SEventually (i, sp) -> SEventually (i - 1, sp)
  | _ -> failwith "Bad arguments for slift"

let vlift = function
  | VHistorically (i, vp) -> VHistorically (i + 1, vp)
  | VAlways (i, vp) -> VAlways (i - 1, vp)
  | _ -> failwith "Bad arguments for vlift"
