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

val sappend: sexpl -> sexpl -> sexpl
val vappend: vexpl -> vexpl -> vexpl
val slift: sexpl -> sexpl
val vlift: vexpl -> vexpl
