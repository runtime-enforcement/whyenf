(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
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
  | SPrev of sexpl
  | SNext of sexpl
  | SOnce of int * sexpl
  | SHistorically of int * int * sexpl list
  | SSince of sexpl * sexpl list
  | SUntil of sexpl * sexpl list
and vexpl =
  | VFF of int
  | VAtom of int * string
  | VNeg of sexpl
  | VDisj of vexpl * vexpl
  | VConjL of vexpl
  | VConjR of vexpl
  | VPrev0
  | VPrevOutL of int
  | VPrevOutR of int
  | VPrev of vexpl
  | VNextOutL of int
  | VNextOutR of int
  | VNext of vexpl
  | VOnceOutL of int
  | VOnceInf of int * int * vexpl list
  | VHistoricallyOutL of int
  | VHistorically of int * vexpl
  | VSince of int * vexpl * vexpl list
  | VSinceInf of int * int * vexpl list
  | VSinceOutL of int
  | VUntil of int * vexpl * vexpl list
  | VUntilInf of int * int * vexpl list

type expl = S of sexpl | V of vexpl

exception VEXPL
exception SEXPL

val unS: expl -> sexpl
val unV: expl -> vexpl

val sappend: sexpl -> sexpl -> sexpl
val vappend: vexpl -> vexpl -> vexpl
val sdrop: sexpl -> sexpl option
val vdrop: vexpl -> vexpl option

val size: expl -> int
val size_le: expl -> expl -> bool
val minsize: expl -> expl -> expl
val minsize_list: expl list -> expl

val wsize: (string, int) Hashtbl.t -> expl -> int
val wsize_le: (string, int) Hashtbl.t -> expl -> expl -> bool

val high: expl -> int
val high_le: expl -> expl -> bool

val low: expl -> int
val low_le: expl -> expl -> bool

val predicates: expl -> int
val predicates_le: expl -> expl -> bool

val s_at: sexpl -> int
val v_at: vexpl -> int
val s_ltp: sexpl -> int
val v_etp: vexpl -> int
val p_at: expl -> int

val s_to_string: string -> sexpl -> string
val v_to_string: string -> vexpl -> string
val expl_to_string: expl -> string
