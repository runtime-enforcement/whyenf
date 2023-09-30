(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Pred

module Fdeque = Core.Fdeque

module Part : sig

  type 'a t = ((Domain.t, Domain.comparator_witness) Setc.t * 'a) list

  val trivial: 'a -> 'a t

  val map: 'a t -> ('a -> 'b) -> 'b t

  val fold_left: 'a t -> 'b -> ('b -> 'a -> 'b) -> 'b

  val filter: 'a t -> ('a -> bool) -> 'a t

  val exists: 'a t -> ('a -> bool) -> bool

  val for_all: 'a t -> ('a -> bool) -> bool

  val values: 'a t -> 'a list

  val tabulate: (Domain.t, Domain.comparator_witness) Set.t -> (Domain.t -> 'a) -> 'a -> 'a t

end

module Proof : sig

  type sp =
    | STT of int
    | SEqConst of int * string * Domain.t
    | SPred of int * string * Term.t list
    | SNeg of vp
    | SOrL of sp
    | SOrR of sp
    | SAnd of sp * sp
    | SImpL of vp
    | SImpR of sp
    | SIffSS of sp * sp
    | SIffVV of vp * vp
    | SExists of string * Domain.t * sp
    | SForall of string * (sp Part.t)
    | SPrev of sp
    | SNext of sp
    | SOnce of int * sp
    | SEventually of int * sp
    | SHistorically of int * int * sp Fdeque.t
    | SHistoricallyOut of int
    | SAlways of int * int * sp Fdeque.t
    | SSince of sp * sp Fdeque.t
    | SUntil of sp * sp Fdeque.t
  and vp =
    | VFF of int
    | VEqConst of int * string * Domain.t
    | VPred of int * string * Term.t list
    | VNeg of sp
    | VOr of vp * vp
    | VAndL of vp
    | VAndR of vp
    | VImp of sp * vp
    | VIffSV of sp * vp
    | VIffVS of vp * sp
    | VExists of string * (vp Part.t)
    | VForall of string * Domain.t * vp
    | VPrev of vp
    | VPrev0
    | VPrevOutL of int
    | VPrevOutR of int
    | VNext of vp
    | VNextOutL of int
    | VNextOutR of int
    | VOnceOut of int
    | VOnce of int * int * vp Fdeque.t
    | VEventually of int * int * vp Fdeque.t
    | VHistorically of int * vp
    | VAlways of int * vp
    | VSinceOut of int
    | VSince of int * vp * vp Fdeque.t
    | VSinceInf of int * int * vp Fdeque.t
    | VUntil of int * vp * vp Fdeque.t
    | VUntilInf of int * int * vp Fdeque.t

  type t = S of sp | V of vp

  val unS: t -> sp
  val unV: t -> vp
  val isS: t -> bool
  val isV: t -> bool

  val s_append: sp -> sp -> sp
  val v_append: vp -> vp -> vp
  val s_drop: sp -> sp option
  val v_drop: vp -> vp option

  val s_at: sp -> int
  val v_at: vp -> int
  val p_at: t -> int

  val s_ltp: sp -> int
  val v_etp: vp -> int

  val s_to_string: string -> sp -> string
  val v_to_string: string -> vp -> string
  val to_string: string -> t -> string

  module Size : sig

    val minp_bool: t -> t -> bool
    val minp: t -> t -> t
    val minp_list: t list -> t

  end

end

module Pdt : sig

  type 'a t = Leaf of 'a | Node of string * ('a t) Part.t

  val apply1: string list -> ('a -> 'b) -> 'a t -> 'b t

  val apply2: string list -> ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

  val apply3: string list -> ('a -> 'b -> 'c -> 'd) -> 'a t -> 'b t -> 'c t -> 'd t

  val split_prod: ('a * 'b) t -> 'a t * 'b t

  val split_list: 'a list t -> 'a t list

  val hide: string list -> (('a, 'a Part.t) Either.t -> 'b) -> 'a t -> 'b t

  val to_string: ('a -> string) -> string -> 'a t -> string

end

type t = Proof.t Pdt.t

val at: Proof.t Pdt.t -> int

val to_string: t -> string

val to_latex: Formula.t -> t -> string
