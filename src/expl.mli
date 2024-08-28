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

  type sub = (Dom.t, Dom.comparator_witness) Setc.t

  type 'a t = (sub * 'a) list

  val trivial: 'a -> 'a t
  val length: 'a t -> int
  val map: 'a t -> ('a -> 'b) -> 'b t
  val map2: 'a t -> (sub * 'a -> sub * 'a) -> 'a t
  val fold_left: 'a t -> 'b -> ('b -> 'a -> 'b) -> 'b
  val filter: 'a t -> ('a -> bool) -> 'a t
  val exists: 'a t -> ('a -> bool) -> bool
  val for_all: 'a t -> ('a -> bool) -> bool
  val values: 'a t -> 'a list
  val tabulate: (Dom.t, Dom.comparator_witness) Set.t -> (Dom.t -> 'a) -> 'a -> 'a t

  val dedup: ('a -> 'a -> bool) -> 'a t -> 'a t
  val map_dedup: ('a -> 'a -> bool) -> 'd t -> ('d -> 'a) -> 'a t
  val map2_dedup: ('a -> 'a -> bool) -> 'a t -> (sub * 'a -> sub * 'a) -> 'a t
  val tabulate_dedup: ('a -> 'a -> bool) -> (Dom.t, Dom.comparator_witness) Set.t -> (Dom.t -> 'a) -> 'a -> 'a t

end

module Pdt : sig

  type 'a t = Leaf of 'a | Node of Lbl.t * ('a t) Part.t

  val apply1: Lbl.tt list -> ('a -> 'b) -> 'a t -> 'b t
  val apply2: Lbl.tt list -> ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val apply3: Lbl.tt list -> ('a -> 'b -> 'c -> 'd) -> 'a t -> 'b t -> 'c t -> 'd t
  val split_prod: ('a * 'b) t -> 'a t * 'b t
  val split_list: 'a list t -> 'a t list
  val hide: Lbl.tt list -> ('a -> 'b) -> ('a Part.t -> 'b) -> 'a t -> 'b t
  val to_string: ('a -> string) -> string -> 'a t -> string

  val eq: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val reduce: ('a -> 'a -> bool) -> 'a t -> 'a t
  val apply1_reduce: ('a -> 'a -> bool) -> Lbl.tt list -> ('b -> 'a) -> 'b t -> 'a t
  val apply2_reduce: ('a -> 'a -> bool) -> Lbl.tt list -> ('b -> 'c -> 'a) -> 'b t -> 'c t -> 'a t
  val apply3_reduce: ('a -> 'a -> bool) -> Lbl.tt list -> ('b -> 'c -> 'd -> 'a) -> 'b t -> 'c t -> 'd t -> 'a t
  val split_prod_reduce: ('a -> 'a -> bool) -> ('a * 'a) t -> 'a t * 'a t
  val split_list_reduce: ('a -> 'a -> bool) -> 'a list t -> 'a t list
  val hide_reduce: string -> ('a -> 'a -> bool) -> Lbl.tt list -> ('b -> 'a) -> ('b t list -> 'a t) -> 'b t -> 'a t

  (*val replace_leaf: Etc.valuation -> 'a -> 'a t -> 'a t*)
  val specialize: Etc.valuation -> 'a t -> 'a
  val specialize_partial: Etc.valuation -> 'a t -> 'a t
  
  (*val simplify: string -> ('a -> 'a -> bool) -> 'a t -> 'a t*)
  (*val simplify_vars: string -> Term.t list -> Term.t list*)
  
  val collect: ('a -> bool) -> Etc.valuation -> string -> 'a t -> (Dom.t, Dom.comparator_witness) Setc.t
  val from_valuation: Lbl.tt list -> Etc.valuation -> 'b -> 'b -> 'b t

  val aggregate: ('a -> bool) -> ((Dom.t, Dom.comparator_witness) Setc.t -> Dom.t option -> 'b) -> ((Dom.t, int, Dom.comparator_witness) Map.t -> Dom.t) -> string -> Pred.Term.t -> string list -> Lbl.tt list -> Lbl.tt list -> 'a t -> 'b t

end


module type ProofT = sig

  type sp
  type vp

  type t = S of sp | V of vp

  val s_equal: sp -> sp -> bool
  val v_equal: vp -> vp -> bool
  val equal: t -> t -> bool

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
  val to_latex: string -> Formula.t -> t -> string
  val to_bool: t -> string

  val make_stt: int -> sp
  val make_seqconst: int -> Term.t -> Dom.t -> sp
  val make_spred: int -> string -> Term.t list -> sp
  val make_sneg: vp -> sp
  val make_sorl: sp -> sp
  val make_sorr: sp -> sp
  val make_sand: sp -> sp -> sp
  val make_simpl: vp -> sp
  val make_simpr: sp -> sp
  val make_siffss: sp -> sp -> sp
  val make_siffvv: vp -> vp -> sp
  val make_sexists: string -> Dom.t -> sp -> sp
  val make_sforall: string -> sp Part.t -> sp
  val make_sprev: sp -> sp
  val make_snext: sp -> sp
  val make_snextassm: int -> sp
  val make_sonce: int -> sp -> sp
  val make_seventually: int -> sp -> sp
  val make_seventuallyassm: int -> Interval.t -> sp
  val make_seventuallynow: sp -> Interval.t -> sp
  val make_shistorically: int -> int -> sp Fdeque.t -> sp
  val make_shistoricallyout: int -> sp
  val make_salways: int -> int -> sp Fdeque.t -> sp
  val make_salwaysassm: int -> sp option -> Interval.t -> sp
  val make_ssince: sp -> sp Fdeque.t -> sp
  val make_suntil: sp -> sp Fdeque.t -> sp
  val make_suntilassm: int -> sp -> Interval.t -> sp
  val make_suntilnow: sp -> Interval.t -> sp

  val make_vff: int -> vp
  val make_veqconst: int -> Term.t -> Dom.t -> vp
  val make_vpred: int -> string -> Term.t list -> vp
  val make_vneg: sp -> vp
  val make_vor: vp -> vp -> vp
  val make_vandl: vp -> vp
  val make_vandr: vp -> vp
  val make_vimp: sp -> vp -> vp
  val make_viffsv: sp -> vp -> vp
  val make_viffvs: vp -> sp -> vp
  val make_vexists: string -> vp Part.t -> vp
  val make_vforall: string -> Dom.t -> vp -> vp
  val make_vprev: vp -> vp
  val make_vprev0: vp
  val make_vprevoutl: int -> vp
  val make_vprevoutr: int -> vp
  val make_vnext: vp -> vp
  val make_vnextoutl: int -> vp
  val make_vnextoutr: int -> vp
  val make_vnextassm: int -> Interval.t -> vp
  val make_vonceout: int -> vp
  val make_vonce: int -> int -> vp Fdeque.t -> vp
  val make_veventually: int -> int -> vp Fdeque.t -> vp
  val make_veventuallyassm: int -> vp option -> Interval.t -> vp
  val make_vhistorically: int -> vp -> vp
  val make_valways: int -> vp -> vp
  val make_valwaysassm: int -> Interval.t -> vp
  val make_valwaysnow: vp -> Interval.t -> vp
  val make_vsinceout: int -> vp
  val make_vsince: int -> vp -> vp Fdeque.t -> vp
  val make_vsinceinf: int -> int -> vp Fdeque.t -> vp
  val make_vuntil: int -> vp -> vp Fdeque.t -> vp
  val make_vuntilinf: int -> int -> vp Fdeque.t -> vp
  val make_vuntilassm: int -> vp -> Interval.t -> vp
  val make_vuntilnow: vp -> Interval.t -> vp

  val decompose_vsince: vp -> (vp * vp Fdeque.t) option
  val decompose_vuntil: vp -> (vp * vp Fdeque.t) option

  module Size : sig

    val minp_bool: t -> t -> bool
    val minp: t -> t -> t
    val minp_list: t list -> t

  end

end

type t_sp =
  | STT of int
  | SEqConst of int * Term.t * Dom.t
  | SPred of int * string * Term.t list
  | SNeg of t_vp
  | SOrL of t_sp
  | SOrR of t_sp
  | SAnd of t_sp * t_sp
  | SImpL of t_vp
  | SImpR of t_sp
  | SIffSS of t_sp * t_sp
  | SIffVV of t_vp * t_vp
  | SExists of string * Dom.t * t_sp
  | SForall of string * (t_sp Part.t)
  | SPrev of t_sp
  | SNext of t_sp
  | SNextAssm of int
  | SOnce of int * t_sp
  | SEventually of int * t_sp
  | SEventuallyAssm of int * Interval.t
  | SEventuallyNow of t_sp * Interval.t
  | SHistorically of int * int * t_sp Fdeque.t
  | SHistoricallyOut of int
  | SAlways of int * int * t_sp Fdeque.t
  | SAlwaysAssm of int * t_sp option * Interval.t
  | SSince of t_sp * t_sp Fdeque.t
  | SUntil of t_sp * t_sp Fdeque.t
  | SUntilAssm of int * t_sp * Interval.t
  | SUntilNow of t_sp * Interval.t
and t_vp =
  | VFF of int
  | VEqConst of int * Term.t * Dom.t
  | VPred of int * string * Term.t list
  | VNeg of t_sp
  | VOr of t_vp * t_vp
  | VAndL of t_vp
  | VAndR of t_vp
  | VImp of t_sp * t_vp
  | VIffSV of t_sp * t_vp
  | VIffVS of t_vp * t_sp
  | VExists of string * (t_vp Part.t)
  | VForall of string * Dom.t * t_vp
  | VPrev of t_vp
  | VPrev0
  | VPrevOutL of int
  | VPrevOutR of int
  | VNext of t_vp
  | VNextOutL of int
  | VNextOutR of int
  | VNextAssm of int * Interval.t
  | VOnceOut of int
  | VOnce of int * int * t_vp Fdeque.t
  | VEventually of int * int * t_vp Fdeque.t
  | VEventuallyAssm of int * t_vp option * Interval.t
  | VHistorically of int * t_vp
  | VAlways of int * t_vp
  | VAlwaysAssm of int * Interval.t
  | VAlwaysNow of t_vp * Interval.t
  | VSinceOut of int
  | VSince of int * t_vp * t_vp Fdeque.t
  | VSinceInf of int * int * t_vp Fdeque.t
  | VUntil of int * t_vp * t_vp Fdeque.t
  | VUntilInf of int * int * t_vp Fdeque.t
  | VUntilAssm of int * t_vp * Interval.t
  | VUntilNow of t_vp * Interval.t

module Proof : ProofT with type sp = t_sp and type vp = t_vp

module LightProof : ProofT with type sp = int and type vp = int

module Make (P : ProofT) : sig

  module Proof : ProofT with type sp = P.sp and type vp = P.vp and type t = P.t
  type t = P.t Pdt.t

  val is_violated: t -> bool
  val is_satisfied: t -> bool
  val at: t -> int

  val to_string: t -> string
  val to_latex: Formula.t -> t -> string
  val to_light_string: t -> string

end
