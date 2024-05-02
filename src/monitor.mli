(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Base
open Etc

module type MonitorT = sig

  module CI : Checker_interface.Checker_interfaceT
  
  module MFormula : sig

    type binop_info
    type prev_info
    type tp_info
    type buft_info
    type once_info
    type next_info
    type eventually_info
    type historically_info
    type always_info
    type buf2t_info
    type since_info
    type until_info

    val empty_binop_info: binop_info

    type t =
      | MTT
      | MFF
      | MEqConst      of Pred.Term.t * Dom.t
      | MPredicate    of string * Pred.Term.t list
      | MNeg          of t
      | MAnd          of Formula.Side.t * t * t * binop_info
      | MOr           of Formula.Side.t * t * t * binop_info
      | MImp          of Formula.Side.t * t * t * binop_info
      | MIff          of Formula.Side.t * Formula.Side.t * t * t * binop_info
      | MExists       of string * Dom.tt * t
      | MForall       of string * Dom.tt * t
      | MPrev         of Interval.t * t * bool * prev_info
      | MNext         of Interval.t * t * bool * next_info
      | MENext        of Interval.t * t * int
      | MOnce         of Interval.t * t * tp_info * once_info
      | MEventually   of Interval.t * t * buft_info * eventually_info
      | MEEventually  of Interval.t * t * int
      | MHistorically of Interval.t * t * tp_info * historically_info
      | MAlways       of Interval.t * t * buft_info * always_info
      | MEAlways      of Interval.t * t * int
      | MSince        of Formula.Side.t * Interval.t * t * t * buf2t_info * since_info
      | MUntil        of Interval.t * t * t * buf2t_info * until_info
      | MEUntil       of Formula.Side.t * Interval.t * t * t * int

    val init: Tformula.t -> t
    val rank: t -> int

    val apply_valuation : Etc.valuation -> t -> t

    val fv: t -> (String.t, Base.String.comparator_witness) Base.Set.t
    val terms: t -> (Pred.Term.t, Pred.Term.comparator_witness) Base.Set.t

    val to_string: t -> string
    val op_to_string: t -> string
    val side_to_string: t -> string

  end

  module FObligation : sig

    open MFormula

    type polarity = POS | NEG

    type kind =
      | FFormula of MFormula.t * int                       (* fun _ -> f *)
      | FInterval of int * Interval.t * MFormula.t * int   (* fun t -> if mem t i then f else Formula.TT *)
      | FUntil of int * Formula.Side.t * Interval.t * MFormula.t * MFormula.t * int (* fun t -> Until (s, sub2 i (t-t0), f1, f2) *)
      | FAlways of int * Interval.t * MFormula.t * int     (* fun t -> Always (sub2 i (t-t0), f1) *)
      | FEventually of int * Interval.t * MFormula.t * int (* fun t -> Eventually (sub2 i (t-t0), f1) *)

    type t = kind * Etc.valuation * polarity

    val equal: t -> t -> bool
    val eval: int -> int -> t -> MFormula.t
    val to_string: t -> string

    include Comparable.S with type t := t

  end

  module FObligations : sig

    type t = (FObligation.t, FObligation.comparator_witness) Set.t

    val to_string: t -> string
    val empty: t
    val accepts_empty: t -> bool

  end


  module MState : sig

    type t = { mf: MFormula.t
             ; tp_cur: timepoint
             ; tp_out: timepoint
             ; ts_waiting: timestamp Queue.t
             ; tsdbs: (timestamp * Db.t) Queue.t
             ; tpts: (timepoint, timestamp) Hashtbl.t }

    val tp_cur: t -> timepoint

    val tsdbs: t -> (timestamp * Db.t) Queue.t

    val init: MFormula.t -> t

    val to_string: string -> t -> string

  end

  val mstep: Out.mode -> Pred.Term.t list -> timestamp -> Db.t -> bool -> MState.t -> FObligations.t ->
             ((timestamp * timepoint) * CI.Expl.t) list * CI.Expl.t * MState.t

  val exec: Out.mode -> string -> Formula.t -> in_channel -> unit

  val exec_vis: MState.t option -> Formula.t -> string -> (MState.t * string)

end

module Make (CI : Checker_interface.Checker_interfaceT) : MonitorT
