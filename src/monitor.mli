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

module MFormula : sig

  type binop_info
  type prev_info
  type tp_info
  type buft_info
  type once_info
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
    | MEqConst      of string * Dom.t
    | MPredicate    of string * Pred.Term.t list
    | MNeg          of t
    | MAnd          of Formula.Side.t * t * t * binop_info
    | MOr           of Formula.Side.t * t * t * binop_info
    | MImp          of Formula.Side.t * t * t * binop_info
    | MIff          of Formula.Side.t * Formula.Side.t * t * t * binop_info
    | MExists       of string * Dom.tt * t
    | MForall       of string * Dom.tt * t
    | MPrev         of Interval.t * t * bool * prev_info
    | MNext         of Interval.t * t * bool * timestamp list
    | MOnce         of Interval.t * t * tp_info * once_info
    | MEventually   of Interval.t * t * buft_info * eventually_info
    | MHistorically of Interval.t * t * tp_info * historically_info
    | MAlways       of Interval.t * t * buft_info * always_info
    | MSince        of Formula.Side.t * Interval.t * t * t * buf2t_info * since_info
    | MUntil        of Formula.Side.t * Interval.t * t * t * buf2t_info * until_info

  val init: Formula.t -> t

  val apply_valuation : Expl.Proof.valuation -> t -> t

  val fv: t -> (String.t, Base.String.comparator_witness) Base.Set.t
  val rank: t -> int

  val to_string: t -> string
  val op_to_string: t -> string

end

module FObligation : sig

  open MFormula

  type polarity = POS | NEG

  type kind =
    | FFormula of MFormula.t                       (* fun _ -> f *)
    | FInterval of int * Interval.t * MFormula.t   (* fun t -> if mem t i then f else Formula.TT *)
    | FUntil of int * Formula.Side.t * Interval.t * MFormula.t * MFormula.t * until_info (* fun t -> Until (s, sub2 i (t-t0), f1, f2) *)
    | FAlways of int * Interval.t * MFormula.t * always_info (* fun t -> Always (sub2 i (t-t0), f1) *)
    | FEventually of int * Interval.t * MFormula.t * eventually_info (* fun t -> Eventually (sub2 i (t-t0), f1) *)

  type t = kind * Expl.Proof.valuation * polarity

  val equal: t -> t -> bool
  val eval: int -> int -> t -> MFormula.t
  val to_string: t -> string

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

end

val mstep: Out.Plain.mode -> string list -> timestamp -> Db.t -> MState.t -> FObligation.t list ->
           ((timestamp * timepoint) * Expl.Proof.t Expl.Pdt.t) list * MState.t

val exec: Out.Plain.mode -> string -> Formula.t -> in_channel -> unit

val exec_vis: MState.t option -> Formula.t -> string -> (MState.t * string)
