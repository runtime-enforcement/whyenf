open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

open Etc

module MFormula : sig

  type binop_info
  type nop_info
  type prev_info
  type once_info
  type next_info
  type eventually_info
  type historically_info
  type always_info
  type since_info
  type until_info

  val empty_binop_info: binop_info
  val empty_nop_info: int -> nop_info

  type core_t =
    | MTT
    | MFF
    | MEqConst      of Term.t * Dom.t
    | MPredicate    of string * Term.t list
    | MAgg          of string * Aggregation.op * Aggregation.op_fun * Term.t * string list * t
    | MTop          of string list * string * Aggregation.op_tfun * Term.t list * string list * t
    | MNeg          of t
    | MAnd          of Side.t * t list * nop_info
    | MOr           of Side.t * t list * nop_info
    | MImp          of Side.t * t * t * binop_info
    | MExists       of string * Dom.tt * bool * t
    | MForall       of string * Dom.tt * bool * t
    | MPrev         of Interval.t * t * prev_info
    | MNext         of Interval.t * t * next_info
    | MENext        of Interval.t * Time.t option * t * valuation
    | MOnce         of Interval.t * t * once_info
    | MEventually   of Interval.t * t * eventually_info
    | MEEventually  of Interval.t * Time.t option * t * valuation
    | MHistorically of Interval.t * t * historically_info
    | MAlways       of Interval.t * t * always_info
    | MEAlways      of Interval.t * Time.t option * t * valuation
    | MSince        of Side.t * Interval.t * t * t * since_info
    | MUntil        of Interval.t * t * t * until_info
    | MEUntil       of Side.t * Interval.t * Time.t option * t * t * valuation
    | MLabel        of string * t

  and t = { mf: core_t;
            filter: Filter.t;
            events: (string, String.comparator_witness) Set.t option;
            obligations: (int, Int.comparator_witness) Set.t option;
            hash: int;
            lbls: Lbl.t list }
  
  val make: core_t -> Filter.t -> t
  val set_make: core_t -> Filter.t -> t
  val map_mf: t -> Filter.t -> ?exquant:bool -> (t -> core_t) -> t
  val map2_mf: t -> t -> Filter.t -> (t -> t -> core_t) -> t
  val mapn_mf: t list -> Filter.t -> (t list -> core_t) -> t

  val _tt : t
  val _ff : t
  
  val init: Tformula.t -> t
  val rank: t -> int

  val apply_valuation : valuation -> t -> t

  val fv: t -> (String.t, Base.String.comparator_witness) Base.Set.t

  val to_string: ?l:int -> t -> string
  val value_to_string: t -> string
  val op_to_string: t -> string
  val side_to_string: t -> string

end

module TS : sig

  type 'a t = { tp : timepoint; ts : timestamp ; data : 'a }

end

module FObligation : sig

  type polarity = POS | NEG

  type kind =
    | FFormula of MFormula.t * int * valuation                       (* fun _ -> f *)
    | FInterval of Time.t * Interval.t * MFormula.t * int * valuation   (* fun t -> if mem t i then f else Formula.TT *)
    | FUntil of Time.t * Side.t * Interval.t * MFormula.t * MFormula.t * int * valuation (* fun t -> Until (s, sub2 i (t-t0), f1, f2) *)
    | FAlways of Time.t * Interval.t * MFormula.t * int * valuation     (* fun t -> Always (sub2 i (t-t0), f1) *)
    | FEventually of Time.t * Interval.t * MFormula.t * int * valuation (* fun t -> Eventually (sub2 i (t-t0), f1) *)

  type t = kind * valuation * polarity

  (*val equal: t -> t -> bool*)
  val fold_map: ('a -> MFormula.t -> 'a * MFormula.t) -> 'a -> t -> 'a * t
  val eval: Time.t -> int -> t -> MFormula.t
  val to_string: t -> string
  val h: t -> int

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

module Memo : sig

  type 'a t
  
  val find : 'a t -> MFormula.t -> FObligation.polarity -> 'a option
  val add_event : 'a t -> string -> 'a t
  val add_obligation : 'a t -> int -> 'a t
  val empty : 'a t

end

type res = Expl.t TS.t list * Expl.t * MFormula.t

val mstep: timepoint -> timestamp -> Db.t -> bool -> MState.t -> FObligations.t ->
           res Memo.t -> res Memo.t * (((timepoint * timestamp) * Expl.t) list * Expl.t * MState.t)

val meval_c: int ref 

