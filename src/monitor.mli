open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

open Etc

type polarity = POS | NEG [@@deriving compare, sexp_of, hash, equal]

type binop_info
and nop_info
and prev_info
and next_info
and once_info
and eventually_info
and historically_info
and always_info
and since_info
and until_info

and mf_core_t =
  | MTT
  | MFF
  | MEqConst      of Term.t * Dom.t
  | MPredicate    of string * Term.t list
  | MAgg          of string * Aggregation.op * Aggregation.op_fun * Term.t * string list * mf_t
  | MTop          of string list * string * Aggregation.op_tfun * Term.t list * string list * mf_t
  | MNeg          of mf_t
  | MAnd          of Side.t * mf_t list * nop_info
  | MOr           of Side.t * mf_t list * nop_info
  | MImp          of Side.t * mf_t * mf_t * binop_info
  | MExists       of string * Dom.tt * bool * mf_t
  | MForall       of string * Dom.tt * bool * mf_t
  | MPrev         of Interval.t * mf_t * prev_info
  | MNext         of Interval.t * mf_t * next_info
  | MENext        of Interval.t * timestamp option * mf_t
  | MOnce         of Interval.t * mf_t * once_info
  | MEventually   of Interval.t * mf_t * eventually_info
  | MEEventually  of Interval.t * timestamp option * mf_t
  | MHistorically of Interval.t * mf_t * historically_info
  | MAlways       of Interval.t * mf_t * always_info
  | MEAlways      of Interval.t * timestamp option * mf_t
  | MSince        of Side.t * Interval.t * mf_t * mf_t * since_info
  | MUntil        of Interval.t * mf_t * mf_t * until_info
  | MEUntil       of Side.t * Interval.t * timestamp option * mf_t * mf_t

and mf_t = {
    mf: mf_core_t;
    filter: Filter.t;
    events: (string, String.comparator_witness) Set.t option;
    obligations: (int, Int.comparator_witness) Set.t option;
    hash: int;
    lbls: Lbl.t list
  } 

and fo =
  | FFormula of mf_t * int * Etc.valuation
  | FInterval of timestamp * Interval.t * mf_t * int * Etc.valuation
  | FUntil of timestamp * Side.t * Interval.t * mf_t * mf_t * int * Etc.valuation
  | FAlways of timestamp * Interval.t * mf_t * int * Etc.valuation
  | FEventually of timestamp * Interval.t * mf_t * int * Etc.valuation

and fix =
  | FEvent of string * Term.t list * polarity * int
  | FOblig of fo * polarity

and fbool =
  | FTrue  of fix list
  | FFalse of fix list

val fix_is_oblig: fix -> bool
val fix_is_event: fix -> bool
val value_to_string: mf_t -> string
val fbool_to_string: fbool -> string
val fix_to_string: fix -> string
val compare_fix: fix -> fix -> int

module MFormula : sig

  val empty_binop_info: binop_info
  val empty_nop_info: int -> nop_info

  type core_t = mf_core_t and t = mf_t
  
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
  val op_to_string: t -> string
  val side_to_string: t -> string

end

module TS : sig

  type 'a t = { tp : timepoint; ts : timestamp ; data : 'a }

end

module FObligation : sig

  type t = fo * polarity

  (*val equal: t -> t -> bool*)
  val fold_map: ('a -> MFormula.t -> 'a * MFormula.t) -> 'a -> t -> 'a * t
  val set_valuation: Etc.valuation -> fo -> fo
  val pop_valuation: fo -> fo * Etc.valuation
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
  
  val find : 'a t -> MFormula.t -> polarity -> 'a option
  val add_event : 'a t -> string -> 'a t
  val add_obligation : 'a t -> int -> 'a t
  val empty : 'a t

end

type res = bool Expl.t TS.t list * fbool Expl.t * MFormula.t

val mstep: timepoint -> timestamp -> Db.t -> bool -> MState.t -> FObligations.t -> bool -> 
           res Memo.t -> res Memo.t * (fbool Expl.t * MState.t)

val meval_c: int ref 


