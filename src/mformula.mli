open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm
module Valuation = ITerm.Valuation

open Etc

module Polarity : sig

  type t = POS | NEG [@@deriving compare, sexp_of, hash, equal]

  val neg : t -> t
  val to_int: t -> int
  val to_string: t -> string
  val value: t option -> t

end

module TS : sig

  type 'a t = { tp : timepoint; ts : timestamp ; data : 'a }

  val make : timepoint -> timestamp -> 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t 
  val map_list : ('a list -> 'b) -> 'a t list -> 'b t

end

module Buf2 : sig

  type ('a, 'b) t = 'a list * 'b list

  val add : 'a list -> 'b list -> ('a, 'b) t -> ('a, 'b) t
  val take : ('a -> 'b -> 'c) -> ('a, 'b) t -> 'c list * ('a, 'b) t

  val map : ('a -> 'b) -> ('c -> 'd) -> ('a, 'c) t -> ('b, 'd) t

end

module Bufn : sig

  type 'a t = 'a list list

  val empty : int -> 'a t
  val add : 'a t -> 'a t -> 'a t
  val take : ('a list -> 'b) -> 'a t -> ('b list * 'a t)
  val map : ('a -> 'b) -> 'a t -> 'b t

end

module Prev : sig

  type t

  val add : Expl.t TS.t list -> t -> t
  val update : t -> t * Expl.t TS.t list
  val approximate : timepoint -> Expl.t TS.t list -> Polarity.t option -> Expl.t

end

module Next : sig

  type t

  val add : Expl.t TS.t list -> t -> t
  val update : t -> t * Expl.t TS.t list
  val approximate : Polarity.t option -> Expl.t

end

module Once : sig

  type t

  val add : Expl.t TS.t list -> t -> t
  val update : t -> t * Expl.t TS.t list
  val approximate : Expl.t TS.t list -> Expl.t -> Interval.t -> timepoint -> Polarity.t option -> Expl.t
  val approximate_historically : Expl.t TS.t list -> Expl.t -> Interval.t -> timepoint -> Polarity.t option -> Expl.t

end

module Eventually : sig

  type t

  val add : Expl.t TS.t list -> t -> t
  val update : t -> t * Expl.t TS.t list

end

module Since : sig

  type t

  val add : Expl.t TS.t list -> Expl.t TS.t list -> t -> t
  val update : (int -> int) -> (int -> int) -> t -> t * Expl.t TS.t list
  val approximate : (int -> int) -> (int -> int) -> Expl.t TS.t list -> Expl.t -> Expl.t -> Interval.t -> timepoint -> Polarity.t option -> Expl.t

end

module Until : sig

  type t
    
  val add : Expl.t TS.t list -> Expl.t TS.t list -> t -> t
  val update : (int -> int) -> (int -> int) -> t -> t * Expl.t TS.t list

end

module MFormula : sig

  type binop_info         = (Expl.t TS.t, Expl.t TS.t) Buf2.t
  type nop_info           = Expl.t TS.t Bufn.t
  type prev_info          = Prev.t
  type next_info          = Next.t
  type once_info          = Once.t
  type eventually_info    = Eventually.t
  type historically_info  = Once.t
  type always_info        = Eventually.t
  type since_info         = Since.t
  type until_info         = Until.t

  val empty_binop_info: binop_info
  val empty_nop_info: int -> nop_info

  type core_t =
    | MTT
    | MFF
    | MEqConst      of Term.t * Dom.t
    | MPredicate    of string * Term.t list
    | MAgg          of string * Aggregation.op * Aggregation.op_fun * MyTerm.t * string list * t
    | MTop          of string list * string * Aggregation.op_tfun * MyTerm.t list * string list * t
    | MNeg          of t
    | MAnd          of Side.t * t list * nop_info
    | MOr           of Side.t * t list * nop_info
    | MImp          of Side.t * t * t * binop_info
    | MExists       of string * Dom.tt * bool * t
    | MForall       of string * Dom.tt * bool * t
    | MPrev         of Interval.t * t * prev_info
    | MNext         of Interval.t * t * next_info
    | MENext        of Interval.t * Time.t option * t * Valuation.t
    | MOnce         of Interval.t * t * once_info
    | MEventually   of Interval.t * t * eventually_info
    | MEEventually  of Interval.t * Time.t option * t * Valuation.t
    | MHistorically of Interval.t * t * historically_info
    | MAlways       of Interval.t * t * always_info
    | MEAlways      of Interval.t * Time.t option * t * Valuation.t
    | MSince        of Side.t * Interval.t * t * t * since_info
    | MUntil        of Interval.t * t * t * until_info
    | MEUntil       of Side.t * Interval.t * Time.t option * t * t * Valuation.t
    | MLabel        of string * t
    | MLet          of string * string list * t * t

  and t = { mf: core_t;
            filter: Filter.t;
            events: (string, String.comparator_witness) Set.t option;
            obligations: (int, Int.comparator_witness) Set.t option;
            hash: int;
            lbls: Lbl.t list;
            projs: int array;
            unprojs: int option array; }

  val equal : t -> t -> bool
  
  val make: core_t -> Filter.t -> t
  val set_make: core_t -> Filter.t -> t

  val init: Tformula.t -> t
  val rank: t -> int
  val size : t -> int
    
  val fv: t -> (string, Term.StringVar.comparator_witness) Base.Set.t

  val to_string: ?l:int -> t -> string
  val value_to_string: t -> string
  val op_to_string: t -> string
  val side_to_string: t -> string

end

module IFormula : sig

  type binop_info         = (Expl.t TS.t, Expl.t TS.t) Buf2.t
  type nop_info           = Expl.t TS.t Bufn.t
  type prev_info          = Prev.t
  type next_info          = Next.t
  type once_info          = Once.t
  type eventually_info    = Eventually.t
  type historically_info  = Once.t
  type always_info        = Eventually.t
  type since_info         = Since.t
  type until_info         = Until.t

  val empty_binop_info: binop_info
  val empty_nop_info: int -> nop_info

  type core_t =
    | MTT
    | MFF
    | MEqConst      of ITerm.t * Dom.t
    | MPredicate    of string * ITerm.t list
    | MAgg          of int * Aggregation.op * Aggregation.op_fun * MyTerm.t * int list * t
    | MTop          of int list * string * Aggregation.op_tfun * MyTerm.t list * int list * t
    | MNeg          of t
    | MAnd          of Side.t * t list * nop_info
    | MOr           of Side.t * t list * nop_info
    | MImp          of Side.t * t * t * binop_info
    | MExists       of int * Dom.tt * bool * t
    | MForall       of int * Dom.tt * bool * t
    | MPrev         of Interval.t * t * prev_info
    | MNext         of Interval.t * t * next_info
    | MENext        of Interval.t * Time.t option * t * Valuation.t
    | MOnce         of Interval.t * t * once_info
    | MEventually   of Interval.t * t * eventually_info
    | MEEventually  of Interval.t * Time.t option * t * Valuation.t
    | MHistorically of Interval.t * t * historically_info
    | MAlways       of Interval.t * t * always_info
    | MEAlways      of Interval.t * Time.t option * t * Valuation.t
    | MSince        of Side.t * Interval.t * t * t * since_info
    | MUntil        of Interval.t * t * t * until_info
    | MEUntil       of Side.t * Interval.t * Time.t option * t * t * Valuation.t
    | MLabel        of string * t
    | MLet          of string * int list * t * t

  and t = { mf: core_t;
            filter: Filter.t;
            events: (string, String.comparator_witness) Set.t option;
            obligations: (int, Int.comparator_witness) Set.t option;
            hash: int;
            lbls: Lbl.t list;
            projs: int array;
            unprojs: int option array; }

  val init : MFormula.t -> t * (string * t) list

  val _tt : t
  val _ff : t
  val _tp : t
  val _neg_tp : t

  val map_mf: t -> Filter.t -> ?exquant:bool -> ?new_events:((string, String.comparator_witness) Set.t option) -> (t -> (t -> t) -> core_t) -> t
  val map2_mf: t -> t -> Filter.t -> ?new_events:((string, String.comparator_witness) Set.t option) -> (t -> t -> (t -> t) -> core_t) -> t
  val mapn_mf: t list -> Filter.t -> ?new_events:((string, String.comparator_witness) Set.t option) -> (t list -> (t -> t) -> core_t) -> t

  val equal : t -> t -> bool
  val rank : t -> int
  val size : t -> int
  
  val make: core_t -> Filter.t -> t

  val unproj: t -> Valuation.t -> Valuation.t
  val apply_valuation : ?parent_lbls:Lbl.t list -> Valuation.t -> t -> t

  val to_string: ?l:int -> t -> string
  val value_to_string: t -> string
  val op_to_string: t -> string
  val side_to_string: t -> string

end

module FObligation : sig

  type kind =
    | FFormula of IFormula.t * int * Valuation.t                          (* fun _ -> f *)
    | FInterval of Time.t * Interval.t * IFormula.t * int * Valuation.t   (* fun t -> if mem t i then f else Formula.TT *)
    | FUntil of Time.t * Side.t * Interval.t * IFormula.t * IFormula.t * int * Valuation.t
                                                                          (* fun t -> Until (s, sub2 i (t-t0), f1, f2) *)
    | FAlways of Time.t * Interval.t * IFormula.t * int * Valuation.t     (* fun t -> Always (sub2 i (t-t0), f1) *)
    | FEventually of Time.t * Interval.t * IFormula.t * int * Valuation.t (* fun t -> Eventually (sub2 i (t-t0), f1) *)

  type t = kind * Valuation.t * Polarity.t

  (*val equal: t -> t -> bool*)
  val fold_map: ('a -> IFormula.t -> 'a * IFormula.t) -> 'a -> t -> 'a * t
  val eval: Time.t -> int -> t -> IFormula.t
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

val approximate_neg : Expl.t -> Expl.t
val approximate_and : (int -> int) list -> Expl.t list -> Expl.t
val approximate_or : (int -> int) list -> Expl.t list -> Expl.t
val approximate_imp : (int -> int) -> (int -> int) -> Expl.t -> Expl.t -> Expl.t
val approximate_enext : Lbl.t list -> FObligations.t -> int * ITerm.Valuation.t -> timepoint -> Polarity.t option -> Expl.t
val approximate_eventually : Lbl.t list -> Expl.t -> FObligations.t -> Interval.t -> (int * ITerm.Valuation.t) option -> timepoint -> Polarity.t option -> Expl.t
val approximate_always : Lbl.t list -> Expl.t -> FObligations.t -> Interval.t -> (int * ITerm.Valuation.t) option -> timepoint -> Polarity.t option -> Expl.t
val approximate_until : Lbl.t list -> (int -> int) -> (int -> int) -> Expl.t -> Expl.t -> FObligations.t -> Interval.t -> (int * ITerm.Valuation.t) option -> timepoint -> Polarity.t option -> Expl.t

val update_neg : Expl.t TS.t list -> Expl.t TS.t list
val update_and : (int -> int) list -> Expl.t TS.t list list -> MFormula.nop_info -> Expl.t TS.t list * MFormula.nop_info
val update_or : (int -> int) list -> Expl.t TS.t list list -> MFormula.nop_info -> Expl.t TS.t list * MFormula.nop_info
val update_imp : (int -> int) -> (int -> int) -> Expl.t TS.t list -> Expl.t TS.t list -> MFormula.binop_info -> Expl.t TS.t list * MFormula.binop_info

