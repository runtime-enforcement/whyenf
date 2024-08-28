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

module Side : sig

  type t = N | L | R | LR [@@deriving compare, sexp_of, hash]

  val equal: t -> t -> bool

  val to_string: t -> string
  val to_string2: t * t -> string
  val of_string: string -> t

end

type t =
  | TT
  | FF
  | EqConst of Term.t * Dom.t
  | Predicate of string * Term.t list
  | Let of string * string list * t * t
  | Agg of string * Aggregation.op * Term.t * string list * t
  | Neg of t
  | And of Side.t * t * t
  | Or of Side.t * t * t
  | Imp of Side.t * t * t
  | Iff of Side.t * Side.t * t * t
  | Exists of string * t
  | Forall of string * t
  | Prev of Interval.t * t
  | Next of Interval.t * t
  | Once of Interval.t * t
  | Eventually of Interval.t * t
  | Historically of Interval.t * t
  | Always of Interval.t * t
  | Since of Side.t * Interval.t * t * t
  | Until of Side.t * Interval.t * t * t [@@deriving compare, sexp_of, hash]

val tt: t
val ff: t
val eqconst: Term.t -> Dom.t -> t
val agg: string -> Aggregation.op -> Term.t -> string list -> t -> t
val predicate: string -> Term.t list -> t
val flet: string -> string list -> t -> t -> t
val neg: t -> t
val conj: Side.t -> t -> t -> t
val disj: Side.t -> t -> t -> t
val imp: Side.t -> t -> t -> t
val iff: Side.t -> Side.t -> t -> t -> t
val exists: string -> t -> t
val forall: string -> t -> t
val prev: Interval.t -> t -> t
val next: Interval.t -> t -> t
val once: Interval.t -> t -> t
val eventually: Interval.t -> t -> t
val historically: Interval.t -> t -> t
val always: Interval.t -> t -> t
val since: Side.t -> Interval.t -> t -> t -> t
val until: Side.t -> Interval.t -> t -> t -> t
val trigger: Side.t -> Interval.t -> t -> t -> t
val release: Side.t -> Interval.t -> t -> t -> t

val fv: t -> (String.t, Base.String.comparator_witness) Base.Set.t
val list_fv: t -> String.t list
val lbls: string list -> t -> Pred.Lbl.tt list
val check_bindings: t -> bool

val equal: t -> t -> bool

val hp: t -> int
val hf: t -> int
val height: t -> int

val subfs_bfs: t list -> t list
val subfs_dfs: t -> t list
val subfs_scope: t -> int -> (int * (int list * int list)) list
val preds: t -> t list
val pred_names: t -> (string, Base.String.comparator_witness) Base.Set.t

val op_to_string: t -> string
val to_string: t -> string
val to_json: t -> string
val to_latex: t -> string

(*val check_types: t -> unit*)
val is_past_guarded: string -> ?vars:((string, Base.String.comparator_witness) Base.Set.t) option -> bool -> t -> bool
val check_agg: (string, Dom.tt, Base.String.comparator_witness) Base.Map.t -> string -> Aggregation.op -> Term.t -> string list -> t -> (string, Dom.tt, Base.String.comparator_witness) Base.Map.t
