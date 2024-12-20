open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

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
  val map_dedup: ('a -> 'a -> bool) -> ('d -> 'a) -> 'd t -> 'a t
  val map2_dedup: ('a -> 'a -> bool) -> (sub * 'a -> sub * 'a) -> 'a t -> 'a t
  val tabulate_dedup: ('a -> 'a -> bool) -> (Dom.t, Dom.comparator_witness) Set.t -> (Dom.t -> 'a) -> 'a -> 'a t

end

module Pdt : sig

  type 'a t = Leaf of 'a | Node of Lbl.t * ('a t) Part.t

  val apply1: Lbl.t list -> ('a -> 'b) -> 'a t -> 'b t
  val apply2: Lbl.t list -> ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val apply3: Lbl.t list -> ('a -> 'b -> 'c -> 'd) -> 'a t -> 'b t -> 'c t -> 'd t
  val applyN: Lbl.t list -> ('a list -> 'b) -> 'a t list -> 'b t

  val split_prod: ('a * 'b) t -> 'a t * 'b t
  val split_list: 'a list t -> 'a t list
  val to_string: ('a -> string) -> string -> 'a t -> string

  val eq: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val reduce: ('a -> 'a -> bool) -> 'a t -> 'a t
  val apply1_reduce: ('a -> 'a -> bool) -> Lbl.t list -> ('b -> 'a) -> 'b t -> 'a t
  val apply2_reduce: ('a -> 'a -> bool) -> Lbl.t list -> ('b -> 'c -> 'a) -> 'b t -> 'c t -> 'a t
  val apply3_reduce: ('a -> 'a -> bool) -> Lbl.t list -> ('b -> 'c -> 'd -> 'a) -> 'b t -> 'c t -> 'd t -> 'a t
  val applyN_reduce: ('a -> 'a -> bool) -> Lbl.t list -> ('b list -> 'a) -> 'b t list -> 'a t
  val split_prod_reduce: ('a -> 'a -> bool) -> ('a * 'a) t -> 'a t * 'a t
  val split_list_reduce: ('a -> 'a -> bool) -> 'a list t -> 'a t list
  val quantify: forall:bool -> string -> 'a t -> 'a t

  val specialize: ('a list -> 'a) -> ('a list -> 'a) -> Etc.valuation -> 'a t -> 'a
  val specialize_partial: Etc.valuation -> 'a t -> 'a t
  
  val collect: ('a -> bool) -> ((Dom.t, Dom.comparator_witness) Setc.t list -> (Dom.t, Dom.comparator_witness) Setc.t) -> ((Dom.t, Dom.comparator_witness) Setc.t list -> (Dom.t, Dom.comparator_witness) Setc.t) -> Etc.valuation -> string -> 'a t -> (Dom.t, Dom.comparator_witness) Setc.t
  val from_valuation: Lbl.t list -> Etc.valuation -> 'b -> 'b -> 'b t

  val exquant: 'a t -> 'a t

end

type t = bool Pdt.t

val is_violated: t -> bool
val is_satisfied: t -> bool

val to_string: t -> string
val to_light_string: t -> string

val pdt_of: int -> string -> Term.t list -> Lbl.t list -> (Lbl.t, Dom.t, 'a) Map.t list -> bool Pdt.t

val table_operator: (Dom.t list list -> Dom.t list list) -> string list -> int -> Term.t list -> string list -> Lbl.t list -> Lbl.t list -> t -> t
val aggregate: ((Dom.t, Dom.comparator_witness) Multiset.t -> Dom.t) -> string -> int -> Term.t -> string list -> Lbl.t list -> Lbl.t list -> t -> t

