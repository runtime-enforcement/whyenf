open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

module type L = sig

  type t [@@deriving equal, compare]

  val minimum : t list -> t
    
  val to_string : t -> string

end

module Part : sig

  type sub = (Dom.t, Dom.comparator_witness) Setc.t

  type 'a t = (sub * 'a) list

  val trivial: 'a -> 'a t
  val get_trivial: 'a t -> 'a option
  val length: 'a t -> int
  val map: 'a t -> ('a -> 'c) -> 'c t
  val map2: 'a t -> (sub * 'a -> 'c) -> 'c list
  val fold_left: 'a t -> 'b -> ('b -> 'a -> 'b) -> 'b
  val filter: 'a t -> ('a -> bool) -> 'a t
  val exists: 'a t -> ('a -> bool) -> bool
  val for_all: 'a t -> ('a -> bool) -> bool
  val values: 'a t -> 'a list
  val find: 'a t -> Dom.t -> 'a
  val find2: 'a t -> (sub -> bool) -> sub * 'a
  val tabulate: (Dom.t, Dom.comparator_witness) Set.t -> (Dom.t -> 'a) -> 'a -> 'a t

  val dedup: ('a -> 'a -> bool) -> 'a t -> 'a t
  val map_dedup: ('a -> 'a -> bool) -> ('d -> 'a) -> 'd t -> 'a t
  val map2_dedup: ('a -> 'a -> bool) -> (sub * 'a -> sub * 'a) -> 'a t -> 'a t
  val tabulate_dedup: ('a -> 'a -> bool) -> (Dom.t, Dom.comparator_witness) Set.t -> (Dom.t -> 'a) -> 'a -> 'a t

end

module Make (Lbl : L) : sig

  type 'a t = Leaf of 'a | Node of Lbl.t * ('a t) Part.t

  val split_prod: ('a * 'b) t -> 'a t * 'b t
  val split_list: 'a list t -> 'a t list
  val to_string: ('a -> string) -> string -> 'a t -> string
  val to_light_string: ('a -> string) -> string -> 'a t -> string

  val eq: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val reduce: ('a -> 'a -> bool) -> 'a t -> 'a t
  val apply1_reduce: ('a -> 'a -> bool) -> ('b -> 'a) -> (Lbl.t -> Lbl.t) -> 'b t -> 'a t
  val apply2_reduce: ('a -> 'a -> bool) -> ('b -> 'c -> 'a) -> (Lbl.t -> Lbl.t) -> (Lbl.t -> Lbl.t) -> 'b t -> 'c t -> 'a t
  val apply3_reduce: ('a -> 'a -> bool) -> ('b -> 'c -> 'd -> 'a) -> (Lbl.t -> Lbl.t) -> (Lbl.t -> Lbl.t) -> (Lbl.t -> Lbl.t) -> 'b t -> 'c t -> 'd t -> 'a t
  val applyN_reduce: ('a -> 'a -> bool) -> ('b list -> 'a) -> (((Lbl.t -> Lbl.t) * 'b t) list) -> 'a t
  val split_prod_reduce: ('a -> 'a -> bool) -> ('a * 'a) t -> 'a t * 'a t
  val split_list_reduce: ('a -> 'a -> bool) -> 'a list t -> 'a t list

end
