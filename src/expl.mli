open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm
module Valuation = ITerm.Valuation

module Fdeque = Core.Fdeque
module Part = Pdt.Part

module Pdt : sig

  module I : Pdt.L with type t = int

  include module type of Pdt.Make(I)

  val specialize: Lbl.t array -> ('a list -> 'a) -> ('a list -> 'a) -> Valuation.t -> 'a t -> 'a
  val specialize_partial: Lbl.t array -> Valuation.t -> 'a t -> 'a t
  
  val collect: Lbl.t array -> ('a -> bool) -> ((Dom.t, Dom.comparator_witness) Setc.t list -> (Dom.t, Dom.comparator_witness) Setc.t) -> ((Dom.t, Dom.comparator_witness) Setc.t list -> (Dom.t, Dom.comparator_witness) Setc.t) -> Valuation.t -> int -> 'a t -> (Dom.t, Dom.comparator_witness) Setc.t
  val from_valuation: ?i:int -> Lbl.t list -> Valuation.t -> 'b -> 'b -> 'b t

end

type t = bool Pdt.t

val is_violated: t -> bool
val is_satisfied: t -> bool

val to_string: t -> string

val pdt_of: ?i:int -> int -> string -> Lbl.t list -> (int, Dom.t, 'a) Map.t list -> bool Pdt.t

val table_operator: (Dom.t list list -> Dom.t list list) -> int list -> (int -> int) -> int -> Term.t list -> string list -> Lbl.t array -> Lbl.t array -> t -> t
val aggregate: ((Dom.t, Dom.comparator_witness) Multiset.t -> Dom.t) -> int -> (int -> int) -> int -> Term.t -> string list -> Lbl.t array -> Lbl.t array -> t -> t
