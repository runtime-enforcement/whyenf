open Base

open MFOTL_lib

type ('a, 'b) t = Finite of ('a, 'b) Set.t | Complement of ('a, 'b) Set.t

val length: ('a, 'b) t -> int
val empty: ('a, 'b) Comparator.Module.t -> ('a, 'b) t
val univ: ('a, 'b) Comparator.Module.t -> ('a, 'b) t
val equal: ('a, 'b) t -> ('a, 'b) t -> bool
val add: ('a, 'b) t -> 'a -> ('a, 'b) t
val singleton: ('a, 'b) Comparator.Module.t -> 'a -> ('a, 'b) t
val is_empty: ('a, 'b) t -> bool
val is_univ: ('a, 'b) t -> bool
val mem: ('a, 'b) t -> 'a -> bool
val comp: ('a, 'b) t -> ('a, 'b) t
val inter: ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
val union: ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
val inter_list: ('a, 'b) Comparator.Module.t -> ('a, 'b) t list -> ('a, 'b) t
val union_list: ('a, 'b) Comparator.Module.t -> ('a, 'b) t list -> ('a, 'b) t
val diff: ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
val some_elt: Dom.tt -> (Dom.t, 'a) t -> Dom.t
val is_finite: ('a, 'b) t -> bool

val to_list: ('a, 'b) t -> 'a list
val to_json: (Dom.t, 'a) t -> string
val to_string: (Dom.t, 'a) t -> string
val to_latex: (Dom.t, 'a) t -> string

type valuation = (string, (Dom.t, Dom.comparator_witness) t, String.comparator_witness) Map.t
val empty_valuation: valuation
