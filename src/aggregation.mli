open Base
open Pred

type op = ASum | AAvg | AMed | ACnt | AMin | AMax | AAssign [@@deriving compare, sexp_of, hash, equal]

type op_fun = (Dom.t, int, Dom.comparator_witness) Map.t -> Dom.t

val order_lbls : Lbl.t list -> Lbl.t list -> Lbl.t -> string list -> Lbl.t list

val op_to_string : op -> string

val ret_tt : op -> Dom.tt -> Dom.tt option
val ret_tt_exn : op -> Dom.tt -> Dom.tt

val eval : op -> Dom.tt -> (Dom.t, int, Dom.comparator_witness) Map.t -> Dom.t
