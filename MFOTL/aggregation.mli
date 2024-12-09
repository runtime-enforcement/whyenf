open Base
(*open Sformula*)

type op = ASum | AAvg | AMed | ACnt | AMin | AMax | AStd | AAssign [@@deriving compare, sexp_of, hash, equal]

type op_fun = (Dom.t, Dom.comparator_witness) Multiset.t -> Dom.t
type op_tfun = Dom.t list list -> Dom.t list list

val op_to_string : op -> string

val ret_tt : op -> Dom.tt -> Dom.tt option
val ret_tt_exn : op -> Dom.tt -> Dom.tt

val eval : op -> Dom.tt -> (Dom.t, Dom.comparator_witness) Multiset.t -> Dom.t

(*val init : Aop.t -> op*)


