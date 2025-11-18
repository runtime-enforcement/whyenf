open Base

open MFOTL_lib

module TrivialInfo : Modules.I with type t = unit
module StringVar : Modules.V with type t = string
module NoOp : Modules.O

module Valuation : Valuation.T with type v = StringVar.t and type c = StringVar.comparator_witness

include module type of Term.Make(StringVar)(Dom)(NoOp)(NoOp)(TrivialInfo)

val init: Sformula.t -> t
