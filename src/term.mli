open Base

open MFOTL_lib

module TrivialInfo : Modules.I with type t = unit
module StringVar : Modules.V with type t = string
module NoOp : Modules.O

include module type of Term.Make(StringVar)(Dom)(NoOp)(NoOp)(TrivialInfo)

val init: Sformula.t -> t
