open Base

module TrivialInfo : MFOTL_Base.I with type t = unit
module StringVar : MFOTL_Base.V with type t = string
module NoOp : MFOTL_Base.O

include module type of MFOTL_Term.Make(StringVar)(Dom)(NoOp)(NoOp)(TrivialInfo)

val init: Sformula.t -> t
