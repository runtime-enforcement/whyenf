open Base

module MyTerm = Term

open MFOTL_lib

module IntVar : Modules.V with type t = int

module Valuation : Valuation.T with type v = int

include module type of Term.Make(IntVar)(Dom)(MyTerm.NoOp)(MyTerm.NoOp)(MyTerm.TrivialInfo)

val init : Lbl.t list -> MyTerm.t -> t
val init_multiple : Lbl.t list -> MyTerm.t list -> t list
val to_term : Lbl.t list -> t -> MyTerm.t
val to_terms : Lbl.t list -> t list -> MyTerm.t list
val of_var : Lbl.t list -> string -> int
val of_vars : Lbl.t list -> string list -> int list
val to_var : Lbl.t list -> int -> string
val to_vars : Lbl.t list -> int list -> string list
