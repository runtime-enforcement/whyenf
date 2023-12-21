(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

module Term : sig

  type t = Var of string | Const of Dom.t [@@deriving compare, sexp_of, hash]

  type comparator_witness

  val unvar: t -> string

  val unconst: t -> Dom.t

  val comparator: (t, comparator_witness) Comparator.t

  val fv_list: t list -> string list

  val equal: t -> t -> bool

  val to_string: t -> string

  val value_to_string: t -> string

  val list_to_string: t list -> string

end

module EnfType : sig

  type t = Cau | Sup | CauSup | Obs [@@deriving compare, sexp_of, hash]

  val neg : t -> t

  val to_int : t -> int

  val to_string : t -> string

  val meet : t -> t -> t

  val join : t -> t -> t

  val leq : t -> t -> bool

  val geq : t -> t -> bool

  val specialize : t -> t -> t option

end

module Sig : sig

  type props = { arity: int; ntconsts: (string * Dom.tt) list; enftype: EnfType.t; rank: int } [@@deriving compare, sexp_of, hash]

  type t = string * props [@@deriving compare, sexp_of, hash]

  val table: (string, props) Hashtbl.t

  val add: string -> (string * Dom.tt) list -> EnfType.t -> int -> unit

  val update_enftype: string -> EnfType.t -> unit

  val vars: string -> string list

  val tconsts: string -> Dom.tt list

  val enftype: string -> EnfType.t

  val rank: string -> int

  val print_table: unit -> unit

end

val check_terms: string -> Term.t list -> Term.t list
