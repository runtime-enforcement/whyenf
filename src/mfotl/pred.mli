(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

module Term : sig

  type t = Var of string | Const of Domain.t [@@deriving compare, sexp_of, hash]

  val equal: t -> t -> bool

  val list_to_string: t list -> string

end

module Sig : sig

  type props = { arity: int; ntconsts: (string * Domain.tt) list } [@@deriving compare, sexp_of, hash]

  type t = string * props [@@deriving compare, sexp_of, hash]

  val table: (string, props) Hashtbl.t

  val n_tt: string -> string -> (string * Domain.tt)

  val add: string -> (string * Domain.tt) list -> unit

end

val make_terms: string -> string list -> Term.t list
