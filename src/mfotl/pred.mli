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

  type const = Int of int | Str of string | Float of float [@@deriving compare, sexp_of, hash]

  type tconst = TInt | TStr | TFloat [@@deriving compare, sexp_of, hash]

  type t = Var of string | Const of const [@@deriving compare, sexp_of, hash]

  val term_equal: t -> t -> bool

  val string_to_const: string -> tconst -> const

  val list_to_string: t list -> string

end

module Sig : sig

  type props = { arity: int; ntconsts: (string * Term.tconst) list } [@@deriving compare, sexp_of, hash]

  type t = string * props [@@deriving compare, sexp_of, hash]

  val sig_table: (string, props) Hashtbl.t

  val ntconst: string -> string -> (string * Term.tconst)

  val sig_pred: string -> (string * Term.tconst) list -> string * props

end

val make_terms: string -> string list -> Term.t list
