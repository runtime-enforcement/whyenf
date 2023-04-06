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

type const = Int of int | Str of string | Float of float [@@deriving compare, sexp_of, hash]

type term = Var of string | Const of const [@@deriving compare, sexp_of, hash]

module TConst : sig
  type t = TInt | TStr | TFloat [@@deriving compare, sexp_of, hash]
end

module Sig : sig
  (* tconsts: name of variable * tconst *)
  type props = { arity: int; ntconsts: (string * TConst.t) list } [@@deriving compare, sexp_of, hash]

  type t = string * props [@@deriving compare, sexp_of, hash]

  val sig_table: (string, props) Hashtbl.t

  val ntconst: string -> string -> (string * TConst.t)

  val sig_pred: string -> (string * TConst.t) list -> unit

end
