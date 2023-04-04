(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

type const = Int of int | Str of string | Float of float [@@deriving sexp_of]

type term = Var of string | Const of const [@@deriving sexp_of]

module TConst : sig
  type t = TInt | TStr | TFloat [@@deriving sexp_of]
end

module Sig : sig
  type t = { arity: int; tconsts: TConst.t list } [@@deriving sexp_of]
end
