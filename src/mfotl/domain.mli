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

type tt = TInt | TStr | TFloat [@@deriving compare, sexp_of, hash]

type t = Int of int | Str of string | Float of float [@@deriving compare, sexp_of, hash]

type comparator_witness

val comparator : (t, comparator_witness) Comparator.t

val equal: t -> t -> bool

val tt_of_string: string -> tt

val string_to_t: string -> tt -> t

val to_string: t -> string

val list_to_string: t list -> string
