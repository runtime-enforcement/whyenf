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

type tt = TInt | TStr | TFloat [@@deriving compare, sexp_of, hash]

type t = Int of int | Str of string | Float of float [@@deriving compare, sexp_of, hash]

type ctxt = (string, tt, String.comparator_witness) Map.t

type comparator_witness

val comparator : (t, comparator_witness) Comparator.t

val equal: t -> t -> bool

val tt_equal: tt -> tt -> bool

val tt_of_string: string -> tt

val tt_of_domain: t -> tt

val tt_to_string: tt -> string

val tt_default: tt -> t

val string_to_t: string -> tt -> t

val to_string: t -> string

val list_to_string: t list -> string

val to_int_exn: t -> int
val to_float_exn: t -> float
val to_string_exn: t -> string
