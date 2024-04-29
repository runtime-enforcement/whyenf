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

  type t = Var of string | Const of Dom.t | App of string * t list [@@deriving compare, sexp_of, hash]

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

val tp_event_name: string
val tick_event_name: string

module Sig : sig

  type pred = { arity: int;
                arg_tts: (string * Dom.tt) list;
                enftype: EnfType.t;
                rank: int } [@@deriving compare, sexp_of, hash]

  type func = { arity: int;
                arg_tts: (string * Dom.tt) list;
                ret_tt: Dom.tt } [@@deriving compare, sexp_of, hash]

  type ty = Pred of pred | Func of func [@@deriving compare, sexp_of, hash]
                                  
  type t = string * ty [@@deriving compare, sexp_of, hash]

  val table: (string, ty) Hashtbl.t

  val add_pred: string -> (string * Dom.tt) list -> EnfType.t -> int -> unit

  val add_func: string -> (string * Dom.tt) list -> Dom.tt -> unit

  val update_enftype: string -> EnfType.t -> unit

  val vars_of_pred: string -> string list

  val arg_tts_of_pred: string -> Dom.tt list

  val enftype_of_pred: string -> EnfType.t

  val rank_of_pred: string -> int

  val print_table: unit -> unit

  val arity: ty -> int
  
  val arg_tts: ty -> (string * Dom.tt) list

end

val check_const: (string, Dom.tt, 'a) Map.t -> Dom.t -> Dom.tt -> (string, Dom.tt, 'a) Map.t
val check_var: (string, Dom.tt, 'a) Map.t -> string -> Dom.tt -> (string, Dom.tt, 'a) Map.t
val check_app: (string, Dom.tt, 'a) Map.t -> string -> Dom.tt -> (string, Dom.tt, 'a) Map.t

val check_terms: (string, Dom.tt, 'a) Map.t -> string -> Term.t list ->  (string, Dom.tt, 'a) Map.t
