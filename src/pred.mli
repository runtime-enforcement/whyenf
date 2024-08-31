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

  val var: string -> t
  val const: Dom.t -> t
  val app: string -> t list -> t

  val unvar: t -> string

  val unconst: t -> Dom.t

  val comparator: (t, comparator_witness) Comparator.t

  val fv_list: t list -> string list

  val equal: t -> t -> bool

  val to_string: t -> string

  val value_to_string: t -> string

  val list_to_string: t list -> string

  val filter_vars: t list -> string list

  val reorder: t list -> string list -> t list

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

val tilde_tp_event_name: string
val tp_event_name: string
val ts_event_name: string
val tick_event_name: string

module Sig : sig

  type pred_kind = Trace | Predicate | External | Builtin | Let [@@deriving compare, sexp_of, hash, equal]

  type pred = { arity: int;
                arg_tts: (string * Dom.tt) list;
                enftype: EnfType.t;
                rank: int;
                kind: pred_kind } [@@deriving compare, sexp_of, hash]

  type ty = Pred of pred | Func of Funcs.t (*[@@deriving compare, sexp_of, hash]*)

  type elt = string * ty (* [@@deriving compare, sexp_of, hash]*)

  type t = (string, ty) Hashtbl.t

  val table: t

  val add_letpred: string -> (string * Dom.tt) list -> unit
  val add_pred: string -> (string * Dom.tt) list -> EnfType.t -> int -> pred_kind -> unit

  val add_func: string -> (string * Dom.tt) list -> Dom.tt -> Funcs.kind -> unit

  val update_enftype: string -> EnfType.t -> unit

  val vars_of_pred: string -> string list
  val arg_tts_of_pred: string -> Dom.tt list
  val enftype_of_pred: string -> EnfType.t
  val rank_of_pred: string -> int
  val kind_of_pred: string -> pred_kind

  val print_table: unit -> unit

  val arity: ty -> int

  val arg_tts: ty -> (string * Dom.tt) list

  val eval: Etc.valuation -> Term.t -> Term.t
  val set_eval: Setc.valuation -> Term.t -> (Term.t, Term.comparator_witness) Setc.t

  val var_tt_of_term: string -> Dom.tt -> Term.t -> Dom.tt option
  val var_tt_of_terms: string -> Dom.tt list -> Term.t list -> Dom.tt option

  val var_tt_of_term_exn: (string, Dom.tt, String.comparator_witness) Map.t -> Term.t -> Dom.tt

end

module Lbl : sig
  
  type t = LVar of string | LClos of string * (Term.t list) * Etc.valuation [@@deriving equal, compare, sexp_of]

  module TLbl : sig

    type t = TLVar of string | TLClos of string * (Term.t list) * ((String.t, String.comparator_witness) Set.t) [@@deriving equal, compare, sexp_of]
    
    val var: string -> t
    val is_var: t -> bool
    val of_term: Term.t -> t

    val fv: t -> (string, String.comparator_witness) Set.t
    val quantify: string -> t -> t option

    type comparator_witness
    val comparator: (t, comparator_witness) Comparator.t

    val to_string: t -> string

  end

  type tt = TLbl.t
  
  val t_of_tt: tt -> t
  val term: t -> Term.t
  val of_term: Term.t -> t
  val to_string: t -> string
  val eval: Etc.valuation -> t -> Term.t
  val matches: tt -> t -> bool

  type comparator_witness
  val comparator: (t, comparator_witness) Comparator.t

end


val check_const: (string, Dom.tt, 'a) Map.t -> Dom.t -> Dom.tt -> (string, Dom.tt, 'a) Map.t
val check_var: (string, Dom.tt, 'a) Map.t -> string -> Dom.tt -> (string, Dom.tt, 'a) Map.t
val check_app: (string, Dom.tt, 'a) Map.t -> string -> Dom.tt -> (string, Dom.tt, 'a) Map.t

val check_term: (string, Dom.tt, 'a) Map.t -> Dom.tt -> Term.t -> (string, Dom.tt, 'a) Map.t
val check_terms: (string, Dom.tt, 'a) Map.t -> string -> Term.t list ->  (string, Dom.tt, 'a) Map.t
