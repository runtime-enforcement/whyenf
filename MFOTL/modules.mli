open Base

module type I = sig

  type t [@@deriving compare, sexp_of, hash, equal]

  val to_string : int -> string -> t -> string
  val dummy : t

end

module type V = sig

  type t [@@deriving compare, sexp_of, hash, equal]

  type comparator_witness
  val comparator : (t, comparator_witness) Comparator.t

  val to_string : t -> string
  val ident : t -> string
  val of_ident : string -> t

  val replace : t -> t -> t

end

module type D = sig

  type t [@@deriving compare, sexp_of, hash, equal]
  type tt [@@deriving compare, sexp_of, hash, equal]

  val to_string : t -> string
  val tt_to_string : tt -> string
  val bool_tt : t
  val tt_of_domain : t -> tt
  
end

module type O = sig

  type t [@@deriving compare, sexp_of, hash, equal]

  val to_string : t -> string
  val prio : t -> int

end

module type S = sig

  type term
  type pred_kind = Trace | Predicate | External | Builtin | Let [@@deriving compare, sexp_of, hash, equal]
  
  val rank_of_pred: string -> int
  val mem: string -> bool
  val enftype_of_pred: string -> Enftype.t
  val kind_of_pred: string -> pred_kind
  val pred_enftype_map: unit -> (string, Enftype.t * int list, String.comparator_witness) Map.t
  val strict_of_func: string -> bool

  val add_letpred_empty: string -> unit
  val update_enftype: string -> Enftype.t -> unit

end
