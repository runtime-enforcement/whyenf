open Base

type t = LVar of string | LEx of string | LAll of string | LClos of string * Term.t list * ((String.t, String.comparator_witness) Set.t) [@@deriving equal, compare, sexp_of]

(*module TLbl : sig

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

  type tt = TLbl.t*)

(*val t_of_tt: tt -> t*)
val var: string -> t
val ex: string -> t
val all: string -> t
val clos: string -> Term.t list -> ((String.t, String.comparator_witness) Set.t) -> t

val exquant: t -> t

val is_var: t -> bool

val term: t -> Term.t
val of_term: Term.t -> t
val to_string: t -> string
val to_string_list: t list -> string

val fv: t -> (string, String.comparator_witness) Set.t
val quantify: forall:bool -> string -> t -> t
val quantify_list: forall:bool -> string -> t list -> t list
val unquantify_list: string -> t list -> t list

val eval: Etc.valuation -> t -> Term.t
(*val matches: tt -> t -> bool*)

type comparator_witness
val comparator: (t, comparator_witness) Comparator.t

val order : t list -> t list -> t -> string list -> t list
