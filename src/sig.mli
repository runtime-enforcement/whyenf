open Base

val tilde_tp_event_name: string
val tp_event_name: string
val ts_event_name: string
val tick_event_name: string

type pred_kind = Trace | Predicate | External | Builtin | Let [@@deriving compare, sexp_of, hash, equal]

type pred = { arity: int;
              arg_ttts: (string * Ctxt.ttt) list;
              enftype: Enftype.t;
              rank: int;
              kind: pred_kind } [@@deriving compare, sexp_of, hash]

type ty = Pred of pred | Func of Funcs.t (*[@@deriving compare, sexp_of, hash]*)

type elt = string * ty (* [@@deriving compare, sexp_of, hash]*)

type t = (string, ty) Hashtbl.t

val table: t

val add_letpred: string -> (string * Ctxt.ttt) list -> unit
val add_pred: string -> (string * Dom.tt) list -> Enftype.t -> int -> pred_kind -> unit

val add_func: string -> (string * Dom.tt) list -> Dom.tt -> Funcs.kind -> bool -> unit

val update_enftype: string -> Enftype.t -> unit

val vars_of_pred: string -> string list
val arg_ttts_of_pred: string -> Ctxt.ttt list
val enftype_of_pred: string -> Enftype.t
val rank_of_pred: string -> int
val kind_of_pred: string -> pred_kind

val print_table: unit -> unit

val arity: ty -> int

val arg_ttts: ty -> (string * Ctxt.ttt) list

val eval: Etc.valuation -> Term.t -> Term.t
val set_eval: Setc.valuation -> Term.t -> (Term.t, Term.comparator_witness) Setc.t

val tt_of_term_exn: Ctxt.t -> Term.t -> Dom.tt

val is_strict: Term.t list -> bool

val check_const: Ctxt.t -> Dom.t -> Ctxt.ttt -> Ctxt.t * Ctxt.ttt
val check_var:   Ctxt.t -> string -> Ctxt.ttt -> Ctxt.t * Ctxt.ttt
val check_app:   Ctxt.t -> string -> Term.t list -> Ctxt.ttt -> Ctxt.t * Ctxt.ttt
val check_term:  Ctxt.t -> Ctxt.ttt -> Term.t -> Ctxt.t * Ctxt.ttt
val check_terms: Ctxt.t -> string -> Term.t list -> Ctxt.t * Ctxt.ttt list
