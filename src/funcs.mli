module Dom = MFOTL_lib.Dom

module Python : sig

  val load: string -> unit

  val call: string -> Dom.t list -> Dom.tt -> Dom.t
  val tcall: string -> Dom.t list list -> Dom.tt list -> Dom.t list list

  val retrieve_db: string -> Dom.tt list -> Dom.t list list
  
end

type kind =
  | Builtin of (Dom.t list -> Dom.t)
  | Table
  | External

type t =
  { arity: int;
    arg_ttts: (string * Ctxt.ttt) list;
    ret_ttts: Ctxt.ttt list;
    kind: kind;
    strict: bool;
  }

val to_string: string -> t -> string

val builtins: (string * t) list

val is_eq: string -> bool

