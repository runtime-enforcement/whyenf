module Python : sig

  val load: string -> unit

  val call: string -> Dom.t list -> Dom.tt -> Dom.t

  val retrieve_db: string -> Dom.tt list -> Dom.t list list
  
end

type kind =
  | Builtin of (Dom.t list -> Dom.t)
  | External

type t =
  { arity: int;
    arg_tts: (string * Dom.tt) list;
    ret_tt: Dom.tt;
    kind: kind;
  }

val to_string: string -> t -> string

val builtins: (string * t) list

val is_eq: string -> bool

val autocast: (string * Dom.tt list * string) list
