module Python : sig

  val load: string -> unit

  val call: string -> Dom.t list -> Dom.tt -> Dom.t
  
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
