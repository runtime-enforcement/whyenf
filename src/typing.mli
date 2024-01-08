open Formula

val is_past_guarded : string -> bool -> t -> bool
val do_type : t -> Tformula.t
val is_transparent: Tformula.t -> bool
