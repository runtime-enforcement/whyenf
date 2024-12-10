module type EnforcerT = sig
  
  val exec: Formula.t -> in_channel -> MFOTL_lib.Time.Span.s -> unit

end

module Make (_: Expl.ExplT) : EnforcerT

