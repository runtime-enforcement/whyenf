open Base
open Interval
open Time

module Z : S with type v = int

module MakeZinterval (S : S) : sig

  type v = Z.v

  module UI : module type of MakeUI(Z)
  module NUI : module type of MakeNUI(Z)
  module BI : module type of MakeBI(Z)
  module UUI : module type of MakeUUI(Z)

  module SInterval : module type of MakeInterval(S)
  
  type t = ZB of BI.t | ZUL of NUI.t | ZUR of UI.t | ZU of UUI.t [@@deriving equal]

  val equal: t -> t -> bool

  val lclosed_UI: v -> t
  val lopen_UI: v -> t
  val rclosed_UI: v -> t
  val ropen_UI: v -> t

  val lopen_ropen_BI: v -> v -> t
  val lopen_rclosed_BI: v -> v -> t
  val lclosed_ropen_BI: v -> v -> t
  val lclosed_rclosed_BI: v -> v -> t  
  val singleton: v -> t

  val is_zero : t -> bool
  val has_zero : t -> bool
  val is_full : t -> bool

  val full : t

  val is_bounded : t -> bool
  val is_nonpositive : t -> bool
  
  val left : t -> v option
  val right : t -> v option

  val lub : t -> t -> t
  val sum : t -> t -> t
  val inv : t -> t
  val mem : v -> t -> bool

  val to_zero : t -> t

  val of_interval: SInterval.t -> t

  val to_string: t -> string
  val to_latex: t -> string

end

include module type of MakeZinterval(Time.Span.S) with type v = int
