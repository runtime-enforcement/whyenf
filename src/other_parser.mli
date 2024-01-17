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

module Stats : sig

  type t = { mutable ev_done: int
           ; mutable tp_done: int
           ; mutable ev_cau: int
           ; mutable ev_sup: int
           ; mutable tp_ins: int
           }

  val add_cau : int -> ?ins:bool -> t -> unit
  val add_sup : int -> t -> unit

end

module Parsebuf : sig

  type t = { lexbuf: Lexing.lexbuf
           ; mutable token: Other_lexer.token
           ; mutable pred_sig: Pred.Sig.t option
           ; mutable ts: int
           ; mutable db: Db.t
           ; stats: Stats.t
           }

end

module Sig : sig

  val parse_from_channel: string -> unit

  val parse_from_string: string -> unit

end

module Trace : sig

  val parse_from_channel: Stdio.In_channel.t -> Parsebuf.t option -> (bool * Parsebuf.t) option

  val parse_from_string: string -> (bool * Parsebuf.t) option

end
