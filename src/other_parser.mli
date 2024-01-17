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

module Parsebuf : sig

  type t = { lexbuf: Lexing.lexbuf
           ; mutable token: Other_lexer.token
           ; mutable pred_sig: Pred.Sig.t option
           ; mutable ts: int
           ; mutable db: Db.t
           ; mutable tp_done: int
           ; mutable ev_done: int }

end

module Sig : sig

  val parse_from_channel: string -> unit

  val parse_from_string: string -> unit

end

module Trace : sig

  val parse_from_channel: Stdio.In_channel.t -> Parsebuf.t option -> (bool * Parsebuf.t) option

  val parse_from_string: string -> (bool * Parsebuf.t) option

end
