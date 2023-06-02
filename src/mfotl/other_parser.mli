(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
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
           ; mutable db: Db.t }

end

module Sig : sig

  val parse_from_channel: string -> unit

  val parse_from_string: string -> unit

end

module Trace : sig

  val parse_from_channel: in_channel -> Parsebuf.t option -> bool * Parsebuf.t

  val parse_from_string: string -> bool * Parsebuf.t

end
