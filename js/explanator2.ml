(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Lib.Util
open Lib.Expl
open Lib.Mtl
open Lib.Io
open Lib.Mtl_parser
open Lib.Mtl_lexer
open Lib.Monitor

module Explanator2 = struct

  let validate_check c =
    match c with
    | "true" -> true
    | "false" -> false
    | _ -> false

  let validate_measure m =
    match m with
    | "size" -> size_le
    | "high" -> high_le
    | "pred" -> predicates_le
    | _ -> (fun _ _ -> true)

  let main_monitor log check measure formula =
    let c = validate_check check in
    let le = validate_measure measure in
    let f = Lib.Mtl_parser.formula Lib.Mtl_lexer.token (Lexing.from_string formula) in
    monitor2 log c le f

end
