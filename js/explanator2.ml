(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl.Util
open Mtl.Expl
open Mtl.Formula
open Mtl.Io
open Mtl.Parser
open Mtl.Lexer
open Mtl.Monitor
open Js_of_ocaml

module Explanator2 = struct

  let validate_measure m =
    match m with
    | "size" -> size_le
    | "wsize" -> high_le
    | _ -> (fun _ _ -> true)

  let get_columns js_formula =
    let formula = (Js_of_ocaml.Js.to_string js_formula) in
    let f = Mtl.Parser.formula Mtl.Lexer.token (Lexing.from_string formula) in
    Js.string (json_table_columns f)

  let monitor_init js_log js_measure js_formula =
    let log = (Js_of_ocaml.Js.to_string js_log) in
    let measure = validate_measure (Js_of_ocaml.Js.to_string js_measure) in
    let formula = (Js_of_ocaml.Js.to_string js_formula) in
    let formula_parsed = Mtl.Parser.formula Mtl.Lexer.token (Lexing.from_string formula) in
    let (obj_opt, s) = monitor_vis None log measure formula_parsed in
    (obj_opt, Js.string(s))

  let monitor_append js_log js_measure js_formula obj_opt =
    let log = (Js_of_ocaml.Js.to_string js_log) in
    let measure = validate_measure (Js_of_ocaml.Js.to_string js_measure) in
    let formula = (Js_of_ocaml.Js.to_string js_formula) in
    let formula_parsed = Mtl.Parser.formula Mtl.Lexer.token (Lexing.from_string formula) in
    let (obj_opt', s) = monitor_vis obj_opt log measure formula_parsed in
    (obj_opt', Js.string(s))

  let (_: unit) =
    Js.export_all
      (object%js
         method getColumns (js_formula: Js.js_string Js.t) = get_columns js_formula
         method monitorInit (js_log: Js.js_string Js.t)
                  (js_measure: Js.js_string Js.t)
                  (js_formula: Js.js_string Js.t) =
           monitor_init js_log js_measure js_formula
         method monitorAppend (js_log: Js.js_string Js.t)
                  (js_measure: Js.js_string Js.t)
                  (js_formula: Js.js_string Js.t)
                  (obj_opt: (mformula * state) option)=
           monitor_append js_log js_measure js_formula obj_opt
       end)


end
