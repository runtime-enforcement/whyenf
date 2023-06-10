(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Js_of_ocaml
open Mfotl

module Explanator2 = struct

  let get_columns js_formula =
    let str_f = Js_of_ocaml.Js.to_string js_formula in
    let f = Formula_parser.formula Formula_lexer.token (Lexing.from_string str_f) in
    Js.string (Out.Json.table_columns f)

  let monitor_init js_log js_sig js_formula =
    let str_log = Js_of_ocaml.Js.to_string js_log in
    let str_sig = Js_of_ocaml.Js.to_string js_sig in
    Base.Hashtbl.clear Pred.Sig.table;
    Other_parser.Sig.parse_from_string str_sig;
    let str_f = Js_of_ocaml.Js.to_string js_formula in
    let f = Formula_parser.formula Formula_lexer.token (Lexing.from_string str_f) in
    let (obj_opt, json) = Monitor.exec_vis None f str_log in
    (obj_opt, Js.string(json))

  let monitor_append js_log js_formula obj_opt =
    let str_log = Js_of_ocaml.Js.to_string js_log in
    let str_f = Js_of_ocaml.Js.to_string js_formula in
    let f = Formula_parser.formula Formula_lexer.token (Lexing.from_string str_f) in
    let (obj_opt', json) = Monitor.exec_vis obj_opt f str_log in
    (obj_opt', Js.string(json))

  let (_: unit) =
    Js.export_all
      (object%js
         method getColumns (js_formula: Js.js_string Js.t) = get_columns js_formula
         method monitorInit (js_log: Js.js_string Js.t)
                  (js_sig: Js.js_string Js.t)
                  (js_formula: Js.js_string Js.t) =
           monitor_init js_log js_sig js_formula
         method monitorAppend (js_log: Js.js_string Js.t)
                  (js_formula: Js.js_string Js.t)
                  (obj_opt: Monitor.MState.t option)=
           monitor_append js_log js_formula obj_opt
       end)

end
