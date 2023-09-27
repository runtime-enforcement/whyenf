(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Js_of_ocaml
open Monitor_lib

module Whymon = struct

  let mstate = ref None

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
    if (Formula.check_bindings f) then
      (let (ms, json) = Monitor.exec_vis None f str_log in
       mstate := Some(ms); Js.string(json))
    else raise (Invalid_argument "formula is invalid: check its quantifier bindings")

  let monitor_append js_log js_formula =
    let str_log = Js_of_ocaml.Js.to_string js_log in
    let str_f = Js_of_ocaml.Js.to_string js_formula in
    let f = Formula_parser.formula Formula_lexer.token (Lexing.from_string str_f) in
    let (ms, json) = Monitor.exec_vis !mstate f str_log in
    mstate := Some(ms); Js.string(json)

  let (_: unit) =
    Js.export_all
      (object%js
         method getColumns (js_formula: Js.js_string Js.t) = get_columns js_formula
         method monitorInit (js_log: Js.js_string Js.t)
                  (js_sig: Js.js_string Js.t)
                  (js_formula: Js.js_string Js.t) =
           monitor_init js_log js_sig js_formula
         method monitorAppend (js_log: Js.js_string Js.t)
                  (js_formula: Js.js_string Js.t) =
           monitor_append js_log js_formula
       end)

end
