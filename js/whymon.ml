(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Core
open Js_of_ocaml
open Monitor_lib

module Whymon = struct

  let mstate = ref None

  let check_sig js_sig =
    try
      let str_sig = Js_of_ocaml.Js.to_string js_sig in
      if String.is_empty str_sig then Js_of_ocaml__Js.bool false
      else
        (Base.Hashtbl.clear Pred.Sig.table;
         Other_parser.Sig.parse_from_string str_sig;
         Js_of_ocaml__Js.bool true)
    with _ -> Js_of_ocaml__Js.bool false

  let check_formula js_formula =
    try
      let str_f = Js_of_ocaml.Js.to_string js_formula in
      if String.is_empty str_f then Js_of_ocaml__Js.bool false
      else (let _ = Formula_parser.formula Formula_lexer.token (Lexing.from_string str_f) in
            Js_of_ocaml__Js.bool true)
    with _ -> Js_of_ocaml__Js.bool false

  let check_log js_log =
    let check_step last_ts_opt db =
      try
        let (_, pb) = Other_parser.Trace.parse_from_string db in
        if (Option.is_none last_ts_opt) || pb.ts >= (Option.value_exn last_ts_opt) then
          (Some(pb.ts), true)
        else (None, false)
      with _ -> (None, false) in
    let str_log = Js_of_ocaml.Js.to_string js_log in
    if String.is_empty str_log then Js_of_ocaml__Js.bool false
    else (let str_dbs = List.map (List.filter (String.split str_log ~on:'@') ~f:(fun s -> not (String.is_empty s)))
                          ~f:(fun s -> "@" ^ s) in
          List.fold_until str_dbs ~init:(None, true)
            ~f:(fun (last_ts_opt, b) str_db ->
              let (last_ts_opt, b) = check_step last_ts_opt str_db in
              if b then Continue (last_ts_opt, b)
              else Stop(Js_of_ocaml__Js.bool b)) ~finish:(fun (_, b) -> Js_of_ocaml__Js.bool b))

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
         method checkSignature (js_sig: Js.js_string Js.t) = check_sig js_sig
         method checkFormula (js_formula: Js.js_string Js.t) = check_formula js_formula
         method checkLog (js_log: Js.js_string Js.t) = check_log js_log
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
