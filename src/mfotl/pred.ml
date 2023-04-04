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

exception Invalid_type of string

type const = Int of int | Str of string | Float of float [@@deriving compare, sexp_of]

type term = Var of string | Const of const [@@deriving sexp_of]

module TConst = struct
  type t = TInt | TStr | TFloat [@@deriving compare, sexp_of, hash]
end

module Sig = struct
  type t = { arity: int; tconsts: TConst.t list } [@@deriving compare, sexp_of, hash]
end

let type_of_const c = match c with
  | Int _ -> TConst.TInt
  | Str _ -> TStr
  | Float _ -> TFloat

let tconst_of_string s = match s with
  | "int" -> TConst.TInt
  | "string" -> TStr
  | "float" -> TFloat
  | t -> raise (Invalid_type ("Invalid type " ^ t))

let make_pred name terms =
  (name, List.length terms, terms)

(* let parse_tuple_sig name terms_str = *)
(*   let terms_t = String.split_on_char ',' terms_str *)
(*                 |> List.filter (fun s -> s <> "") *)
(*                 |> List.map (fun s -> String.trim s) in *)
(*   if terms_t = [] then *)
(*     Hashtbl.add preds_sig name (0, []) *)
(*   else *)
(*     Hashtbl.add preds_sig name (List.length terms_t) *)
(*       (List.map(fun s -> *)
(*            let subs = String.split_on_char ':' sub in *)
(*            if List.length subs = 2 || *)
(*          ) terms_str) *)
