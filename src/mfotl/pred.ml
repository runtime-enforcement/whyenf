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

type const = Int of int | Str of string | Float of float [@@deriving compare, sexp_of, hash]

type term = Var of string | Const of const [@@deriving compare, sexp_of, hash]

module TConst = struct
  type t = TInt | TStr | TFloat [@@deriving compare, sexp_of, hash]
end

module Sig = struct
  (* tconsts: name of variable * tconst *)
  type props = { arity: int; ntconsts: (string * TConst.t) list } [@@deriving compare, sexp_of, hash]

  type t = string * props [@@deriving compare, sexp_of, hash]

  let sig_table : (string, props) Hashtbl.t = Hashtbl.create (module String)

  let tconst_of_string s = match s with
    | "int" -> TConst.TInt
    | "string" -> TStr
    | "float" -> TFloat
    | t -> raise (Invalid_argument (Printf.sprintf "type " ^ t ^ " is not supported"))

  let ntconst v_name st = (v_name, tconst_of_string st)

  let sig_pred p_name ntconsts =
    Hashtbl.add_exn sig_table p_name { arity = List.length ntconsts; ntconsts }

end

let type_of_const c = match c with
  | Int _ -> TConst.TInt
  | Str _ -> TStr
  | Float _ -> TFloat

let make_pred p_name terms =
  (p_name, List.length terms, terms)
