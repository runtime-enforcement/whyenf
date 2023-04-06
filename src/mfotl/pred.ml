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

let const_equal c1 c2 = match c1, c2 with
  | Int i1, Int i2 -> Int.equal i1 i2
  | Str s1, Str s2 -> String.equal s1 s2
  | Float f1, Float f2 -> Float.equal f1 f2
  | _ -> false

let term_equal t1 t2 = match t1, t2 with
  | Var x1, Var x2 -> String.equal x1 x2
  | Const c1, Const c2 -> const_equal c1 c2
  | _ -> false

module TConst = struct
  type t = TInt | TStr | TFloat [@@deriving compare, sexp_of, hash]
end

let tconst_of_string = function
  | "int" -> TConst.TInt
  | "string" -> TStr
  | "float" -> TFloat
  | t -> raise (Invalid_argument (Printf.sprintf "type %s is not supported" t))

let t_of_const = function
  | Int _ -> TConst.TInt
  | Str _ -> TStr
  | Float _ -> TFloat

let string_to_const s t = match t with
  | TConst.TInt -> Int (int_of_string s)
  | TStr -> Str s
  | TFloat -> Float (float_of_string s)

module Sig = struct
  (* tconsts: name of variable * tconst *)
  type props = { arity: int; ntconsts: (string * TConst.t) list } [@@deriving compare, sexp_of, hash]

  type t = string * props [@@deriving compare, sexp_of, hash]

  let sig_table : (string, props) Hashtbl.t = Hashtbl.create (module String)

  let ntconst v_name st = (v_name, tconst_of_string st)

  let sig_pred p_name ntconsts =
    let props = { arity = List.length ntconsts; ntconsts } in
    let () = Hashtbl.add_exn sig_table p_name props in
    (p_name, props)

end
