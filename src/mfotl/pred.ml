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

module Term = struct

  type const = Int of int | Str of string | Float of float [@@deriving compare, sexp_of, hash]

  type tconst = TInt | TStr | TFloat [@@deriving compare, sexp_of, hash]

  type t = Var of string | Const of const [@@deriving compare, sexp_of, hash]

  let const_equal c c' = match c, c' with
    | Int v, Int v' -> Int.equal v v'
    | Str v, Str v' -> String.equal v v'
    | Float v, Float v' -> Float.equal v v'
    | _ -> false

  let term_equal t t' = match t, t' with
    | Var x, Var x' -> String.equal x x'
    | Const c, Const c' -> const_equal c c'
    | _ -> false

  let tconst_of_string = function
    | "int" -> TInt
    | "string" -> TStr
    | "float" -> TFloat
    | t -> raise (Invalid_argument (Printf.sprintf "type %s is not supported" t))

  let t_of_const = function
    | Int _ -> TInt
    | Str _ -> TStr
    | Float _ -> TFloat

  let string_to_const s t = match t with
    | TInt -> Int (int_of_string s)
    | TStr -> Str s
    | TFloat -> Float (float_of_string s)

  let const_to_string = function
    | Int v -> string_of_int v
    | Str v -> v
    | Float v -> string_of_float v

  let rec list_to_string trms =
    match trms with
    | [] -> ""
    | (Var x) :: trms -> if List.is_empty trms then x
                         else Printf.sprintf "%s, %s" x (list_to_string trms)
    | (Const d) :: trms -> if List.is_empty trms then (const_to_string d)
                           else Printf.sprintf "%s, %s" (const_to_string d) (list_to_string trms)

end

module Sig = struct

  type props = { arity: int; ntconsts: (string * Term.tconst) list } [@@deriving compare, sexp_of, hash]

  type t = string * props [@@deriving compare, sexp_of, hash]

  let sig_table : (string, props) Hashtbl.t = Hashtbl.create (module String)

  let ntconst v_name st = (v_name, Term.tconst_of_string st)

  let sig_pred p_name ntconsts =
    let props = { arity = List.length ntconsts; ntconsts } in
    let () = Hashtbl.add_exn sig_table p_name props in
    (p_name, props)

end

let make_terms p_name strms =
  let sig_pred = Hashtbl.find_exn Sig.sig_table p_name in
  if List.length strms = sig_pred.arity then
    List.map2_exn strms sig_pred.ntconsts
      (fun s ntc -> if String.equal s (fst ntc) then Term.Var s
                    else Const (Term.string_to_const s (snd ntc)))
  else raise (Invalid_argument (Printf.sprintf "arity of %s is %d" p_name sig_pred.arity))
