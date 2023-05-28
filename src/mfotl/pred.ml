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
open Stdio

module Term = struct

  module T = struct

    type t = Var of string | Const of Domain.t [@@deriving compare, sexp_of, hash]

    let unvar = function
      | Var x -> x
      | Const _ -> raise (Invalid_argument "unvar is undefined for Consts")

    let rec fv_list = function
      | [] -> []
      | Const c :: trms -> fv_list trms
      | Var x :: trms -> [Var x] @ fv_list trms

    let equal t t' = match t, t' with
      | Var x, Var x' -> String.equal x x'
      | Const d, Const d' -> Domain.equal d d'
      | _ -> false

    let to_string = function
      | Var x -> Printf.sprintf "Var %s" x
      | Const d -> Printf.sprintf "Const %s" (Domain.to_string d)

    let rec list_to_string trms =
      match trms with
      | [] -> ""
      | (Var x) :: trms -> if List.is_empty trms then x
                           else Printf.sprintf "%s, %s" x (list_to_string trms)
      | (Const d) :: trms -> if List.is_empty trms then (Domain.to_string d)
                             else Printf.sprintf "%s, %s" (Domain.to_string d) (list_to_string trms)

  end

  include T
  include Comparator.Make(T)

end

module Sig = struct

  type props = { arity: int; ntconsts: (string * Domain.tt) list } [@@deriving compare, sexp_of, hash]

  type t = string * props [@@deriving compare, sexp_of, hash]

  let table: (string, props) Hashtbl.t = Hashtbl.create (module String)

  let table_tt: (string, Domain.tt) Hashtbl.t = Hashtbl.create (module String)

  let n_tt v_name st = (v_name, Domain.tt_of_string st)

  let term_tt x = Hashtbl.find_exn table_tt x

  let term_default x = Domain.tt_default (Hashtbl.find_exn table_tt x)

  let add p_name ntconsts =
    let props = { arity = List.length ntconsts; ntconsts } in
    List.iter ntconsts ~f:(fun (name, tt) -> Hashtbl.add_exn table_tt name tt);
    Hashtbl.add_exn table p_name props

  let print_table () =
    Hashtbl.iteri table ~f:(fun ~key:n ~data:ps ->
        Stdio.printf "%s(%s)\n" n
          (String.drop_prefix (List.fold ps.ntconsts ~init:"" ~f:(fun acc (var, tt) ->
               acc ^ "," ^ var ^ ":" ^ (Domain.tt_to_string tt))) 1))

end

let make_terms p_name strms =
  let sig_pred = Hashtbl.find_exn Sig.table p_name in
  if List.length strms = sig_pred.arity then
    List.map2_exn strms sig_pred.ntconsts
      (fun s ntc -> if String.equal s (fst ntc) then Term.Var s
                    else Const (Domain.string_to_t s (snd ntc)))
  else raise (Invalid_argument (Printf.sprintf "arity of %s is %d" p_name sig_pred.arity))
