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

  type t = Var of string | Const of Domain.t [@@deriving compare, sexp_of, hash]

  let equal t t' = match t, t' with
    | Var x, Var x' -> String.equal x x'
    | Const d, Const d' -> Domain.equal d d'
    | _ -> false

  let rec list_to_string trms =
    match trms with
    | [] -> ""
    | (Var x) :: trms -> if List.is_empty trms then x
                         else Printf.sprintf "%s, %s" x (list_to_string trms)
    | (Const d) :: trms -> if List.is_empty trms then (Domain.to_string d)
                           else Printf.sprintf "%s, %s" (Domain.to_string d) (list_to_string trms)

end

module Sig = struct

  type props = { arity: int; ntconsts: (string * Domain.tt) list } [@@deriving compare, sexp_of, hash]

  type t = string * props [@@deriving compare, sexp_of, hash]

  let table : (string, props) Hashtbl.t = Hashtbl.create (module String)

  let n_tt v_name st = (v_name, Domain.tt_of_string st)

  let add p_name ntconsts =
    let props = { arity = List.length ntconsts; ntconsts } in
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
