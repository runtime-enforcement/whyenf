(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Etc
open Formula
open Checker.Whymon

module Fdeque = Core.Fdeque

let int_of_nat n = Z.to_int (integer_of_nat n)
let nat_of_int i = nat_of_integer (Z.of_int i)
let enat_of_integer i = Enat (nat_of_integer i)

module E = Expl


module Checker_domain = struct

  let to_string = function
    | EString v -> v
    | EInt v -> Int.to_string (Z.to_int v)

  let list_to_string ds =
    String.drop_suffix (List.fold ds ~init:"" ~f:(fun acc d -> acc ^ (to_string d) ^ ", ")) 2

end

module Checker_term = struct

  let to_string = function
    | Var x -> Printf.sprintf "Var %s" x
    | Const d -> Printf.sprintf "Const %s" (Checker_domain.to_string d)

  let rec list_to_string trms =
    match trms with
    | [] -> ""
    | (Var x) :: trms -> if List.is_empty trms then x
                         else Printf.sprintf "%s, %s" x (list_to_string trms)
    | (Const d) :: trms -> if List.is_empty trms then (Checker_domain.to_string d)
                           else Printf.sprintf "%s, %s" (Checker_domain.to_string d) (list_to_string trms)

end

module Checker_set = struct

  let to_string cs =
    let rec format = function
      | [] -> ""
      | [x] -> Checker_domain.to_string x
      | x :: xs -> Printf.sprintf "%s, " (Checker_domain.to_string x) ^ (format xs) in
    match cs with
    | Set s -> Printf.sprintf "Set {%s}" (format s)
    | Coset s -> Printf.sprintf "Coset {%s}" (format s)

end

module Checker_part = struct

  let rec el_to_string indent f (sub, v) =
    Printf.sprintf "%sset = {%s}\n%s%s" indent (Checker_set.to_string sub) indent (f indent v)

  let to_string indent f = function
    | [] -> indent ^ "[]"
    | [x] -> indent ^ Etc.eat "[" ((el_to_string indent f x) ^ "]")
    | x :: xs ->
       List.fold_left ~f:(fun s el -> Etc.eat (s ^ "\n" ^ indent ^ "; ") (el_to_string indent f el))
         ~init:(indent ^ Etc.eat "[ " (el_to_string indent f x)) xs ^ " ]"

end

module Checker_trace = struct

  type t = ((string * event_data list) set * nat) list

  let evt_to_string (name, ds) =
    Printf.sprintf "[debug] %s(%s)" name (Checker_domain.list_to_string ds)

  let db_to_string db =
    List.fold db ~init:"" ~f:(fun acc evt -> acc ^ evt_to_string evt ^ "\n")

  let to_string trace_lst = List.fold_left trace_lst ~init:"" ~f:(fun acc (db, ts) ->
                                acc ^ Printf.sprintf "[debug] TS = %d:\n" (int_of_nat ts) ^
                                  (match db with
                                   | Set s -> db_to_string s
                                   | Coset _ -> raise (Failure "set of dbs should not be converted to coset")) ^ "\n")

end

module type Checker_interfaceT = sig

  module Expl : sig

    module Proof: E.ProofT
    type t = Proof.t E.Pdt.t

    val is_violated: t -> bool
    val is_satisfied: t -> bool
    val at: t -> int

    val to_string: t -> string
    val to_latex: Formula.t -> t -> string
    val to_light_string: t -> string

  end

  module Vis : sig

    val to_json: Formula.t -> Expl.Proof.t E.Pdt.t -> string

  end

  module Checker_pdt : sig

    type t = (event_data, (event_data sproof, event_data vproof) sum) pdt

    val to_string: string -> t -> string

  end

  val check: (timestamp * (string * Dom.t list, 'a) Base.Set.t) list -> Formula.t -> Expl.t list ->
             (bool * (event_data, (event_data sproof, event_data vproof) sum) pdt * Checker_trace.t) list

  val false_paths: (timestamp * (string * Dom.t list, 'a) Base.Set.t) list -> Formula.t -> Expl.t list ->
                   (Dom.t, Dom.comparator_witness) Setc.t list list option list

end


module LightChecker_interface = struct

  module E = Expl
  module Expl = Expl.Make (Expl.LightProof)
  module Vis = Vis.LightExpl

  module Checker_pdt = struct

    type t = (event_data, (event_data sproof, event_data vproof) sum) pdt

    let proof_to_string indent = function
      | Inl p -> "S"
      | Inr p -> "V"

    let rec to_string indent = function
      | Leaf pt -> Printf.sprintf "%s Leaf (%s)\n%s" indent (proof_to_string "" pt) indent
      | Node (x, part) -> Printf.sprintf "%s Node (%s,\n%s)\n" indent x
                            (Checker_part.to_string "    " to_string (subsvals part))
    
  end

  let check _ _ _ = failwith "check not supported in light mode"
  let false_paths _ _ _ = failwith "false_paths not supported in light mode"
    

end
