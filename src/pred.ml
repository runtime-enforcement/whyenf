(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
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

    type t = Var of string | Const of Dom.t | App of string * t list [@@deriving compare, sexp_of, hash]

    let unvar = function
      | Var x -> x
      | Const _ -> raise (Invalid_argument "unvar is undefined for Consts")
      | App _ -> raise (Invalid_argument "unvar is undefined for Apps")

    let unconst = function
      | Var _ -> raise (Invalid_argument "unconst is undefined for Vars")
      | App _ -> raise (Invalid_argument "unconst is undefined for Apps")
      | Const c -> c

    let rec fv_list = function
      | [] -> []
      | Const c :: trms -> fv_list trms
      | Var x :: trms -> x :: fv_list trms
      | App (_, trms) :: trms' -> fv_list trms @ fv_list trms'

    let rec equal t t' = match t, t' with
      | Var x, Var x' -> String.equal x x'
      | Const d, Const d' -> Dom.equal d d'
      | App (f, ts), App (f', ts') ->
         String.equal f f' &&
           (match List.map2 ts ts' ~f:equal with
            | Ok b -> List.for_all b (fun x -> x)
            | Unequal_lengths -> false)
      | _ -> false

    let rec to_string = function
      | Var x -> Printf.sprintf "Var %s" x
      | Const d -> Printf.sprintf "Const %s" (Dom.to_string d)
      | App (f, ts) -> Printf.sprintf "App %s(%s)" f (String.concat ~sep:", " (List.map ts ~f:to_string))

    let rec value_to_string = function
      | Var x -> Printf.sprintf "%s" x
      | Const d -> Printf.sprintf "%s" (Dom.to_string d)
      | App (f, ts) -> Printf.sprintf "%s(%s)" f (String.concat ~sep:", " (List.map ts ~f:value_to_string))

    let rec list_to_string trms = String.concat ~sep:", " (List.map trms ~f:value_to_string)

  end

  include T
  include Comparator.Make(T)

end

module EnfType = struct

  type t = Cau | Sup | CauSup | Obs [@@deriving compare, sexp_of, hash]

  let neg = function
    | Cau    -> Sup
    | Sup    -> Cau
    | CauSup -> CauSup
    | Obs    -> Obs
  
  let to_int = function
    | Cau    -> 1
    | Sup    -> 2
    | CauSup -> 3
    | Obs    -> 0

  let to_string = function
    | Cau    -> "Cau"
    | Sup    -> "Sup"
    | CauSup -> "CauSup"
    | Obs    -> "Obs"

  let meet a b = match a, b with
    | _, _ when a == b -> a
    | Cau, Sup | Sup, Cau | CauSup, _ | _, CauSup -> CauSup
    | Obs, x | x, Obs -> x

  let join a b = match a, b with
    | _, _ when a == b -> a
    | Cau, Sup | Sup, Cau | Obs, _ | _, Obs -> Obs
    | Cau, _ | _, Cau -> Cau
    | _, _ -> Sup

  let leq a b = (join a b) == a
  let geq a b = (meet a b) == b

  let specialize a b = if leq b a then Some b else None

end

let tp_event_name = "~tp"
let tick_event_name = "tick"

module Sig = struct

  type pred = { arity: int;
                arg_tts: (string * Dom.tt) list;
                enftype: EnfType.t;
                rank: int } [@@deriving compare, sexp_of, hash]

  let string_of_pred name pred =
    let f acc (var, tt) = acc ^ "," ^ var ^ ":" ^ (Dom.tt_to_string tt) in
    Printf.sprintf "%s(%s)" name
      (String.drop_prefix (List.fold pred.arg_tts ~init:"" ~f) 1)

  type func = { arity: int;
                arg_tts: (string * Dom.tt) list;
                ret_tt: Dom.tt } [@@deriving compare, sexp_of, hash]

  let string_of_func name func =
    let f acc (var, tt) = acc ^ "," ^ var ^ ":" ^ (Dom.tt_to_string tt) in
    Printf.sprintf "%s(%s) : %s" name
      (String.drop_prefix (List.fold func.arg_tts ~init:"" ~f) 1)
      (Dom.tt_to_string func.ret_tt)
  
  type ty = Pred of pred | Func of func [@@deriving compare, sexp_of, hash]
  
  let string_of_ty name = function
    | Pred pred -> string_of_pred name pred
    | Func func -> string_of_func name func

  let arity = function
    | Pred pred -> pred.arity
    | Func func -> func.arity

  let arg_tts = function
    | Pred pred -> pred.arg_tts
    | Func func -> func.arg_tts

  let unpred = function
    | Pred pred -> pred
    | Func func -> raise (Invalid_argument "unpred is undefined for Funs")

  let unfunc = function
    | Func func -> func
    | Pred pred -> raise (Invalid_argument "unfunc is undefined for Preds")

  type t = string * ty [@@deriving compare, sexp_of, hash]

  let table: (string, ty) Hashtbl.t =
    let table = Hashtbl.create (module String) in
    Hashtbl.add_exn table ~key:tp_event_name
      ~data:(Pred { arity = 0; arg_tts = []; enftype = Cau; rank = 0 });
    Hashtbl.add_exn table ~key:tick_event_name
      ~data:(Pred { arity = 0; arg_tts = []; enftype = Obs; rank = 0 });
    table
  
  let add_pred p_name arg_tts enftype rank =
    Hashtbl.add_exn table ~key:p_name ~data:(Pred { arity = List.length arg_tts; arg_tts; enftype; rank })

  let add_func f_name arg_tts ret_tt =
    Hashtbl.add_exn table ~key:f_name ~data:(Func { arity = List.length arg_tts; arg_tts; ret_tt })

  let update_enftype name enftype =
    Hashtbl.update table name ~f:(fun (Some (Pred x)) -> Pred { x with enftype })

  let vars_of_pred name = List.map (unpred (Hashtbl.find_exn table name)).arg_tts ~f:fst

  let arg_tts_of_pred name = List.map (unpred (Hashtbl.find_exn table name)).arg_tts ~f:snd

  let ret_tt_of_func name = (unfunc (Hashtbl.find_exn table name)).ret_tt

  let enftype_of_pred name = (unpred (Hashtbl.find_exn table name)).enftype

  let rank_of_pred name = (unpred (Hashtbl.find_exn table name)).rank

  let print_table () =
    Hashtbl.iteri table ~f:(fun ~key:n ~data:ps -> Stdio.printf "%s\n" (string_of_ty n ps))

end

let check_const types c tt =
  if Dom.tt_equal (Dom.tt_of_domain c) tt then
    types
  else
    raise (Invalid_argument (
               Printf.sprintf "type clash for constant %s: found %s, expected %s"
                 (Dom.to_string c)
                 (Dom.tt_to_string (Dom.tt_of_domain c))
                 (Dom.tt_to_string tt)))

let check_var types v tt =
  match Map.find types v with
  | None -> Map.add_exn types ~key:v ~data:tt
  | Some tt' when Dom.tt_equal tt tt' -> types
  | Some tt' ->
     raise (Invalid_argument (
                Printf.sprintf "type clash for variable %s: found %s, expected %s"
                  v (Dom.tt_to_string tt) (Dom.tt_to_string tt')))

let check_app types f tt =
  if Dom.tt_equal (Sig.ret_tt_of_func f) tt then
    types
  else
    raise (Invalid_argument (
               Printf.sprintf "type clash for return type of %s: found %s, expected %s"
                 f
                 (Dom.tt_to_string (Sig.ret_tt_of_func f))
                 (Dom.tt_to_string tt)))

let rec check_terms types p_name trms =
  let sig_pred = Hashtbl.find_exn Sig.table p_name in
  if List.length trms = Sig.arity sig_pred then
    List.fold2_exn trms (Sig.arg_tts sig_pred) ~init:types 
      ~f:(fun types t ntc ->
        let tt' = snd ntc in
        match t with
        | Term.Var x -> check_var types x tt'
        | Const c -> check_const types c tt'
        | App (f, trms) -> check_app (check_terms types f trms) f tt'
      )
  else raise (Invalid_argument (Printf.sprintf "arity of %s is %d" p_name (Sig.arity sig_pred)))
