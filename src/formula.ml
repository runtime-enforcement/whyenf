(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*           (see file LICENSE for more details)                   *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Sformula

module Modules = MFOTL_lib.Modules
module MFOTL = MFOTL_lib.MFOTL
module Dom = MFOTL_lib.Dom
module Side = MFOTL_lib.Side
module Aggregation = MFOTL_lib.Aggregation

module StringVar : Modules.V with type t = string and type comparator_witness = String.comparator_witness = struct

  module T = struct

    type t = string [@@deriving compare, sexp_of, hash, equal]
    
    let to_string s = s
    let ident s = s
    let of_ident s = s

    let replace _ z = z
    
  end

  include T
  
  let comparator = String.comparator
  type comparator_witness = String.comparator_witness
  
end

let dummy = Term.TrivialInfo.dummy

include MFOTL.Make(Term.TrivialInfo)(StringVar)(Dom)(Term)

let aggregation_init = function
  | Sformula.Aop.ASum -> Aggregation.ASum
  | AAvg -> AAvg
  | AMed -> AMed
  | ACnt -> ACnt
  | AMin -> AMin
  | AMax -> AMax
  | AStd -> AStd

let rec init sf : t =
  let side s_opt = Side.value s_opt in
  let form = match sf with
    | SConst (CBool true)               -> tt
    | SConst (CBool false)              -> ff
    | SBop (None, t, Bop.BEq, SConst c) -> eqconst (Term.init t) (Const.to_dom c)
    | SBop (None, _, bop, _) as term when Bop.is_relational bop
      -> eqconst (Term.init term) (Dom.Int 1)
    | SAgg (s, aop, x, y, t)            -> agg s (aggregation_init aop) (Term.init x) y (init t)
    | STop (s, op, x, y, t)             -> top s op (List.map ~f:Term.init x) y (init t)
    | SAssign (t, s, x)                 -> let f = init t in
                                           agg s (Aggregation.AAssign) (Term.init x) (list_fv f) f
    | SApp (p, ts)                      -> predicate p (List.map ~f:Term.init ts)
    | SLet (x, enftype, y, t, u)        -> flet x enftype y (init t) (init u)
    | SExists (xs, t)                   -> (List.fold_right xs ~init:(init t)
                                              ~f:(fun x f -> make_dummy (exists x f))).form
    | SForall (xs, t)                   -> (List.fold_right xs ~init:(init t)
                                              ~f:(fun x f -> make_dummy (forall x f))).form
    | SUop (Uop.UNot, t)                -> neg (init t)
    | SUtop (i, Utop.UPrev, t)          -> prev i (init t)
    | SUtop (i, Utop.UNext, t)          -> next i (init t)
    | SUtop (i, Utop.UHistorically, t)  -> historically i (init t)
    | SUtop (i, Utop.UAlways, t)        -> always i (init t)
    | SUtop (i, Utop.UOnce, t)          -> once i (init t)
    | SUtop (i, Utop.UEventually, t)    -> eventually i (init t)
    | SBop (s_opt, t, Bop.BAnd, u)      -> conj (side s_opt) (init t) (init u)
    | SBop (s_opt, t, Bop.BOr, u)       -> disj (side s_opt) (init t) (init u)
    | SBop (s_opt, t, Bop.BImp, u)      -> imp (side s_opt) (init t) (init u)
    | SBop2 (s_opt, t, Bop2.BIff, u)    -> let s1, s2 = Side.value2 s_opt in
                                           iff s1 s2 (init t) (init u) dummy dummy
    | SBtop (s_opt, i, t, Btop.BSince, u) -> since (side s_opt) i (init t) (init u)
    | SBtop (s_opt, i, t, Btop.BUntil, u) -> until (side s_opt) i (init t) (init u)
    | SBtop (s_opt, i, t, Btop.BRelease, u) -> release (side s_opt) i (init t) (init u) dummy dummy dummy
    | SBtop (s_opt, i, t, Btop.BTrigger, u) -> trigger (side s_opt) i (init t) (init u) dummy dummy dummy
    | sf ->
       raise (Errors.FormulaError
                (Printf.sprintf "Expression %s is not a valid MFOTL formula"
                   (Sformula.to_string sf)))
  in ac_simplify (make_dummy form)

let check_agg types s op x y f =
  let x_tt = Sig.tt_of_term_exn types x in
  match Aggregation.ret_tt op x_tt with
  | None -> raise (Invalid_argument (
                       Printf.sprintf "type clash for aggregation operator %s: invalid type %s"
                         (Aggregation.op_to_string op) (Dom.tt_to_string x_tt)))
  | Some s_tt ->
     let types, _ = Sig.check_var types s (Ctxt.TConst s_tt) in
     let vars = (Term.fv_list [x]) @ y in
     let fv = fv f in
     List.iter vars ~f:(
         fun x ->
         if not (Set.mem fv x) then
           raise (Invalid_argument (
                      Printf.sprintf "variable %s is used in aggregation, but not free in %s"
                        x (to_string_typed f)))
         else ());
     (*if Set.mem fv s then
       raise (Invalid_argument (
       Printf.sprintf "variable %s is both the target of an aggregation and free in %s"
       s (to_string f)));*)
     types, s_tt

let check_top types s op x y f =
  let _ = List.map ~f:(Sig.tt_of_term_exn types) x in
  let arg_ttts = Sig.arg_ttts_of_func op in
  let ret_ttts = Sig.ret_ttts_of_func op in
  let types = List.fold2_exn ~init:types
                ~f:(fun types trm ttt -> fst (Sig.check_term types trm ttt)) arg_ttts x in
  let types = List.fold2_exn ~init:types
                ~f:(fun types ttt x -> fst (Sig.check_var types x ttt)) ret_ttts s in
  let vars = (Term.fv_list x) @ y in
  let fv = fv f in
  List.iter vars ~f:(
      fun x ->
      if not (Set.mem fv x) then
        raise (Invalid_argument (
                   Printf.sprintf "variable %s is used in aggregation, but not free in %s"
                     x (to_string_typed f)))
      else ());
  types, List.map ~f:Ctxt.unconst ret_ttts















