(*******************************************************************)

(*     This is part of WhyEnf, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Base

module Enftype = MFOTL_lib.Enftype
module MFOTL = MFOTL_lib.MFOTL
module Modules = MFOTL_lib.Modules
module Etc = MFOTL_lib.Etc
module Dom = MFOTL_lib.Dom
module Filter = MFOTL_lib.Filter

type info_type = {
    enftype: Enftype.t;
    filter:  Filter.t;
    flag:    bool;
  } [@@deriving compare, sexp_of, hash, equal]

module TypeInfo : Modules.I with type t = info_type = struct

  type t = info_type [@@deriving compare, sexp_of, hash, equal]

  let to_string l s info =
    if Enftype.is_only_observable info.enftype then
      s
    else
      Printf.sprintf (Etc.paren l 0 "%s : %s") s (Enftype.to_string info.enftype)

  let dummy = { enftype = Enftype.obs; filter = Filter.tt; flag = false }

end 

include MFOTL.Make(TypeInfo)(Tterm.TypedVar)(Dom)(Tterm)

include Formula.MFOTL_Enforceability(Sig)

let rec core_of_formula (f : Formula.typed_t) let_types (types: Ctxt.t) : Ctxt.t * core_t * Enftype.t * bool =
  let f_q ?(true_ok=true) f x =
    if is_past_guarded x true f then
      true
    else if is_past_guarded x false f && true_ok then
      false
    else
      (Stdio.print_endline ("However, the formula is not  because the variable\n "
                            ^ x
                            ^ "\nis not monitorable in\n "
                            ^ Formula.to_string_typed f);
       raise (Invalid_argument
                (Printf.sprintf "variable %s is not monitorable in %s" x (Formula.to_string_typed f))))
  in 
  let f_q_nonvar f x =
    let nonvars = Set.filter (Formula.terms f) ~f:(fun t -> not (Term.is_var t)) in
    let nonvars_fvs = Term.fv_list (Set.elements nonvars) in
    if List.mem nonvars_fvs x ~equal:String.equal then
      f_q f x
    else
      true in
  match f.form with
  | TT -> types, TT, Enftype.cau, false
  | FF -> types, FF, Enftype.sup, false
  | EqConst (trm, c) ->
     let types, _ = Sig.check_term types (Ctxt.TConst (Dom.tt_of_domain c)) trm in
     types, EqConst (Tterm.convert types trm, c), Enftype.obs, false
  | Predicate (e, trms) when not (Sig.equal_pred_kind (Sig.kind_of_pred e) Sig.Predicate) ->
     let types, _ = Sig.check_terms types e trms in
     let enftype  = Sig.enftype_of_pred e in
     types, Predicate (e, Tterm.convert_multiple types trms),
     Enftype.join enftype Enftype.obs, false
  | Predicate (e, trms) ->
     let types, _ = Sig.check_terms types e trms in
     let enftype  = Sig.enftype_of_pred e in
     types, EqConst (Tterm.make_dummy (Tterm.App (e, Tterm.convert_multiple types trms)), Dom.Int 1),
     Enftype.join enftype Enftype.obs, false
  | Predicate' (e, trms, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Predicate' (e, Tterm.convert_multiple types trms, mf), mf.info.enftype, false
  | Let _ -> raise (Invalid_argument "Let bindings must be unrolled to convert to Tformula")
  | Let' (r, trms, f, g) ->
     let _, mf = of_formula f ~let_types types in
     let types, mg = of_formula g ~let_types types in
     types, Let' (r, Tterm.convert_vars types trms, mf, mg),
     Enftype.join mf.info.enftype mg.info.enftype, false
  | Agg (s, op, x, y, f) ->
     let types, mf = of_formula f ~let_types types in
     let types, s_tt = Formula.check_agg types s op x y f in
     let vars_to_monitor =
       Term.fv_list [x]
       @ (List.filter (Set.elements (Formula.fv f))
            ~f:(fun x -> List.mem y x ~equal:String.equal)) in
     ignore (List.map vars_to_monitor ~f:(f_q ~true_ok:false f));
     types, Agg ((s, s_tt), op, Tterm.convert types x, Tterm.convert_vars types y, mf),
     mf.info.enftype, false
  | Top (s, op, x, y, f) ->
     let types, mf = of_formula f ~let_types types in
     let types, s_ttts = Formula.check_top types s op x y f in
     let vars_to_monitor =
       Term.fv_list x
       @ (List.filter (Set.elements (Formula.fv f))
            ~f:(fun x -> List.mem y x ~equal:String.equal)) in
     ignore (List.map vars_to_monitor ~f:(f_q ~true_ok:false f));
     types, Top (List.zip_exn s s_ttts, op, Tterm.convert_multiple types x, Tterm.convert_vars types y, mf),
     mf.info.enftype, false
  | Neg f ->
     let types, mf = of_formula f ~let_types types in
     types, Neg mf, mf.info.enftype, false
  | And (s, fs) ->
     let types, mfs = List.fold_map fs ~init:types ~f:(fun types f -> of_formula f ~let_types types) in
     let mf1, mf_rest = List.hd_exn mfs, List.tl_exn mfs in
     let enftype = List.fold_left ~init:mf1.info.enftype
                     ~f:(fun enftype mf -> Enftype.join enftype mf.info.enftype) mf_rest in
     types, And (s, mfs), enftype, false
  | Or (s, fs) ->
     let types, mfs = List.fold_map fs ~init:types ~f:(fun types f -> of_formula f ~let_types types) in
     let mf1, mf_rest = List.hd_exn mfs, List.tl_exn mfs in
     let enftype = List.fold_left ~init:mf1.info.enftype
                     ~f:(fun enftype mf -> Enftype.join enftype mf.info.enftype) mf_rest in
     types, Or (s, mfs), enftype, false
  | Imp (s, f, g) ->
     let types, mf = of_formula f ~let_types types in
     let types, mg = of_formula g ~let_types types in
     types, Imp (s, mf, mg), Enftype.join mf.info.enftype mg.info.enftype, false
  | Exists (x, f) ->
     let types, mf = of_formula f ~let_types types in
     (*print_endline "--core_of_formula.Exists";
       print_endline (Formula.to_string f);*)
     (*Map.iteri types ~f:(fun ~key ~data -> print_endline (key ^ " -> " ^ Dom.tt_to_string data));*)
     types, Exists ((x, Ctxt.get_tt_exn x types), mf), mf.info.enftype, f_q_nonvar f x
  | Forall (x, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Forall ((x, Ctxt.get_tt_exn x types), mf), mf.info.enftype, f_q_nonvar f x
  | Prev (i, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Prev (i, mf), mf.info.enftype, false
  | Next (i, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Next (i, mf), mf.info.enftype, false
  | Once (i, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Once (i, mf), mf.info.enftype, false
  | Eventually (i, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Eventually (i, mf), mf.info.enftype, true
  | Historically (i, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Historically (i, mf), mf.info.enftype, false
  | Always (i, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Always (i, mf), mf.info.enftype, true
  | Since (s, i, f, g) ->
     let types, mf = of_formula f ~let_types types in
     let types, mg = of_formula g ~let_types types in
     types, Since (s, i, mf, mg), Enftype.join mf.info.enftype mg.info.enftype, false
  | Until (s, i, f, g) ->
     let types, mf = of_formula f ~let_types types in
     let types, mg = of_formula g ~let_types types in
     types, Until (s, i, mf, mg), Enftype.join mf.info.enftype mg.info.enftype, true
  | Type (f, ty) ->
     let types, mf = of_formula f ~let_types types in
     types, Type (mf, ty), mf.info.enftype, false

and of_formula f ?(let_types=Map.empty (module String)) (types: Ctxt.t) =
  let types, f, enftype, flag = core_of_formula f let_types types in
  types, make f { enftype; filter = Filter.tt; flag }

let of_formula' f =
  snd (of_formula f Ctxt.empty)
