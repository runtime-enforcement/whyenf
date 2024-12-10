open Base

module MyTerm = Term
open MFOTL_lib
module Ctxt = Ctxt.Make(Dom)
module Term = MyTerm

include MFOTL.Make(Term.TrivialInfo)(Tterm.TypedVar)(Dom)(Tterm)

include Formula.MFOTL_Enforceability(Sig)

let rec core_of_formula (f : Formula.t) let_types (types: Ctxt.t) : Ctxt.t * core_t =
  match f.form with
  | TT -> types, TT
  | FF -> types, FF
  | EqConst (trm, c) ->
     let types, _ = Sig.check_term types (Ctxt.TConst (Dom.tt_of_domain c)) trm in
     types, EqConst (Tterm.convert types trm, c)
  | Predicate (e, trms) when Map.mem let_types e ->
     let types, ttts = Sig.check_terms_ttts types e (Map.find_exn let_types e) trms in
     types, Predicate (e, Tterm.convert_multiple types trms)
  | Predicate (e, trms) when not (Sig.equal_pred_kind (Sig.kind_of_pred e) Sig.Predicate) ->
     let types, _ = Sig.check_terms types e trms in
     types, Predicate (e, Tterm.convert_multiple types trms)
  | Predicate (e, trms) ->
     let types, _ = Sig.check_terms types e trms in
     types, EqConst (Tterm.make_dummy (Tterm.App (e, Tterm.convert_multiple types trms)), Dom.Int 1)
  | Predicate' (e, trms, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Predicate' (e, Tterm.convert_multiple types trms, mf)
  | Let (r, enftype_opt, vars, f, g) ->
     let types, mf = of_formula f ~let_types types in
     List.iter vars ~f:(
         fun v -> if not (Ctxt.mem types v) then
                    raise (Invalid_argument (Printf.sprintf "Variable %s in let-bound predicate %s is unused" v r)));
     let let_types = Map.add_exn let_types r (List.map ~f:(fun v -> Ctxt.get_ttt_exn v types) vars) in
     let types, mg = of_formula g ~let_types types in
     types, Let (r, enftype_opt, Tterm.convert_vars types vars, mf, mg)
  | Let' (r, vars, f, g) ->
     let types, mf = of_formula f ~let_types types in
     let types, mg = of_formula g ~let_types types in
     types, Let' (r, Tterm.convert_vars types vars, mf, mg)
  | Agg (s, op, x, y, f) ->
     let types, mf = of_formula f ~let_types types in
     let types, s_tt = Formula.check_agg types s op x y f in
     let vars_to_monitor =
       Term.fv_list [x]
       @ (List.filter (Set.elements (Formula.fv f))
            ~f:(fun x -> List.mem y x ~equal:String.equal)) in
     types, Agg ((s, s_tt), op, Tterm.convert types x, Tterm.convert_vars types y, mf)
  | Top (s, op, x, y, f) ->
     let types, mf = of_formula f ~let_types types in
     let types, s_ttts = Formula.check_top types s op x y f in
     let vars_to_monitor =
       Term.fv_list x
       @ (List.filter (Set.elements (Formula.fv f))
            ~f:(fun x -> List.mem y x ~equal:String.equal)) in
     types, Top (List.zip_exn s s_ttts, op, Tterm.convert_multiple types x, Tterm.convert_vars types y, mf)
  | Neg f ->
     let types, mf = of_formula f ~let_types types in
     types, Neg mf
  | And (s, fs) ->
     let types, mfs = List.fold_map fs ~init:types ~f:(fun types f -> of_formula f ~let_types types) in
     types, And (s, mfs)
  | Or (s, fs) ->
     let types, mfs = List.fold_map fs ~init:types ~f:(fun types f -> of_formula f ~let_types types) in
     types, Or (s, mfs)
  | Imp (s, f, g) ->
     let types, mf = of_formula f ~let_types types in
     let types, mg = of_formula g ~let_types types in
     types, Imp (s, mf, mg)
  | Exists (x, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Exists ((x, Ctxt.get_tt_exn x types), mf)
  | Forall (x, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Forall ((x, Ctxt.get_tt_exn x types), mf)
  | Prev (i, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Prev (i, mf)
  | Next (i, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Next (i, mf)
  | Once (i, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Once (i, mf)
  | Eventually (i, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Eventually (i, mf)
  | Historically (i, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Historically (i, mf)
  | Always (i, f) ->
     let types, mf = of_formula f ~let_types types in
     types, Always (i, mf)
  | Since (s, i, f, g) ->
     let types, mf = of_formula f ~let_types types in
     let types, mg = of_formula g ~let_types types in
     types, Since (s, i, mf, mg)
  | Until (s, i, f, g) ->
     let types, mf = of_formula f ~let_types types in
     let types, mg = of_formula g ~let_types types in
     types, Until (s, i, mf, mg)
  | Type (f, ty) ->
     let types, mf = of_formula f ~let_types types in
     types, Type (mf, ty)

and of_formula f ?(let_types=Map.empty (module String)) (types: Ctxt.t) =
  let types, f = core_of_formula f let_types types in
  types, make_dummy f

let of_formula' f =
  snd (of_formula f Ctxt.empty)

