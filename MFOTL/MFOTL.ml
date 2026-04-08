open Base

open Modules

exception FormulaError of string

module Make
         (Info : I)
         (Var  : V)
         (Dom  : D)
         (Term : Term.T with type v = Var.t and type d = Dom.t) = struct

  (* Main datatype: abstract MFOTL+ formulae *)

  type ('i, 'v, 'd, 't) _core_t =
    | TT
    | FF
    | EqConst of 't * 'd
    | Predicate of string * 't list
    | Predicate' of string * 't list * ('i, 'v, 'd, 't) _t
    | Let of string * Enftype.t * ('v * Dom.tt option) list * ('i, 'v, 'd, 't) _t * ('i, 'v, 'd, 't) _t
    | Let' of string * Enftype.t * ('v * Dom.tt option) list * ('i, 'v, 'd, 't) _t * ('i, 'v, 'd, 't) _t
    | Agg of 'v * Aggregation.op *  't * 'v list * ('i, 'v, 'd, 't) _t
    | Top of 'v list * string * 't list * 'v list * ('i, 'v, 'd, 't) _t
    | Neg of ('i, 'v, 'd, 't) _t
    | And of Side.t * ('i, 'v, 'd, 't) _t list
    | Or of Side.t * ('i, 'v, 'd, 't) _t list
    | Imp of Side.t * ('i, 'v, 'd, 't) _t * ('i, 'v, 'd, 't) _t
    | Exists of 'v * ('i, 'v, 'd, 't) _t
    | Forall of 'v * ('i, 'v, 'd, 't) _t
    | Prev of Interval.t * ('i, 'v, 'd, 't) _t
    | Next of Interval.t * ('i, 'v, 'd, 't) _t
    | Once of Interval.t * ('i, 'v, 'd, 't) _t
    | Eventually of Interval.t * ('i, 'v, 'd, 't) _t
    | Historically of Interval.t * ('i, 'v, 'd, 't) _t
    | Always of Interval.t * ('i, 'v, 'd, 't) _t
    | Since of Side.t * Interval.t * ('i, 'v, 'd, 't) _t * ('i, 'v, 'd, 't) _t
    | Until of Side.t * Interval.t * ('i, 'v, 'd, 't) _t * ('i, 'v, 'd, 't) _t
    | Type of ('i, 'v, 'd, 't) _t * Enftype.t
    | Label of string * ('i, 'v, 'd, 't) _t
  [@@deriving compare, sexp_of, hash, equal]

  and ('i, 'v, 'd, 't) _t = { form : ('i, 'v, 'd, 't) _core_t; info : 'i}
  [@@deriving compare, sexp_of, hash, equal]

  type core_t = (Info.t, Var.t, Dom.t, Term.t) _core_t [@@deriving compare, sexp_of, hash, equal]
  type t      = (Info.t, Var.t, Dom.t, Term.t) _t      [@@deriving compare, sexp_of, hash, equal]

  let rec core_equal f g =
    let fa x y ~f = match List.for_all2 x y ~f with Ok b -> b | _ -> false in
    match f.form, g.form with
    | Predicate' (_, _, f), _ -> core_equal f g
    | _, Predicate' (_, _, g) -> core_equal f g
    | Let' (_, _, _, _, f), _ -> core_equal f g
    | _, Let' (_, _, _, _, g) -> core_equal f g 
    | TT, TT
    | FF, FF -> true
    | EqConst (trm, d), EqConst (trm', d') -> Term.core_equal trm trm' && Dom.equal d d'
    | Predicate (e, trms), Predicate (e', trms') ->
       String.equal e e' && fa trms trms' ~f:Term.core_equal
    | Let (e, enftype, trms, f, g), Let (e', enftype', trms', f', g') ->
       String.equal e e' && Enftype.equal enftype enftype'
       && fa trms trms' ~f:(fun (x, _) (x', _) -> Var.equal_ident x x')
       && core_equal f f' && core_equal g g'
    | Agg (x, op, y, z, f), Agg (x', op', y', z', f') ->
       Var.equal_ident x x' && Aggregation.equal_op op op' && Term.core_equal y y'
       && fa z z' ~f:Var.equal_ident && core_equal f f'
    | Top (x, op, y, z, f), Top (x', op', y', z', f') ->
       fa x x' ~f:Var.equal && String.equal op op' && fa y y' ~f:Term.equal
       && fa z z' ~f:Var.equal && core_equal f f'
    | Neg f, Neg f' -> core_equal f f'
    | And (s, fs), And (s', fs')
    | Or (s, fs), Or (s', fs') -> Side.equal s s' && fa fs fs' ~f:core_equal
    | Imp (s, f, g), Imp (s', f', g') -> Side.equal s s' && core_equal f f' && core_equal g g'
    | Exists (x, f), Exists (x', f')
    | Forall (x, f), Forall (x', f') -> Var.equal_ident x x' && core_equal f f'
    | Prev (i, f), Prev (i', f')
    | Next (i, f), Next (i', f')
    | Once (i, f), Once (i', f')
    | Eventually (i, f), Eventually (i', f')
    | Historically (i, f), Historically (i', f')
    | Always (i, f), Always (i', f') -> Interval.equal i i' && core_equal f f'
    | Since (s, i, f, g), Since (s', i', f', g')
    | Until (s, i, f, g), Until (s', i', f', g') ->
       Side.equal s s' && Interval.equal i i' && core_equal f f' && core_equal g g'
    | Type (f, enftype), Type (f', enftype') -> core_equal f f' && Enftype.equal enftype enftype'
    | Label (s, f), Label (s', f') -> String.equal s s' && core_equal f f'
    | _, _ -> false

  (* Abstract MFOTL+ formulae with enforcement types *)

  type typed_info = {
      info : Info.t;
      enftype : Enftype.t;
      filter : Filter.t;
      flag : bool;
      tabular: bool;
    } [@@deriving compare, sexp_of, hash, equal]

  module TypedInfo : Modules.I with type t = typed_info = struct

    type t = typed_info [@@deriving compare, sexp_of, hash, equal]

    let to_string l s info =
      (if Enftype.is_only_observable info.enftype then
         s
       else
         Printf.sprintf (Etc.paren l 0 "%s : %s") s (Enftype.to_string info.enftype))

    let dummy = { info = Info.dummy; enftype = Enftype.bot; filter = Filter.tt; flag = false; tabular = false }

  end 

  type core_typed_t = (TypedInfo.t, Var.t, Dom.t, Term.t) _core_t [@@deriving equal]
  type typed_t      = (TypedInfo.t, Var.t, Dom.t, Term.t) _t      [@@deriving equal]

  let rec map_info ~f:(f:'a -> 'b) (formula: ('a, Var.t, Dom.t, Term.t) _t) : ('b, Var.t, Dom.t, Term.t) _t =
    let form = match formula.form with
      | TT -> TT
      | FF -> FF
      | EqConst (t, c) -> EqConst (t, c)
      | Predicate (e, ts) -> Predicate (e, ts)
      | Predicate' (e, ts, mf) -> Predicate' (e, ts, map_info ~f mf)
      | Let (e, ty_opt, vars, mf, mg) -> Let (e, ty_opt, vars, map_info ~f mf, map_info ~f mg)
      | Let' (e, ty_opt, vars, mf, mg) -> Let' (e, ty_opt, vars, map_info ~f mf, map_info ~f mg)
      | Agg (s, op, x, y, mf) -> Agg (s, op, x, y, map_info ~f mf)
      | Top (s, op, x, y, mf) -> Top (s, op, x, y, map_info ~f mf)
      | Neg mf -> Neg (map_info ~f mf)
      | And (s, mfs) -> And (s, List.map ~f:(map_info ~f) mfs)
      | Or (s, mfs) -> Or (s, List.map ~f:(map_info ~f) mfs)
      | Imp (s, mf, mg) -> Imp (s, map_info ~f mf, map_info ~f mg)
      | Exists (x, mf) -> Exists (x, map_info ~f mf)
      | Forall (x, mf) -> Forall (x, map_info ~f mf)
      | Prev (i, mf) -> Prev (i, map_info ~f mf)
      | Next (i, mf) -> Next (i, map_info ~f mf)
      | Once (i, mf) -> Once (i, map_info ~f mf)
      | Eventually (i, mf) -> Eventually (i, map_info ~f mf)
      | Historically (i, mf) -> Historically (i, map_info ~f mf)
      | Always (i, mf) -> Always (i, map_info ~f mf)
      | Since (s, i, mf, mg) -> Since (s, i, map_info ~f mf, map_info ~f mg)
      | Until (s, i, mf, mg) -> Until (s, i, map_info ~f mf, map_info ~f mg)
      | Type (mf, ty) -> Type (map_info ~f mf, ty)
      | Label (s, mf) -> Label (s, map_info ~f mf)
    in { form; info = f formula.info }

  let untyped = map_info ~f:(fun info -> info.info)

  (* Free variables, terms, predicates, degree, size, exists *)

  let rec fv f =
    match f.form with
    | TT | FF -> Set.empty (module Var)
    | EqConst (trm, _) -> Set.of_list (module Var) (Term.fv_list [trm])
    | Predicate (_, trms) -> Set.of_list (module Var) (Term.fv_list trms)
    | Predicate' (_, trms, f) -> Set.union (Set.of_list (module Var) (Term.fv_list trms)) (fv f)
    | Let (_, _, _, _, f)
      | Let' (_, _, _, _, f)
      | Neg f
      | Prev (_, f)
      | Once (_, f)
      | Historically (_, f)
      | Eventually (_, f)
      | Always (_, f)
      | Next (_, f)
      | Type (f, _)
      | Label (_, f) -> fv f
    | Agg (s, _, _, y, _) -> Set.of_list (module Var) (s::y)
    | Top (s, _, _, y, _) -> Set.of_list (module Var) (s@y)
    | Exists (x, f)
      | Forall (x, f) -> Set.filter (fv f) ~f:(fun y -> not (Var.equal_ident x y))
    | And (_, fs)
      | Or (_, fs) -> Set.union_list (module Var) (List.map fs ~f:fv)
    | Imp (_, f1, f2)
      | Since (_, _, f1, f2)
      | Until (_, _, f1, f2) -> Set.union (fv f1) (fv f2)

  let fvs fs = Set.union_list (module Var) (List.map ~f:fv fs)

  let list_fv e = Set.elements (fv e)

  let rec terms f = match f.form with
    | TT | FF -> Set.empty (module Term)
    | EqConst (trm, _) -> Set.singleton (module Term) trm
    | Agg (s, _, _, y, _) -> Set.of_list (module Term) (List.map (s::y) ~f:(fun v -> Term.dummy_var v))
    | Top (s, _, _, y, _) -> Set.of_list (module Term) (List.map (s@y) ~f:(fun v -> Term.dummy_var v))
    | Predicate (_, trms) -> Set.of_list (module Term) trms
    | Exists (x, f) | Forall (x, f) ->
       let filter y = not (List.mem (Term.fv_list [y]) x ~equal:Var.equal_ident) in
       Set.filter (terms f) ~f:filter
    | Predicate' (_, _, f)
      | Let (_, _, _, _, f)
      | Let' (_, _, _, _, f)
      | Neg f
      | Prev (_, f)
      | Once (_, f)
      | Historically (_, f)
      | Eventually (_, f)
      | Always (_, f)
      | Next (_, f)
      | Type (f, _)
      | Label (_, f) -> terms f
    | And (_, fs)
      | Or (_, fs) -> Set.union_list (module Term) (List.map fs ~f:terms)
    | Imp (_, f1, f2)
      | Since (_, _, f1, f2)
      | Until (_, _, f1, f2) -> Set.union (terms f1) (terms f2)

  let rec predicates ?(lets=Map.empty (module String)) f = match f.form with
    | TT
      | FF
      | EqConst _ -> Set.empty (module String)
    | Predicate (r, trms) -> Option.value ~default:(Set.singleton (module String) r) (Map.find lets r)
    | Let (r, _, _, f, g) -> predicates ~lets:(Map.update lets r ~f:(fun _ -> predicates ~lets f)) g
    | Predicate' (_, _, f)
      | Let' (_, _, _, _, f)
      | Neg f 
      | Exists (_, f)
      | Forall (_, f)
      | Prev (_, f)
      | Next (_, f)
      | Once (_, f)
      | Eventually (_, f)
      | Historically (_, f)
      | Always(_, f) 
      | Agg (_, _, _, _, f)
      | Top (_, _, _, _, f)
      | Type (f, _)
      | Label (_, f) -> predicates ~lets f
    | Imp (_, f, g)
      | Since (_, _, f, g)
      | Until (_, _, f, g) -> Set.union (predicates ~lets f) (predicates ~lets g)
    | And (_, fs)
      | Or (_, fs) -> Set.union_list (module String) (List.map fs ~f:(predicates ~lets))

  let merge_maps =
    Map.merge ~f:(fun ~key -> function
        | `Both (t, u) -> Some (Enftype.join t u)
        | `Left t -> Some t
        | `Right t -> Some t)

  let merge_all_maps =
    List.fold_left ~init:(Map.empty (module String)) ~f:merge_maps

  let rec typed_predicates ?(lets=Map.empty (module String)) f =
    match f.form with
    | TT
      | FF
      | EqConst _ -> Map.empty (module String)
    | Predicate (r, trms) -> Option.value ~default:(Map.singleton (module String) r f.info.enftype) (Map.find lets r)
    | Let (r, _, _, f, g) -> typed_predicates ~lets:(Map.update lets r ~f:(fun _ -> typed_predicates ~lets f)) g
    | Predicate' (_, _, f)
      | Let' (_, _, _, _, f)
      | Neg f 
      | Exists (_, f)
      | Forall (_, f)
      | Prev (_, f)
      | Next (_, f)
      | Once (_, f)
      | Eventually (_, f)
      | Historically (_, f)
      | Always(_, f) 
      | Agg (_, _, _, _, f)
      | Top (_, _, _, _, f)
      | Type (f, _)
      | Label (_, f) -> typed_predicates ~lets f
    | Imp (_, f, g)
      | Since (_, _, f, g)
      | Until (_, _, f, g) -> merge_maps (typed_predicates ~lets f) (typed_predicates ~lets g)
    | And (_, fs)
      | Or (_, fs) -> merge_all_maps (List.map ~f:(typed_predicates ~lets) fs)
          
  (*Set.union_list (module String) (List.map fs ~f:(predicates ~lets))*)

  let rec deg f = match f.form with
    | TT
      | FF
      | EqConst _ 
      | Predicate _ -> 2
    | Predicate' (_, _, f)
      | Let' (_, _, _, _, f)
      | Neg f 
      | Exists (_, f)
      | Forall (_, f)
      | Prev (_, f)
      | Next (_, f)
      | Once (_, f)
      | Eventually (_, f)
      | Historically (_, f)
      | Always (_, f)
      | Type (f, _)
      | Label (_, f)
      | Agg (_, _, _, _, f)
      | Top (_, _, _, _, f)
      | Let (_, _, _, _, f) -> deg f
    | Imp (_, f, g)
      | Since (_, _, f, g)
      | Until (_, _, f, g) -> max 2 (max (deg f) (deg g))
    | And (_, fs)
      | Or (_, fs) -> List.fold_left (List.map fs ~f:deg) ~init:1 ~f:max

  let rec size f = match f.form with
    | TT
      | FF -> 1
    | EqConst (t, _) -> 1 + Term.size t
    | Predicate (_, ts) -> 1 + List.fold ~f:(+) ~init:0 (List.map ~f:Term.size ts)
    | Predicate' (_, _, f)
      | Let' (_, _, _, _, f) -> size f
    | Neg f 
      | Exists (_, f)
      | Forall (_, f)
      | Prev (_, f)
      | Next (_, f)
      | Once (_, f)
      | Eventually (_, f)
      | Historically (_, f)
      | Always (_, f)
      | Type (f, _)
      | Label (_, f)
      | Agg (_, _, _, _, f)
      | Top (_, _, _, _, f) -> 1 + size f
    | Imp (_, f, g)
      | Since (_, _, f, g)
      | Until (_, _, f, g)
      | Let (_, _, _, f, g) -> 1 + size f + size g
    | And (_, fs)
    | Or (_, fs) -> 1 + List.fold_left ~f:(+) ~init:0 (List.map ~f:size fs)

  let rec height f = match f.form with
    | TT
    | FF 
    | EqConst _ 
    | Predicate _ -> 1
    | Predicate' (_, _, f)
      | Let' (_, _, _, _, f) -> size f
    | Neg f 
      | Exists (_, f)
      | Forall (_, f)
      | Prev (_, f)
      | Next (_, f)
      | Once (_, f)
      | Eventually (_, f)
      | Historically (_, f)
      | Always (_, f)
      | Type (f, _)
      | Label (_, f)
      | Agg (_, _, _, _, f)
      | Top (_, _, _, _, f) -> 1 + size f
    | Imp (_, f, g)
      | Since (_, _, f, g)
      | Until (_, _, f, g)
      | Let (_, _, _, f, g) -> 1 + size f + size g
    | And (_, fs)
      | Or (_, fs) -> 1 + List.fold_left ~f:(+) ~init:0 (List.map ~f:size fs)

  let rec exists_subformula ~f_term ~f_fun f =
    f_fun f || begin
        match f.form with
        | TT
          | FF -> false
        | EqConst (t, _) -> f_term t
        | Predicate (_, ts) -> List.exists ~f:f_term ts
        | Predicate' (_, _, f)
          | Let' (_, _, _, _, f) -> exists_subformula ~f_term ~f_fun f
        | Neg f 
          | Exists (_, f)
          | Forall (_, f)
          | Prev (_, f)
          | Next (_, f)
          | Once (_, f)
          | Eventually (_, f)
          | Historically (_, f)
          | Always (_, f)
          | Type (f, _)
          | Label (_, f)
          | Agg (_, _, _, _, f)
          | Top (_, _, _, _, f)
          | Let (_, _, _, _, f) -> exists_subformula ~f_term ~f_fun f
        | Imp (_, f, g)
          | Since (_, _, f, g)
          | Until (_, _, f, g) -> exists_subformula ~f_term ~f_fun f || exists_subformula ~f_term ~f_fun g
        | And (_, fs)
          | Or (_, fs) -> List.exists ~f:(exists_subformula ~f_term ~f_fun) fs
    end

  (* Functional constructors *)

  let tt = TT
  let ff = FF
  let eqconst x d = EqConst (x, d)
  let agg s op x y f = Agg (s, op, x, y, f)
  let assign s x f = Agg (s, Aggregation.AAssign, x, Set.elements (fv f), f)
  let top s op x y f = Top (s, op, x, y, f)
  let predicate p_name trms = Predicate (p_name, trms)
  let flet r enftype vars f g = Let (r, Option.value ~default:Enftype.obs enftype, vars, f, g)
  let neg f = Neg f
  let conj s f g = And (s, [f; g])
  let disj s f g = Or (s, [f; g])
  let conjs s fs = And (s, fs)
  let disjs s fs = Or (s, fs)
  let imp s f g = Imp (s, f, g)
  let exists x f = Exists (x, f)
  let forall x f = Forall (x, f)
  let prev i f = Prev (i, f)
  let next i f = Next (i, f)
  let once i f = Once (i, f)
  let eventually i f = Eventually (i, f)
  let historically i f = Historically (i, f)
  let always i f = Always (i, f)
  let since s i f g = Since (s, i, f, g)
  let until s i f g = Until (s, i, f, g)
  let ftype f ty = Type (f, ty)
  let label s f = Label (s, f)

  (* Function constructors for non-native operators *)

  let term t = eqconst t (Dom.bool_tt)
  let iff s t f g impl_info impr_info = conj N { form = imp s f g; info = impl_info } { form = imp t g f; info = impr_info }
  let trigger s i f g f_info g_info outer_info = neg ({ form = since s i { form = neg f; info = f_info } { form = neg g; info = g_info }; info = outer_info })
  let release s i f g f_info g_info outer_info = neg ({ form = until s i { form = neg f; info = f_info } { form = neg g; info = g_info }; info = outer_info })

  let make form info = { form; info }

  let make_dummy form = make form Info.dummy

  (* Substitution of free variables by terms as specified in mapping v *)

  let subst_var v s =
    match Map.find v s with
    | Some trm ->
       (match Term.unvar_opt trm with
        | Some z -> Var.replace z s
        | None ->
           raise (FormulaError (
                      Printf.sprintf "cannot substitute non-variable term %s for aggregation variable %s"
                        (Term.to_string trm) (Var.to_string s))))
    | None -> s

  let subst_vars v s = List.map ~f:(subst_var v) s
  
  let rec subst v ff =
    let form = match ff.form with
      | TT | FF -> ff.form
      | EqConst (trm, c) -> EqConst (Term.subst v trm, c)
      | Agg (s, op, t, y, f) ->
         (*Stdio.print_endline (String.concat ~sep:"," (List.map ~f:Var.to_string y));
         Stdio.print_endline (String.concat ~sep:"," (List.map ~f:Var.to_string (subst_vars v y)));*)
         Agg (subst_var v s, op, Term.subst v t, subst_vars v y, subst v f)
      | Top (s, op, t, y, f) -> Top (subst_vars v s, op, Term.substs v t, subst_vars v y, subst v f)
      | Predicate (r, trms) -> Predicate (r, Term.substs v trms)
      | Predicate' (r, trms, f) -> Predicate' (r, Term.substs v trms, subst v f)
      | Exists (x, f) -> Exists (x, subst (Map.remove v x) f)
      | Forall (x, f) -> Forall (x, subst (Map.remove v x) f)
      | Let (r, enftype, vars, f, g) ->
         let filter x = not (List.mem (List.map ~f:fst vars) x ~equal:Var.equal_ident) in
         Let (r, enftype, vars, f, subst (Map.filter_keys v ~f:filter) g)
      | Let' (r, enftype, vars, f, g) -> Let' (r, enftype, vars, f, subst v g)
      | Neg f -> Neg (subst v f)
      | Prev (i, f) -> Prev (i, subst v f)
      | Once (i, f) -> Once (i, subst v f)
      | Historically (i, f) -> Historically (i, subst v f)
      | Eventually (i, f) -> Eventually (i, subst v f)
      | Always (i, f) -> Always (i, subst v f)
      | Next (i, f) -> Next (i, subst v f)
      | And (s, fs) -> And (s, List.map fs ~f:(subst v))
      | Or (s, fs) -> Or (s, List.map fs ~f:(subst v))
      | Imp (s, f1, f2) -> Imp (s, subst v f1, subst v f2)
      | Since (s, i, f1, f2) -> Since (s, i, subst v f1, subst v f2)
      | Until (s, i, f1, f2) -> Until (s, i, subst v f1, subst v f2)
      | Type (f, ty) -> Type (subst v f, ty)
      | Label (s, f) -> Label (s, subst v f) in
    { ff with form }

  (* Substitution of predicates, depending on polarity *)
  let rec map_predicate ~f ?(pol=true) ff =
    let m = map_predicate ~f in
    let form = match ff.form with
      | TT | FF | EqConst _ -> ff.form
      | Agg (s, op, t, y, f) -> Agg (s, op, t, y, m ~pol f)
      | Top (s, op, t, y, f) -> Top (s, op, t, y, m ~pol f)
      | Predicate (r, trms) -> Predicate (f pol r, trms)
      | Predicate' (r, trms, f') -> Predicate' (f pol r, trms, m ~pol f')
      | Exists (x, f) -> Exists (x, m ~pol f)
      | Forall (x, f) -> Forall (x, m ~pol f)
      | Let (r, enftype, vars, f, g) -> Let (r, enftype, vars, m ~pol f, m ~pol g)
      | Let' (r, enftype, vars, f, g) -> Let' (r, enftype, vars, m ~pol f, m ~pol g)
      | Neg f -> Neg (m ~pol:(not pol) f)
      | Prev (i, f) -> Prev (i, m ~pol f)
      | Once (i, f) -> Once (i, m ~pol f)
      | Historically (i, f) -> Historically (i, m ~pol f)
      | Eventually (i, f) -> Eventually (i, m ~pol f)
      | Always (i, f) -> Always (i, m ~pol f)
      | Next (i, f) -> Next (i, m ~pol f)
      | And (s, fs) -> And (s, List.map fs ~f:(m ~pol))
      | Or (s, fs) -> Or (s, List.map fs ~f:(m ~pol))
      | Imp (s, f1, f2) -> Imp (s, m ~pol:(not pol) f1, m ~pol f2)
      | Since (s, i, f1, f2) -> Since (s, i, m ~pol f1, m ~pol f2)
      | Until (s, i, f1, f2) -> Until (s, i, m ~pol f1, m ~pol f2)
      | Type (f, ty) -> Type (m ~pol f, ty)
      | Label (s, f) -> Label (s, m ~pol f) in
    { ff with form }

  (* Mapping of constants in terms *)

  let rec map_consts ~f (ff : t) : t =
    let map_consts_multiple = List.map ~f:(Term.map_consts ~f) in
    let form = match ff.form with
      | TT | FF -> ff.form
      | EqConst (trm, c) -> EqConst (Term.map_consts ~f trm, f c)
      | Agg (s, op, t, y, f') ->
         (*Stdio.print_endline (String.concat ~sep:"," (List.map ~f:Var.to_string y));
         Stdio.print_endline (String.concat ~sep:"," (List.map ~f:Var.to_string (subst_vars v y)));*)
         Agg (s, op, Term.map_consts ~f t, y, map_consts ~f f')
      | Top (s, op, t, y, f') -> Top (s, op, map_consts_multiple t, y, map_consts ~f f')
      | Predicate (r, trms) -> Predicate (r, map_consts_multiple trms)
      | Predicate' (r, trms, f') -> Predicate' (r, map_consts_multiple trms, map_consts ~f f')
      | Exists (x, f') -> Exists (x, map_consts ~f f')
      | Forall (x, f') -> Forall (x, map_consts ~f f')
      | Let (r, enftype, vars, f', g) -> Let (r, enftype, vars, map_consts ~f f', map_consts ~f g)
      | Let' (r, enftype, vars, f', g) -> Let' (r, enftype, vars, map_consts ~f f', map_consts ~f g)
      | Neg f' -> Neg (map_consts ~f f')
      | Prev (i, f') -> Prev (i, map_consts ~f f')
      | Once (i, f') -> Once (i, map_consts ~f f')
      | Historically (i, f') -> Historically (i, map_consts ~f f')
      | Eventually (i, f') -> Eventually (i, map_consts ~f f')
      | Always (i, f') -> Always (i, map_consts ~f f')
      | Next (i, f') -> Next (i, map_consts ~f f')
      | And (s, fs) -> And (s, List.map fs ~f:(map_consts ~f))
      | Or (s, fs) -> Or (s, List.map fs ~f:(map_consts ~f))
      | Imp (s, f1, f2) -> Imp (s, map_consts ~f f1, map_consts ~f f2)
      | Since (s, i, f1, f2) -> Since (s, i, map_consts ~f f1, map_consts ~f f2)
      | Until (s, i, f1, f2) -> Until (s, i, map_consts ~f f1, map_consts ~f f2)
      | Type (f', ty) -> Type (map_consts ~f f', ty) 
      | Label (s, f') -> Label (s, map_consts ~f f') in
    { ff with form }

  (* Printing *)

  let op_to_string f = match f.form with
    | TT -> Printf.sprintf "⊤"
    | FF -> Printf.sprintf "⊥"
    | EqConst (_, _) -> Printf.sprintf "="
    | Predicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
    | Predicate' (r, trms, _) -> Printf.sprintf "%s٭(%s)" r (Term.list_to_string trms)
    | Let (r, _, _, _, _) -> Printf.sprintf "LET %s" r
    | Let' (r, _, _, _, _) -> Printf.sprintf "LET٭ %s" r
    | Agg (_, op, x, y, _) -> Printf.sprintf "%s(%s; %s)" (Aggregation.op_to_string op) (Term.value_to_string x)
                                (String.concat ~sep:", " (List.map ~f:Var.to_string y))
    | Top (_, op, x, y, _) -> Printf.sprintf "%s(%s; %s)" op (Term.list_to_string x) (String.concat ~sep:", " (List.map ~f:Var.to_string y))
    | Neg _ -> Printf.sprintf "¬"
    | And (_, _) -> Printf.sprintf "∧"
    | Or (_, _) -> Printf.sprintf "∨"
    | Imp (_, _, _) -> Printf.sprintf "→"
    | Exists (x, _) -> Printf.sprintf "∃ %s." (Var.to_string x)
    | Forall (x, _) -> Printf.sprintf "∀ %s." (Var.to_string x)
    | Prev (i, _) -> Printf.sprintf "●%s" (Interval.to_string i)
    | Next (i, _) -> Printf.sprintf "○%s" (Interval.to_string i)
    | Once (i, _) -> Printf.sprintf "⧫%s" (Interval.to_string i)
    | Eventually (i, _) -> Printf.sprintf "◊%s" (Interval.to_string i)
    | Historically (i, _) -> Printf.sprintf "■%s" (Interval.to_string i)
    | Always (i, _) -> Printf.sprintf "□%s" (Interval.to_string i)
    | Since (_, i, _, _) -> Printf.sprintf "S%s" (Interval.to_string i)
    | Until (_, i, _, _) -> Printf.sprintf "U%s" (Interval.to_string i)
    | Type _ -> Printf.sprintf ":"
    | Label (s, _) -> Printf.sprintf "{%s}" s

  let string_of_opt_typed_var = function
    | (s, None) -> Var.to_string s
    | (s, Some tt) -> Printf.sprintf "%s : %s" (Var.to_string s) (Dom.tt_to_string tt)

  let latex_of_opt_typed_var = function
    | (s, None) -> Var.to_string s
    | (s, Some tt) -> Printf.sprintf "%s : %s" (Var.to_latex s) (Dom.tt_to_string tt)
 
  let to_string_core_rec to_string_rec l f =
    match f with
    | TT -> Printf.sprintf "⊤"
    | FF -> Printf.sprintf "⊥"
    | EqConst (trm, c) ->
       Printf.sprintf (Etc.paren l 40 "(%s) = %s")
         (Term.value_to_string trm) (Dom.to_string c)
    | Predicate (r, trms) ->
       Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
    | Predicate' (r, trms, _) ->
       Printf.sprintf "%s٭(%s)" r (Term.list_to_string trms)
    | Let (r, enftype, vars, f, g) ->
       Printf.sprintf (Etc.paren l 4 "LET %s(%s)%s = %a IN %a") r
         (Etc.string_list_to_string (List.map ~f:string_of_opt_typed_var vars))
         (Enftype.to_string_let enftype)
         (fun _ -> to_string_rec 4) f
         (fun _ -> to_string_rec 4) g
    | Let' (r, enftype, vars, f, g) ->
       Printf.sprintf (Etc.paren l 4 "LET %s٭(%s)%s = %a IN %a")
         r (Etc.string_list_to_string (List.map ~f:string_of_opt_typed_var vars))
         (Enftype.to_string_let enftype)
         (fun _ -> to_string_rec 4) f
         (fun _ -> to_string_rec 4) g
    | Agg (s, Aggregation.AAssign, x, _, f) ->
       Printf.sprintf (Etc.paren l 5 "%s; %s <- %s")
         (to_string_rec 5 f) (Var.to_string s)
         (Term.value_to_string x)
    | Agg (s, op, x, y, f) ->
       Printf.sprintf (Etc.paren l 5 "%s <- %s(%s; %s; %s)")
         (Var.to_string s) (Aggregation.op_to_string op)
         (Term.value_to_string x) (String.concat ~sep:", " (List.map ~f:Var.to_string y))
         (to_string_rec 5 f)
    | Top (s, op, x, y, f) ->
       Printf.sprintf (Etc.paren l 5 "[%s] <- %s([%s]; %s; %s)")
         (String.concat ~sep:", " (List.map ~f:Var.to_string s)) op
         (Term.list_to_string x) (String.concat ~sep:", " (List.map ~f:Var.to_string y))
         (to_string_rec 5 f)
    | Neg f ->
       Printf.sprintf (Etc.paren l 55 "¬%a")
         (fun _ -> to_string_rec 55) f
    | And (s, fs) ->
       Printf.sprintf (Etc.paren l 50 "%s")
         (String.concat ~sep:(" ∧" ^ Side.to_string s ^ " ")
            (List.map ~f:(to_string_rec 50) fs))
    | Or (s, fs) ->
       Printf.sprintf (Etc.paren l 40 "%s")
         (String.concat ~sep:(" ∨" ^ Side.to_string s ^ " ")
            (List.map ~f:(to_string_rec 40) fs))
    | Imp (s, f, g) ->
       Printf.sprintf (Etc.paren l 30 "%a →%a %a")
         (fun _ -> to_string_rec 30) f
         (fun _ -> Side.to_string) s
         (fun _ -> to_string_rec 30) g
    | Exists (x, f) ->
       Printf.sprintf (Etc.paren l 6 "∃%a. %a")
         (fun _ -> Var.to_string) x
         (fun _ -> to_string_rec 6) f
    | Forall (x, f) ->
       Printf.sprintf (Etc.paren l 6 "∀%a. %a")
         (fun _ -> Var.to_string) x
         (fun _ -> to_string_rec 6) f
    | Prev (i, f) ->
       Printf.sprintf (Etc.paren l 50 "●%a %a")
         (fun _ -> Interval.to_string) i
         (fun _ -> to_string_rec 50) f
    | Next (i, f) ->
       Printf.sprintf (Etc.paren l 50 "○%a %a")
         (fun _ -> Interval.to_string) i
         (fun _ -> to_string_rec 50) f
    | Once (i, f) ->
       Printf.sprintf (Etc.paren l 50 "⧫%a %a")
         (fun _ -> Interval.to_string) i
         (fun _ -> to_string_rec 50) f
    | Eventually (i, f) ->
       Printf.sprintf (Etc.paren l 50 "◊%a %a")
         (fun _ -> Interval.to_string) i
         (fun _ -> to_string_rec 50) f
    | Historically (i, f) ->
       Printf.sprintf (Etc.paren l 50 "■%a %a")
         (fun _ -> Interval.to_string) i
         (fun _ -> to_string_rec 50) f
    | Always (i, f) ->
       Printf.sprintf (Etc.paren l 50 "□%a %a")
         (fun _ -> Interval.to_string) i
         (fun _ -> to_string_rec 50) f
    | Since (s, i, f, g) ->
       Printf.sprintf (Etc.paren l 45 "%a S%a%a %a")
         (fun _ -> to_string_rec 45) f
         (fun _ -> Interval.to_string) i
         (fun _ -> Side.to_string) s
         (fun _ -> to_string_rec 45) g
    | Until (s, i, f, g) ->
       Printf.sprintf (Etc.paren l 45 "%a U%a%a %a")
         (fun _ -> to_string_rec 45) f
         (fun _ -> Interval.to_string) i
         (fun _ -> Side.to_string) s
         (fun _ -> to_string_rec 45) g
    | Type (f, ty) ->
       Printf.sprintf (Etc.paren l 0 "%a : %s")
         (fun _ -> to_string_rec 0) f
         (Enftype.to_string ty)
    | Label (s, f) ->
       Printf.sprintf "{\"%s\"}{%a}" s
         (fun _ -> to_string_rec 0) f

  let rec to_string_rec l f =
    Info.to_string l (to_string_core_rec to_string_rec l f.form) f.info

  let rec to_string_typed_rec l f =
    TypedInfo.to_string l (to_string_core_rec to_string_typed_rec l f.form) f.info

  let to_string = to_string_rec 0
  let to_string_typed = to_string_typed_rec 0

  let rec to_string_value_rec l (f: ('i, Var.t, Dom.t, Term.t) _t)  =
    match f.form with
    | TT -> Printf.sprintf "⊤"
    | FF -> Printf.sprintf "⊥"
    | EqConst (trm, c) ->
       Printf.sprintf (Etc.paren l 40 "(%s) = %s")
         (Term.value_to_string trm) (Dom.to_string c)
    | Predicate (r, trms) ->
       Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
    | Predicate' (r, trms, _) ->
       Printf.sprintf "%s٭(%s)" r (Term.list_to_string trms)
    | Let (r, enftype, vars, f, g) ->
       Printf.sprintf (Etc.paren l 4 "LET %s(%s)%s = %a IN %a") r
         (Etc.string_list_to_string (List.map ~f:string_of_opt_typed_var vars))
         (Enftype.to_string_let enftype)
         (fun _ -> to_string_value_rec 4) f
         (fun _ -> to_string_value_rec 4) g
    | Let' (r, enftype, vars, f, g) ->
       Printf.sprintf (Etc.paren l 4 "LET %s٭(%s)%s = %a IN %a")
         r (Etc.string_list_to_string (List.map ~f:string_of_opt_typed_var vars))
         (Enftype.to_string_let enftype)
         (fun _ -> to_string_value_rec 4) f
         (fun _ -> to_string_value_rec 4) g
    | Agg (s, Aggregation.AAssign, x, _, f) ->
       Printf.sprintf (Etc.paren l 5 "%s; %s <- %s")
         (to_string_value_rec 5 f) (Var.to_string s)
         (Term.value_to_string x)
    | Agg (s, op, x, y, f) ->
       Printf.sprintf (Etc.paren l 5 "%s <- %s(%s; %s; %s)")
         (Var.to_string s) (Aggregation.op_to_string op)
         (Term.value_to_string x) (String.concat ~sep:", " (List.map ~f:Var.to_string y))
         (to_string_value_rec 5 f)
    | Top (s, op, x, y, f) ->
       Printf.sprintf (Etc.paren l 5 "[%s] <- %s([%s]; %s; %s)")
         (String.concat ~sep:", " (List.map ~f:Var.to_string s)) op
         (Term.list_to_string x) (String.concat ~sep:", " (List.map ~f:Var.to_string y))
         (to_string_value_rec 5 f)
    | Neg f ->
       Printf.sprintf (Etc.paren l 55 "¬%a")
         (fun _ -> to_string_value_rec 55) f
    | And (s, fs) ->
       Printf.sprintf (Etc.paren l 50 "%s")
         (String.concat ~sep:(" ∧" ^ Side.to_string s ^ " ")
            (List.map ~f:(to_string_value_rec 50) fs))
    | Or (s, fs) ->
       Printf.sprintf (Etc.paren l 40 "%s")
         (String.concat ~sep:(" ∨" ^ Side.to_string s ^ " ")
            (List.map ~f:(to_string_value_rec 40) fs))
    | Imp (s, f, g) ->
       Printf.sprintf (Etc.paren l 30 "%a →%a %a")
         (fun _ -> to_string_value_rec 30) f
         (fun _ -> Side.to_string) s
         (fun _ -> to_string_value_rec 30) g
    | Exists (x, f) ->
       Printf.sprintf (Etc.paren l 6 "∃%a. %a")
         (fun _ -> Var.to_string) x
         (fun _ -> to_string_value_rec 6) f
    | Forall (x, f) ->
       Printf.sprintf (Etc.paren l 6 "∀%a. %a")
         (fun _ -> Var.to_string) x
         (fun _ -> to_string_value_rec 6) f
    | Prev (i, f) ->
       Printf.sprintf (Etc.paren l 50 "●%a %a")
         (fun _ -> Interval.to_string) i
         (fun _ -> to_string_value_rec 50) f
    | Next (i, f) ->
       Printf.sprintf (Etc.paren l 50 "○%a %a")
         (fun _ -> Interval.to_string) i
         (fun _ -> to_string_value_rec 50) f
    | Once (i, f) ->
       Printf.sprintf (Etc.paren l 50 "⧫%a %a")
         (fun _ -> Interval.to_string) i
         (fun _ -> to_string_value_rec 50) f
    | Eventually (i, f) ->
       Printf.sprintf (Etc.paren l 50 "◊%a %a")
         (fun _ -> Interval.to_string) i
         (fun _ -> to_string_value_rec 50) f
    | Historically (i, f) ->
       Printf.sprintf (Etc.paren l 50 "■%a %a")
         (fun _ -> Interval.to_string) i
         (fun _ -> to_string_value_rec 50) f
    | Always (i, f) ->
       Printf.sprintf (Etc.paren l 50 "□%a %a")
         (fun _ -> Interval.to_string) i
         (fun _ -> to_string_value_rec 50) f
    | Since (s, i, f, g) ->
       Printf.sprintf (Etc.paren l 45 "%a S%a%a %a")
         (fun _ -> to_string_value_rec 45) f
         (fun _ -> Interval.to_string) i
         (fun _ -> Side.to_string) s
         (fun _ -> to_string_value_rec 45) g
    | Until (s, i, f, g) ->
       Printf.sprintf (Etc.paren l 45 "%a U%a%a %a")
         (fun _ -> to_string_value_rec 45) f
         (fun _ -> Interval.to_string) i
         (fun _ -> Side.to_string) s
         (fun _ -> to_string_value_rec 45) g
    | Type (f, ty) ->
       Printf.sprintf (Etc.paren l 0 "%a : %s")
         (fun _ -> to_string_value_rec 0) f
         (Enftype.to_string ty)
    | Label (s, f) ->
       Printf.sprintf "{\"%s\"}{%a}" s
         (fun _ -> to_string_value_rec 0) f

  let to_string_value f = to_string_value_rec 0 f

  let to_latex_core_rec to_latex_rec l f =
    match f with
    | TT -> Printf.sprintf "\\bot"
    | FF -> Printf.sprintf "\\top"
    | EqConst (trm, c) ->
       Printf.sprintf (Etc.paren l 40 "%s \\approx %s")
         (Term.value_to_latex trm) (Dom.to_latex c)
    | Predicate (r, trms) ->
       Printf.sprintf "\\mathsf{%s}(%s)"
         (Etc.latex_string r)
         (Term.list_to_latex trms)
    | Predicate' (r, trms, _) ->
       Printf.sprintf "\\mathsf{%s}^\\star(%s)"
         (Etc.latex_string r)
         (Term.list_to_latex trms)
    | Let (r, enftype, vars, f, g) ->
       Printf.sprintf (Etc.paren l 4 "\\llet\\,\\mathsf{%s}(%s)\\texttt{%s} = %a\\,\\iin\\,%a")
         (Etc.latex_string r)
         (Etc.string_list_to_string (List.map ~f:latex_of_opt_typed_var vars))
         (Enftype.to_string_let enftype)
         (fun _ -> to_latex_rec 4) f
         (fun _ -> to_latex_rec 4) g
    | Let' (r, enftype, vars, f, g) ->
       Printf.sprintf (Etc.paren l 4 "\\llet\\,\\mathsf{%s}^\\star(%s)%s = %a\\,\\iin\\,%a")
         (Etc.latex_string r)
         (Etc.string_list_to_string (List.map ~f:latex_of_opt_typed_var vars))
         (Enftype.to_string_let enftype)
         (fun _ -> to_latex_rec 4) f
         (fun _ -> to_latex_rec 4) g
    | Agg (s, op, x, y, f) ->
       Printf.sprintf (Etc.paren l 5 "%s \\gets \\mathtt{%s}(%s; %s; %s)")
         (Var.to_latex s)
         (Aggregation.op_to_string op)
         (Term.value_to_latex x) (String.concat ~sep:", " (List.map ~f:Var.to_latex y))
         (to_latex_rec 5 f)
    | Top (s, op, x, y, f) ->
       Printf.sprintf (Etc.paren l 5 "[%s] \\gets \\mathtt{%s}([%s]; %s; %s)")
         (String.concat ~sep:", " (List.map ~f:Var.to_latex s))
         (Etc.latex_string op)
         (Term.list_to_string x) (String.concat ~sep:", " (List.map ~f:Var.to_latex y))
         (to_latex_rec 5 f)
    | Neg f ->
       Printf.sprintf (Etc.paren l 55 "\\neg%a")
         (fun _ -> to_latex_rec 55) f
    | And (s, fs) ->
       Printf.sprintf (Etc.paren l 50 "%s")
         (String.concat ~sep:(" \\land" ^ Side.to_string s ^ " ")
            (List.map ~f:(to_latex_rec 50) fs))
    | Or (s, fs) ->
       Printf.sprintf (Etc.paren l 40 "%s")
         (String.concat ~sep:(" \\lor" ^ Side.to_string s ^ " ")
            (List.map ~f:(to_latex_rec 40) fs))
    | Imp (s, f, g) ->
       Printf.sprintf (Etc.paren l 30 "%a \\Rightarrow%a %a")
         (fun _ -> to_latex_rec 30) f
         (fun _ -> Side.to_string) s
         (fun _ -> to_latex_rec 30) g
    | Exists (x, f) ->
       Printf.sprintf (Etc.paren l 6 "\\exists%a.~%a")
         (fun _ -> Var.to_latex) x
         (fun _ -> to_latex_rec 6) f
    | Forall (x, f) ->
       Printf.sprintf (Etc.paren l 6 "\\forall%a.~%a")
         (fun _ -> Var.to_latex) x
         (fun _ -> to_latex_rec 6) f
    | Prev (i, f) ->
       Printf.sprintf (Etc.paren l 50 "\\Prev_{%a} %a")
         (fun _ -> Interval.to_latex) i
         (fun _ -> to_latex_rec 50) f
    | Next (i, f) ->
       Printf.sprintf (Etc.paren l 50 "\\Next_{%a} %a")
         (fun _ -> Interval.to_latex) i
         (fun _ -> to_latex_rec 50) f
    | Once (i, f) ->
       Printf.sprintf (Etc.paren l 50 "\\Once_{%a} %a")
         (fun _ -> Interval.to_latex) i
         (fun _ -> to_latex_rec 50) f
    | Eventually (i, f) ->
       Printf.sprintf (Etc.paren l 50 "\\Eventually_{%a} %a")
         (fun _ -> Interval.to_latex) i
         (fun _ -> to_latex_rec 50) f
    | Historically (i, f) ->
       Printf.sprintf (Etc.paren l 50 "\\PGlobally_{%a} %a")
         (fun _ -> Interval.to_latex) i
         (fun _ -> to_latex_rec 50) f
    | Always (i, f) ->
       Printf.sprintf (Etc.paren l 50 "\\Always_{%a} %a")
         (fun _ -> Interval.to_latex) i
         (fun _ -> to_latex_rec 50) f
    | Since (s, i, f, g) ->
       Printf.sprintf (Etc.paren l 45 "%a \\Since_{%a}%a %a")
         (fun _ -> to_latex_rec 45) f
         (fun _ -> Interval.to_latex) i
         (fun _ -> Side.to_string) s
         (fun _ -> to_latex_rec 45) g
    | Until (s, i, f, g) ->
       Printf.sprintf (Etc.paren l 45 "%a \\UUntil_{%a}%a %a")
         (fun _ -> to_latex_rec 45) f
         (fun _ -> Interval.to_latex) i
         (fun _ -> Side.to_string) s
         (fun _ -> to_latex_rec 45) g
    | Type (f, ty) ->
       Printf.sprintf (Etc.paren l 0 "%a : %s")
         (fun _ -> to_latex_rec 0) f
         (Enftype.to_string ty)
    | Label (s, f) ->
       Printf.sprintf "\\{\"%s\"\\}\\{%a\\}" s
         (fun _ -> to_string_rec 0) f
       
  let rec to_latex_rec l f =
    Info.to_string l (to_latex_core_rec to_latex_rec l f.form) f.info

  let to_latex = to_latex_rec 0

  let rec to_json t = match t.form with
    | TT -> "{ \"constructor\": \"TT\" }"
    | FF -> "{ \"constructor\": \"FF\" }"
    | EqConst (term, dom) -> 
      Printf.sprintf "{ \"constructor\": \"EqConst\", \"term\": %s, \"const\": %s }"
        (Term.to_json term) (Dom.to_json dom)
    | Predicate (name, terms) -> 
      Printf.sprintf "{ \"constructor\": \"Predicate\", \"name\": \"%s\", \"args\": [%s] }"
        name (String.concat ~sep:", " (List.map terms ~f:Term.to_json))
    | Predicate' (name, terms, phi) -> 
      Printf.sprintf "{ \"constructor\": \"Predicate'\", \"name\": \"%s\", \"args\": [%s], \"formula\": %s }"
        name (String.concat ~sep:", " (List.map terms ~f:Term.to_json)) (to_json phi)
    | Let (name, typ, bindings, phi1, phi2) -> 
      Printf.sprintf
        "{ \"constructor\": \"Let\", \"name\": \"%s\", \"type\": \"%s\", \"bindings\": [%s], \"body\": %s, \"in\": %s }"
        name (Enftype.to_string typ)
        (String.concat ~sep:", " (List.map bindings ~f:(fun (v, opt_d) -> Printf.sprintf "\"%s\"" (Var.to_string v))))
        (to_json phi1) (to_json phi2)
    | Let' (name, typ, bindings, phi1, phi2) -> 
      Printf.sprintf
        "{ \"constructor\": \"Let'\", \"name\": \"%s\", \"type\": \"%s\", \"bindings\": [%s], \"body\": %s, \"in\": %s }"
        name (Enftype.to_string typ)
        (String.concat ~sep:", " (List.map bindings ~f:(fun (v, opt_d) -> Printf.sprintf "\"%s\"" (Var.to_string v))))
        (to_json phi1) (to_json phi2)
    | Agg (v, op, term, vars, phi) -> 
      Printf.sprintf
        "{ \"constructor\": \"Agg\", \"var\": \"%s\", \"op\": \"%s\", \"term\": %s, \"group_by\": [%s], \"formula\": %s }"
        (Var.to_string v) (Aggregation.op_to_string op) (Term.to_json term)
        (String.concat ~sep:", " (List.map vars ~f:(fun v -> Printf.sprintf "\"%s\"" (Var.to_string v))))
        (to_json phi)
    | Top (vars1, name, terms, vars2, phi) -> 
      Printf.sprintf
        "{ \"constructor\": \"Top\", \"vars\": [%s], \"name\": \"%s\", \"terms\": [%s], \"group_by\": [%s], \"formula\": %s }"
        (String.concat ~sep:", " (List.map vars1 ~f:(fun v -> Printf.sprintf "\"%s\"" (Var.to_string v))))
        name
        (String.concat ~sep:", " (List.map terms ~f:Term.to_json))
        (String.concat ~sep:", " (List.map vars2 ~f:(fun v -> Printf.sprintf "\"%s\"" (Var.to_string v))))
        (to_json phi)
    | Neg phi -> 
      Printf.sprintf "{ \"constructor\": \"Neg\", \"arg\": %s }" (to_json phi)
    | And (side, phis) -> 
      Printf.sprintf "{ \"constructor\": \"And\", \"side\": \"%s\", \"args\": [%s] }"
        (Side.to_string side) (String.concat ~sep:", " (List.map phis ~f:to_json))
    | Or (side, phis) -> 
      Printf.sprintf "{ \"constructor\": \"Or\", \"side\": \"%s\", \"args\": [%s] }"
        (Side.to_string side) (String.concat ~sep:", " (List.map phis ~f:to_json))
    | Imp (side, phi1, phi2) -> 
      Printf.sprintf "{ \"constructor\": \"Imp\", \"side\": \"%s\", \"left\": %s, \"right\": %s }"
        (Side.to_string side) (to_json phi1) (to_json phi2)
    | Exists (v, phi) -> 
      Printf.sprintf "{ \"constructor\": \"Exists\", \"var\": \"%s\", \"formula\": %s }"
        (Var.to_string v) (to_json phi)
    | Forall (v, phi) -> 
      Printf.sprintf "{ \"constructor\": \"Forall\", \"var\": \"%s\", \"formula\": %s }"
        (Var.to_string v) (to_json phi)
    | Prev (intv, phi) -> 
      Printf.sprintf "{ \"constructor\": \"Prev\", \"interval\": %s, \"formula\": %s }"
        (Interval.to_json intv) (to_json phi)
    | Next (intv, phi) -> 
      Printf.sprintf "{ \"constructor\": \"Next\", \"interval\": %s, \"formula\": %s }"
        (Interval.to_json intv) (to_json phi)
    | Once (intv, phi) -> 
      Printf.sprintf "{ \"constructor\": \"Once\", \"interval\": %s, \"formula\": %s }"
        (Interval.to_json intv) (to_json phi)
    | Eventually (intv, phi) -> 
      Printf.sprintf "{ \"constructor\": \"Eventually\", \"interval\": %s, \"formula\": %s }"
        (Interval.to_json intv) (to_json phi)
    | Historically (intv, phi) -> 
      Printf.sprintf "{ \"constructor\": \"Historically\", \"interval\": %s, \"formula\": %s }"
        (Interval.to_json intv) (to_json phi)
    | Always (intv, phi) -> 
      Printf.sprintf "{ \"constructor\": \"Always\", \"interval\": %s, \"formula\": %s }"
        (Interval.to_json intv) (to_json phi)
    | Since (side, intv, phi1, phi2) -> 
      Printf.sprintf "{ \"constructor\": \"Since\", \"side\": \"%s\", \"interval\": %s, \"left\": %s, \"right\": %s }"
        (Side.to_string side) (Interval.to_json intv) (to_json phi1) (to_json phi2)
    | Until (side, intv, phi1, phi2) -> 
      Printf.sprintf "{ \"constructor\": \"Until\", \"side\": \"%s\", \"interval\": %s, \"left\": %s, \"right\": %s }"
        (Side.to_string side) (Interval.to_json intv) (to_json phi1) (to_json phi2)
    | Type (phi, typ) -> 
      Printf.sprintf "{ \"constructor\": \"Type\", \"formula\": %s, \"type\": \"%s\" }"
        (to_json phi) (Enftype.to_string typ)
    | Label (label, phi) -> 
      Printf.sprintf "{ \"constructor\": \"Label\", \"label\": \"%s\", \"formula\": %s }"
        label (to_json phi)

  (* Generates EXISTS x1, ..., xk. f where {x1, ..., xk} are the free variables of f not in y  *)

  let exists_of_agg y f info =
    (*print_endline ("exists_of_agg " ^ to_string f);*)
    let z = List.filter (list_fv f) ~f:(fun x -> not (List.mem y x ~equal:Var.equal_ident)) in
    (*print_endline ("-> " ^ to_string (List.fold_right z ~f:(fun z f -> { form = Exists (z, f); info = info z f }) ~init:f));*)
    List.fold_right z ~f:(fun z f -> { form = Exists (z, f); info = info z f }) ~init:f

  (* Unrolling of let bindings *)

  let unroll_let ?(moderate=true) =
    let is_linear (trms: Term.t list) =
      not (List.exists trms ~f:Term.is_const)
      && Int.equal (List.length (Etc.dedup ~equal:Term.equal trms)) (List.length trms) in
    let rec aux (v : (string, bool * Var.t list * t, String.comparator_witness) Map.t) f =
      let form = match f.form with
        | TT -> TT
        | FF -> FF
        | EqConst (x, c) -> EqConst (x, c)
        | Predicate (r, trms) ->
           (match Map.find v r with
             | None -> Predicate (r, trms) (* Not a let-bound predicate: do not unroll *)
             | Some (false, vars, e) -> (* Must unroll because of definition of let binding *)
               Predicate' (r, trms, subst (Map.of_alist_exn (module Var) (List.zip_exn vars trms)) e)
             | Some (true, _, _) when is_linear trms -> (* Let-bound predicate with linear pattern: do not unroll *)
               Predicate (r, trms)
             | Some (true, vars, e) -> (* Let-bound predicate with non-linear pattern: must unroll *)
               Predicate' (r, trms, subst (Map.of_alist_exn (module Var) (List.zip_exn vars trms)) e))
        | Let (r, enftype, vars, f, g) ->
          let v' b = Map.update v r ~f:(fun _ -> (b, List.map ~f:fst vars, aux v f)) in
          (* Do not unroll if: moderate is false OR binding is trivial OR there are captured variables *)
          (if moderate && height f > 1
              && Set.is_subset (fv f)
                (Set.of_list (module Var) (List.map ~f:fst vars)) then
             Let (r, enftype, vars, aux v f, aux (v' true) g)
          else
             Let' (r, enftype, vars, aux v f, aux (v' false) g))
        | Agg (s, op, x, y, f) -> Agg (s, op, x, y, aux v f)
        | Top (s, op, x, y, f) -> Top (s, op, x, y, aux v f)
        | Neg f -> Neg (aux v f)
        | And (s, fs) -> And (s, List.map ~f:(aux v) fs)
        | Or (s, fs) -> Or (s, List.map ~f:(aux v) fs)
        | Imp (s, f, g) -> Imp (s, aux v f, aux v g)
        | Exists (x, f) -> Exists (x, aux v f)
        | Forall (x, f) -> Forall (x, aux v f)
        | Prev (i, f) -> Prev (i, aux v f)
        | Next (i, f) -> Next (i, aux v f)
        | Once (i, f) -> Once (i, aux v f)
        | Eventually (i, f) -> Eventually (i, aux v f)
        | Historically (i, f) -> Historically (i, aux v f)
        | Always (i, f) -> Always (i, aux v f)
        | Since (s, i, f, g) -> Since (s, i, aux v f, aux v g)
        | Until (s, i, f, g) -> Until (s, i, aux v f, aux v g)
        | Type (f, ty) -> Type (aux v f, ty)
        | Label (s, f) -> Label (s, aux v f)
        | Predicate' _ | Let' _ -> raise (FormulaError ("Cannot unroll Predicate' or Let'"))
      in { f with form }
    in aux (Map.empty (module String))

  let rec unprime f =
    let form = match f.form with
      | TT -> TT
      | FF -> FF
      | EqConst (x, c) -> EqConst (x, c)
      | Predicate (r, trms) -> Predicate (r, trms)
      | Let (r, enftype, vars, f, g) -> Let (r, enftype, vars, unprime f, unprime g)
      | Agg (s, op, x, y, f) -> Agg (s, op, x, y, unprime f)
      | Top (s, op, x, y, f) -> Top (s, op, x, y, unprime f)
      | Neg f -> Neg (unprime f)
      | And (s, fs) -> And (s, List.map ~f:unprime fs)
      | Or (s, fs) -> Or (s, List.map ~f:unprime fs)
      | Imp (s, f, g) -> Imp (s, unprime f, unprime g)
      | Exists (x, f) -> Exists (x, unprime f)
      | Forall (x, f) -> Forall (x, unprime f)
      | Prev (i, f) -> Prev (i, unprime f)
      | Next (i, f) -> Next (i, unprime f)
      | Once (i, f) -> Once (i, unprime f)
      | Eventually (i, f) -> Eventually (i, unprime f)
      | Historically (i, f) -> Historically (i, unprime f)
      | Always (i, f) -> Always (i, unprime f)
      | Since (s, i, f, g) -> Since (s, i, unprime f, unprime g)
      | Until (s, i, f, g) -> Until (s, i, unprime f, unprime g)
      | Type (f, ty) -> Type (unprime f, ty)
      | Label (_, f) -> (unprime f).form
      | Let' (_, _, _, _, g)
        | Predicate' (_, _, g) -> (unprime g).form 
    in { f with form }

  (* Erasure of labels *)

  let erase_label =
     let rec aux f =
      let form = match f.form with
        | TT -> TT
        | FF -> FF
        | EqConst (x, c) -> EqConst (x, c)
        | Predicate (r, trms) -> Predicate (r, trms)
        | Let (r, enftype, vars, f, g) -> Let (r, enftype, vars, aux f, aux g)
        | Agg (s, op, x, y, f) -> Agg (s, op, x, y, aux f)
        | Top (s, op, x, y, f) -> Top (s, op, x, y, aux f)
        | Neg f -> Neg (aux f)
        | And (s, fs) -> And (s, List.map ~f:(aux) fs)
        | Or (s, fs) -> Or (s, List.map ~f:(aux) fs)
        | Imp (s, f, g) -> Imp (s, aux f, aux g)
        | Exists (x, f) -> Exists (x, aux f)
        | Forall (x, f) -> Forall (x, aux f)
        | Prev (i, f) -> Prev (i, aux f)
        | Next (i, f) -> Next (i, aux f)
        | Once (i, f) -> Once (i, aux f)
        | Eventually (i, f) -> Eventually (i, aux f)
        | Historically (i, f) -> Historically (i, aux f)
        | Always (i, f) -> Always (i, aux f)
        | Since (s, i, f, g) -> Since (s, i, aux f, aux g)
        | Until (s, i, f, g) -> Until (s, i, aux f, aux g)
        | Type (f, ty) -> Type (aux f, ty)
        | Label (_, f) -> (aux f).form
        | Predicate' (r, trms, f) -> Predicate' (r, trms, aux f)
        | Let' (r, enftype, trms, f, g) -> Let' (r, enftype, trms, aux f, aux g)
      in { f with form }
    in aux

  (* Alpha-convert vars to remove shadowing *)

  let convert_vars f =
    let return f i v = f, (i, v) in
    let (>>|) func fi i v = let f, (i, v) = fi i v in func f, (i, v) in
    let (>>=) func fi i v = let f, (i, v) = fi i v in let g, (i, v) = func f i v in g, (i, v) in
    let name x k = Printf.sprintf "%s.%d" x k in
    let fresh (i, v) x =
      let xk, k = match Map.find i x with
        | Some k -> name (Var.ident x) (k+1), k+1
        | None -> (Var.ident x), 0 in
      let xk = Var.replace (Var.of_ident xk) x in
      (Map.update i x ~f:(fun _ -> k), (Map.update v x ~f:(fun _ -> Term.dummy_var xk))), xk in
    (*let vv = Var.of_ident "v" in*)
    (*let var_subst v x = match Map.find v x with Some (Term.Var x) -> x | _ -> x in
      let vars_subst v xs = List.map xs ~f:(var_subst v) in*)
    let rec aux f i v =
      let g = match f.form with
        | TT -> return TT 
        | FF -> return FF
        | EqConst (x, c) -> return (EqConst (Term.subst v x, c))
        | Predicate (r, trms) -> return (Predicate (r, Term.substs v trms))
        | Predicate' (r, trms, f) ->
           (fun f -> return (Predicate' (r, Term.substs v trms, f))) >>= (aux f)
           (*let process_trm (i, v) trm = match Term.unvar_opt trm with
             | Some x -> let (i, v), xk = fresh (i, v) x  in (i, v), (xk, None)
             | None   -> let (i, v), xk = fresh (i, v) vv in (i, v), (xk, Some trm) in
           (fun i v -> let (i, v), trms' = List.fold_map trms ~init:(i, v) ~f:process_trm in
                       let e f = function (xk, Some trm) -> make_dummy (exists xk (make_dummy (assign xk trm f))) | _ -> f in
                       let q f = List.fold_left trms' ~init:f ~f:e in
                       ((fun f -> return (Predicate' (r, Term.substs v trms, q f))) >>= (aux f)) i v)*)
        | Let (r, enftype, vars, f, g) ->
          (*(fun i v -> let (i, v'), vars = List.fold_map vars ~init:(i, v) ~f:(fun a (v, x) -> let a, v = fresh a v in (a, (v, x))) in
                       let f, (i, _) = aux f i v' in
                       ((fun g -> return (Let (r, enftype, vars, f, g))) >>= (aux g)) i v)*)
          (fun i v -> let (i, v'), vars = List.fold_map vars ~init:(i, v) ~f:(fun a (v, x) -> let a, v = fresh a v in (a, (v, x))) in
                       let f, (i, _) = aux f i v' in
                       ((fun f -> (fun g -> return (Let (r, enftype, vars, f, g))) >>= (aux g)) >>= (aux f)) i v)
        | Let' (r, enftype, vars, f, g) ->
           (fun i v -> let (i, v'), vars = List.fold_map vars ~init:(i, v) ~f:(fun a (v, x) -> let a, v = fresh a v in (a, (v, x))) in
                       let f, (i, _) = aux f i v' in
                       ((fun g -> return (Let' (r, enftype, vars, f, g))) >>= (aux g)) i v)
        | Agg (s, op, x, y, f) ->
           (fun i v -> (*let x = Term.subst v x in
                       let y = subst_vars v y in*)
                       let fvs = Set.elements (Set.diff (fv f) (Set.of_list (module Var) ((Term.fv_list [x])@y))) in
                       let (i, v'), _ = List.fold_map fvs ~init:(i, v) ~f:fresh in
                       ((fun f -> return (Agg (subst_var v s, op, Term.subst v' x, subst_vars v' y, f)))
                        >>= (aux f)) i v')
        | Top (s, op, x, y, f) ->
           (fun i v -> (*let x = Term.substs v x in
                       let y = subst_vars v y in*)
                       let fvs = Set.elements (Set.diff (fv f) (Set.of_list (module Var) ((Term.fv_list x) @y))) in
                       let (i, v'), _ = List.fold_map fvs ~init:(i, v) ~f:fresh in
                       ((fun f -> return (Top (subst_vars v s, op, Term.substs v' x, subst_vars v' y, f)))
                        >>= (aux f)) i v')
        | Neg f -> (fun f -> return (Neg f)) >>= (aux f)
        (*| And (s, f, g) ->
          (fun f -> (fun g -> return (And (s, f, g))) >>= (aux v g)) >>= (aux v f)*)
        | And (s, fs) ->
           (List.fold_left
              ~init:(fun fs -> return (And (s, fs)))
              ~f:(fun g f fs -> (fun f -> g (f :: fs)) >>= (aux f)) fs) []
        (*| Or (s, fs) -> (fun f -> (fun g -> return (Or (s, f, g))) >>= (aux v g)) >>= (aux v f)*)
        | Or (s, fs) ->
           (List.fold_left
              ~init:(fun fs -> return (Or (s, fs)))
              ~f:(fun g f fs -> (fun f -> g (f :: fs)) >>= (aux f)) fs) []
        | Imp (s, f, g) -> (fun f -> (fun g -> return (Imp (s, f, g))) >>= (aux g)) >>= (aux f)
        | Exists (x, f) -> (fun i v -> let (i, v), xk = fresh (i, v) x in
                                       ((fun f -> return (Exists (Var.replace xk x, f))) >>= (aux f)) i v)
        | Forall (x, f) -> (fun i v -> let (i, v), xk = fresh (i, v) x in
                                       ((fun f -> return (Forall (Var.replace xk x, f))) >>= (aux f)) i v)
        | Prev (i, f) -> (fun f -> Prev (i, f)) >>| (aux f)
        | Next (i, f) -> (fun f -> Next (i, f)) >>| (aux f)
        | Once (i, f) -> (fun f -> Once (i, f)) >>| (aux f)
        | Eventually (i, f) -> (fun f -> Eventually (i, f)) >>| (aux f)
        | Historically (i, f) -> (fun f -> Historically (i, f)) >>| (aux f)
        | Always (i, f) -> (fun f -> Always (i, f)) >>| (aux f)
        | Since (s, i, f, g) -> (fun f -> (fun g -> return (Since (s, i, f, g))) >>= (aux g)) >>= (aux f)
        | Until (s, i, f, g) -> (fun f -> (fun g -> return (Until (s, i, f, g))) >>= (aux g)) >>= (aux f)
        | Type (f, ty) -> (fun f -> return (Type (f, ty))) >>= (aux f)
        | Label (s, f) -> (fun f -> return (Label (s, f))) >>= (aux f)
      in let form, b = g i v in
         (*Stdio.print_endline (to_string f);
         Stdio.print_endline (Etc.list_to_string "" (fun _ (var, term) -> Var.to_string var ^ " -> " ^ Term.to_string term) (Map.to_alist v));
         Stdio.print_endline (Etc.list_to_string "" (fun _ (var, i) -> Var.to_string var ^ " -> " ^ Int.to_string i) (Map.to_alist i));
         Stdio.print_endline ("-> " ^ to_string { f with form } ^ "\n");*)
         { f with form }, b
    in fst (aux f (Map.empty (module Var)) (Map.empty (module Var)))

  (* Pull quantifiers after temporal operators -- to be used after alpha-conversion *)

  let rec all_exists form = match form.form with
    | Exists (x, f) -> let xs, forms = all_exists f in x :: xs, f :: forms
    | _ -> [], []

  let rec destruct_quants form = match form.form with
    | Exists (x, f) -> let xs, bs, fs = destruct_quants f in x :: xs, false :: bs, f :: fs
    | Forall (x, f) -> let xs, bs, fs = destruct_quants f in x :: xs, true  :: bs, f :: fs
    | _ -> [], [], []

  let rec construct_quants xs bs fs f =
    match xs, bs, fs with
    | [], [], [] -> f
    | x :: xs, true  :: bs, f' :: fs -> Forall (x, { f' with form = construct_quants xs bs fs f })
    | x :: xs, false :: bs, f' :: fs -> Exists (x, { f' with form = construct_quants xs bs fs f })

  let rec destruct_nexts form = match form.form with
    | Next (i, f) -> let is, fs = destruct_nexts f in i :: is, f :: fs
    | _ -> [], []

  let rec construct_nexts is fs f =
    match is, fs with
    | [], [] -> f
    | i :: is, f' :: fs -> Next (i, { f' with form = construct_nexts is fs f })

  let push_negs f =
    let rec aux p f =
      let form = match f.form with
        | TT -> if p then TT else FF
        | FF -> if p then FF else TT
        | EqConst _
        | Predicate _
        | Predicate' _ -> if p then f.form else Neg f
        | Let (r, enftype, vars, f, g) -> Let (r, enftype, vars, aux true f, aux p g)
        | Let' (r, enftype, vars, f, g) -> Let' (r, enftype, vars, aux true f, aux p g)
        | Agg (s, op, x, y, f) -> let form = Agg (s, op, x, y, aux true f) in if p then Neg { f with form } else f.form
        | Top (s, op, x, y, f) -> let form = Top (s, op, x, y, aux true f) in if p then Neg { f with form } else f.form
        | Neg f -> (aux (not p) f).form
        | And (s, fs) -> if p then And (s, List.map ~f:(aux true) fs) else Or (s, List.map ~f:(aux false) fs)
        | Or (s, fs) -> if p then Or (s, List.map ~f:(aux true) fs) else And (s, List.map ~f:(aux false) fs)
        | Imp (s, f, g) -> if p then Imp (s, aux true f, aux true g) else And (s, [aux true f; aux false g])
        | Exists (x, f) ->
          if p then Exists (x, aux true f) else Neg ({ f with form = Exists (x, aux true f) })
              (*if p then Exists (x, aux true f) else Forall (x, aux false f)*)
        | Forall (x, f) ->
          if p then Forall (x, aux true f) else Neg ({ f with form = Forall (x, aux true f) })
              (*if p then Forall (x, aux true f) else Exists (x, aux false f)*)
        | Prev (i, f) -> let f' = aux true f in if p then Prev (i, f') else Neg { f with form = Prev (i, f') }
        | Next (i, f) -> let f' = aux true f in if p then Next (i, f') else Neg { f with form = Next (i, f') }
        | Once (i, f) -> let f' = aux true f in if p then Once (i, f') else Neg { f with form = Once (i, f') }
        | Eventually (i, f) -> if p then Eventually (i, aux true f) else Always (i, aux false f)
        | Historically (i, f) -> if p then Historically (i, aux true f) else Once (i, aux false f)
        | Always (i, f) -> if p then Always (i, aux true f) else Eventually (i, aux false f)
        | Since (s, i, f, g) ->
          if p then Since (s, i, aux true f, aux true g)
          else Neg ({ f with form = Since (s, i, aux true f, aux true g) })
        | Until (s, i, f, g) ->
          if p then Until (s, i, aux true f, aux true g)
          else Neg ({ f with form = Until (s, i, aux true f, aux true g) })
        | Type (f, ty) -> if p then Type (aux true f, ty) else Type (aux false f, Enftype.neg ty)
        | Label (s, f) -> Label (s, aux p f)
      in { f with form } 
    in aux true f

  let push_quants f =
    let rec add_quants f = function
      | [] -> f
      | (true, x) :: quants -> Forall (x, make_dummy (add_quants f quants))
      | (false, x) :: quants -> Exists (x, make_dummy (add_quants f quants)) in
    let sort_quants quants fs = 
      let (quants_global, quants_one, _, _) =
        List.fold_right quants ~init:([], [], true, None)
          ~f:(fun (b, x) (quants_global, quants_one, continue, b_opt) ->
              let b_opt = Some (Option.value b_opt ~default:b) in
              if continue && Bool.equal (Option.value_exn b_opt) b then (
                let c = List.count fs ~f:(fun f -> Set.mem (fv f) x) in
                match c with
                | 0 -> (quants_global, quants_one, true, b_opt)
                | 1 -> (quants_global, (b, x) :: quants_one, true, b_opt)
                | _ -> ((b, x) :: quants_global, quants_one, true, b_opt)
              )
              else ((b, x) :: quants_global, quants_one, false, b_opt)) in
      quants_global, quants_one in
    let rec add_relevant_quants (quants: (bool * Var.t) list) f =
      let vars = fvs [f] in
      let relevant_quants = List.filter quants ~f:(fun (_, x) -> Set.mem vars x) in
      aux relevant_quants f 
    and aux (quants: (bool * Var.t) list) f =
      let form = match f.form with
        | TT
        | FF
        | EqConst _
        | Predicate _
        | Predicate' _ -> add_quants f.form quants
        | Let (r, enftype, vars, f, g) -> Let (r, enftype, vars, aux [] f, aux quants g)
        | Let' (r, enftype, vars, f, g) -> Let' (r, enftype, vars, aux [] f, aux quants g)
        | Agg (s, op, x, y, f) -> add_quants (Agg (s, op, x, y, aux [] f)) quants
        | Top (s, op, x, y, f) -> add_quants (Top (s, op, x, y, aux [] f)) quants
        | Neg f ->
          Neg (aux (List.map ~f:(fun (b, x) -> (not b, x)) quants) f)
        | And (s, fs) ->
          let quants_global, quants_one = sort_quants quants fs in
          let fs = List.map ~f:(add_relevant_quants quants_one) fs in
          add_quants (And (s, fs)) quants_global
        | Or (s, fs) ->
          let quants_global, quants_one = sort_quants quants fs in
          let fs = List.map ~f:(add_relevant_quants quants_one) fs in
          add_quants (Or (s, fs)) quants_global
        | Imp (s, f, g) ->
          let quants_global, quants_one = sort_quants quants [f; g] in
          let quants_one_neg = List.map ~f:(fun (b, x) -> (not b, x)) quants_one in
          let f = add_relevant_quants quants_one_neg f in
          let g = add_relevant_quants quants_one g in
          add_quants (Imp (s, f, g)) quants_global
        | Exists (x, f) -> (aux (quants @ [(false, x)]) f).form
        | Forall (x, f) -> (aux (quants @ [(true, x)]) f).form
        | Prev (i, f) -> add_quants (Prev (i, aux [] f)) quants
        | Next (i, f) -> add_quants (Next (i, aux [] f)) quants
        | Once (i, f) -> add_quants (Once (i, aux [] f)) quants
        | Eventually (i, f) -> add_quants (Eventually (i, aux [] f)) quants
        | Historically (i, f) -> add_quants (Historically (i, aux [] f)) quants
        | Always (i, f) -> add_quants (Always (i, aux [] f)) quants
        | Since (s, i, f, g) -> add_quants (Since (s, i, aux [] f, aux [] g)) quants
        | Until (s, i, f, g) -> add_quants (Until (s, i, aux [] f, aux [] g)) quants
        | Type (f, ty) -> Type (aux quants f, ty)
        | Label (s, f) -> Label (s, aux quants f)
      in let r = { f with form } in
      (*print_endline (Printf.sprintf "push_quants([%s], %s) = %s"
                       (String.concat ~sep:", " (List.map quants ~f:(fun (b, x) -> Bool.to_string b ^ "/" ^ Var.to_string x)))
                       (to_string f) (to_string r));*)
      r
           
    in aux [] f

  

  (* Alpha-convert let bindings to remove shadowing *)

  let convert_lets f =
    let return f i = f, i in
    let (>>|) func fi i = let f, i = fi i in func f, i in
    let (>>=) func fi i = let f, i = fi i in let g, i = func f i in g, i in
    let name x k = Printf.sprintf "%s.%d" x k in
    let fresh i r v =
      let rk, k = match Map.find i r with Some k -> name r (k+1), k+1 | None -> r, 0 in
      (Map.update i r ~f:(fun _ -> k)), (rk, (Map.update v r ~f:(fun _ -> rk))) in
    let rec aux v f i =
      let g = match f.form with
        | TT -> return TT
        | FF -> return FF
        | EqConst (x, c) -> return (EqConst (x, c))
        | Predicate (r, trms) ->
           return (Predicate (Option.value (Map.find v r) ~default:r, trms))
        | Predicate' (r, trms, f) ->
           (fun f -> return (Predicate' (Option.value (Map.find v r) ~default:r, trms, f))) >>= (aux v f)
        | Let (r, enftype, vars, f, g) ->
           (fun i -> let i, (rk, v) = fresh i r v in
                     ((fun f -> (fun g -> return (Let (rk, enftype, vars, f, g))) >>= (aux v g))>>= (aux v f)) i)
        | Let' (r, enftype, vars, f, g) ->
           (fun i -> let i, (rk, v) = fresh i r v in
                     ((fun f -> (fun g -> return (Let' (rk, enftype, vars, f, g))) >>= (aux v g)) >>= (aux v f)) i)
        | Agg (s, op, x, y, f) -> (fun f -> return (Agg (s, op, x, y, f))) >>= (aux v f)
        | Top (s, op, x, y, f) -> (fun f -> return (Top (s, op, x, y, f))) >>= (aux v f)
        | Neg f -> (fun f -> return (Neg f)) >>= (aux v f)
        (*| And (s, f, g) -> (fun f -> (fun g -> return (And (s, f, g))) >>= (aux v g)) >>= (aux v f)*)
        | And (s, fs) ->
           (List.fold_left
              ~init:(fun fs -> return (And (s, fs)))
              ~f:(fun g f fs -> (fun f -> g (f :: fs)) >>= (aux v f)) fs) []
        (*| Or (s, f, g) -> (fun f -> (fun g -> return (Or (s, f, g))) >>= (aux v g)) >>= (aux v f)*)
        | Or (s, fs) ->
           (List.fold_left
              ~init:(fun fs -> return (Or (s, fs)))
              ~f:(fun g f fs -> (fun f -> g (f :: fs)) >>= (aux v f)) fs) []
        | Imp (s, f, g) -> (fun f -> (fun g -> return (Imp (s, f, g))) >>= (aux v g)) >>= (aux v f)
        | Exists (x, f) -> (fun f -> Exists (x, f)) >>| (aux v f)
        | Forall (x, f) -> (fun f -> Forall (x, f)) >>| (aux v f)
        | Prev (i, f) -> (fun f -> Prev (i, f)) >>| (aux v f)
        | Next (i, f) -> (fun f -> Next (i, f)) >>| (aux v f)
        | Once (i, f) -> (fun f -> Once (i, f)) >>| (aux v f)
        | Eventually (i, f) -> (fun f -> Eventually (i, f)) >>| (aux v f)
        | Historically (i, f) -> (fun f -> Historically (i, f)) >>| (aux v f)
        | Always (i, f) -> (fun f -> Always (i, f)) >>| (aux v f)
        | Since (s, i, f, g) -> (fun f -> (fun g -> return (Since (s, i, f, g))) >>= (aux v g)) >>= (aux v f)
        | Until (s, i, f, g) -> (fun f -> (fun g -> return (Until (s, i, f, g))) >>= (aux v g)) >>= (aux v f)
        | Type (f, ty) -> (fun f -> Type (f, ty)) >>| (aux v f)
        | Label (s, f) -> (fun f -> Label (s, f)) >>| (aux v f)
      in let form, b = g i in { f with form }, b
    in fst (aux (Map.empty (module String)) f (Map.empty (module String)))

  let pull_lets f =
    let rec map1 f p = let f, flets = aux f in p f, flets 
    and map2 f g p = let f, flets = aux f and g, glets = aux g in p f g, flets @ glets 
    and mapn fs p = let l = List.map ~f:aux fs in p (List.map ~f:fst l), List.concat_map ~f:snd l 
    and aux f : t * 'a list =
      let form, flets =
        match f.form with
        | TT
        | FF
        | EqConst _ 
        | Predicate _
        | Predicate' _ ->
          f.form, []
        | Let (r, enftype, vars, f, g) -> 
          let f, flets = aux f in
          let g, glets = aux g in
          g.form, flets @ (r, enftype, vars, f) :: glets
        | Let' (r, enftype, vars, f, g) -> map1 g (fun g -> Let' (r, enftype, vars, f, g))
        | Agg (s, op, x, y, f) -> map1 f (fun f -> Agg (s, op, x, y, f))
        | Top (s, op, x, y, f) -> map1 f (fun f -> Top (s, op, x, y, f))
        | Neg f -> map1 f (fun f -> Neg f)
        | And (s, fs) -> mapn fs (fun fs -> And (s, fs))
        | Or (s, fs) -> mapn fs (fun fs -> Or (s, fs))
        | Imp (s, f, g) -> map2 f g (fun f g -> Imp (s, f, g))
        | Exists (x, f) -> map1 f (fun f -> Exists (x, f))
        | Forall (x, f) -> map1 f (fun f -> Forall (x, f))
        | Prev (i, f) -> map1 f (fun f -> Prev (i, f))
        | Next (i, f) -> map1 f (fun f -> Next (i, f))
        | Once (i, f) -> map1 f (fun f -> Once (i, f))
        | Eventually (i, f) -> map1 f (fun f -> Eventually (i, f))
        | Historically (i, f) -> map1 f (fun f -> Historically (i, f))
        | Always (i, f) -> map1 f (fun f -> Always (i, f))
        | Since (s, i, f, g) -> map2 f g (fun f g -> Since (s, i, f, g))
        | Until (s, i, f, g) -> map2 f g (fun f g -> Until (s, i, f, g))
        | Type (f, ty) -> map1 f (fun f -> Type (f, ty))
        | Label (s, f) -> map1 f (fun f -> Label (s, f))
      in { f with form }, flets 
    in
    let init, flets = aux f in
    let f (r, enftype, vars, f) g = { g with form = Let (r, enftype, vars, f, g) } in
    List.fold_right ~f ~init flets

  (* AC-rewriting *)
  
  let rec ac_simplify_core =
    let unpr' f = match f.form with Predicate' (_, _, f) -> f.form | _ -> f.form in
    let or_bool f g = match unpr' f with TT -> TT | FF -> FF | _ -> g f in
    function
    | TT -> TT
    | FF -> FF
    | EqConst (x, v) -> EqConst (x, v)
    | Predicate (e, t) -> Predicate (e, t)
    | Predicate' (e, t, f) -> Predicate' (e, t, ac_simplify f)
    | Let (r, enftype_opt, vars, f, g) -> Let (r, enftype_opt, vars, ac_simplify f, ac_simplify g)
    | Let' (r, enftype_opt, vars, f, g) -> Let' (r, enftype_opt, vars, ac_simplify f, ac_simplify g)
    | Agg (s, op, x, y, f) -> Agg (s, op, x, y, ac_simplify f)
    | Top (s, op, x, y, f) -> Top (s, op, x, y, ac_simplify f)
    | Neg { form = Neg f } -> (ac_simplify f).form
    | Neg f ->
      let f = ac_simplify f in
      (match unpr' f with TT -> FF | FF -> TT | _ -> Neg f)
    | And (s, fs) -> 
       let fs = List.map fs ~f:ac_simplify in
       let f fs f' = match unpr' f' with
         | And (s', fs') when Side.equal s s' -> fs @ fs'
         | TT -> fs
         | _ -> fs @ [f'] in
       let fs = List.fold_left fs ~init:[] ~f in
       if List.exists fs ~f:(fun f' -> match unpr' f' with FF -> true | _ -> false)
       then FF
       else if List.is_empty fs then TT
       else if List.length fs = 1 then (List.hd_exn fs).form
       else And (s, fs)
    | Or (s, fs) ->
       let fs = List.map fs ~f:ac_simplify in
       let f fs f' = match unpr' f' with
         | Or (s', fs') when Side.equal s s' -> fs @ fs'
         | FF -> fs
         | _ -> fs @ [f'] in
       let fs = List.fold_left fs ~init:[] ~f in
       if List.exists fs ~f:(fun f' -> match unpr' f' with TT -> true | _ -> false)
       then TT
       else if List.is_empty fs then FF
       else if List.length fs = 1 then (List.hd_exn fs).form
       else Or (s, fs)
    | Imp (s, f, g) ->
      let f = ac_simplify f in
      let g = ac_simplify g in
      (match unpr' f, unpr' g with
       | FF, _ | _, TT -> TT
       | TT, FF -> FF
       | TT, _ -> g.form
       | _, FF -> Neg f
       | _, _ -> Imp (s, f, g))
    | Exists (x, f) ->
      or_bool (ac_simplify f) (fun f -> Exists (x, f))
    | Forall (x, f) ->
      or_bool (ac_simplify f) (fun f -> Forall (x, f))
    | Prev (i, f) -> Prev (i, ac_simplify f)
    | Next (i, f) -> Next (i, ac_simplify f)
    | Once (i, f) ->
      let f = ac_simplify f in
      (match unpr' f with
       | FF -> FF
       | TT when Interval.has_zero i -> TT
       | _ -> Once (i, f))
    | Eventually (i, f) ->
      let f = ac_simplify f in
      (match unpr' f with
       | FF -> FF
       | TT when Interval.has_zero i -> TT
       | _ -> Eventually (i, f))
    | Historically (i, f) ->
      let f = ac_simplify f in
      (match unpr' f with
       | FF when Interval.has_zero i -> FF
       | TT -> TT
       | _ -> Historically (i, f))
    | Always (i, f) ->
      let f = ac_simplify f in
      (match unpr' f with
       | FF when Interval.has_zero i -> FF
       | TT -> TT
       | _ -> Always (i, f))
    | Since (s, i, f, g) ->
      let f = ac_simplify f in
      let g = ac_simplify g in
      (match unpr' f, unpr' g with
       | _, FF -> FF
       | FF, g -> g
       | TT, TT when Interval.has_zero i -> TT
       | TT, _ -> Once (i, g)
       | _, _ -> Since (s, i, f, g))
    | Until (s, i, f, g) ->
      let f = ac_simplify f in
      let g = ac_simplify g in
      (match unpr' f, unpr' g with
       | _, FF -> FF
       | FF, g -> g
       | TT, TT when Interval.has_zero i -> TT
       | TT, _ -> Eventually (i, g)
       | _, _ -> Until (s, i, f, g))
    | Type (f, ty) -> or_bool (ac_simplify f) (fun f -> Type (f, ty))
    | Label (s, f) -> or_bool (ac_simplify f) (fun f -> Label (s, f))

  and ac_simplify f =
    { f with form = ac_simplify_core f.form }
      
  (* Simplify formulae *)

  let rec simplify_core = function
    | TT -> TT
    | FF -> FF
    | EqConst (x, v) ->
      (match Term.unconst_opt x with
       | Some d when Dom.equal v d -> TT
       | Some _ -> FF
       | None -> EqConst (x, v))
    | Predicate (e, t) -> Predicate (e, t)
    | Predicate' (e, t, f) -> Predicate' (e, t, simplify f)
    | Let (r, enftype_opt, vars, f, g) -> Let (r, enftype_opt, vars, simplify f, simplify g)
    | Let' (r, enftype_opt, vars, f, g) -> Let' (r, enftype_opt, vars, simplify f, simplify g)
    | Agg (s, op, x, y, f) -> Agg (s, op, x, y, simplify f)
    | Top (s, op, x, y, f) -> Top (s, op, x, y, simplify f)
    | Neg f -> Neg (simplify f)
    | And (s, fs) -> And (s, List.map ~f:simplify fs)
    | Or (s, fs) -> Or (s, List.map ~f:simplify fs)
    | Imp (s, f, g) -> Imp (s, simplify f, simplify g)
    | Exists (x, f) -> Exists (x, simplify f)
    | Forall (x, f) -> Forall (x, simplify f)
    | Prev (i, f) -> Prev (i, simplify f)
    | Next (i, f) -> Next (i, simplify f)
    | Once (i, f) -> Once (i, simplify f)
    | Eventually (i, f) -> Eventually (i, simplify f)
    | Historically (i, f) -> Historically (i, simplify f)
    | Always (i, f) -> Always (i, simplify f)
    | Since (s, i, f, g) -> Since (s, i, simplify f, simplify g)
    | Until (s, i, f, g) -> Until (s, i, simplify f, simplify g)
    | Type (f, ty) -> Type (simplify f, ty)
    | Label (s, f) -> Label (s, simplify f)

  and simplify f =
    { f with form = simplify_core f.form }

  (* Relative interval *)
  
  let rec relative_interval ?(itl_itvs=Map.empty (module String)) f =
    let relative_interval' = relative_interval in
    let relative_interval = relative_interval ~itl_itvs in
    let i = 
      match f.form with
      | TT | FF | EqConst (_, _) -> Zinterval.singleton (Zinterval.Z.zero)
      | Predicate (r, _) ->
         begin match Map.find itl_itvs r with
         | Some i -> i
         | None -> Zinterval.singleton 0
         end
      | Neg f | Exists (_, f) | Forall (_, f) | Agg (_, _, _, _, f)
        | Top (_, _, _, _, f) | Predicate' (_, _, f) | Let' (_, _, _, _, f) | Type (f, _) | Label (_, f)
        -> relative_interval f
      | Imp (_, f1, f2)
        -> Zinterval.lub (relative_interval f1) (relative_interval f2)
      | And (_, f :: fs) | Or (_, f :: fs)
        -> List.fold ~init:(relative_interval f) ~f:(fun i g -> Zinterval.lub i (relative_interval g)) fs
      | And (_, []) | Or (_, []) -> Zinterval.singleton (Zinterval.Z.zero)
      | Prev (i, f) | Once (i, f) | Historically (i, f)
        -> let i' = Zinterval.inv (Zinterval.of_interval i) in
           Zinterval.lub (Zinterval.to_zero i') (Zinterval.sum i' (relative_interval f))
      | Next (i, f) | Eventually (i, f) | Always (i, f)
        -> let i = Zinterval.of_interval i in
           Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i (relative_interval f))
      | Since (_, i, f1, f2) ->
         let i' = Zinterval.inv (Zinterval.of_interval i) in
         (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i') (relative_interval f1))
            (Zinterval.sum i' (relative_interval f2)))
      | Until (_, i, f1, f2) ->
         let i' = Zinterval.of_interval i in
         (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i') (relative_interval f1))
            (Zinterval.sum i' (relative_interval f2)))
      | Let (e, _, _, f, g) ->
         let i = relative_interval f in
         relative_interval' ~itl_itvs:(Map.update itl_itvs e (fun _ -> i)) g in
    (*Stdio.print_endline (Printf.sprintf "MFOTL.relative_interval (%s) = %s" (op_to_string f) (Zinterval.to_string i));*)
    i

  let relative_intervals ?(itl_itvs=Map.empty (module String)) fs =
    let itvs = (List.map fs ~f:(relative_interval ~itl_itvs:itl_itvs)) in
    List.fold itvs ~init:(Zinterval.singleton 0) ~f:Zinterval.lub

  let relative_past ?(itl_itvs=Map.empty (module String)) f =
    Zinterval.is_nonpositive (relative_interval ~itl_itvs f)

  let is_right_bounded f = Option.is_some (Zinterval.right (relative_interval f))

  (* Strictness *)
  
  let strict ?(itl_strict=Map.empty (module String)) ?(itv=Zinterval.singleton 0) ?(fut=false) f =
    let rec _strict itl_strict itv fut f =
      let _strict' = _strict in
      let _strict = _strict itl_strict in
      ((Zinterval.has_zero itv) && fut)
      || (match f.form with
          | TT | FF | EqConst (_, _) -> false
          | Predicate (r, _) ->
             begin match Map.find itl_strict r with
             | Some b -> not b
             | None -> false
             end
          | Neg f | Exists (_, f) | Forall (_, f) | Agg (_, _, _, _, f)
            | Top (_, _, _, _, f) | Predicate' (_, _, f) | Let' (_, _, _, _, f)
            | Type (f, _) | Label (_, f) -> _strict itv fut f
          | Imp (_, f1, f2)
            -> (_strict itv fut f1) || (_strict itv fut f2)
          | And (_, fs) | Or (_, fs)
            -> List.exists ~f:(_strict itv fut) fs
          | Prev (i, f) | Once (i, f) | Historically (i, f)
            -> _strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f
          | Next (i, f) | Eventually (i, f) | Always (i, f)
            -> _strict (Zinterval.sum (Zinterval.of_interval i) itv) true f
          | Since (_, i, f1, f2)
            -> (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f1)
               || (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f2)
          | Until (_, i, f1, f2)
            -> (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) true f1)
               || (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) true f2)
          | Let (e, _, _, f, g)
            -> let strict_e = _strict itv fut f in
               _strict' (Map.update itl_strict e (fun _ -> strict_e )) itv fut g)
    in not (_strict itl_strict itv fut f)

  let stricts ?(itl_strict=Map.empty (module String)) ?(itv=Zinterval.singleton 0) ?(fut=false) =
    List.for_all ~f:(strict ~itl_strict ~itv ~fut)

  (* Monotonicity *)

  let rec predicates_of_formula f =
    let combine_str_info_maps m1 m2 =
      Map.merge m1 m2 ~f:(fun ~key:_ -> function
          | `Both (v1, v2) -> Some (v1 @ v2)
          | `Left v -> Some v
          | `Right v -> Some v) in
    match f.form with
    | TT | FF | EqConst (_, _) -> Map.empty (module String)
    | Predicate (x, _) -> Map.of_alist_exn (module String) [(x, [f.info])]
    | Let (e, _, _, f, g) -> 
       let preds = predicates_of_formula f in
       let preds' = Map.remove (predicates_of_formula g) e in
       combine_str_info_maps preds preds'
    | Neg f
      | Agg (_, _, _, _, f)
      | Top (_, _, _, _, f)
      | Exists (_, f)
      | Forall (_, f)
      | Prev (_, f)
      | Next (_, f)
      | Once (_, f)
      | Eventually (_, f)
      | Historically (_, f)
      | Always (_, f)
      | Predicate' (_, _, f)
      | Let' (_, _, _, _, f)
      | Type (f, _)
      | Label (_, f) ->
       predicates_of_formula f
    | And (_, fs)
      | Or (_, fs) ->
       List.fold ~init:(Map.empty (module String)) ~f:(fun acc f -> combine_str_info_maps acc (predicates_of_formula f)) fs
    | Imp (_, f, g)
      | Until (_, _, f, g)
      | Since (_, _, f, g) ->
       let f_preds = predicates_of_formula f in
       let g_preds = predicates_of_formula g in
       combine_str_info_maps f_preds g_preds

  let rec non_monotone_predicates
      ?(let_ctxt_mon: 'str_str_info_map=Map.empty (module String))
      ?(let_ctxt_anti_mon: 'str_str_info_map=Map.empty (module String))
      ?(init_mon: 'str_info_map=Set.empty (module String))
      ?(init_anti_mon: 'str_info_map=Set.empty (module String)) f :
    ((string, String.comparator_witness) Set.t * (string, String.comparator_witness) Set.t) =
    (** computes the predicates that appear non-(anti)-monotonically in a formula f *)
    (* Because f.info is 'abstract' one cannot directly access lexing positional information
       The position information will later be extracted and combined *)
    let r =
    match f.form with
    | TT | FF | EqConst (_, _) -> init_mon, init_anti_mon
    | Predicate (r, _) ->
      let mon =
        if Map.mem let_ctxt_mon r
        then Set.union init_mon (Map.find_exn let_ctxt_mon r)
        else init_mon in
      let anti_mon =
        if Map.mem let_ctxt_anti_mon r
        then Set.union init_anti_mon (Map.find_exn let_ctxt_anti_mon r)
        else Set.add init_anti_mon r in
      mon, anti_mon
    | Neg f ->
      let anti_mon, mon = non_monotone_predicates
        ~let_ctxt_mon ~let_ctxt_anti_mon
        ~init_mon:init_anti_mon ~init_anti_mon:init_mon f in 
        mon, anti_mon
    | Let (e, _, _, f, g) ->
      let f_mon, f_anti_mon =
        non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon ~init_mon ~init_anti_mon f in
      let ctxt_mon = Map.update let_ctxt_mon e ~f:(fun _ -> f_mon) in
      let ctxt_anti_mon = Map.update let_ctxt_anti_mon e ~f:(fun _ -> f_anti_mon) in
      non_monotone_predicates ~let_ctxt_mon:ctxt_mon ~let_ctxt_anti_mon:ctxt_anti_mon
        ~init_mon:f_mon ~init_anti_mon:f_anti_mon g
    | Agg (_, _, _, _, f)
      (* [JD] this is a conservative overestimation of which predicates
      appear (non)-monotone in an aggregation.
      as such it just marks all predicates that appear in the 
      aggregation as (potentially) (non)-monotone *)
      (* TODO[JD]: actully figure out when a predicate is (non)-monotone in an aggregation *)
    | Top (_, _, _, _, f) ->
      (* [JD] this is a conservative overestimation of which predicates
      appear (non)-monotone in a table-operator.
      as such it just marks all predicates that appear in the 
      aggregation as (potentially) (non)-monotone *)
      (* TODO[JD]: actully figure out when a predicate is (non)-monotone in a table-operator *)
      let preds = predicates f in
      let mon = Set.union init_mon preds in
      let anti_mon = Set.union init_anti_mon preds in
      mon, anti_mon
    | And (_, fs)
    | Or (_, fs) ->
      let mono_maps = List.map fs ~f:(fun f ->
          non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon ~init_mon ~init_anti_mon f) in
      let mons, anti_mons = List.unzip mono_maps in
      Set.union_list (module String) mons, Set.union_list (module String) anti_mons
    | Imp (_, f, g) ->
      let f_mon, f_anti_mon =
        non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon ~init_mon ~init_anti_mon f in
      let g_mon, g_anti_mon =
        non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon ~init_mon ~init_anti_mon g in
      Set.union f_anti_mon g_mon, Set.union f_mon g_anti_mon
    | Until (_, _, f, g)
    | Since (_, _, f, g) ->
      let f_mon, f_anti_mon =
        non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon ~init_mon ~init_anti_mon f in
      let g_mon, g_anti_mon =
        non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon ~init_mon ~init_anti_mon g in
      Set.union f_mon g_mon, Set.union f_anti_mon g_anti_mon
    | Exists (_, f)
    | Forall (_, f)
    | Prev (_, f)
    | Next (_, f)
    | Once (_, f)
    | Eventually (_, f)
    | Historically (_, f)
    | Always (_, f)
    | Predicate' (_, _, f)
    | Let' (_, _, _, _, f)
    | Type (f, _)
    | Label (_, f) ->
      non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon ~init_mon ~init_anti_mon f
    in
    (*print_endline (Printf.sprintf "nmp(%s) = { mp = [%s], ap = [%s] }"
                     (to_string_value f)
                     (String.concat ~sep:", " (Set.elements (fst r)))
                     (String.concat ~sep:", " (Set.elements (snd r))));*)
    r

  (* Enforceability *)

  let formula_to_string = to_string

  module MFOTL_Enforceability (Sig : Modules.S) = struct

    (* Rank *)

    let rec rank f = match f.form with
      | TT | FF -> 0
      | EqConst _ -> 0
      | Predicate (r, _) -> Sig.rank_of_pred r
      | Predicate' (_, _, f)
        | Let (_, _, _, _, f)
        | Let' (_, _, _, _, f)
        | Neg f
        | Exists (_, f)
        | Forall (_, f)
        | Prev (_, f)
        | Next (_, f)
        | Once (_, f)
        | Eventually (_, f)
        | Historically (_, f)
        | Always (_, f)
        | Agg (_, _, _, _, f)
        | Top (_, _, _, _, f)
        | Type (f, _)
        | Label (_, f) -> rank f
      | Imp (_, f, g)
        | Since (_, _, f, g)
        | Until (_, _, f, g) -> rank f + rank g
      | And (_, fs)
        | Or (_, fs) -> let f f = rank f in
                        List.fold ~f:(+) ~init:0 (List.map fs ~f)

    
    (* Conversion:
      *1. Pull out: lets to the beginning of the formula
                    all temporal operators into lets at the beginning of the formula
                    all existential quantifiers out of the formula
       2. Go through the lets and convert them to filters, checking past-guardedness
          of all variables in the arguments and computing conditions for
          causability/suppressability
       4. Go through the formula after the lets and normalize it

    *)

    (* Pulling out let bindings, temporal operators, and quantifiers *)

    let strip_exists f =
      match f |> all_exists |> snd |> List.last with
      | Some f -> f
      | _ -> f

    let add_back_exists f xs fs =
      List.fold_right (List.zip_exn xs fs)
          ~f:(fun (x, f') f -> { f' with form = Exists (x, f) }) ~init:f

    let rec pull_lets ?(i=0) (form:(Info.t, Var.t, Dom.t, Term.t) _t) :
      int * (string * Enftype.t option * (Var.t * Dom.tt option) list * (Info.t, Var.t, Dom.t, Term.t) _t) list * (Info.t, Var.t, Dom.t, Term.t) _t =
      let r = 
      match form.form with
      | TT | FF | EqConst _ | Predicate _ -> (i, [], form)
      | Predicate' (_, _, f)
      | Let' (_, _, _, _, f)
      | Type (f, _) -> pull_lets ~i f
      | Let (e, enftype, vars, f, g) ->
        let i, letsf, f = pull_lets ~i f in
        let i, letsg, g = pull_lets ~i g in
        i, letsf @ (e, Some enftype, vars, f) :: letsg, g
      | Neg f ->
        let i, letsf, f = pull_lets ~i f in
        i, letsf, { f with form = Neg f }
      | Exists (x, _) ->
        (*print_endline "-- Exists";
          print_endline ("form = " ^ to_string form);*)
        let xs, fs = all_exists form in
        (*print_endline ("xs = " ^  String.concat ~sep:", " (List.map ~f:Var.to_string xs));*)
        let i, lets, f = pull_lets ~i (List.last_exn fs) in
        let e = "Exists" ^ string_of_int i in
        let fvs = Set.elements (fv form) in
        let vars = List.map ~f:(fun v -> (v, None)) fvs in
        let g = add_back_exists f xs fs in
        i + 1, lets @ [e, None, vars, { f with form = g.form }],
        { f with form = Predicate (e, List.map ~f:Term.dummy_var fvs) }
      | Forall (x, f) ->
        pull_lets ~i { form with form = Neg ({ form with form = Exists (x, { form with form = Neg f }) }) }
      | Prev (itv, f) ->
        let i, lets, f = pull_lets ~i f in
        let e = "Prev" ^ string_of_int i in
        let fvs = Set.elements (fv f) in
        let vars = List.map ~f:(fun v -> (v, None)) fvs in
        i + 1, lets @ [e, None, vars, { f with form = Prev (itv, f) }],
        { f with form = Predicate (e, List.map ~f:Term.dummy_var fvs) }
      | Once (itv, f) ->
        let i, lets, f = pull_lets ~i f in
        let e = "Once" ^ string_of_int i in
        let fvs = Set.elements (fv f) in
        let vars = List.map ~f:(fun v -> (v, None)) fvs in
        i + 1, lets @ [e, None, vars, { f with form = Once (itv, f) }],
        { f with form = Predicate (e, List.map ~f:Term.dummy_var fvs) }
      | Next (itv, f) ->
        let i, lets, f = pull_lets ~i f in
        i, lets, { form with form = Next (itv, f) }
      | Eventually (itv, f) ->
        let i, lets, f = pull_lets ~i f in
        i, lets, { form with form = Eventually (itv, f) }
      | Historically (itv, f) ->
        let i, lets, f = pull_lets ~i f in
        let e = "Historically" ^ string_of_int i in
        let fvs = Set.elements (fv f) in
        let vars = List.map ~f:(fun v -> (v, None)) fvs in
        i + 1, lets @ [e, None, vars, { f with form = Historically (itv, f) }],
        { f with form = Predicate (e, List.map ~f:Term.dummy_var fvs) }
      | Always (itv, f) ->
        let i, lets, f = pull_lets ~i f in
        i, lets, { form with form = Always (itv, f) }
      | Since (s, itv, f, g) ->
        let i, letsf, f = pull_lets ~i f in
        let i, letsg, g = pull_lets ~i g in
        let e = "Since" ^ string_of_int i in
        (* Both sides of a Since must bind all table columns (for constant-time
           add/remove), so the columns are fv(f) ∩ fv(g), not their union. *)
        let fvs = Set.elements (Set.inter (fv f) (fv g)) in
        let vars = List.map ~f:(fun v -> (v, None)) fvs in
        i + 1, letsf @ letsg @ [e, None, vars, { f with form = Since (s, itv, f, g) }],
        { f with form = Predicate (e, List.map ~f:Term.dummy_var fvs) }
      | Until (s, itv, f, g) ->
        let i, letsf, f = pull_lets ~i f in
        let i, letsg, g = pull_lets ~i g in
        i, letsf @ letsg, { form with form = Until (s, itv, f, g) }
      | And (s, fs) ->
        let i, lets, fs = List.fold_right fs ~init:(i, [], [])
            ~f:(fun f (i, lets, fs) -> let i, lets', f = pull_lets ~i f in i, lets' @ lets, f :: fs) in
        i, lets, { form with form = And (s, fs) }
      | Or (s, fs) ->
        let i, lets, fs = List.fold_right fs ~init:(i, [], [])
            ~f:(fun f (i, lets, fs) -> let i, lets', f = pull_lets ~i f in i, lets' @ lets, f :: fs) in
        i, lets, { form with form = Or (s, fs) }
      | Imp (s, f, g) ->
        let i, letsf, f = pull_lets ~i f in
        let i, letsg, g = pull_lets ~i g in
        i, letsf @ letsg, { form with form = Imp (s, f, g) }
      | Label (s, f) ->
        let i, lets, f = pull_lets ~i f in
        let e = "Label" ^ string_of_int i ^ ":" ^ s in
        let fvs = Set.elements (fv f) in
        let vars = List.map ~f:(fun v -> (v, None)) fvs in
        i + 1, lets @ [e, None, vars, f],
        { f with form = Predicate (e, List.map ~f:Term.dummy_var fvs) }
      | _ -> failwith ("unsupported constructor " ^ op_to_string form)
      in (*print_endline (Printf.sprintf "pull_lets(%s)=%s" (to_string form) (to_string (match r with (_, _, f) -> f)));*) r

    let do_pull_lets f =
      let i, lets, f = pull_lets f in lets, f

    (* Present-guardedness checks and guards *)

    type trigger = {
      guards: t list list; (* DNF *)
      filter: t
    } [@@deriving equal]

    let trigger_to_string trigger =
      Printf.sprintf "{ guards = [%s];\n  filter = %s }"
        (Etc.string_list_to_string (List.map trigger.guards ~f:(
             fun fs -> "[" ^ Etc.string_list_to_string (List.map ~f:to_string fs))))
        (to_string trigger.filter)

    let of_trigger p trigger =
      let filter = trigger.filter |> push_negs |> ac_simplify in
      match trigger.guards with
      | [] -> filter
      | guards ->
        let guard_f = make_dummy (Or (N, List.map ~f:(
            fun fs -> make_dummy (And (N, fs))) guards)) in
        if p then
          make_dummy (And (N, [guard_f; filter]))
        else
          make_dummy (Imp (N, guard_f, filter))

    let non_monotone_predicates_of_trigger
        ~let_ctxt_mon:(let_ctxt_mon:(string, (string, Base.String.comparator_witness) Base.Set.t, Base.String.comparator_witness) Base.Map.t)
        ~let_ctxt_anti_mon:(let_ctxt_anti_mon:(string, (string, Base.String.comparator_witness) Base.Set.t, Base.String.comparator_witness) Base.Map.t)
        p trigger =
      let filter_mon, filter_anti_mon =
        non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon trigger.filter in
      let guard_maps = List.map trigger.guards ~f:(fun fs ->
          non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon (make_dummy (And (N, fs)))) in
      let guard_mon, guard_anti_mon =
        List.fold guard_maps
          ~f:(fun (init_mon, init_anti_mon) (mon, anti_mon) ->
              Set.union init_mon mon, Set.union init_anti_mon anti_mon)
          ~init:(Set.empty (module String), Set.empty (module String)) in
      match trigger.guards with
      | [] ->
        if p then filter_mon, filter_anti_mon else filter_anti_mon, filter_mon
      | _ ->
        let guard_mon, guard_anti_mon =
          if p then guard_mon, guard_anti_mon else guard_anti_mon, guard_mon in
        Set.union guard_mon filter_mon,
        Set.union guard_anti_mon filter_anti_mon
                         

    (* Enforceability typing *)
    
    module Errors = struct

      type error =
        | ECast of string * Enftype.t * Enftype.t
        | EFormula of string option * t * Enftype.t
        | EConj of error list
        | EDisj of error list
        | ERule of string  [@@deriving equal]

      let rec to_string ?(n=0) e =
        let sp = Etc.spaces (2*n) in
        let lb = "\n" ^ sp in
        (match e with
         | ECast (e, t', t) -> "make "
                               ^ e
                               ^ " "
                               ^ Enftype.to_string t
                               ^ " (currently, it has type "
                               ^ Enftype.to_string t'
                               ^ ")"
         | EFormula (None, f, t) -> "make "
                                    ^ formula_to_string f
                                    ^ " "
                                    ^ Enftype.to_string t
                                    ^ ", but this is impossible"
         | EFormula (Some s, f, t) -> "make "
                                      ^ formula_to_string f
                                      ^ " "
                                      ^ Enftype.to_string t
                                      ^ ", but this is impossible"
                                      ^ " (" ^ s ^ ")"
         | EConj es -> "at the same time"
                       ^ String.concat (List.map ~f:(fun e -> lb ^ "* " ^ to_string ~n:(n+1) e) es)
         | EDisj es -> "either"
                       ^ String.concat (List.map ~f:(fun e -> lb ^ "* " ^ to_string ~n:(n+1) e) es)
         | ERule s -> s)

      let rec ac_flatten = function
        | EConj es ->
           let es = List.map ~f:ac_flatten es in
           let es = List.concat_map es ~f:(function EConj xs -> xs | c -> [c]) in
           (match es with [c] -> c | _ -> EConj es)
        | EDisj es ->
           let es = List.map ~f:ac_flatten es in
           let es = List.concat_map es ~f:(function EDisj xs -> xs | c -> [c]) in
           (match es with [c] -> c | _ -> EDisj es)
        | c -> c

      let rec ac_simplify = function
        | EConj es ->
           let es = List.map ~f:ac_simplify es in
           let f_has_ff = function EDisj [] -> true | _ -> false in
           (if List.exists es ~f:f_has_ff then
              EDisj []
            else
              match ac_flatten (EConj es) with
              | EConj es' ->
                 (*Stdio.print_endline (Printf.sprintf "dedup.conj.1(\n-%s\n,\n %s\n) = %s\n\n" (to_string (CConj cs)) (String.concat ~sep:"\n " (List.map ~f:to_string cs')) (to_string (CConj cs')));*)
                 let es', _ =
                   let is_weaker_clause c ds =
                     (* All disjuncts in d' are in d, so d is unnecessary *)
                     let isin d = List.for_all ~f:(List.mem d ~equal:equal_error) in
                     let d = match c with EDisj d -> d | _ -> [c] in
                     d, List.exists ds ~f:(isin d) in
                   let f c (cs, ds) =
                     let d, b = is_weaker_clause c ds in
                     if b then (cs, ds) else (c::cs, d::ds) in
                   List.fold_right es' ~init:([], []) ~f
                 in
                 (*Stdio.print_endline (Printf.sprintf "dedup.conj(\n-%s\n,\n %s\n) = %s\n\n" (to_string (CConj cs)) (String.concat ~sep:"\n " (List.map ~f:to_string cs)) (to_string (CConj cs')));*)
                 EConj es'
              | c -> c)
        | EDisj es ->
           let es = List.map ~f:ac_simplify es in
           let f_has_tt = function EConj [] -> true | _ -> false in
           (if List.exists es ~f:f_has_tt then
              EConj []
            else
              match ac_flatten (EDisj es) with
              | EDisj es' -> 
                 let es', _ =
                   let is_weaker_clause c ds =
                     (* All conjuncts in d' are in d, so d is unnecessary *)
                     let isin d = List.for_all ~f:(List.mem d ~equal:equal_error) in
                     let d = match c with EConj d -> d | _ -> [c] in
                     d, List.exists ds ~f:(isin d) in
                   let f c (cs, ds) =
                     let d, b = is_weaker_clause c ds in
                     if b then (cs, ds) else (c::cs, d::ds) in
                   List.fold_right es' ~init:([], []) ~f 
                 in
                 (*Stdio.print_endline (Printf.sprintf "dedup.disj(\n-%s\n,\n %s\n) = %s\n\n" (to_string (CDisj cs))(String.concat ~sep:"\n " (List.map ~f:to_string cs)) (to_string (CDisj cs')));*)
                 EDisj es'
              | c -> c)
        | c -> c
            

    end

    module Constraints = struct

      open Enftype.Constraint

      type constr =
        | CTT
        | CFF
        | CGeq of string * Enftype.t
        | CLeq of string * Enftype.t
        | CConj of constr list
        | CDisj of constr list [@@deriving equal, compare, sexp_of]

      (*let rec to_string_rec l = function
        | CTT -> Printf.sprintf "⊤"
        | CFF -> Printf.sprintf "⊥"
        | CGeq (s, t) -> Printf.sprintf "t(%s) ≽ %s" s (Enftype.to_string t)
        | CLeq (s, t) -> Printf.sprintf "%s ≽ t(%s)" (Enftype.to_string t) s
        | CConj cs -> Printf.sprintf (Etc.paren l 4 "%s")
                        (String.concat ~sep:" ∧ " (List.map ~f:(to_string_rec 4) cs))
        | CDisj cs -> Printf.sprintf (Etc.paren l 3 "%s")
                        (String.concat ~sep:" ∨ " (List.map ~f:(to_string_rec 3) cs))

      let to_string = to_string_rec 0

      let verdict_to_string = function
        | Possible c -> Printf.sprintf "Possible(%s)" (to_string c)
        | Impossible e -> Printf.sprintf "Impossible(%s)" (Errors.to_string e)*)

      let geq s t = CGeq (s, t)
      let leq s t = CLeq (s, t)

      let rec ac_flatten = function
        | CConj cs ->
           let cs = List.map ~f:ac_flatten cs in
           let cs = List.concat_map cs ~f:(function CConj xs -> xs | CTT -> [] | c -> [c]) in
           (match cs with [] -> CTT | [c] -> c | _ -> CConj cs)
        | CDisj cs ->
           let cs = List.map ~f:ac_flatten cs in
           let cs = List.concat_map cs ~f:(function CDisj xs -> xs | CFF -> [] | c -> [c]) in
           (match cs with [] -> CFF | [c] -> c | _ -> CDisj cs)
        | c -> c

      let rec ac_simplify = function
        | CConj cs ->
           let cs = List.map ~f:ac_simplify cs in
           let f_has_ff = function CFF -> true | _ -> false in
           (if List.exists cs ~f:f_has_ff then
              CFF
            else
              match ac_flatten (CConj cs) with
              | CConj cs' ->
                 (*Stdio.print_endline (Printf.sprintf "dedup.conj.1(\n-%s\n,\n %s\n) = %s\n\n" (to_string (CConj cs)) (String.concat ~sep:"\n " (List.map ~f:to_string cs')) (to_string (CConj cs')));*)
                 let cs', _ =
                   let is_weaker_clause c ds =
                     (* All disjuncts in d' are in d, so d is unnecessary *)
                     let isin d = List.for_all ~f:(List.mem d ~equal:equal_constr) in
                     let d = match c with CDisj d -> d | _ -> [c] in
                     d, List.exists ds ~f:(isin d) in
                   let f c (cs, ds) =
                     let d, b = is_weaker_clause c ds in
                     if b then (cs, ds) else (c::cs, d::ds) in
                   List.fold_right cs' ~init:([], []) ~f
                 in
                 (*Stdio.print_endline (Printf.sprintf "dedup.conj(\n-%s\n,\n %s\n) = %s\n\n" (to_string (CConj cs)) (String.concat ~sep:"\n " (List.map ~f:to_string cs)) (to_string (CConj cs')));*)
                 CConj cs'
              | c -> c)
        | CDisj cs ->
           let cs = List.map ~f:ac_simplify cs in
           let f_has_tt = function CTT -> true | _ -> false in
           (if List.exists cs ~f:f_has_tt then
              CTT
            else
              match ac_flatten (CDisj cs) with
              | CDisj cs' -> 
                 let cs', _ =
                   let is_weaker_clause c ds =
                     (* All conjuncts in d' are in d, so d is unnecessary *)
                     let isin d = List.for_all ~f:(List.mem d ~equal:equal_constr) in
                     let d = match c with CConj d -> d | _ -> [c] in
                     d, List.exists ds ~f:(isin d) in
                   let f c (cs, ds) =
                     let d, b = is_weaker_clause c ds in
                     if b then (cs, ds) else (c::cs, d::ds) in
                    List.fold_right cs' ~init:([], []) ~f
                 in
                 (*Stdio.print_endline (Printf.sprintf "dedup.disj(\n-%s\n,\n %s\n) = %s\n\n" (to_string (CDisj cs))(String.concat ~sep:"\n " (List.map ~f:to_string cs)) (to_string (CDisj cs')));*)
                 CDisj cs'
              | c -> c)
        | c -> c

      let rec cartesian a = function
          [] -> []
        | h::t -> (List.map a ~f:(fun x -> (x, h))) @ cartesian a t

      let try_merge (a, b) =
        try Some (Map.merge a b ~f:merge)
        with CannotMerge k -> (*print_endline ("Cannot merge: "^k);*)None

      let rec to_string_rec l = function
        | CTT -> Printf.sprintf "⊤"
        | CFF -> Printf.sprintf "⊥"
        | CGeq (s, t) -> Printf.sprintf "t(%s) ≽ %s" s (Enftype.to_string t)
        | CLeq (s, t) -> Printf.sprintf "%s ≽ t(%s)" (Enftype.to_string t) s
        | CConj cs -> Printf.sprintf (Etc.paren l 4 "%s")
                        (String.concat ~sep:" ∧ " (List.map ~f:(to_string_rec 4) cs))
        | CDisj cs -> Printf.sprintf (Etc.paren l 3 "%s")
                        (String.concat ~sep:" ∨ " (List.map ~f:(to_string_rec 3) cs))

      let to_string = to_string_rec 0


      let rec solve c : (string, Enftype.Constraint.t, Base.String.comparator_witness) Base.Map.t list =
        (*Stdio.print_endline ("solve(" ^  (to_string c) ^ ")");*)
        let r = match c with
          | CTT -> [Map.empty (module String)]
          | CFF (*| CGeq (_, Obs)*) -> []
          | CGeq (s, t) -> [Map.singleton (module String) s (lower t)]
          | CLeq (s, t) -> [Map.singleton (module String) s (upper t)]
          | CConj [] -> [Map.empty (module String)]
          | CConj (c::cs) ->
             (*Stdio.print_endline ("CConj(" ^ string_of_int (List.length (c::cs)) ^ ")");*)
             let f sol d = List.filter_map (cartesian sol (solve d)) ~f:try_merge in
             List.fold_left cs ~init:(solve c) ~f
          | CDisj cs -> List.concat_map cs ~f:solve
        in  (*Stdio.printf "solve(%s)=[%s]\n" (to_string c) (String.concat ~sep:"; " (List.map r ~f:(fun m -> String.concat ~sep:", " (List.map (Map.to_alist m) ~f:(fun (key, constr) -> key ^ " matches " ^ Enftype.Constraint.to_string constr)))));*)
        r

    end

    module Verdict = struct

      type 'a v = Possible of 'a list | Impossible of Errors.error

      let conj ~f c d = match c, d with
        | Impossible c, Impossible d -> Impossible (Errors.ac_simplify (EConj [c; d]))
        | Impossible c, _ | _, Impossible c -> Impossible c
        | Possible c, Possible d -> Possible (f c d)

      let disj c d = match c, d with
        | Impossible c, Impossible d -> Impossible (Errors.ac_simplify (EDisj [c; d]))
        | Impossible _, _ -> d
        | _, Impossible _ -> c
        | Possible c, Possible d -> Possible (c @ d)

      let conjs ~f = function
        | c::cs -> List.fold_left ~init:c ~f:(conj ~f) cs

      let disjs = function
        | [] -> Impossible (EDisj [])
        | c::cs -> List.fold_left ~init:c ~f:disj cs

      let rec all = function
        | [] -> Possible []
        | (Possible c)::cs ->
          (match all cs with
           | Possible cs -> Possible (c::cs)
           | Impossible err -> Impossible err)
        | (Impossible c)::cs ->
          (match all cs with
           | Possible cs -> Impossible c
           | Impossible d -> Impossible (Errors.ac_simplify (EDisj [c; d])))

      let rec any = function
        | [] -> Impossible (EDisj [])
        | (Possible c)::cs ->
          (match all cs with
           | Possible cs -> Possible (c::cs)
           | Impossible err -> Possible [c])
        | (Impossible c)::cs ->
          (match all cs with
           | Possible cs -> Possible cs
           | Impossible d -> Impossible (Errors.ac_simplify (EConj [c; d])))

      let (let*) x f = match x with
        | Possible sols -> Possible (f sols)
        | Impossible err -> Impossible err

      let (let**) x f = match x with
        | Possible sols -> f sols
        | Impossible err -> Impossible err

      let verdict_to_string ~to_string = function
        | Possible c -> Printf.sprintf "Possible(%s)" (to_string c)
        | Impossible e -> Printf.sprintf "Impossible(%s)" (Errors.to_string e)

      let map ~f = function
        | Possible sols -> Possible (f sols)
        | Impossible err -> Impossible err
      
    end

    type clause = {
      trigger: trigger;
      effects: t list
    }

    let clause_to_string clause =
      Printf.sprintf "{ trigger = %s;\n  effects = [%s] }"
        (trigger_to_string clause.trigger)
        (Etc.string_list_to_string (List.map ~f:to_string clause.effects))

    type enf_sols = (clause list * Constraints.constr) Verdict.v

    let enf_sols_to_string enf_sols =
      Printf.sprintf "[%s]"
        (Etc.string_list_to_string (List.map enf_sols ~f:(fun (clauses, constr) ->
             Printf.sprintf "{ clauses = [%s];\n  constr = %s }"
               (Etc.string_list_to_string (List.map ~f:clause_to_string clauses))
               (Constraints.to_string constr))))

    let merge_clauses_constr clauses_constrs clauses_constrs' =
      let clauses_constrs' = Etc.cartesian [clauses_constrs; clauses_constrs'] in
      List.map clauses_constrs' ~f:(fun clauses_constrs ->
          let clauses, constrs = List.unzip clauses_constrs in
          (List.concat clauses, Constraints.ac_simplify (Constraints.CConj constrs)))

    type switch =
      | SOnce of trigger
      | SPrev of trigger
      | SSince of trigger * trigger
      | SNow of trigger

    let switch_to_string = function
      | SOnce trigger -> "⧫(" ^ trigger_to_string trigger ^ ")"
      | SPrev trigger -> "●(" ^ trigger_to_string trigger ^ ")"
      | SSince (ltrigger, rtrigger) -> "(" ^ trigger_to_string ltrigger ^ ") S (" ^ trigger_to_string rtrigger ^ ")"
      | SNow trigger -> trigger_to_string trigger

    let of_switch p = function
      | SOnce trigger -> make_dummy (Once (Interval.full, of_trigger p trigger))
      | SPrev trigger -> make_dummy (Prev (Interval.full, of_trigger p trigger))
      | SSince (ltrigger, rtrigger) -> make_dummy (Since (N, Interval.full, of_trigger (not p) ltrigger, of_trigger p rtrigger))
      | SNow trigger -> of_trigger p trigger

    type let_def = {
      name: string;
      args: (Var.t * Dom.tt option) list;
      body: t;
      cau_sols: enf_sols;
      sup_sols: enf_sols;
      switch_pos_opt: switch option;
      switch_neg_opt: switch option;
    }

    let let_def_to_string let_def =
      let o default f x = Option.value (Option.map ~f x) ~default in
      Printf.sprintf "{ name = %s;\n  args = [%s];\n  body = %s;\n  cau_sols = %s;\n  sup_sols = %s;\n  trigger_pos_opt = %s;\n  trigger_neg_opt = %s }"
        let_def.name
        (Etc.string_list_to_string (List.map let_def.args ~f:(
             fun (v, tt_opt) -> Var.to_string v ^ o "" (fun tt -> ": " ^ Dom.tt_to_string tt) tt_opt)))
        (to_string let_def.body)
        (Verdict.verdict_to_string ~to_string:enf_sols_to_string let_def.cau_sols)
        (Verdict.verdict_to_string ~to_string:enf_sols_to_string let_def.sup_sols)
        (o "None" switch_to_string let_def.switch_pos_opt)
        (o "None" switch_to_string let_def.switch_neg_opt)
        

    type let_map = (string, let_def, String.comparator_witness) Map.t

    let let_map_to_string m =
      String.concat ~sep:"\n" (List.map ~f:(fun (key, let_def) -> key ^ " -> " ^ let_def_to_string let_def)
                                 (Map.to_alist m))
      
    let rec make_past_only (p: bool) form =
      let open Verdict in
      match form.form with
      | TT | FF | EqConst (_, _) | Predicate (_, _) -> form
      | Neg f ->
        let f = make_past_only (not p) f in
        { form with form = Neg f }
      | And (s, fs) ->
        let fs = List.map ~f:(make_past_only p) fs in
        { form with form = And (s, fs) }
      | Or (s, fs) ->
        let fs = List.map ~f:(make_past_only p) fs in
        { form with form = Or (s, fs) }
      | Imp (s, f, g) ->
        let f = make_past_only (not p) f in
        let g = make_past_only p g in
        { form with form = Imp (s, f, g) }
      | Until (s, i, f, g) when p && Interval.has_zero i -> make_past_only p g
      | Until (s, i, f, g) when p -> make_dummy FF
      | Until (s, i, f, g) -> make_dummy TT
      | Since (s, i, f, g) ->
        let f = make_past_only (not p) f in
        let g = make_past_only p g in
        { form with form = Since (s, i, f, g) }
      | Exists (x, f) ->
        let f = make_past_only p f in
        { form with form = Exists (x, f) }
      | Forall (x, f) ->
        let f = make_past_only p f in
        { form with form = Forall (x, f) }
      | Prev (i, f) ->
        let f = make_past_only p f in
        { form with form = Prev (i, f) }
      | Next (i, f) when p -> make_dummy FF
      | Next (i, f) -> make_dummy TT
      | Once (i, f) ->
        let f = make_past_only p f in
        { form with form = Once (i, f) }
      | Eventually (i, f) when Interval.has_zero i -> make_past_only p f
      | Eventually (i, f) when p -> make_dummy FF
      | Eventually (i, f) -> make_dummy TT
      | Historically (i, f) ->
        let f = make_past_only p f in
        { form with form = Historically (i, f) }
      | Always (i, f) when p && Interval.has_zero i ->
        let f = make_past_only (not p) (make_dummy (Neg f)) in
        { form with form = Neg f }
      | Always (i, f) when p -> make_dummy FF
      | Always (i, f) -> make_dummy TT
      | Label (s, f) ->
        let f = make_past_only p f in
        { form with form = Label (s, f) }

    let init_trigger filter =
      { guards = []; filter }

        (* Given a formula f with a free variable x, find p_1, ..., p_k, g such that
       if p is true:  f = (p_1 | ... | p_k) & g
       if p is false: f =  p_1 | ... | p_k -> g
       in both cases: x is one of the arguments of each of p_1, ..., p_k.
       If this is not possible, the variable x is not present-guarded; return None *)
    let rec pull_guard (m: let_map) (x: Var.t) (p: bool) (trigger: trigger) : trigger option =
      let npg = pull_guard m x in
      (* First, check if one of the existing guards already does the job *)
      let with_existing_guard = List.for_all trigger.guards ~f:(
          List.exists ~f:(fun guard -> match guard.form with
              | Predicate (_, trms) ->
                List.exists ~f:(Term.equal (Term.dummy_var x)) trms
              | _ -> false)) in
      if with_existing_guard
      then Some trigger
      (* If it not the case, look for a new guard *)
      else begin
        let rec aux p filter =
          let r = 
          match filter.form, p with
          | TT, false -> Some trigger
          | FF, true  -> Some trigger
          | Predicate (r, trms), true when List.exists ~f:(Term.equal (Term.dummy_var x)) trms ->
            (match Map.find m r with
             | Some let_def when Option.is_none let_def.switch_pos_opt -> None
             | _ -> Some { guards = List.map ~f:(fun fs -> filter :: fs) trigger.guards;
                           filter = make_dummy TT })
          | EqConst (trm, _), true when Term.equal (Term.dummy_var x) trm ->
            Some { guards = List.map ~f:(fun fs -> filter :: fs) trigger.guards;
                   filter = make_dummy TT }
          | Neg f, _ ->
            Option.map (aux (not p) f) ~f:(fun trigger ->
                { trigger with filter = ac_simplify (make_dummy (Neg trigger.filter)) })
          | And (_, fs), true -> 
            Option.map ~f:(fun (i, trigger) ->
                let a, b = List.split_n fs i in
                let form = And (N, a @ trigger.filter :: (List.tl_exn b)) in
                let filter = ac_simplify { filter with form } in
                { trigger with filter })
              (List.find_mapi ~f:(fun i f ->
                   Option.map ~f:(fun trigger -> (i, trigger)) (aux true f)) fs)
          | And (_, fs), false ->
            Option.map (Option.all (List.map ~f:(aux false) fs)) ~f:(fun triggers ->
                let guards = List.concat_map ~f:(fun t -> t.guards) triggers in
                let filter = ac_simplify (make_dummy (
                    And (N, List.map ~f:(of_trigger false) triggers))) in
                { guards; filter })
          | Or (_, fs), false ->
             Option.map ~f:(fun (i, trigger) ->
                let a, b = List.split_n fs i in
                let form = Or (N, a @ trigger.filter :: (List.tl_exn b)) in
                let filter = ac_simplify { filter with form } in
                { trigger with filter })
              (List.find_mapi ~f:(fun i f ->
                   Option.map ~f:(fun trigger -> (i, trigger)) (aux false f)) fs)
          | Or (_, fs), true ->
            Option.map (Option.all (List.map ~f:(aux true) fs)) ~f:(fun triggers ->
                let guards = List.concat_map ~f:(fun t -> t.guards) triggers in
                let filter = ac_simplify (make_dummy (
                    Or (N, List.map ~f:(of_trigger true) triggers))) in
                { guards; filter })
          | Imp (_, f1, f2), false ->
            (match aux true f1, aux false f2 with
             | Some trigger, _ ->
               Some { trigger with filter = ac_simplify (make_dummy (Imp (N, trigger.filter, f2))) }
             | _, Some trigger ->
               Some { trigger with filter = ac_simplify (make_dummy (Imp (N, f1, trigger.filter))) }
             | _ -> None)
          (*| And (_, fs), false
          | Or (_, fs), true ->
            Option.map (Option.all (List.map ~f:(aux false) fs)) ~f:(fun triggers ->
                { trigger with guards = List.concat_map triggers ~f:(fun trigger -> trigger.guards) })*)
          | Imp (_, f1, f2), true ->
            (match aux false f1, aux true f2 with
             | Some trigger1, Some trigger2 ->
               Some { trigger with guards = trigger1.guards @ trigger2.guards }
             | _ -> None)
          | Exists (y, f), _
          | Forall (y, f), _ when not (Var.equal_ident x y) ->
            Option.map ~f:(fun trigger -> { trigger with filter = f }) (aux p f)
          | Label (s, f), _ ->
            Option.map (aux p f) ~f:(fun trigger ->
                { trigger with filter = { filter with form = Label (s, trigger.filter) } })
          | _ -> None
          in
          (*print_endline
            (Printf.sprintf "pull_guard.aux(%s, %b, %s) = %s"
               (Var.to_string x) p (to_string filter)
               (Option.value ~default:"None" (Option.map ~f:trigger_to_string r)));*)
          r
        in aux p trigger.filter
      end


    (* Check that all variables in a formula are past-guarded and, if possible, normalize the formula *)
    let normalize_trigger ?(vars=None) (m: let_map) (trigger: trigger) (p: bool) (orig_f: t) : trigger Verdict.v =
      let vars = match vars with
        | None -> Set.elements (fvs (trigger.filter :: List.concat trigger.guards))
        | Some vars -> vars in
      List.fold_right
        ~f:(fun x ->
            function
            | Verdict.Impossible e -> Impossible e
            | Possible [trigger] -> 
              match pull_guard m x p trigger with
              | None -> Impossible (Errors.ERule ("Variable " ^ Var.to_string x ^
                                                  " is not guarded in " ^ to_string orig_f
                                                  ^ " (polarity: " ^ (if p then "+" else "-") ^ ")"
                                                  ^ " (computed filter: " ^ trigger_to_string trigger ^ ")"))
              | Some trigger -> Possible [trigger])
        ~init:(Possible [trigger]) vars

    let maps_of_lets lets =
      let pred_map =
        List.fold_left lets
          ~init:(Map.empty (module String))
          ~f:(fun lets (e, _, _, f) -> Map.update lets e (fun _ -> predicates ~lets f)) in
      let mon_map, anti_mon_map =
        List.fold_left lets
          ~init:(Map.empty (module String), Map.empty (module String))
          ~f:(fun (let_ctxt_mon, let_ctxt_anti_mon) (e, _, _, f) ->
              (*print_endline "right here!";
                print_endline (to_string_value f);*)
              let mon, anti_mon = non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon f in
              Map.update let_ctxt_mon e (fun _ -> mon),
              Map.update let_ctxt_anti_mon e (fun _ -> anti_mon)) in
      pred_map, mon_map, anti_mon_map

    (* Using topological sort, reorders the patterns (trigger, effects) so that for any event e caused/suppressed 
         by patt1 and used in an trigger of patt2, patt1 is before patt2. This constraint can be ignored if e is caused
         and appears *antimonotonically* in the trigger of patt2, or if e is suppressed and appears *monotonically*
         in the trigger of patt1 (uses non_monotone_predicates). Returns None if no such ordering exists. *)
    let order_clauses
        (clauses: clause list)
        ~lets:(lets: (string, (string, String.comparator_witness) Set.t, String.comparator_witness) Map.t)
        ~let_ctxt_mon:(let_ctxt_mon: (string, (string, String.comparator_witness) Set.t, String.comparator_witness) Map.t)
        ~let_ctxt_anti_mon:(let_ctxt_anti_mon: (string, (string, String.comparator_witness) Set.t, String.comparator_witness) Map.t)
      : clause Verdict.v =
      let n = List.length clauses in
      (* For each pattern: (caused_preds, supped_preds, trigger_preds, monotone_preds_in_trigger, antimonotone_preds_in_trigger) *)
      let info = List.map clauses ~f:(fun clause ->
          let cp = Set.union_list (module String)
              (List.map clause.effects ~f:(fun effect -> match effect.form with
                   | Neg _ 
                   | Eventually (_, { form = Neg _ }) -> Set.empty (module String)
                   | _ -> predicates ~lets effect)) in
          let sp = Set.union_list (module String)
              (List.map clause.effects ~f:(fun effect -> match effect.form with
                   | Neg _ 
                   | Eventually (_, { form = Neg _ }) -> predicates ~lets effect
                   | _ -> Set.empty (module String))) in
          let ep = Set.union_list (module String)
              (List.map clause.effects ~f:(predicates ~lets)) in
          let tp = predicates ~lets (of_trigger true clause.trigger) in
          let mp, ap = non_monotone_predicates_of_trigger ~let_ctxt_mon ~let_ctxt_anti_mon true clause.trigger in
          (cp, sp, tp, mp, ap, clause)) in
      (*print_endline (String.concat ~sep:", " (List.mapi ~f:(
          fun i (cp, sp, tp, mp, ap, clause) ->
          string_of_int i ^ " -> {\n" ^
          "cp = [" ^ String.concat ~sep:", " (Set.elements cp) ^ "];\n" ^ 
          "sp = [" ^ String.concat ~sep:", " (Set.elements sp) ^ "];\n" ^
          "tp = [" ^ String.concat ~sep:", " (Set.elements tp) ^ "];\n" ^
          "mp = [" ^ String.concat ~sep:", " (Set.elements mp) ^ "];\n" ^
          "ap = [" ^ String.concat ~sep:", " (Set.elements ap) ^ "];\n" ^
          " clause = " ^ clause_to_string clause ^ "}") info));*)
      (* adj_labeled.(i) = list of (j, predicate, action) where action is "Cau" or "Sup":
         add edge i->j if some effect predicate of i appears non-antimonotonically in trigger_j.
         Exception: if e appears antimonotonically in trigger_j (i.e., in anti_mon_trig_j,
         the first return of non_monotone_predicates), causing/suppressing e cannot make
         trigger_j fire, so no ordering constraint is needed. *)
      let adj_labeled = List.mapi info ~f:(fun i info_i ->
          let (cp_i, sp_i, _, _, _, _) = info_i in
          List.filter_mapi info ~f:(fun j info_j ->
              (*if i = j then None
                else*)
                let (_, _, tp_j, mon_j, anti_mon_j, _) = info_j in
                let cau_event = Set.find (Set.inter cp_i tp_j)
                    ~f:(fun e -> Set.mem anti_mon_j e) (* NON-antimonotonic: causing e may fire trigger_j *)
                in
                let sup_event = Set.find (Set.inter sp_i tp_j)
                    ~f:(fun e -> Set.mem mon_j e) (* NON-monotonic: suppressing e may fire trigger_j *)
                in
                (match cau_event, sup_event with
                 | Some e, _ -> Some (j, e, Printf.sprintf "Cau-%d→%d" i j)
                 | None, Some e -> Some (j, e, Printf.sprintf "Sup-%d→%d" i j)
                 | None, None -> None))) in
      let adj = List.map adj_labeled ~f:(List.map ~f:(fun (j, _, _) -> j)) in
      (*print_endline (String.concat ~sep:", " (List.mapi adj ~f:(fun i js ->
          string_of_int i ^ " -> [" ^
          String.concat ~sep:", " (List.map ~f:string_of_int js) ^ "]")));*)
      (* Compute in-degrees *)
      let all_targets = List.concat adj in
      let in_deg =
        List.fold (List.range 0 n) ~init:(Map.empty (module Int)) ~f:(fun m i ->
            Map.set m ~key:i ~data:(List.count all_targets ~f:(fun k -> k = i))) in
      (* Find one cycle in the subgraph of [adj] induced by the [remaining] nodes using DFS. *)
      let find_cycle_in_subgraph adj remaining =
        let remaining_set = Set.of_list (module Int) remaining in
        let rec dfs visited stack v =
          if List.mem ~equal:Int.equal stack v then
            (* Found a back edge; extract cycle from stack *)
            let rec take_until acc = function
              | [] -> acc
              | x :: xs ->
                if Int.equal x v then List.rev (v :: acc)
                else take_until (x :: acc) xs
            in
            Some (take_until [] stack)
          else if Set.mem visited v then
            None
          else
            let visited = Set.add visited v in
            let stack   = v :: stack in
            let succs =
              List.filter (List.nth_exn adj v)
                ~f:(fun u -> Set.mem remaining_set u)
            in
            let rec loop = function
              | [] -> None
              | u :: us ->
                (match dfs visited stack u with
                 | Some c -> Some c
                 | None -> loop us)
            in
            loop succs
        in
        let rec try_nodes = function
          | [] -> None
          | v :: vs ->
            (match dfs (Set.empty (module Int)) [] v with
             | Some c -> Some c
             | None -> try_nodes vs)
        in
        try_nodes remaining
      in
      (* Format a cycle as "E0 (Cau) E1 (Sup) E2 ... E0"
         where each Ei is the predicate on the incoming edge of node i,
         and (Cau)/(Sup) is the action on the outgoing edge.
         Example: "B (Cau) B"  or  "B (Cau) C (Cau) D (Cau) B" *)
      let format_cycle adj_labeled cycle =
        let cycle = List.rev cycle in  (* DFS returns in reverse; restore forward order *)
        let k = List.length cycle in
        let get_edge vi vj =
          List.find_exn (List.nth_exn adj_labeled vi)
            ~f:(fun (j, _, _) -> Int.equal j vj)
          |> (fun (_, event, action) -> (event, action))
        in
        (* edge_labels.(i) = (predicate, action) on the edge cycle[i] -> cycle[(i+1) mod k] *)
        let edge_labels = List.mapi cycle ~f:(fun i vi ->
            get_edge vi (List.nth_exn cycle ((i + 1) mod k))) in
        (* label(i) = predicate on the *incoming* edge of node i = event of edge (i-1)→i *)
        let incoming_event i = fst (List.nth_exn edge_labels ((i - 1 + k) mod k)) in
        let outgoing_action i = snd (List.nth_exn edge_labels i) in
        let parts = List.init k ~f:(fun i ->
            incoming_event i ^ " (" ^ outgoing_action i ^ ")") in
        String.concat ~sep:" " parts ^ " " ^ incoming_event 0
      in
      (* Purely functional Kahn's topological sort *)
      let rec kahn in_deg result =
        let ready = List.filter_map (Map.to_alist in_deg)
            ~f:(fun (i, d) -> if d = 0 then Some i else None) in
        match ready with
        | [] ->     if Map.is_empty in_deg then
        (* DAG: everything processed *)
            Verdict.Possible (List.rev result)
          else begin
            (* There is a cycle: vertices remaining in in_deg *)
            let remaining = Map.keys in_deg in
            match find_cycle_in_subgraph adj remaining with
            | Some cycle ->
              Impossible (ERule ("There is an enforcement cycle: " ^
                                 format_cycle adj_labeled cycle ^ ". " ^
                                 "Break this cycle to proceed."))
            | None ->
              (* Should not happen if there is a cycle, but keep the old behaviour *)
              assert false
          end
        | i :: _ ->
          let in_deg = Map.remove in_deg i in
          let in_deg = List.fold (List.nth_exn adj i) ~init:in_deg
              ~f:(fun m j -> Map.update m j ~f:(function None -> 0 | Some k -> k - 1)) in
          kahn in_deg (i :: result)
      in
      (*List.iter clauses ~f:(fun clause -> print_endline (clause_to_string clause));*)
      Verdict.map (kahn in_deg []) ~f:(List.map ~f:(fun i -> List.nth_exn clauses i))

    let fix_predicate_names m pol e =
      match Map.find m e with
      | Some ({ switch_neg_opt = Some _ } as let_def) ->
        e ^ (if pol then "_pos" else "_neg")
      | _ -> e 

    let fix_predicate_names_clauses_constr m =
      List.map ~f:(fun (clauses, constrs) ->
          List.map clauses ~f:(fun { trigger; effects } ->
              { trigger = { guards = List.map ~f:(List.map ~f:(map_predicate ~pol:false ~f:(fix_predicate_names m))) trigger.guards;
                            filter = map_predicate ~pol:false ~f:(fix_predicate_names m) trigger.filter };
                effects = List.map ~f:(map_predicate ~f:(fix_predicate_names m)) effects }),
          constrs)

    let types (t: Enftype.t) (f: t) (b: Interval.v) =
      
      let set_b = function
        | Interval.U a -> Interval.B (a, b)
        | B _ as i -> i in

      (* Create a type-appropriate dummy constant for eliminating a quantified variable.
         If the Term module provides type info (e.g. Tterm), the correct type is used. *)
      let dummy_for_var x = Term.dummy_for_var x in

      let f = push_quants f in

      (*print_endline "1) after push_quants";
        print_endline (to_string f);*)
      
      let lets, f = do_pull_lets f in
      
      (*print_endline "2) pulled lets, obtained";
      print_endline ("lets:\n" ^ (String.concat ~sep:"\n" (List.map lets ~f:(fun (e, _, args, f) -> e ^ "(" ^ String.concat ~sep:", " (List.map ~f:(fun (a, _) -> Var.to_string a) args) ^  ") = " ^ to_string f))));
        print_endline ("f:\n" ^ to_string f);*)

      
      let f = match f.form with
        | Always (itv, f) when Interval.is_full itv -> f
        | And (s, fs) ->
          let fs = List.map ~f:(function
              | { form = Always (itv, f) } when Interval.is_full itv -> f
              | f -> f) fs in
          make_dummy (And (s, fs))
        | _ -> f in

      (*print_endline "3) removing Always";
        print_endline ("f:\n" ^ to_string f);*)

      let pred_map, mon_map, anti_mon_map = maps_of_lets lets in

      let order_clauses = order_clauses ~lets:pred_map ~let_ctxt_mon:mon_map ~let_ctxt_anti_mon:anti_mon_map in

      (* Main auxiliary function: normalize enforceable formula *)
      let rec aux (m: let_map) (t: Enftype.t) (f: t) : enf_sols =
        let open Verdict in
        let r = 
        match Enftype.is_causable t, Enftype.is_suppressable t with
        | true, true -> Impossible (Errors.EFormula (Some "no formula can be both causable and suppressable", f, t))
        | true, false -> begin
            match f.form with 
            | TT -> Possible [([{ trigger = init_trigger (make_dummy TT); effects = [] }], Constraints.CTT)]
            | Predicate (e, terms) -> begin
                match Map.find m e with
                | Some def -> 
                  let* solutions = def.cau_sols in
                  List.map solutions ~f:(fun (clauses, constr) ->
                      [{ trigger = init_trigger (make_dummy TT);
                         effects = [{ f with form = Predicate ("Cau_" ^ e, terms) }] }], constr)
                | None when Sig.mem e ->
                  let enftype = Sig.enftype_of_pred e in
                  if Enftype.geq enftype Enftype.cau then
                    Possible [([{ trigger = init_trigger (make_dummy TT);
                                  effects = [f] }],
                               Constraints.CConj [Constraints.CLeq (e, enftype);
                                                  Constraints.CGeq (e, Enftype.cau)])]
                  else Impossible (Errors.ECast (e, Enftype.cau, enftype))
                | None -> Impossible (Errors.ECast (e, Enftype.obs, Enftype.sup))
              end 
            | Neg f -> aux m (Enftype.neg t) f
            | And (_, fs) -> 
                let enf_sols_list = List.map ~f:(aux m t) fs in
                let** enf_sols = all enf_sols_list in
                let solutions_comb = Etc.cartesian enf_sols in
                disjs (List.map solutions_comb ~f:(fun solutions ->
                    let clauses, constrs = List.unzip solutions in
                    (* let* clauses = Verdict.all (List.map ~f:order_clauses clauses) in*)  
                    Possible [(List.concat clauses, Constraints.CConj constrs)]))
            | Or (L, f :: fs) ->
              let* solutions = aux m t f in
              List.map solutions ~f:(fun (clauses, constr) ->
                  List.map clauses ~f:(fun { trigger; effects } ->
                      { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, trigger.filter :: List.map fs ~f:(fun g -> make_dummy (Neg g))))) };
                        effects }),
                  constr)
            | Or (R, fs) ->
              let f = List.last_exn fs in
              let fs = fs |> List.rev |> List.tl_exn |> List.rev in
              let* solutions = aux m t f in
              List.map solutions ~f:(fun (clauses, constr) ->
                  List.map clauses ~f:(fun { trigger; effects } ->
                      { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, trigger.filter :: List.map fs ~f:(fun g -> make_dummy (Neg g))))) };
                        effects }),
                  constr) 
            | Or (_, fs) ->
              let rec run (left: t list) = function
                | [] -> Impossible (EDisj [])
                | f :: right ->
                  disj (let* solutions = aux m t f in
                         List.map solutions ~f:(fun (clauses, constr) ->
                             List.map clauses ~f:(fun { trigger; effects } ->
                                 { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, trigger.filter :: List.map (left @ right) ~f:(fun g -> make_dummy (Neg g))))) };
                                   effects }),
                             constr))
                    (run (f::left) right)
              in run [] fs
            | Imp (L, f, g) ->
              let* solutions = aux m (Enftype.neg t) f in
              List.map solutions
                ~f:(fun (clauses, constr) ->
                    List.map clauses ~f:(fun { trigger; effects } ->
                        { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, [trigger.filter; make_dummy (Neg g)]))) };
                          effects }),
                    constr) 
            | Imp (R, f, g) ->
              let* solutions = aux m t g in
              List.map solutions ~f:(fun (clauses, constr) ->
                  List.map clauses ~f:(fun { trigger; effects } ->
                      { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, [trigger.filter; f]))) };
                        effects }),
                  constr) 
            | Imp (_, f, g) ->
              disj
                (let* solutions = aux m (Enftype.neg t) f in
                 List.map solutions ~f:(fun (clauses, constr) ->
                     List.map clauses ~f:(fun { trigger; effects } ->
                         { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, [trigger.filter; make_dummy (Neg g)]))) };
                           effects }),
                     constr))
                (let* solutions = aux m t g in
                 List.map solutions ~f:(fun (clauses, constr) ->
                  List.map clauses ~f:(fun { trigger; effects } ->
                      { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, [trigger.filter; f]))) };
                        effects }),
                  constr))
            | Exists (x, f) ->
              aux m t (subst (Map.singleton (module Var) x (dummy_for_var x)) f)
            | Forall (x, f) ->
              let** solutions = aux m t f in
              disjs (List.map solutions ~f:(fun (clauses, constr) ->
                  match all (List.map clauses ~f:(fun { trigger; effects } ->
                      let vars = Some (Set.elements (fvs effects)) in
                      match normalize_trigger ~vars m trigger false f with
                      | Possible [trigger] -> Possible [{ trigger; effects }]
                      | Impossible error -> Impossible error)) with
                  | Possible clauses -> Possible [List.concat clauses, constr]
                  | Impossible errors -> Impossible errors))
            | Eventually (i, f) ->
              let** solutions = aux m t f in
              let solutions =
                List.filter_map solutions ~f:(fun (clauses, constr) ->
                    match Option.all (List.map clauses ~f:(fun { trigger; effects } ->
                        let is_trigger_trivial = match trigger.filter.form with TT -> true | _ -> false in
                        let are_effects_simple = List.for_all effects
                            ~f:(fun effect -> match effect.form with Predicate _  -> true | _ -> false) in
                        if is_trigger_trivial && are_effects_simple then
                          Some { trigger; effects = List.map effects ~f:(fun f -> make_dummy (Eventually (set_b i, f))) }
                        else
                          None))
                    with | Some clauses -> Some (clauses, constr)
                         | None -> None) in
              (match solutions with
               | [] -> Impossible (
                   Errors.EFormula (Some (
                       "this is not enforceable inside " ^
                       op_to_string (make_dummy (Eventually (i, f)))), f, t))
               | solutions -> Possible solutions)
            | Until (s, i, { form = TT }, g) ->
              aux m t { f with form = Eventually (i, g) }
            | Until (s, i, _, g) when Interval.has_zero i ->
              aux m t g
            | Next (i, f) when not (Interval.is_zero i) && Interval.has_zero i ->
              let inner_is, inner_fs = destruct_nexts f in
              let is = i :: inner_is in
              let fs = f :: inner_fs in
              let is = List.map ~f:set_b is in
              let f = Option.value ~default:f (List.last fs) in
              let** solutions = aux m t f in
              let solutions =
                List.filter_map solutions ~f:(fun (clauses, constr) ->
                    match Option.all (List.map clauses ~f:(fun { trigger; effects } ->
                        let are_effects_simple = List.for_all effects
                            ~f:(fun effect -> match effect.form with
                                | Predicate _ | Neg { form = Predicate _ } -> true | _ -> false) in
                        let suppressed = List.filter_map effects
                            ~f:(fun effect -> match effect.form with
                                | Neg ({ form = Predicate _ } as p) -> Some p | _ -> None) in
                        let is_trigger_trivial = match trigger.filter.form with
                          | TT -> true
                          | _ -> List.mem suppressed trigger.filter ~equal:core_equal in
                        let are_effects_simple = List.for_all effects
                            ~f:(fun effect -> match effect.form with
                                | Predicate _ | Neg { form = Predicate _ } -> true | _ -> false) in
                        if is_trigger_trivial && are_effects_simple then
                          begin
                            if not (List.is_empty effects) then
                              Some { trigger = init_trigger (make_dummy TT);
                                     effects = List.map effects ~f:(fun f ->
                                         make_dummy (construct_nexts is fs f.form)) } (* TODO[FH]: Set info properly? *)
                            else
                              None
                          end
                        else
                          None))
                    with | Some clauses -> Some (clauses, constr)
                         | None -> None) in
              (match solutions with
               | [] -> Impossible (
                   Errors.EFormula (Some (
                       "this is not enforceable inside " ^
                       op_to_string (make_dummy (Next (i, f)))), f, t))
               | solutions -> Possible solutions)
            | Label (_, f) -> aux m t f
            | _ -> Impossible (Errors.EFormula (None, f, t))
          end
        | false, true -> begin
            match f.form with
            | FF -> Possible [([{ trigger = init_trigger (make_dummy TT); effects = [] }], Constraints.CTT)]
            | Predicate (e, terms) -> begin
                match Map.find m e with
                | Some def ->
                  let* solutions = def.sup_sols in
                  List.map solutions ~f:(fun (clauses, constr) ->
                      [{ trigger = init_trigger f;
                         effects = [{ f with form = Predicate ("Sup_" ^ e, terms) }] }], constr)
                | None when Sig.mem e ->
                  let enftype = Sig.enftype_of_pred e in
                  if Enftype.geq enftype Enftype.sup then
                    Possible [[{ trigger = init_trigger f;
                                 effects = [make_dummy (Neg f)] }],
                              Constraints.CConj [Constraints.CLeq (e, enftype);
                                                 Constraints.CGeq (e, Enftype.sup)]]
                  else Impossible (Errors.ECast (e, enftype, Enftype.sup))
                | None -> Impossible (Errors.ECast (e, Enftype.obs, Enftype.sup))
              end
            | Neg f -> aux m (Enftype.neg t) f
            | Or (_, fs) ->
              let enf_sols_list = List.map ~f:(aux m t) fs in
              let enf_sols = all enf_sols_list in
              map ~f:(fun solutions_list ->
                  let solutions_comb = Etc.cartesian solutions_list in
                  List.filter_map solutions_comb ~f:(fun solutions ->
                      let clauses, constrs = List.unzip solutions in
                      (*match Verdict.all (List.map ~f:order_clauses clauses) with
                        | Possible clauses ->*) Some (List.concat clauses, Constraints.CConj constrs)
                      (*| Impossible _ -> None *))) enf_sols
            | And (L, f :: fs) ->
              let* solutions = aux m t f in
              List.map solutions ~f:(fun (clauses, constr) ->
                  List.map clauses ~f:(fun { trigger; effects } ->
                      { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, trigger.filter :: fs))) };
                        effects }),
                  constr)
            | And (R, fs) ->
              let f = List.last_exn fs in
              let fs = fs |> List.rev |> List.tl_exn |> List.rev in
              let* solutions = aux m t f in
              List.map solutions ~f:(fun (clauses, constr) ->
                  List.map clauses ~f:(fun { trigger; effects } ->
                      { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, trigger.filter :: fs))) };
                        effects }),
                  constr)
            | And (_, fs) ->
              let rec run (left: t list) = function
                | [] -> Impossible (EDisj [])
                | f :: right ->
                  disj (let* solutions = aux m t f in
                         List.map solutions ~f:(fun (clauses, constr) ->
                             List.map clauses ~f:(fun { trigger; effects } ->
                                 { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, trigger.filter :: left @ right))) };
                                   effects }),
                             constr))
                    (run (f::left) right)
              in run [] fs
            | Imp (L, f, g) ->
              let* solutions = aux m (Enftype.neg t) f in
              List.map solutions
                ~f:(fun (clauses, constr) ->
                    List.map clauses ~f:(fun { trigger; effects } ->
                        { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, [trigger.filter; make_dummy (Neg g)]))) };
                          effects }),
                    constr)
            | Imp (R, f, g) ->
              let* solutions = aux m t g in
              List.map solutions ~f:(fun (clauses, constr) ->
                  List.map clauses ~f:(fun { trigger; effects } ->
                      { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, [trigger.filter; f]))) };
                        effects }),
                  constr)
            | Imp (_, f, g) ->
              disj
                (let* solutions = aux m (Enftype.neg t) f in
                 List.map solutions ~f:(fun (clauses, constr) ->
                     List.map clauses ~f:(fun { trigger; effects } ->
                         { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, [trigger.filter; make_dummy (Neg g)]))) };
                           effects }),
                     constr))
                (let* solutions = aux m t g in
                 List.map solutions ~f:(fun (clauses, constr) ->
                  List.map clauses ~f:(fun { trigger; effects } ->
                      { trigger = { trigger with filter = ac_simplify (make_dummy (And (N, [trigger.filter; f]))) };
                        effects }),
                  constr))
            | Forall (x, f) ->
              aux m t (subst (Map.singleton (module Var) x (dummy_for_var x)) f)
            | Exists (x, f) ->
              let** solutions = aux m t f in
              disjs (List.map solutions ~f:(fun (clauses, constr) ->
                  match all (List.map clauses ~f:(fun { trigger; effects } ->
                      let vars = Some (Set.elements (fvs effects)) in
                      match normalize_trigger ~vars m trigger true f with
                      | Possible [trigger] -> Possible [{ trigger; effects }]
                      | Impossible error -> Impossible error)) with
                  | Possible clauses -> Possible [List.concat clauses, constr]
                  | Impossible errors -> Impossible errors))
            | Always (i, f) ->
              let* solutions = aux m t f in
              List.filter_map solutions ~f:(fun (clauses, constr) ->
                  match Option.all (List.map clauses ~f:(fun { trigger; effects } ->
                      let is_trigger_trivial = match trigger.filter.form with TT -> true | _ -> false in
                      let are_effects_simple = List.for_all effects
                          ~f:(fun effect -> match effect.form with Predicate _ -> true | _ -> false) in
                      if is_trigger_trivial && are_effects_simple then
                        Some { trigger; effects = List.map effects ~f:(fun f -> make_dummy (Eventually (set_b i, make_dummy (Neg f)))) }
                      else
                        None))
                  with | Some clauses -> Some (clauses, constr)
                       | None -> None)
            | Until (s, i, f, g) when Interval.has_zero i ->
              aux m t { f with form = And (s, [f; g]) }
            | Until (s, i, f, _) ->
              aux m t f
            | Next (i, f) when not (Interval.is_zero i) && Interval.has_zero i ->
              let inner_is, inner_fs = destruct_nexts f in
              let is = i :: inner_is in
              let fs = f :: inner_fs in
              let is = List.map ~f:set_b is in
              let f = Option.value ~default:f (List.last fs) in
              let** solutions = aux m t f in
              let solutions = 
              List.filter_map solutions ~f:(fun (clauses, constr) ->
                  match Option.all (List.map clauses ~f:(fun { trigger; effects } ->
                      let are_effects_simple = List.for_all effects
                          ~f:(fun effect -> match effect.form with
                              | Predicate _ | Neg { form = Predicate _ } -> true | _ -> false) in
                      let suppressed = List.filter_map effects
                          ~f:(fun effect -> match effect.form with
                              | Neg ({ form = Predicate _} as p) -> Some p | _ -> None) in
                      let is_trigger_trivial = match trigger.filter.form with
                        | TT -> true
                        | _ -> List.mem suppressed trigger.filter ~equal:core_equal in
                      if is_trigger_trivial && are_effects_simple then
                        begin
                          if not (List.is_empty effects) then
                            Some { trigger = init_trigger (make_dummy TT);
                                   effects = List.map effects ~f:(fun f ->
                                       make_dummy (construct_nexts is fs f.form)) } (* TODO[FH]: Set info properly? *)
                          else
                            Some { trigger = init_trigger (make_dummy TT);
                                   effects = [make_dummy (construct_nexts is fs TT)] }
                        end
                      else
                        None))
                  with | Some clauses -> Some (clauses, constr)
                       | None -> None) in
              (match solutions with
               | [] -> Impossible (
                   Errors.EFormula (Some (
                       "this is not enforceable inside " ^
                       op_to_string (make_dummy (Eventually (i, f)))), f, t))
               | solutions -> Possible solutions)
            | Label (_, f) -> aux m t f
            | _ -> Impossible (Errors.EFormula (None, f, t))
          end
        | false, false -> assert false
        in
        let r = Verdict.map r ~f:(fix_predicate_names_clauses_constr m) in
        (*print_endline (Printf.sprintf "aux(%s, %s) = %s" (to_string f) (Enftype.to_string t) (Verdict.verdict_to_string ~to_string:enf_sols_to_string r));*)
        r
      in

      let type_let_aux_sols m let_def =
        let body = let_def.body in
        let args = let_def.args |> List.map ~f:fst |> List.map ~f:Term.dummy_var in
        let cau_sols = aux m Enftype.cau body in
        let sup_sols = aux m Enftype.sup body in
        let cau_sols = Verdict.map ~f:(fix_predicate_names_clauses_constr m) cau_sols in
        let sup_sols = Verdict.map ~f:(fix_predicate_names_clauses_constr m) sup_sols in
        let set_enftype e t (clauses, constr)  =
          (List.map clauses ~f:(fun clause ->
               let n =
                 if Enftype.is_causable t
                 then "Cau_" ^ e
                 else "Sup_" ^ e in
               let g = make_dummy (Predicate (n, args)) in
               let c = { clause with
                 trigger =
                   { guards =
                       if List.is_empty clause.trigger.guards then [[g]]
                       else List.map ~f:(fun fs -> g :: fs) clause.trigger.guards;
                     filter = clause.trigger.filter } } in
               (*print_endline (clause_to_string c);*)
                 c
             ),
           Constraints.ac_simplify (Constraints.CConj [constr; CGeq (e, t); CLeq (e, t)])) in
        Verdict.map ~f:(List.map ~f:(set_enftype let_def.name Enftype.cau)) cau_sols,
        Verdict.map ~f:(List.map ~f:(set_enftype let_def.name Enftype.sup)) sup_sols in

      let type_let_aux m let_def trigger =
        let cau_sols, sup_sols = type_let_aux_sols m let_def in
        let trigger_pos = { trigger with filter = make_past_only true trigger.filter }
        and trigger_neg = { trigger with filter = make_past_only false trigger.filter } in
        let trigger_neg_opt =
          if equal_core_t trigger_pos.filter.form trigger_neg.filter.form
          then None
          else Some trigger_neg in
        cau_sols, sup_sols, trigger_pos, trigger_neg_opt in
      
      (* Type a let-bound expression *)
      let type_let ((m: let_map), (errors: Errors.error list)) (let_def: let_def)
        : let_map * (Errors.error list) =
        let open Verdict in
        let body = let_def.body in
        let args = let_def.args |> List.map ~f:fst |> List.map ~f:Term.dummy_var in
        (* Strip existential quantifiers *)
        let g = strip_exists body in
        (*print_endline ("normalize_trigger: " ^ let_def.name);*)
        (* Additional check for temporal operators *)
        match g.form with
        | Since (s, i, f, g) -> 
          begin
            let ft = normalize_trigger m (init_trigger f) false body in
            let gt = normalize_trigger m (init_trigger g) true body in
            match ft, gt with
            | Impossible error_f, Impossible error_g -> (m, error_f :: error_g :: errors)
            | Impossible error_f, _ -> (m, error_f :: errors)
            | _, Impossible error_g -> (m, error_g :: errors)
            | Possible [trigger_f], Possible [trigger_g] ->
              let _, sup_sols_f, trigger_pos_f, trigger_neg_opt_f = type_let_aux m { let_def with body = f } trigger_f in
              let cau_sols_g, sup_sols_g, trigger_pos_g, trigger_neg_opt_g = type_let_aux m { let_def with body = g } trigger_g in
              let switch_pos = SSince (trigger_pos_f, trigger_pos_g)
              and switch_neg_opt = Option.map2 ~f:(fun trigger_neg_f trigger_neg_g -> SSince (trigger_neg_f, trigger_neg_g)) trigger_neg_opt_f trigger_neg_opt_g in
              let cau_sols, sup_sols = 
                if Interval.has_zero i then
                  cau_sols_g, conj ~f:merge_clauses_constr sup_sols_f sup_sols_g
                else
                  Impossible (EFormula (Some "Since's interval does not contain 0", g, Enftype.cau)),
                  sup_sols_g
              in
              let cau_sols = Verdict.map cau_sols ~f:(fun clauses_constrs ->
                  List.map clauses_constrs ~f:(fun (clauses, constr) ->
                    List.map clauses ~f:(fun { trigger; effects } ->
                        let g = make_dummy (Predicate (let_def.name, args)) in
                        let filter = ac_simplify (make_dummy (
                            And (N, [trigger.filter; make_dummy (Neg g)]))) in
                        { trigger = { trigger with filter }; effects }), constr)) in
              let sup_sols = Verdict.map sup_sols ~f:(fun clauses_constrs ->
                  List.map clauses_constrs ~f:(fun (clauses, constr) ->
                    List.map clauses ~f:(fun { trigger; effects } ->
                        let g = make_dummy (Predicate (let_def.name, args)) in
                        let filter = ac_simplify (make_dummy (
                            And (N, [trigger.filter; g]))) in
                        { trigger = { trigger with filter }; effects }), constr)) in
              let m = Map.update m let_def.name
                  ~f:(fun _ -> { let_def with cau_sols = cau_sols;
                                              sup_sols = sup_sols;
                                              switch_pos_opt = Some switch_pos;
                                              switch_neg_opt }) in
              (m, errors)
          end
        | Once (i, f) -> 
          begin
            let ft = normalize_trigger m (init_trigger f) true body in
            match ft with
            | Impossible error_f -> (m, error_f :: errors)
            | Possible [trigger] ->
              let cau_sols, trigger_pos, trigger_neg_opt =
                if Interval.has_zero i then
                  let cau_sols, _, trigger_pos, trigger_neg_opt = type_let_aux m { let_def with body = f } trigger in
                  cau_sols, trigger_pos, trigger_neg_opt
                else
                  let _, _, trigger_pos, trigger_neg_opt = type_let_aux m { let_def with body = f } trigger in
                  Impossible (EFormula (Some "Once's interval does not contain 0", g, Enftype.cau)),
                  trigger_pos, trigger_neg_opt in
              let switch_pos = SOnce trigger_pos
              and switch_neg_opt = Option.map ~f:(fun trigger_neg -> SNow trigger_neg) trigger_neg_opt in
              let m = Map.update m let_def.name
                  ~f:(fun _ -> { let_def with cau_sols = cau_sols;
                                              switch_pos_opt = Some switch_pos;
                                              switch_neg_opt }) in
              (m, errors)
          end
        | Prev (i, f) -> 
          begin
            let ft = normalize_trigger m (init_trigger f) true body in
            match ft with
            | Impossible error_f -> (m, error_f :: errors)
            | Possible [trigger] ->
              let _, _, trigger_pos, trigger_neg_opt = type_let_aux m { let_def with body = f } trigger in
              let switch_pos = SPrev trigger_pos in
              let m = Map.update m let_def.name
                  ~f:(fun _ -> { let_def with switch_pos_opt = Some switch_pos }) in
              (m, errors)
          end
        | _ -> begin
            let gt = normalize_trigger m (init_trigger g) true body in
            match gt with
            | Impossible _ ->
              let cau_sols, sup_sols = type_let_aux_sols m let_def in
              let m = Map.update m let_def.name 
                  ~f:(fun _ -> { let_def with cau_sols = cau_sols; sup_sols = sup_sols }) in
              (m, errors)
            | Possible [trigger] ->
              let cau_sols, sup_sols, trigger_pos, trigger_neg_opt = type_let_aux m let_def trigger in
              let switch_pos = SNow trigger_pos
              and switch_neg_opt = Option.map ~f:(fun trigger_neg -> SNow trigger_neg) trigger_neg_opt in
              let m = Map.update m let_def.name
                  ~f:(fun _ -> { let_def with cau_sols = cau_sols;
                                              sup_sols = sup_sols;
                                              switch_pos_opt = Some switch_pos;
                                              switch_neg_opt }) in
              (m, errors)
          end
      in
      
      let raw_lets = lets in
      let lets = List.map lets ~f:(fun (name, enftype_opt, args, body) ->
          { name; args; body;
            cau_sols = Impossible (Errors.EFormula (None, body, Enftype.cau));
            sup_sols = Impossible (Errors.EFormula (None, body, Enftype.sup));
            switch_pos_opt = None; switch_neg_opt = None }) in
      let m, errors = List.fold_left ~init:(Map.empty (module String), []) ~f:type_let lets in

      match errors with
      | [] -> Verdict.Possible [raw_lets, m, aux m Enftype.cau f]
      | errors -> Impossible (EConj errors)


    let compile_clause ({ trigger; effects }: clause) =
      let f enftype = map_info ~f:(fun info -> { TypedInfo.dummy with info; enftype }) in
      let c = f Enftype.cau and s = f Enftype.sup and o = f Enftype.obs in
      let trigger = { trigger with filter = make_past_only true trigger.filter } in
      let effects : typed_t list = List.map effects ~f:(fun (effect: t) ->
          match effect.form with
          | Neg { form; info }
            (*| Eventually (_, { form = Neg { form; info } })*) ->
            let effect = s effect in
            { effect with info = { effect.info with enftype = Enftype.cau } }
          | _ -> c effect) in
      let init = ac_simplify
          { form = Imp (R, o (of_trigger true trigger),
                        { form = And (L, effects);
                          info = { TypedInfo.dummy with enftype = Enftype.cau } });
            info = { TypedInfo.dummy with enftype = Enftype.cau } } in
      let vars = Set.elements (fvs [init]) in
      let f = List.fold_right vars ~init
          ~f:(fun x f -> { form = Forall (x, f); info = { TypedInfo.dummy with enftype = Enftype.cau } }) in
      { f with form = Always (Interval.full, f) }

    let compile_formula lets fs : typed_t =
      let init = ac_simplify { form = And (LR, fs); info = { TypedInfo.dummy with enftype = Enftype.cau } } in
      List.fold_right lets ~init
        ~f:(fun (e, enftype, vars, f_pos, f_neg_opt, _) g ->
            match f_neg_opt with
            | Some f_neg ->
              { form = Let (e ^ "_pos", Enftype.obs, vars, f_pos,
                            { form = Let (e ^ "_neg", Enftype.obs, vars, f_neg, g);
                              info = { TypedInfo.dummy with enftype = Enftype.cau } });
                info = { TypedInfo.dummy with enftype = Enftype.cau } }
            | None ->
              { form = Let (e, Enftype.obs, vars, f_pos, g);
                info = { TypedInfo.dummy with enftype = Enftype.cau } })

    let find_let_clauses m sol key cau =
      match Map.find m key with
      | None -> None
      | Some def ->
        match if cau then def.cau_sols else def.sup_sols with
        | Impossible _ -> None
        | Possible solutions -> 
          match List.find solutions ~f:(fun (_, sub_constr) ->
              not (List.is_empty (
                  List.filter_map
                    (Constraints.solve (Constraints.ac_simplify sub_constr))
                    ~f:(fun sub_sol -> Constraints.try_merge (sol, sub_sol))))) with
          | None -> None
          | Some (sub_clauses, _) -> Some sub_clauses

    let compile_lets (m: let_map) (sol: (string, Enftype.Constraint.t, String.comparator_witness) Map.t) =
      List.map ~f:(fun (e, orig_enftype_opt, orig_args, orig_f) ->
        let enftype = match Map.find sol e with
          | Some constr -> Some (Enftype.Constraint.solve constr)
          | None -> orig_enftype_opt in
        let body_pos, body_neg_opt, clauses_opt =
          let default () = map_info ~f:(fun info -> { TypedInfo.dummy with info }) orig_f in
          ((match Option.bind (Map.find m e) ~f:(fun def -> Option.map def.switch_pos_opt ~f:(fun trigger_opt -> trigger_opt, def.args)) with
              | Some (trigger_pos, args) ->
                let f = of_switch true trigger_pos in
                let vars = Set.elements (Set.diff (fv f) (Set.of_list (module Var) (List.map ~f:fst args))) in
                let f = List.fold_right vars ~init:f ~f:(fun x f -> make_dummy (Exists (x, f))) in
                map_info ~f:(fun info -> { TypedInfo.dummy with info }) f
              | None -> default ()),
           ((match Option.bind (Map.find m e) ~f:(fun def -> Option.map def.switch_neg_opt ~f:(fun trigger_opt -> trigger_opt, def.args)) with
              | Some (trigger_pos, args) ->
                let f = of_switch true trigger_pos in
                let vars = Set.elements (Set.diff (fv f) (Set.of_list (module Var) (List.map ~f:fst args))) in
                let f = List.fold_right vars ~init:f ~f:(fun x f -> make_dummy (Exists (x, f))) in
                Some (map_info ~f:(fun info -> { TypedInfo.dummy with info }) f)
              | None -> None)), 
           match enftype with
           | Some et when Enftype.is_causable et && not (Enftype.is_suppressable et) ->
             find_let_clauses m sol e true
           | Some et when Enftype.is_suppressable et && not (Enftype.is_causable et) ->
             find_let_clauses m sol e false
           | _ -> None)
        in
        (e, enftype, orig_args, body_pos, body_neg_opt, clauses_opt))

    type pg_map = (string, Etc.string_set_list, String.comparator_witness) Map.t
    type t_map  = (string, Enftype.t * int list, String.comparator_witness) Map.t

    type compiled_let =
      string
      * Enftype.t option
      * (Var.t * Dom.tt option) list
      * typed_t
      * typed_t option
      * clause list option
        
    let do_type ?(verbose=true) ?(moderate=true) f b =
      let orig_f = f in
      let error err =
        Stdio.print_endline ("The formula\n "
                             ^ to_string f
                             ^ "\nis not enforceable:\n"
                             ^ Errors.to_string (Errors.ac_simplify err));
        raise (FormulaError (Printf.sprintf "this formula is not enforceable")) in
      let f = f |> push_negs |> convert_vars |> convert_lets |> unroll_let ~moderate |> simplify |> ac_simplify in
      if not (Set.is_empty (fv f)) && verbose then (
        Stdio.print_endline ("The formula\n "
                             ^ to_string f
                             ^ "\nis not closed: free variables are "
                             ^ String.concat ~sep:", " (List.map ~f:Var.to_string (Set.elements (fv f))));
        ignore (raise (FormulaError (Printf.sprintf "this formula is not closed"))));
      match types Enftype.cau f b with
      | Impossible err -> error err
      | Possible [lets, m, sols] ->
        match sols with
        | Verdict.Impossible err -> error err
        | Possible solutions ->
          (*print_endline ("len(solutions)="^string_of_int (List.length solutions));*)
          match (Verdict.disjs (List.map solutions ~f:(fun (clauses, constr) ->
              (*print_endline "checking one solution!";
                print_endline ("m:\n" ^ let_map_to_string m);
                print_endline ("lets:\n" ^ (String.concat ~sep:"\n" (List.map lets ~f:(fun (e, _, _, f) -> e ^ "(...) = " ^ to_string f))));
                print_endline ("clauses:\n" ^ (String.concat ~sep:"\n" (List.map clauses ~f:(fun { trigger; effects } -> to_string trigger.filter ^ " → " ^ String.concat ~sep:" & " (List.map ~f:to_string effects)))));
                print_endline ("constr:\n" ^ Constraints.to_string constr);*)
              let constr = Constraints.ac_simplify constr in
              match Constraints.solve constr with
              | sol::_ ->
                let lets = compile_lets m sol lets in
                (*print_endline ("lets:\n" ^ (String.concat ~sep:"\n" (List.map lets ~f:(fun (a, b, c, d, _, _) -> a ^ "(...) = " ^ to_string_value d))));*)
                let pred_map, mon_map, anti_mon_map = maps_of_lets (List.map ~f:(fun (a, b, c, d, _, _) -> (a, b, c, d)) lets) in
                (*let order_clauses = order_clauses ~lets:pred_map ~let_ctxt_mon:mon_map ~let_ctxt_anti_mon:anti_mon_map in*)
                let let_clauses = List.concat (List.filter_map lets ~f:(fun (_, _, _, _, _, clauses_opt) -> clauses_opt)) in
                (*print_endline "##clauses##";
                print_endline (String.concat ~sep:"\n" (List.map ~f:clause_to_string (clauses @ let_clauses)));
                  print_endline "##endclauses##";*)
                (*begin match (order_clauses (clauses @ let_clauses) with
                  | Possible clauses -> 
                    let fs = List.map clauses ~f:compile_clause in
                    Verdict.Possible [compile_formula lets fs]
                  | Impossible err -> Impossible err*)
                let fs = List.map (clauses @ List.rev let_clauses) ~f:compile_clause in
                Verdict.Possible [compile_formula lets fs]
              | [] -> Impossible (ERule ("Constraint system " ^ Constraints.to_string constr ^ " is not solvable"))))) with
          | Possible (f::_) -> f
          | Impossible err -> error err

    let do_type_and_compile ?(verbose=true) ?(moderate=true) f b =
      let orig_f = f in
      let error err =
        Stdio.print_endline ("The formula\n "
                             ^ to_string f
                             ^ "\nis not enforceable:\n"
                             ^ Errors.to_string (Errors.ac_simplify err));
        raise (FormulaError (Printf.sprintf "this formula is not enforceable")) in
      let f = f |> push_negs |> convert_vars |> convert_lets |> unroll_let ~moderate |> simplify |> ac_simplify in
      if not (Set.is_empty (fv f)) && verbose then (
        Stdio.print_endline ("The formula\n "
                             ^ to_string f
                             ^ "\nis not closed: free variables are "
                             ^ String.concat ~sep:", " (List.map ~f:Var.to_string (Set.elements (fv f))));
        ignore (raise (FormulaError (Printf.sprintf "this formula is not closed"))));
      match types Enftype.cau f b with
      | Impossible err -> error err
      | Possible [lets, m, sols] ->
        (match sols with
        | Verdict.Impossible err -> error err
        | Possible solutions ->
          match (Verdict.disjs (List.map solutions ~f:(fun (clauses, constr) ->
              let constr = Constraints.ac_simplify constr in
              match Constraints.solve constr with
              | sol::_ ->
                let lets = compile_lets m sol lets in
                let pred_map, mon_map, anti_mon_map = maps_of_lets (List.map ~f:(fun (a, b, c, d, _, _) -> (a, b, c, d)) lets) in
                let let_clauses = List.concat (List.filter_map lets ~f:(fun (_, _, _, _, _, clauses_opt) -> clauses_opt)) in
                let all_clauses = clauses @ List.rev let_clauses in
                let fs = List.map all_clauses ~f:compile_clause in
                Verdict.Possible [(lets, all_clauses, m, compile_formula lets fs)]
              | [] -> Impossible (ERule ("Constraint system " ^ Constraints.to_string constr ^ " is not solvable"))))) with
          | Possible ((lets, all_clauses, m, f)::_) -> (lets, all_clauses, m, f)
          | Impossible err -> error err)

  end

end
