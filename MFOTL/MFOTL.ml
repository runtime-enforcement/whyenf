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
      | Let' (_, _, _, _, f) -> height f
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
      | Top (_, _, _, _, f) -> 1 + height f
    | Imp (_, f, g)
      | Since (_, _, f, g)
      | Until (_, _, f, g)
      | Let (_, _, _, f, g) -> max (height f) (height g) + 1
    | And (_, fs)
      | Or (_, fs) -> 1 + List.fold_left ~f:max ~init:0 (List.map ~f:height fs)

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

  let print_stats f =
    Stdio.printf "Formula size   = %d\nFormula height = %d\n" (size f) (height f)

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
      
  (* AC-rewriting *)
  
  (* Remove duplicate sub-formulas, preserving the order of first occurrence.
     Polymorphic in the info type, so structural [Poly.equal] is used (formulas
     are first-order data).  O(n²) but the lists here are short; enforces ∧/∨
     idempotence. *)
  let stable_dedup fs =
    List.rev (List.fold fs ~init:[] ~f:(fun acc f ->
        if List.mem acc f ~equal:Poly.equal then acc else f :: acc))

  (* Drop list elements that are subsumed by another element.  [parts_of] maps an
     element to the set of atoms whose *superset* makes it redundant:
       - in an OR of ANDs:  (A∧B) ∨ (A∧B∧C) ≡ (A∧B)   — drop the superset conjunction
       - in an AND of ORs:  (A∨B) ∧ (A∨B∨C) ≡ (A∨B)   — drop the superset disjunction
     Order is preserved (∧/∨ carry an enforcement Side, so children are not
     reordered); ties between equal part-sets are broken by position. *)
  let remove_subsumed parts_of fs =
    List.filteri fs ~f:(fun i f ->
        let fp = parts_of f in
        not (List.existsi fs ~f:(fun j g ->
            j <> i
            && List.for_all (parts_of g) ~f:(fun c -> List.mem fp c ~equal:Poly.equal)
            && (List.length (parts_of g) < List.length fp || j < i))))

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
       (* Idempotence (A ∧ A ≡ A): drop duplicate conjuncts, keeping first occurrence. *)
       let fs = stable_dedup fs in
       (* Absorption (A ∧ (A ∨ B) ≡ A): drop conjuncts that are a superset
          disjunction of another conjunct. *)
       let disjuncts_of f' = match unpr' f' with Or (_, gs) -> gs | _ -> [f'] in
       let fs = remove_subsumed disjuncts_of fs in
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
       (* Idempotence (A ∨ A ≡ A): drop duplicate disjuncts, keeping first occurrence. *)
       let fs = stable_dedup fs in
       (* Subsumption (A ∨ (A ∧ B) ≡ A): drop disjuncts that are a superset
          conjunction of another disjunct. *)
       let conjuncts_of f' = match unpr' f' with And (_, gs) -> gs | _ -> [f'] in
       let fs = remove_subsumed conjuncts_of fs in
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
      let f = ac_simplify f in
      (match unpr' f with TT -> TT | FF -> FF | _ -> Exists (x, f))
    | Forall (x, f) ->
      let f = ac_simplify f in
      (match unpr' f with TT -> TT | FF -> FF | _ -> Forall (x, f))
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
    | Type (f, ty) ->
      let f = ac_simplify f in
      (match unpr' f with FF -> FF | TT -> TT | _ -> Type (f, ty))
    | Label (s, f) ->
      let f = ac_simplify f in
      (match unpr' f with FF -> FF | TT -> TT | _ -> Label (s, f))

  and ac_simplify f =
    let form = ac_simplify_core f.form in
    { f with form }
      
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
          (*print_endline (Printf.sprintf "ac_simplify(%s)=" (to_string_value f));*)
          let f = ac_simplify (aux v f) in
          (*print_endline (Printf.sprintf "%s" (to_string_value f));*)
          let v' b = Map.update v r ~f:(fun _ -> (b, List.map ~f:fst vars, f)) in
          (* Do not unroll if: moderate is false OR binding is trivial OR there are captured variables *)
          (if moderate && height f > 1
              && Set.is_subset (fv f)
                (Set.of_list (module Var) (List.map ~f:fst vars)) then
             Let (r, enftype, vars, f, aux (v' true) g)
          else
             Let' (r, enftype, vars, f, aux (v' false) g))
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
                        >>= (aux f)) i v)
        | Top (s, op, x, y, f) ->
           (fun i v -> (*let x = Term.substs v x in
                       let y = subst_vars v y in*)
                       let fvs = Set.elements (Set.diff (fv f) (Set.of_list (module Var) ((Term.fv_list x) @y))) in
                       let (i, v'), _ = List.fold_map fvs ~init:(i, v) ~f:fresh in
                       ((fun f -> return (Top (subst_vars v s, op, Term.substs v' x, subst_vars v' y, f)))
                        >>= (aux f)) i v)
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
        | Agg (s, op, x, y, f) -> let form = Agg (s, op, x, y, aux true f) in if p then form else Neg { f with form }
        | Top (s, op, x, y, f) -> let form = Top (s, op, x, y, aux true f) in if p then form else Neg { f with form }
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
    (* TODO: push quants into Once etc. if possible *)
    let rec add_quants f = function
      | [] -> f
      | (true, x) :: quants -> Forall (x, make_dummy (add_quants f quants))
      | (false, x) :: quants -> Exists (x, make_dummy (add_quants f quants)) in
    let rec add_exists f = function
      | (false, x) :: quants -> Exists (x, make_dummy (add_quants f quants))
      | _ -> f in
    let sort_quants ?(only=None) quants fs = 
      let (quants_global, quants_one, _, _) =
        List.fold_right quants ~init:([], [], true, only)
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
        | Prev (i, f) ->
          let quants_global, quants_one = sort_quants ~only:(Some false) quants [f] in
          let f = add_relevant_quants quants_one f in
          add_quants (Prev (i, f)) quants
        | Next (i, f) -> add_quants (Next (i, aux [] f)) quants
        | Once (i, f) ->
          let quants_global, quants_one = sort_quants ~only:(Some false) quants [f] in
          let f = add_relevant_quants quants_one f in
          add_quants (Once (i, f)) quants
        | Eventually (i, f) -> add_quants (Eventually (i, aux [] f)) quants
        | Historically (i, f) ->
          let quants_global, quants_one = sort_quants ~only:(Some true) quants [f] in
          let f = add_relevant_quants quants_one f in
          add_quants (Historically (i, f)) quants
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


end
