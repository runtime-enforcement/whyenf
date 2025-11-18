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

  let rec core_equal (f: t) (g: t) =
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
      flag : bool
    } [@@deriving compare, sexp_of, hash, equal]

  module TypedInfo : Modules.I with type t = typed_info = struct

    type t = typed_info [@@deriving compare, sexp_of, hash, equal]

    let to_string l s info =
      if Enftype.is_only_observable info.enftype then
        s
      else
        Printf.sprintf (Etc.paren l 0 "%s : %s") s (Enftype.to_string info.enftype)

    let dummy = { info = Info.dummy; enftype = Enftype.bot; filter = Filter.tt; flag = false }

  end 

  type core_typed_t = (TypedInfo.t, Var.t, Dom.t, Term.t) _core_t
  type typed_t      = (TypedInfo.t, Var.t, Dom.t, Term.t) _t

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
    | EqConst (trm, _) -> (match Term.unvar_opt trm with
                           | Some x -> Set.of_list (module Var) [x]
                           | None   -> Set.empty (module Var))
    | Predicate (_, trms) -> Set.of_list (module Var) (Term.fv_list trms)
    | Predicate' (_, _, f) -> fv f
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

  let rec predicates f = match f.form with
    | TT
      | FF
      | EqConst _ -> []
    | Predicate (r, trms) -> [r, trms]
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
      | Always(_, f) 
      | Agg (_, _, _, _, f)
      | Top (_, _, _, _, f)
      | Type (f, _)
      | Label (_, f) -> predicates f
    | Imp (_, f, g)
      | Since (_, _, f, g)
      | Until (_, _, f, g) -> predicates f @ predicates g
    | And (_, fs)
      | Or (_, fs) -> List.concat_map fs ~f:predicates

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

  (* Generates EXISTS x1, ..., xk. f where {x1, ..., xk} are the free variables of f not in y  *)

  let exists_of_agg y f info =
    (*print_endline ("exists_of_agg " ^ to_string f);*)
    let z = List.filter (list_fv f) ~f:(fun x -> not (List.mem y x ~equal:Var.equal_ident)) in
    (*print_endline ("-> " ^ to_string (List.fold_right z ~f:(fun z f -> { form = Exists (z, f); info = info z f }) ~init:f));*)
    List.fold_right z ~f:(fun z f -> { form = Exists (z, f); info = info z f }) ~init:f

  (* Unrolling of let bindings *)

  let unroll_let =
    let rec aux (v : (string, Var.t list * t, String.comparator_witness) Map.t) f =
      let form = match f.form with
        | TT -> TT
        | FF -> FF
        | EqConst (x, c) -> EqConst (x, c)
        | Predicate (r, trms) ->
           (match Map.find v r with
            | None -> Predicate (r, trms)
            | Some (vars, e) -> Predicate' (r, trms, subst (Map.of_alist_exn (module Var) (List.zip_exn vars trms)) e))
        | Let (r, enftype, vars, f, g) ->
           Let' (r, enftype, vars, aux v f, aux (Map.update v r ~f:(fun _ -> (List.map ~f:fst vars, aux v f))) g)
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
           (fun i v -> let (i, v'), vars = List.fold_map vars ~init:(i, v) ~f:(fun a (v, x) -> let a, v = fresh a v in (a, (v, x))) in
                       let f, (i, _) = aux f i v' in
                       ((fun g -> return (Let (r, enftype, vars, f, g))) >>= (aux g)) i v)
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

  (* AC-rewriting *)
  
  let rec ac_simplify_core ?(debug=false) =
    let unpr' f = match f.form with Predicate' (_, _, f) -> f.form | _ -> f.form in
    let or_bool f g = match unpr' f with TT -> TT | FF -> FF | _ -> g f in
    let ac_simplify = ac_simplify ~debug in
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

  and ac_simplify ?(debug=false) f =
    (*if debug then
      print_endline (Printf.sprintf "ac_simplify(%s)=%s" (to_string_value f) (to_string_value {f with form =ac_simplify_core f.form}));*)
    { f with form = ac_simplify_core ~debug f.form }
      
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
      | Let _ -> raise (FormulaError "Let bindings must be unrolled to compute a relative interval") in
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
    let rec _strict itv fut f =
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
          | Let _ -> raise (FormulaError "Let bindings must be unrolled to compute strictness"))
    in not (_strict itv fut f)

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

  let rec non_monotone_predicates ?(let_ctxt_mon: 'str_str_info_map=Map.empty (module String)) ?(let_ctxt_anti_mon: 'str_str_info_map=Map.empty (module String)) ?(init_mon: 'str_info_map=Map.empty (module String)) ?(init_anti_mon: 'str_info_map= Map.empty (module String)) f : ('str_info_map * 'str_info_map) =
    (** computes the predicates that appear none-(anti)-monotonely in a formula f
        along with information such as a which occurrence of a predicate is none-(anti)-monotone *)
    (* Because f.info is 'abstract' one cannot directly access lexing positional information
       The position information will later be extracted and combined *)
    let combine_str_info_maps m1 m2 =
      Map.merge m1 m2 ~f:(fun ~key:_ -> function
          | `Both (v1, v2) -> Some (v1 @ v2)
          | `Left v -> Some v
          | `Right v -> Some v) in
    match f.form with
    | TT | FF | EqConst (_, _) -> init_mon, init_anti_mon
    | Predicate (r, _) ->
      let mon =
        if Map.mem let_ctxt_mon r then
          combine_str_info_maps init_mon (Map.find_exn let_ctxt_mon r)
        else init_mon in
      let anti_mon =
        if Map.mem let_ctxt_anti_mon r then
          combine_str_info_maps init_anti_mon (Map.find_exn let_ctxt_anti_mon r)
        else Map.update init_anti_mon r
              ~f:(fun info -> match info with
                    | None -> [f.info]
                    | Some info -> f.info :: info) in
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
      let preds = predicates_of_formula f in
      let mon = combine_str_info_maps init_mon preds in
      let anti_mon = combine_str_info_maps init_anti_mon preds in
      mon, anti_mon
    | And (_, fs)
    | Or (_, fs) ->
      let mono_maps = List.map fs ~f:(fun f ->
        non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon ~init_mon ~init_anti_mon f) in
      List.fold ~f:(fun (init_mon, init_anti_mon) (mon, anti_mon) ->
        let mon = combine_str_info_maps init_mon mon in
        let anti_mon = combine_str_info_maps init_anti_mon anti_mon in
        mon, anti_mon) ~init:(init_mon, init_anti_mon) mono_maps
    | Imp (_, f, g)
    | Until (_, _, f, g)
    | Since (_, _, f, g) ->
      let f_mon, f_anti_mon =
        non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon ~init_mon ~init_anti_mon f in
      let g_mon, g_anti_mon =
        non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon ~init_mon ~init_anti_mon g in
      let mon = combine_str_info_maps f_mon g_mon in
      let anti_mon = combine_str_info_maps f_anti_mon g_anti_mon in
      mon, anti_mon
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

    (* Past-guardedness check *)

    let eib r i b = Printf.sprintf "%s.%d.%b" r i b

    type pg_map = (string, Etc.string_set_list, String.comparator_witness) Map.t
    type t_map  = (string, Enftype.t * int list, String.comparator_witness) Map.t

    let rec solve_past_guarded (ts: pg_map) (x: Var.t) p (f:('i, Var.t, Dom.t, Term.t) _t)  =
      let matches ts x r i t = Term.equal (Term.dummy_var x) t && Map.mem ts (eib r i p) in
      let map_var default f t = match Term.unvar_opt t with Some y -> f y | None -> default in
      let rec aux ts x p (f: ('i, Var.t, Dom.t, Term.t) _t) =
        let s =
          match f.form, p with
          | TT, false -> [Set.empty (module String)]
          | FF, true -> [Set.empty (module String)]
          | EqConst (y, _), true ->
             map_var [] (fun y -> if Var.equal_ident x y
                                  then [Set.empty (module String)] else []) y
          | Predicate (r, trms), _ when List.existsi ~f:(matches ts x r) trms ->
            (*print_endline "Predicate--case 1";*)
             let f i t = if matches ts x r i t then Some (Map.find_exn ts (eib r i p)) else None in
             List.concat (List.filter_mapi trms ~f)
          | Predicate (r, trms), true
               when List.exists ~f:(map_var false (Var.equal_ident x)) trms
                    && Sig.mem r
                    && Enftype.is_observable (Sig.enftype_of_pred r) ->
               (*print_endline "Predicate--case 2";*)
             [Set.singleton (module String) r]
          | Predicate' (_, _, f), _ -> aux ts x p f
          | Let (e, _, vars, f, g), _ ->
            (*let f i ts z =
               let ts = Map.update ts (eib e i true) ~f:(fun _ -> aux ts z true f) in
               Map.update ts (eib e i false) ~f:(fun _ -> aux ts z false f) in
              let ts = List.foldi vars ~init:ts ~f in*)
            let ts = solve_past_guarded_multiple_vars ts vars e f in
            aux ts x p g
          | Let' (_, _, _, _, f), _ -> aux ts x p f
          | Agg (s, _, t, _, f), true when Var.equal_ident s x ->
             let sols_list = List.map (Term.fv_list [t]) ~f:(fun z -> aux ts z p f) in
             List.map ~f:(Etc.inter_list (module String)) (Etc.cartesian sols_list)
          | Agg (_, _, _, y, f), _ when List.mem y x ~equal:Var.equal_ident ->
             aux ts x p f
          | Top (_, _, _, y, f), _ when List.mem y x ~equal:Var.equal_ident -> aux ts x p f
          | Top (s, _, x', _, f), true when List.mem s x ~equal:Var.equal_ident ->
             (*print_endline "#############################";
               print_endline "solve_past_guarded.Top--begin";*)
             let sols_list = List.map (Term.fv_list x') ~f:(fun z -> aux ts z p f) in
             (*print_endline "solve_past_guarded.Top--end";
               print_endline "#############################";
               print_endline "";
               print_endline "";*)
             List.map ~f:(Etc.inter_list (module String)) (Etc.cartesian sols_list)
          | Neg f, _ -> aux ts x (not p) f
          | And (_, fs'), true | Or (_, fs'), false ->
             Etc.dedup ~equal:Set.equal (List.concat_map fs' ~f:(aux ts x p))
          | Imp (_, f', g'), false ->
             Etc.dedup ~equal:Set.equal (aux ts x (not p) f' @ aux ts x p g')
          | And (_, fs'), false | Or (_, fs'), true ->
             List.map ~f:(Etc.inter_list (module String)) (Etc.cartesian (List.map fs' ~f:(aux ts x p)))
          | Imp (_, f', g'), true ->
             List.map ~f:(Etc.inter_list (module String)) (Etc.cartesian [aux ts x (not p) f'; aux ts x p g'])
          | Exists (y, f), _ | Forall (y, f), _ when not (Var.equal_ident x y) -> aux ts x p f
          | Prev (_, f), true | Once (_, f), true -> aux ts x p f
          | Once (i, f), false | Eventually (i, f), false when Interval.has_zero i -> aux ts x p f
          | Historically (_, f), false | Always (_, f), false -> aux ts x p f
          | Historically (i, f), true | Always (i, f), true when Interval.has_zero i -> aux ts x p f
          | Since (_, i, f, g), true when not (Interval.has_zero i) ->
             aux ts x p (make (conj N f g) f.info)
          | Since (_, _, _, g), true -> aux ts x p g
          | Since (_, i, _, g), false | Until (_, i, _, g), false when Interval.has_zero i -> aux ts x p g
          | Until (_, i, f, _), true when not (Interval.has_zero i) -> aux ts x p f
          | Until (_, _, f, g), true -> aux ts x p (make (disj N f g) f.info)
          | Label (_, f), _ -> aux ts x p f
          | _ -> [] in
        (*Stdio.print_endline (Printf.sprintf "solve_past_guarded(%s, %s, %b) = [%s]"
                               (Var.to_string x)
                               (to_string_value f) p
                               (*(String.concat ~sep:"; " (List.map ~f:(fun (k, _) -> Printf.sprintf "%s -> [%s]" k (String.concat ~sep:"; " (List.map ~f:(fun es -> "{" ^ (String.concat ~sep:", " (Set.elements es)) ^ "}") s))) (Map.to_alist ts)))*)
                               (String.concat ~sep:"; " (List.map ~f:(fun es -> "{" ^ (String.concat ~sep:", " (Set.elements es)) ^ "}") s)) );*)
        (*Stdio.print_endline (Printf.sprintf "solve_past_guarded([%s], %s, %b, %s) = [%s]"
                         (String.concat ~sep:"; " (List.map ~f:(fun (k, _) -> Printf.sprintf "%s -> %s" k (String.concat ~sep:"; " (List.map ~f:(fun es -> "{" ^ (String.concat ~sep:", " (Set.elements es)) ^ "}") s))) (Map.to_alist ts)))
          (Var.to_string x) p (op_to_string f)
          (String.concat ~sep:"; " (List.map ~f:(fun es -> "{" ^ (String.concat ~sep:", " (Set.elements es)) ^ "}") s)) );*)        s in
      aux ts x p f

    and solve_past_guarded_multiple_vars (ts: pg_map) (x: (Var.t * Dom.tt option) list) e f : pg_map =
      let f i ts (x, _) = 
        let ts = Map.update ts (eib e i true) ~f:(fun _ -> let r = solve_past_guarded ts x true f in (*Stdio.print_endline ("add_mapping: " ^ eib e i true ^ " -> " ^ (String.concat ~sep:"; " (List.map ~f:(fun es -> "{" ^ (String.concat ~sep:", " (Set.elements es)) ^ "}") r)));*) r) in
        Map.update ts (eib e i false) ~f:(fun _ -> let r = solve_past_guarded ts x false f in   (*Stdio.print_endline ("add_mapping: " ^ eib e i true ^ " -> " ^ (String.concat ~sep:"; " (List.map ~f:(fun es -> "{" ^ (String.concat ~sep:", " (Set.elements es)) ^ "}") r)));*) r)
      in List.foldi x ~init:ts ~f

    let solve_past_guarded_multiple ts (x : Var.t) e fs =
      Etc.inter_string_set_list (List.map ~f:(solve_past_guarded ts x e) fs)

    let is_past_guarded ?(ts=Map.empty (module String)) x p f =
      not (List.is_empty (solve_past_guarded ts x p f))

    let is_past_guarded_multiple ?(ts=Map.empty (module String)) x p =
      List.for_all ~f:(is_past_guarded ~ts x p) 

    (* Present filters *)

    let rec present_filter_ ?(b=true) f =
      let open Filter in
      let filter = 
        match f.form with
        | TT -> if b then tt else ff
        | FF -> if b then ff else tt
        | Predicate (e, _) when b ->
           (match Sig.kind_of_pred e with
            | Trace when Enftype.is_observable (Sig.enftype_of_pred e) -> An e
            | _ -> tt)
        | Neg f -> present_filter_ ~b:(not b) f
        | And (_, fs) when b -> AllOf (List.map ~f:(present_filter_ ~b) fs)
        | And (_, fs) -> OneOf (List.map ~f:(present_filter_ ~b) fs)
        | Or (_, fs) when b -> OneOf (List.map ~f:(present_filter_ ~b) fs)
        | Or (_, fs) -> AllOf (List.map ~f:(present_filter_ ~b) fs)
        | Imp (_, f, g) when b -> OneOf [present_filter_ ~b:(not b) f; present_filter_ ~b g]
        | Imp (_, f, g) -> AllOf [present_filter_ ~b:(not b) f; present_filter_ ~b g]
        | Exists (_, f) | Forall (_, f) | Label (_, f) | Predicate' (_, _, f) -> present_filter_ ~b f
        | _ -> tt
      in (*print_endline (Printf.sprintf "present_filter_ %s (%s) = %s" (Bool.to_string b) (formula_to_string f) (to_string filter));*)
      filter

    let present_filter ?(b=true) f =
      let filter = Filter.simplify (present_filter_ ~b f) in
      (*print_endline (Printf.sprintf "present_filter %s (%s) = %s" (Bool.to_string b) (formula_to_string f) (Filter.to_string filter));*)
      filter

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

      type verdict = Possible of constr | Impossible of Errors.error

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

      let conj c d = match c, d with
        | Possible CTT, _ -> d
        | _, Possible CTT -> c
        | Impossible c, Impossible d -> Impossible (Errors.ac_simplify (EConj [c; d]))
        | Impossible c, _ | _, Impossible c -> Impossible c
        | Possible c, Possible d -> Possible (ac_simplify (CConj [c; d]))

      let disj c d = match c, d with
        | Impossible c, Impossible d -> Impossible (Errors.ac_simplify (EDisj [c; d]))
        | Impossible _, _ -> d
        | _, Impossible _ -> c
        | Possible CTT, _ | _, Possible CTT -> Possible CTT
        | Possible c, Possible d -> Possible (ac_simplify (CDisj [c; d]))

      let conjs = function
        | [] -> Possible CTT
        | c::cs -> List.fold_left ~init:c ~f:conj cs
      
      let disjs = function
        | [] -> Impossible (EDisj [])
        | c::cs -> List.fold_left ~init:c ~f:disj cs

      let rec cartesian a = function
          [] -> []
        | h::t -> (List.map a ~f:(fun x -> (x, h))) @ cartesian a t

      let try_merge (a, b) =
        try Some (Map.merge a b ~f:merge)
        with CannotMerge -> None

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

      let verdict_to_string = function
        | Possible c -> Printf.sprintf "Possible(%s)" (to_string c)
        | Impossible e -> Printf.sprintf "Impossible(%s)" (Errors.to_string e)

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

    (* Predicate e must have enftype at least t, at most its type in ts, and not be CauSup*)
    let types_predicate_lower (ts: t_map) (t: Enftype.t) (e: string) =
      let t' = fst (Map.find_exn ts e) in
      if Enftype.geq t' t then
        Constraints.Possible (CConj [Constraints.geq e t; Constraints.leq e t'])
      else
        Constraints.Impossible (ECast (e, t', t))

    (* Predicate e must be strict; only add the constraint if the event is more than obs *)
    let types_predicate_strict (ts: t_map) (e: string) =
      let t' = fst (Map.find_exn ts e) in
      let t' = Enftype.meet t' Enftype.sct in
      if Enftype.leq t' Enftype.obs then
        Constraints.Possible CTT
      else
        Constraints.Possible (Constraints.leq e t')

    let terms_are_strict trms =
      List.for_all (Term.fn_list trms) ~f:(fun name -> Sig.strict_of_func name)

    let observable ?(itl_observable=Map.empty (module String)) f =
      List.for_all (predicates f)
        ~f:(fun (e, _) -> match Map.find itl_observable e with
                          | Some b -> b
                          | None -> Enftype.is_observable (Sig.enftype_of_pred e))

    let observable_multiple ?(itl_observable=Map.empty (module String)) =
      List.for_all ~f:(observable ~itl_observable)

    let strictly_relative_past
          ?(itl_itvs=Map.empty (module String))
          ?(itl_strict=Map.empty (module String))
          ?(itl_observable=Map.empty (module String)) f =
      relative_past ~itl_itvs f && strict ~itl_strict f && observable ~itl_observable f
    
    let types
          ?(itl_itvs=Map.empty (module String))
          ?(itl_strict=Map.empty (module String))
          ?(itl_observable=Map.empty (module String))
          (t: Enftype.t) (pgs: pg_map) (f: t) =
      let error s = Constraints.Impossible (EFormula (Some s, f, t)) in
      let strictly_relative_past = strictly_relative_past ~itl_itvs ~itl_strict ~itl_observable in
      let transparently = Enftype.geq t Enftype.tcausable || Enftype.geq t Enftype.tsuppressable in
      let only_if_strictly_relative_past fs constr =
        if not transparently then
          constr
        else
          (let not_srp = List.filter fs ~f:(fun f -> not (strictly_relative_past f)) in
           match not_srp with
           | [] -> constr
           | fs -> error (Printf.sprintf "for transparent causability %s must be SRP"
                            (String.concat ~sep:", " (List.map ~f:to_string fs)))) in
      let only_if_bounded i constr =
        if not transparently || Interval.is_bounded i then
          constr
        else
          error (Printf.sprintf "for transparent causability the interval %s must be bounded"
                   (Interval.to_string i)) in
      let rolling_only_if_strictly_relative_past fs f_to_constr =
        let rec aux acc = function
          | [] -> Constraints.Possible CTT
          | [f] -> only_if_strictly_relative_past acc (f_to_constr f)
          | f :: fs -> Constraints.disj
                         (aux (f::acc) fs)
                         (only_if_strictly_relative_past (acc@fs) (f_to_constr f)) in
        aux [] fs in
      let ts = Sig.pred_enftype_map () in
      let rec aux (t: Enftype.t) (pgs: pg_map) (ts: t_map) (f: t) =
        (*print_endline (Printf.sprintf "types: t=%s, f=%s" (Enftype.to_string t) (to_string f));*)
        let aux' t f = aux t pgs ts f in
        let r = match Enftype.is_causable t, Enftype.is_suppressable t with
          | true, true ->
             Constraints.Impossible (
                 EFormula (Some (to_string f
                                 ^ " is never both causable and suppressable"), f, t))
          | true, false -> begin
              match f.form with
              | TT -> Constraints.Possible CTT
              | Predicate (e, terms) ->
                 let _, is     = Map.find_exn ts e in
                 let terms     = List.filteri terms
                                   ~f:(fun i _ -> List.mem is i ~equal:Int.equal) in
                 let fvs       = Term.fv_list terms in
                 let fvs_ids   = Etc.dedup ~equal:String.equal (List.map ~f:Var.ident fvs)  in
                 let es        = List.map fvs_ids
                                   ~f:(fun x -> Option.value (Map.find pgs x) ~default:[]) in
                 let unguarded = List.filter_map (List.zip_exn fvs_ids es) ~f:(fun (x, e) ->
                                     if List.is_empty e then Some x else None) in
                 (match List.map ~f:(Set.union_list (module String)) (Etc.cartesian es) with
                  | [] -> Impossible (EFormula (Some ("no guards found for "
                                                      ^ String.concat ~sep:", " unguarded), f, t))
                  | es_ncau_list ->
                     let c =
                       (if terms_are_strict terms then (
                          (*print_endline "case 1";*)
                          Constraints.disjs
                            (List.map es_ncau_list ~f:(fun es_ncau ->
                                 Constraints.conj (types_predicate_lower ts t e)
                                   (Constraints.conjs (List.map (Set.elements es_ncau)
                                                         ~f:(types_predicate_strict ts)))))
                        )
                        else if Enftype.is_strict t then (
                          (*print_endline "case 2";*)
                          error (Printf.sprintf
                                   "the predicate %s cannot be SCau since it has non-strict terms"
                                   (to_string f))
                        )
                        else (
                          (*print_endline "case 3";*)
                          Constraints.disjs
                            (List.map es_ncau_list ~f:(fun es_ncau ->
                                 Constraints.conj (types_predicate_lower ts Enftype.ncaubot e)
                                   (Constraints.conjs (List.map (Set.elements es_ncau)
                                                         ~f:(types_predicate_strict ts))))))
                       )
                     in c) 
              | Let (e, enftype, vars, f, g) ->
                 let f_unguarded i (x, _) = if not (is_past_guarded x false f) then Some (x, i) else None in
                 let unguarded_x, unguarded_i = List.unzip (List.filter_mapi vars ~f:f_unguarded) in
                 let pgs' = List.fold_left unguarded_x ~init:pgs ~f:(fun m x -> Map.update m (Var.ident x) ~f:(fun _ -> [Set.empty (module String)])) in
                 let pgs'' = solve_past_guarded_multiple_vars pgs vars e f in
                 Constraints.conj (aux enftype pgs' ts f) (aux t pgs'' (Map.update ts e ~f:(fun _ -> enftype, unguarded_i)) g)
              | Neg f -> aux' (Enftype.neg t) f 
              | And (_, fs) ->
                 only_if_strictly_relative_past fs (Constraints.conjs (List.map ~f:(aux' t) fs))
              | Or (L, f :: fs) ->
                 only_if_strictly_relative_past fs (aux' t f)
              | Or (R, fs) ->
                 only_if_strictly_relative_past (List.drop_last_exn fs) (aux' t f)
              | Or (_, fs) ->
                 rolling_only_if_strictly_relative_past fs (aux' t)
              | Imp (L, f, g) ->
                 only_if_strictly_relative_past [g] (aux' (Enftype.neg t) f)
              | Imp (R, f, g) ->
                 only_if_strictly_relative_past [f] (aux' t g)
              | Imp (_, f, g) ->
                 Constraints.disj
                   (only_if_strictly_relative_past [g] (aux' (Enftype.neg t) f))
                   (only_if_strictly_relative_past [f] (aux' t g))
              | Exists (x, f) ->
                 aux t (Map.update pgs (Var.ident x) ~f:(fun _ -> [Set.empty (module String)])) ts f
              | Forall (x, f) ->
                 let es = solve_past_guarded pgs x false f in
                 (match es with
                  | [] -> error ("for causability " ^ Var.to_string x ^ " must be past-guarded")
                  | _  -> aux t (Map.update pgs (Var.ident x) ~f:(fun _ -> es)) ts f)
              | Next (i, f) when Interval.has_zero i && not (Interval.is_zero i) -> aux' t f
              | Next _ -> error "○ with non-[0,a) interval, a > 0, is never causable"
              | Once (i, g) when Interval.has_zero i -> aux' t g
              | Since (_, i, f, g) when Interval.has_zero i ->
                 only_if_strictly_relative_past [f] (aux' t g)
              | Once _ | Since _ -> error "⧫[a,b) or S[a,b) with a > 0 is never causable"
              | Eventually (i, f) -> only_if_bounded i (aux' t f)
              | Always (_, f) -> aux' t f
              | Until (LR, i, f, g) ->
                 only_if_bounded i (Constraints.conj (aux' t f) (aux' t g))
              | Until (_, i, f, g) when Interval.has_zero i ->
                 only_if_bounded i (only_if_strictly_relative_past [f] (aux' t g))
              | Until (_, i, f, g) ->
                 only_if_bounded i (Constraints.conj (aux' t f) (aux' t g))
              | Prev _ -> error "● is never causable"
              | Label (_, f) -> aux' t f
              | _ -> Impossible (EFormula (None, f, t))
            end
          | false, true -> begin
              match f.form with
              | FF -> Possible CTT
              | Predicate (e, _) -> types_predicate_lower ts t e
              | Let (e, enftype, vars, f, g) ->
                 let f_unguarded i (x, _) = if not (is_past_guarded x false f) then Some (x, i) else None in
                 let unguarded_x, unguarded_i = List.unzip (List.filter_mapi vars ~f:f_unguarded) in
                 let pgs' = List.fold_left unguarded_x ~init:pgs ~f:(fun m x -> Map.update m (Var.ident x) ~f:(fun _ -> [Set.empty (module String)])) in
                 let pgs'' = solve_past_guarded_multiple_vars pgs vars e f in
                 Constraints.conj (aux enftype pgs' ts f) (aux t pgs'' (Map.update ts e ~f:(fun _ -> Enftype.ncau, unguarded_i)) g)
              | Agg (_, _, _, (_::_ as y), f) -> aux t pgs ts (exists_of_agg y f (fun _ _ -> Info.dummy))
              | Top (_, _, _, (_::_ as y), f) -> aux t pgs ts (exists_of_agg y f (fun _ _ -> Info.dummy))
              | Neg f -> aux' (Enftype.neg t) f
              | And (L, f :: fs) ->
                 only_if_strictly_relative_past fs (aux' t f)
              | And (R, fs) ->
                 only_if_strictly_relative_past (List.drop_last_exn fs) (aux' t (List.last_exn fs))
              | And (_, fs) ->
                 rolling_only_if_strictly_relative_past fs (aux' t)
              | Or (_, fs) ->
                 only_if_strictly_relative_past fs (Constraints.conjs (List.map ~f:(aux' t) fs))
              | Imp (_, f, g) ->
                 only_if_strictly_relative_past [f; g] (Constraints.conj (aux' (Enftype.neg t) f) (aux' t g))
              | Exists (x, f) ->
                 let es = solve_past_guarded pgs x true f in
                 (match es with
                  | [] -> error ("for suppressability " ^ Var.to_string x ^ " must be past-guarded")
                  | _  -> aux t (Map.update pgs (Var.ident x) ~f:(fun _ -> es)) ts f)
              | Forall (_, f) -> aux' t f
              | Next (_, f) -> aux' t f
              | Historically (i, f) when Interval.has_zero i -> aux' t f
              | Historically _ -> error "■[a,b) with a > 0 is never suppressable"
              | Since (_, i, f, g) when not (Interval.has_zero i) ->
                 only_if_strictly_relative_past [g] (aux' t f)
              | Since (_, _, f, g) ->
                 Constraints.conj (only_if_strictly_relative_past [g] (aux' t f)) (aux' t g)
              | Eventually (_, f) -> aux' t f
              | Always (i, f) ->
                 only_if_bounded i (aux' t f)
              | Until (L, i, f, _) when not (Interval.has_zero i) -> aux' t f
              | Until (R, _, f, g) ->
                 only_if_strictly_relative_past [f] (aux' t g)
              | Until (_, i, f, g) when not (Interval.has_zero i) ->
                 only_if_strictly_relative_past [g] (aux' t f)
              | Until (_, _, _, g) ->
                 only_if_strictly_relative_past [f] (aux' t g)
              | Prev _ -> error "● is never suppressable"
              | Label (_, f) -> aux' t f
              | _ -> Impossible (EFormula (None, f, t))
            end
          | false, false -> Possible CTT
        in
        (*Stdio.printf "types.aux(%s, %s)=%s\n" (Enftype.to_string t) (to_string f) (Constraints.verdict_to_string r);*)
        r
      in aux t pgs ts f

    let rec convert b enftype formula : typed_t option =
      let rec of_formula (f : t) : typed_t =
        let form = match f.form with
          | TT -> TT
          | FF -> FF
          | EqConst (t, c) -> EqConst (t, c)
          | Predicate (e, ts) -> Predicate (e, ts)
          | Predicate' (e, ts, f) -> Predicate' (e, ts, of_formula f)
          | Let (e, typ_opt, vars, f, g) -> Let (e, typ_opt, vars, of_formula f, of_formula g)
          | Let' (e, typ_opt, vars, f, g) -> Let' (e, typ_opt, vars, of_formula f, of_formula g)
          | Agg (s, op, x, y, f) -> Agg (s, op, x, y, of_formula f)
          | Top (s, op, x, y, f) -> Top (s, op, x, y, of_formula f)
          | Neg f -> Neg (of_formula f)
          | And (s, fs) -> And (s, List.map ~f:of_formula fs)
          | Or (s, fs) -> Or (s, List.map ~f:of_formula fs)
          | Imp (s, f, g) -> Imp (s, of_formula f, of_formula g)
          | Exists (x, f) -> Exists (x, of_formula f)
          | Forall (x, f) -> Forall (x, of_formula f)
          | Prev (i, f) -> Prev (i, of_formula f)
          | Next (i, f) -> Next (i, of_formula f)
          | Once (i, f) -> Once (i, of_formula f)
          | Eventually (i, f) -> Eventually (i, of_formula f)
          | Historically (i, f) -> Historically (i, of_formula f)
          | Always (i, f) -> Always (i, of_formula f)
          | Since (s, i, f, g) -> Since (s, i, of_formula f, of_formula g)
          | Until (s, i, f, g) -> Until (s, i, of_formula f, of_formula g)
          | Type (f, ty) -> Type (of_formula f, ty)
          | Label (s, f) -> Label (s, of_formula f)
        in
        let enftype = if observable f then Enftype.obs else Enftype.bot in
        { form; info = { info = f.info; enftype; filter = Filter.tt; flag = false } }
      in
      let convert = convert b in
      let default_L (s: Side.t) = if Side.equal s R then Side.R else L in
      let opt_filter (x : typed_t option) = match x with
        | Some x -> x.info.filter
        | None   -> Filter.tt in
      let conj_filter ?(b=true) ?(neg=false) f g =
        (Filter.conj (present_filter ~b f) (present_filter ~b:(if neg then not b else b) g)) in
      let conj_filters ?(b=true) = function
        | [] -> Filter.tt
        | fs -> Filter.conjs (List.map ~f:(present_filter ~b) fs) in
      let set_b = function
        | Interval.U a -> Interval.B (a, b)
        | B _ as i -> i in
      let apply1 ?(temporal=false) ?(flag=false) f comb  =
        Option.map f ~f:comb, (if temporal then Filter.tt else opt_filter f), flag in
      let apply1' ?(new_filter=None) ?(flag=false) f comb =
        Some (comb f), Option.fold new_filter ~init:Filter.tt ~f:Filter.conj, flag in
      let apply2 ?(temporal=false) ?(flag=false) f g comb =
        Option.map2 f g ~f:comb,
        (if temporal then Filter.tt else Filter.disj (opt_filter f) (opt_filter g)), flag in
      let applyn ?(temporal=false) ?(flag=false) (fs: typed_t option list) comb =
        Option.map ~f:comb (Option.all fs),
        (if temporal then Filter.tt else Filter.disjs (List.map ~f:opt_filter fs)), flag in
      let apply2' ?(temporal=false) ?(flag=false) f g comb new_filter =
        Option.map f ~f:(fun x -> comb x g),
        (if temporal then Filter.tt else Filter.conj (opt_filter f) new_filter), flag in
      let f, filter, flag =
        (*print_endline "Convert:";
        print_endline ("formula: " ^ to_string formula);
        print_endline ("operator: " ^ op_to_string formula);
        print_endline ("enftype: " ^ Enftype.to_string enftype);
        print_endline ("is_causable: " ^ Bool.to_string (Enftype.is_causable enftype));
        print_endline ("is_suppressable: " ^ Bool.to_string (Enftype.is_suppressable enftype));*)
        match Enftype.is_causable enftype, Enftype.is_suppressable enftype with
        | true, _ -> begin
            match formula.form with
            | TT -> Some TT, Filter.tt, false
            | Predicate (e, trms) when Enftype.is_causable (Sig.enftype_of_pred e) ->
               Some (Predicate (e, trms)), Filter.tt, false
            | Predicate' (e, trms, f) ->
               apply1 (convert enftype f)
                 (fun mf -> Predicate' (e, trms, mf)) 
            | Let' (e, enftype', vars, f, g) ->
               apply2 (convert enftype' f) (convert enftype g)
                 (fun mf mg -> Let' (e, enftype', vars, mf, mg)) 
            | Neg f -> apply1 (convert (Enftype.neg enftype) f) (fun mf -> Neg mf) 
            | And (s, fs) -> applyn (List.map ~f:(convert enftype) fs)
                               (fun mfs -> And (default_L s, mfs))
            | Or (L, f :: gs) -> apply2' (convert enftype f) (List.map ~f:of_formula gs)
                                   (fun mf mgs -> Or (L, mf :: mgs))
                                   (conj_filters ~b:false gs)
            | Or (R, fs) -> let fs, g = List.drop_last_exn fs, List.last_exn fs in
                            apply2' (convert enftype g) (List.map ~f:of_formula fs)
                              (fun mg mfs -> Or (R, mfs @ [mg]))
                              (conj_filters ~b:false fs)
            | Or (_, fs) ->
               begin
                 let converted_fs = List.map ~f:(convert enftype) fs in
                 match List.findi converted_fs ~f:(fun _ -> Option.is_some) with
                 | Some (mf_i, mf_opt) -> 
                    let mf = Option.value_exn mf_opt in
                    let gs = List.filteri fs ~f:(fun i _ -> not Int.(i = mf_i)) in
                    apply1' ~new_filter:(Some (conj_filters ~b:false fs))
                      (List.map ~f:of_formula gs)
                      (fun mgs -> Or (L, mf :: mgs))
                 | None -> None, Filter.tt, false
               end
            | Imp (L, f, g) -> apply2' (convert (Enftype.neg enftype) f) (of_formula g)
                                 (fun mf mg -> Imp (L, mf, mg)) 
                                 (conj_filter ~neg:true f g)
            | Imp (R, f, g) -> apply2' (convert enftype g) (of_formula f)
                                 (fun mg mf -> Imp (R, mf, mg)) 
                                 (conj_filter ~neg:true f g)
            | Imp (_, f, g) ->
               begin
                 match convert (Enftype.neg enftype) f with
                 | Some mf -> apply1'
                                ~new_filter:(Some (conj_filter ~neg:true f g))
                                (of_formula g)
                                (fun mg -> Imp (L, mf, mg)) 
                 | None    -> apply2' (convert enftype g) (of_formula f)
                                (fun mg mf -> Imp (R, mf, mg)) 
                                (conj_filter ~neg:true f g)
               end
            | Exists (x, f) ->
               begin
                 match convert enftype f with
                 | Some mf -> Some (Exists (x, mf)), mf.info.filter, true
                 | None    -> None, Filter.tt, false
               end
            | Forall (x, f) ->
               begin
                 match convert enftype f with
                 | Some mf -> Some (Forall (x, mf)), mf.info.filter, false
                 | None    -> None, Filter.tt, false
               end
            | Next (i, f) when Interval.has_zero i && not (Interval.is_zero i) -> 
               apply1 ~temporal:true (convert enftype f) (fun mf -> Next (i, mf))
            | Once (i, f) when Interval.has_zero i ->
               apply1 (convert enftype f) (fun mf -> Once (i, mf))
            | Since (_, i, f, g) when Interval.has_zero i ->
               apply2' (convert enftype g) (of_formula f)
                 (fun mg mf -> Since (R, i, mf, mg)) 
                 Filter.tt
            | Eventually (i, f) ->
               apply1 ~temporal:true ~flag:(Interval.is_bounded i) (convert enftype f)
                 (fun mf -> Eventually (set_b i, mf)) 
            | Always (i, f) ->
               apply1 ~temporal:true ~flag:true (convert enftype f)
                 (fun mf -> Always (i, mf))
            | Until (LR, i, f, g) ->
               apply2 ~temporal:true ~flag:(Interval.is_bounded i) (convert enftype f) (convert enftype g)
                 (fun mf mg -> Until (LR, set_b i, mf, mg))
            | Until (_, i, f, g) when Interval.has_zero i ->
               apply2' ~temporal:true ~flag:(Interval.is_bounded i) (convert enftype g) (of_formula f)
                 (fun mg mf -> Until (R, set_b i, mf, mg))
                 Filter.tt
            | Until (_, i, f, g) ->
               apply2 ~temporal:true ~flag:(Interval.is_bounded i) (convert enftype f) (convert enftype g)
                 (fun mf mg -> Until (LR, set_b i, mf, mg))
            | Label (s, f) -> apply1 (convert enftype f) (fun mf -> Label (s, mf))
            | _ -> None, Filter.tt, false
          end
        | _, true -> begin
            match formula.form with
            | FF -> Some FF, Filter.tt, false
            | Predicate (e, trms) when Enftype.is_suppressable (Sig.enftype_of_pred e) ->
               Some (Predicate (e, trms)), Filter.An e, false
            | Predicate' (e, trms, f) ->
               apply1 (convert enftype f)
                 (fun mf -> Predicate' (e, trms, mf)) 
            | Let' (e, enftype', vars, f, g) ->
               apply2 (convert enftype' f) (convert enftype g)
                 (fun mf mg -> Let' (e, enftype', vars, mf, mg)) 
            | Agg (_, _, _, y, f) | Top (_, _, _, y, f) ->
               begin
                 match convert enftype (exists_of_agg y f (fun _ _ -> f.info)) with
                 | Some mf -> apply1' (of_formula formula)
                                (fun mg -> And (L, [mf; mg]))
                 | None    -> None, Filter.tt, false
               end
            | Neg f -> apply1 (convert (Enftype.neg enftype) f) (fun mf -> Neg mf)

            | And (L, f :: gs) -> apply2' (convert enftype f) (List.map ~f:of_formula gs)
                                    (fun mf mgs -> And (L, mf :: mgs))
                                    (conj_filters gs)
            | And (R, fs) -> let fs, g = List.drop_last_exn fs, List.last_exn fs in
                             apply2' (convert enftype g) (List.map ~f:of_formula fs)
                               (fun mg mfs -> And (R, mfs @ [mg]))
                               (conj_filters fs)
            | And (_, fs) ->
               begin
                 let converted_fs = List.map ~f:(convert enftype) fs in
                 match List.findi converted_fs ~f:(fun _ -> Option.is_some) with
                 | Some (mf_i, mf_opt) ->
                    let mf = Option.value_exn mf_opt in
                    let gs = List.filteri fs ~f:(fun i _ -> not Int.(i = mf_i)) in
                    apply1' ~new_filter:(Some (conj_filters fs))
                      (List.map ~f:of_formula gs)
                      (fun mgs -> And (L, mf :: mgs))
                 | None -> None, Filter.tt, false
               end
            | Or (s, fs) -> applyn (List.map ~f:(convert enftype) fs)
                               (fun mfs -> Or (default_L s, mfs))
            | Imp (s, f, g) -> apply2 (convert (Enftype.neg enftype) f) (convert enftype g)
                                 (fun mf mg -> Imp (default_L s, mf, mg))
            | Exists (x, f) ->
               begin
                 match convert enftype f with
                 | Some mf -> Some (Exists (x, mf)), mf.info.filter, true
                 | None    -> None, Filter.tt, false
               end
            | Forall (x, f) ->
               begin
                 match convert enftype f  with
                 | Some mf -> Some (Forall (x, mf)), mf.info.filter, false
                 | None    -> None, Filter.tt, false
               end
            | Next (i, f) -> apply1 ~temporal:true (convert enftype f)
                               (fun mf -> Next (i, mf)) 
            | Historically (i, f) when Interval.has_zero i ->
               apply1 (convert enftype f) (fun mf -> Historically (i, mf)) 
            | Since (_, i, f, g) when not (Interval.has_zero i) ->
               apply2' (convert enftype f) (of_formula g)
                 (fun mf mg -> Since (L, i, mf, mg)) 
                 Filter.tt
            | Since (_, i, f, g) ->
               let since_f = of_formula (make_dummy (Since (N, i, f, g))) in
               apply2 (convert enftype f) (convert enftype g)
                 (fun mf mg ->
                   let f = And (L, [mf; since_f]) in
                   Or (L, [mg; make f { info = formula.info; enftype; filter = Filter.tt; flag = false }]))
            | Eventually (i, f) ->
               apply1 ~temporal:true ~flag:true (convert enftype f)
                 (fun mf -> Eventually (i, mf))
            | Always (i, f) ->
               apply1 ~temporal:true ~flag:(Interval.is_bounded i) (convert enftype f)
                 (fun mf -> Always (set_b i, mf))
            | Until (L, i, f, g) when not (Interval.has_zero i) ->
               apply2' ~temporal:true ~flag:true (convert enftype f) (of_formula g)
                 (fun mf mg -> Until (L, i, mf, mg))
                 Filter.tt
            | Until (R, i, f, g) ->
               apply2' ~temporal:true ~flag:true (convert enftype g) (of_formula f)
                 (fun mg mf -> Until (R, i, mf, mg))
                 Filter.tt
            | Until (_, i, f, g) when not (Interval.has_zero i) ->
               begin
                 match convert enftype f with
                 | None    ->
                    apply2' ~temporal:true (convert enftype g) (of_formula f)
                      (fun mg mf -> Until (R, i, mf, mg))
                      Filter.tt
                 | Some mf ->
                    apply1' ~flag:true (of_formula g)
                      (fun mg -> Until (L, i, mf, mg))
               end
            | Until (_, i, f, g) ->
               apply2' ~temporal:true ~flag:true (convert enftype g) (of_formula f)
                 (fun mg mf -> Until (R, i, mf, mg))
                 Filter.tt
            | Label (s, f) -> apply1 (convert enftype f) (fun mf -> Label (s, mf))
            | _ -> None, Filter.tt, false
          end
        | _, _ -> let f = of_formula formula in
                  Some f.form, Filter.tt, false
      in
      let enftype = if observable formula then Enftype.join Enftype.obs enftype else enftype in
      let r = (match f with
               | Some f -> Some (make f { info = formula.info; enftype; filter; flag })
               | None -> None) in
      (*print_endline (Printf.sprintf "MFOTL.convert(%s,%s)" (match r with Some f -> to_string_typed f | _ -> "") (Filter.to_string filter));*)
      r

    let convert' b f =
      convert b Enftype.causable f

    let do_type f b =
      let orig_f = f in
      let f = convert_lets f in
      if not (Set.is_empty (fv f)) then (
        Stdio.print_endline ("The formula\n "
                             ^ to_string f
                             ^ "\nis not closed: free variables are "
                             ^ String.concat ~sep:", " (List.map ~f:Var.to_string (Set.elements (fv f))));
        ignore (raise (FormulaError (Printf.sprintf "formula %s is not closed" (to_string f)))));
      match types Enftype.causable (Map.empty (module String)) f with
      | Possible c ->
         begin
           let c = Constraints.ac_simplify c in
           (*print_endline (Constraints.to_string c);*)
           match Constraints.solve c with
           | sol::_ ->
              begin
                (*print_endline "Computed enforceability types:";*)
                let set_enftype ~key ~data bound =
                  if Sig.mem key then (
                    let enftype = Enftype.Constraint.solve data in
                    Sig.update_enftype key enftype;
                    (*print_endline (Printf.sprintf "%s: %s" key (Enftype.to_string enftype));*)
                    bound
                  )
                  else (
                    Sig.add_letpred_empty key;
                    key::bound
                  ) in
                let _ = Map.fold sol ~init:[] ~f:set_enftype in
                let f = f |> unroll_let |> simplify |> convert_vars in
                (*List.iter (Set.elements (fv f)) ~f:(fun v -> print_endline ("var: " ^  (Var.to_string v)));*)
                match convert' b f with
                | Some f' -> let f' = ac_simplify ~debug:true f' in
                             Stdio.print_endline ("The formula\n "
                                                  ^ to_string orig_f
                                                  ^ "\nis enforceable and types to\n "
                                                  ^ to_string_typed f');
                             f'
                | None    -> Stdio.print_endline ("The formula\n "
                                                  ^ to_string f
                                                  ^ "\n cannot be converted.");
                             raise (FormulaError (Printf.sprintf "formula %s cannot be converted"
                                                    (to_string f)))
              end
           | _ -> Stdio.print_endline ("The formula\n "
                                       ^ to_string orig_f
                                       ^ "\nis not enforceable because the constraint\n "
                                       ^ Constraints.to_string c
                                       ^ "\nhas no solution.");
                  raise (FormulaError (Printf.sprintf "formula %s is not enforceable" (to_string f)))
         end
      | Impossible e ->
         Stdio.print_endline ("The formula\n "
                              ^ to_string orig_f
                              ^ "\nis not enforceable. To make it enforceable, you would need to\n "
                              ^ Errors.to_string e);
         raise (FormulaError (Printf.sprintf "formula %s is not enforceable" (to_string f)))


    let is_transparent (f: typed_t) = 
      let rec aux (f: typed_t) = 
        (*print_endline ("aux " ^ to_string f);*)
        let b =
          let flag = f.info.flag in
          match Enftype.is_causable f.info.enftype, Enftype.is_suppressable f.info.enftype with
          | true, false -> begin
              match f.form with
              | TT | Predicate (_, _) -> true
              | Neg f | Exists (_, f) | Forall (_, f)
                | Once (_, f) | Next (_, f) | Historically (_, f) | Always (_, f)
                | Predicate' (_, _, f) | Let' (_, _, _, _, f) | Label (_, f) -> aux f
              | Eventually (_, f) -> flag && aux f
              | Or (L, [f; g]) | Imp (L, f, g)
                -> aux f && strictly_relative_past g
              | Or (R, [f; g]) | Imp (R, f, g)
                -> aux g && strictly_relative_past f
              | And (_, fs) -> List.for_all ~f:strictly_relative_past fs
              | Since (_, _, f, g) -> aux g && strictly_relative_past f
              | Until (R, _, f, g) -> flag && aux g && strictly_relative_past f
              | Until (LR, _, f, g) -> flag && aux f && aux g
              | _ -> false
            end
          | false, true -> begin
              let flag = f.info.flag in
              match f.form with
              | FF | Predicate (_, _) -> true
              | Neg f | Exists (_, f) | Forall (_, f)
                | Once (_, f) | Next (_, f) | Historically (_, f) | Eventually (_, f)
                | Predicate' (_, _, f) | Let' (_, _, _, _, f) | Label (_, f) -> aux f
              | Always (_, f) -> flag && aux f
              | And (L, f :: gs) 
                -> aux f && List.for_all ~f:strictly_relative_past gs
              | And (R, (_::_ as fs)) ->
                 aux (List.last_exn fs) && List.for_all ~f:strictly_relative_past (List.drop_last_exn fs)
              | Or (_, fs) -> List.for_all ~f:strictly_relative_past fs
              | Since (L, _, f, g) -> aux f && strictly_relative_past g
              | Until (R, _, f, g) -> aux g && strictly_relative_past f
              | Until (_, _, f, g) -> aux f && strictly_relative_past g
              | _ -> false
            end
          | _ -> raise (FormulaError (
                            Printf.sprintf
                              "cannot check transparency of formula with type %s: type must be either causable or suppressable, but not both"
                          (Enftype.to_string f.info.enftype)))
        in b
      in
      aux f

    
  end

end

