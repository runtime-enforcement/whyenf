open Base
open MFOTL_lib
open Tyformula

module Var  = Tterm.TypedVar
module Term = Tterm

(* ------------------------------------------------------------------ *)
(* let_extraction record                                                *)
(* ------------------------------------------------------------------ *)

type let_def = {
  le_name    : string;
  le_enftype : Enftype.t option;
  le_args    : (Var.t * Dom.tt option) list;
  le_body    : Tyformula.t;   (* body after ac_simplify / pull_lets recursion *)
  le_origin  : Tyformula.t;   (* original formula node before transformation *)
}

let let_def_to_string le =
  Printf.sprintf "LET %s(%s)%s = %s IN" le.le_name
    (Etc.string_list_to_string (List.map ~f:string_of_opt_typed_var le.le_args))
    (Option.value_map le.le_enftype ~default:"" ~f:Enftype.to_string_let)
    (Tyformula.to_string le.le_body)

(* ------------------------------------------------------------------ *)
(* strip_exists / add_back_exists                                       *)
(* ------------------------------------------------------------------ *)

let strip_exists f =
  match f |> all_exists |> snd |> List.last with
  | Some f -> f
  | _ -> f

let add_back_exists f xs fs =
  List.fold_right (List.zip_exn xs fs)
    ~f:(fun (x, f') f -> { f' with form = Exists (x, f) }) ~init:f

(* ------------------------------------------------------------------ *)
(* pull_lets / do_pull_lets                                             *)
(* ------------------------------------------------------------------ *)

let rec pull_lets ?(i=0) ?(m:(string, Var.t list * t, String.comparator_witness) Map.t=Map.empty (module String)) form =
  let open Tyformula in
  let r =
    match form.form with
    | Predicate (r, trms) ->
      (match Map.find m r with
       | None -> (i, [], form)
       (* Keep the typed parameter variables: [Var.of_ident] would default the
          type to TInt, so substitution would fail to match the (correctly
          typed) variables in the body and leave them dangling/free. *)
       | Some (vars, e) -> (i, [], subst (Map.of_alist_exn (module Var) (List.zip_exn vars trms)) e))
    | TT | FF | EqConst _  -> (i, [], form)
    | Predicate' (_, _, f)
    | Let' (_, _, _, _, f)
    | Type (f, _) -> pull_lets ~i ~m f
    | Let (e, enftype, vars, f, g) ->
      let i, letsf, f = pull_lets ~i ~m f in
      (if Enftype.is_suppressable enftype || Enftype.is_causable enftype || height f > 1 then
         let i, letsg, g = pull_lets ~i ~m g in
         let origin = f in
         i, letsf @ { le_name = e; le_enftype = Some enftype; le_args = vars;
                      le_body = f; le_origin = origin } :: letsg, g
       else
         let i, letsg, g = pull_lets ~i ~m:(Map.update m e ~f:(fun _ -> (List.map ~f:(fun (v, _) -> v) vars, f))) g in
         i, letsf @ letsg, g)
    | Neg f ->
      let i, letsf, f = pull_lets ~i ~m f in
      i, letsf, { f with form = Neg f }
    | Exists (x, f)
    | Forall (x, f) when not (Set.mem (fvs [f]) x) ->
      pull_lets ~i ~m f
    | Exists (_x, _) ->
      let origin = form in
      let xs, fs = all_exists form in
      let i, lets, f = pull_lets ~i ~m (List.last_exn fs) in
      let e = "Exists" ^ string_of_int i in
      let fvs = Set.elements (fv form) in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      let g = add_back_exists f xs fs in
      i + 1, lets @ [{ le_name = e; le_enftype = None; le_args = vars;
                       le_body = { f with form = g.form }; le_origin = origin }],
      { f with form = Predicate (e, List.map ~f:Tterm.dummy_var fvs) }
    | Forall (x, f) ->
      (* Collect a maximal block of consecutive universals  ∀x₁…∀xₙ. f  and
         rewrite it as  ¬∃x₁…∃xₙ. ¬f  in a single step.  Rewriting one
         quantifier at a time interleaves double negations
         (¬∃x.¬(¬∃y.¬…)), which prevents [all_exists] from grouping the
         existentials: each ends up in its own let, and the enforcement
         realiser then emits a redundant chain of [Sup_Exists] obligation
         events — one per variable.  Keeping the block together yields a
         single ∃-let discharged by one guarded suppression clause. *)
      let rec all_forall form = match form.form with
        | Forall (y, g) -> let ys, h = all_forall g in (y :: ys, h)
        | _ -> ([], form) in
      let xs, body = all_forall { form with form = Forall (x, f) } in
      let neg_body = { form with form = Neg body } in
      let exists = List.fold_right xs ~init:neg_body
          ~f:(fun y g -> { form with form = Exists (y, g) }) in
      pull_lets ~i ~m { form with form = Neg exists }
    | Prev (itv, f) ->
      let origin = form in
      let i, lets, f = pull_lets ~i ~m f in
      let e = "Prev" ^ string_of_int i in
      let fvs = Set.elements (fv f) in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      i + 1, lets @ [{ le_name = e; le_enftype = None; le_args = vars;
                       le_body = { f with form = Prev (itv, f) }; le_origin = origin }],
      { f with form = Predicate (e, List.map ~f:Tterm.dummy_var fvs) }
    | Once (itv, f) ->
      let origin = form in
      let i, lets, f = pull_lets ~i ~m f in
      let e = "Once" ^ string_of_int i in
      let fvs = Set.elements (fv f) in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      i + 1, lets @ [{ le_name = e; le_enftype = None; le_args = vars;
                       le_body = { f with form = Once (itv, f) }; le_origin = origin }],
      { f with form = Predicate (e, List.map ~f:Tterm.dummy_var fvs) }
    | Agg (s, op, x, y, f) ->
      (* Lift the aggregation into an observable let, like Once.  Its free
         variables are the grouping vars ++ result var (= fv of the node), and
         its inner subformula has its own lets pulled (so e.g. an inner Once is
         already a named let, enabling incremental detection). *)
      let origin = form in
      let fvs = Set.elements (fv form) in
      let i, lets, f = pull_lets ~i ~m f in
      let e = "Agg" ^ string_of_int i in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      i + 1, lets @ [{ le_name = e; le_enftype = None; le_args = vars;
                       le_body = { f with form = Agg (s, op, x, y, f) }; le_origin = origin }],
      { f with form = Predicate (e, List.map ~f:Tterm.dummy_var fvs) }
    | Top (s, op, x, y, f) ->
      let origin = form in
      let fvs = Set.elements (fv form) in
      let i, lets, f = pull_lets ~i ~m f in
      let e = "Top" ^ string_of_int i in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      i + 1, lets @ [{ le_name = e; le_enftype = None; le_args = vars;
                       le_body = { f with form = Top (s, op, x, y, f) }; le_origin = origin }],
      { f with form = Predicate (e, List.map ~f:Tterm.dummy_var fvs) }
    | Next (itv, f) ->
      let i, lets, f = pull_lets ~i ~m f in
      i, lets, { form with form = Next (itv, f) }
    | Eventually (itv, f) ->
      let i, lets, f = pull_lets ~i ~m f in
      i, lets, { form with form = Eventually (itv, f) }
    | Historically (itv, f) ->
      let origin = form in
      let i, lets, f = pull_lets ~i ~m f in
      let e = "Historically" ^ string_of_int i in
      let fvs = Set.elements (fv f) in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      i + 1, lets @ [{ le_name = e; le_enftype = None; le_args = vars;
                       le_body = { f with form = Historically (itv, f) }; le_origin = origin }],
      { f with form = Predicate (e, List.map ~f:Tterm.dummy_var fvs) }
    | Always (itv, f) ->
      let i, lets, f = pull_lets ~i ~m f in
      i, lets, { form with form = Always (itv, f) }
    | Since (_, itv, f, g) when !Global.fix_since && Interval.is_full itv
                                && not (Set.is_subset (fv f) ~of_:(fv g)) ->
      (* f S g  ≡  ⧫g ∧ ¬((¬g) S X)  with  X = ¬f ∧ ¬g ∧ ●⧫g: f S g fails
         after some g iff a step after the last g falsifies f.  The inner S has
         the variables of f only on its right, which the next case handles.
         Only for unbounded intervals. *)
      let once_g = { g with form = Once (Interval.full, g) } in
      let neg h = { h with form = Neg h } in
      let x = { f with form = And (N, [neg f; neg g; { g with form = Prev (Interval.full, once_g) }]) } in
      let inner = { form with form = Since (N, Interval.full, neg g, x) } in
      pull_lets ~i ~m { form with form = And (N, [once_g; neg inner]) }
    | Since (s, itv, f, g) when !Global.fix_since
                                && not (Set.is_subset (fv g) ~of_:(fv f)) ->
      (* f S g  ≡  (f ∨ ¬⧫g) S g: after the anchor, ⧫g holds, so the new left
         operand is equivalent to f; it has the variables of g too.  For
         f = ¬L this is  ¬(L ∧ ⧫g) S g. *)
      let not_once_g = { g with form = Neg { g with form = Once (Interval.full, g) } } in
      let f' = { f with form = Or (N, [f; not_once_g]) } in
      pull_lets ~i ~m { form with form = Since (s, itv, f', g) }
    | Since (s, itv, f, g) ->
      let origin = form in
      let i, letsf, f = pull_lets ~i ~m f in
      let i, letsg, g = pull_lets ~i ~m g in
      let e = "Since" ^ string_of_int i in
      (* The table of  f S g  is keyed on the variables of both operands, and
         its remove clause (from f) must bind all of them: reject operands with
         different free variables.  For  ¬L(x̄) S R(x̄, ȳ),  the equivalent
         ¬(L(x̄) ∧ ⧫R(x̄, ȳ)) S R(x̄, ȳ)  has the same variables on both sides. *)
      if not (Set.equal (fv f) (fv g)) then begin
        Stdio.print_endline
          ("The formula\n " ^ Tyformula.to_string form
           ^ "\nis not supported: the operands of S must have the same free variables"
           ^ " (rewrite ¬L S R as ¬(L ∧ ⧫R) S R, or use -fix-since)");
        raise (Errors.FormulaError "operands of S with different free variables")
      end;
      let fvs = Set.elements (Set.inter (fv f) (fv g)) in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      i + 1, letsf @ letsg @ [{ le_name = e; le_enftype = None; le_args = vars;
                                 le_body = { f with form = Since (s, itv, f, g) }; le_origin = origin }],
      { f with form = Predicate (e, List.map ~f:Tterm.dummy_var fvs) }
    | Until (s, itv, f, g) ->
      let i, letsf, f = pull_lets ~i ~m f in
      let i, letsg, g = pull_lets ~i ~m g in
      i, letsf @ letsg, { form with form = Until (s, itv, f, g) }
    | And (s, fs) ->
      let i, lets, fs = List.fold_right fs ~init:(i, [], [])
          ~f:(fun f (i, lets, fs) -> let i, lets', f = pull_lets ~i ~m f in i, lets' @ lets, f :: fs) in
      i, lets, { form with form = And (s, fs) }
    | Or (s, fs) ->
      let i, lets, fs = List.fold_right fs ~init:(i, [], [])
          ~f:(fun f (i, lets, fs) -> let i, lets', f = pull_lets ~i ~m f in i, lets' @ lets, f :: fs) in
      i, lets, { form with form = Or (s, fs) }
    | Imp (s, f, g) ->
      let i, letsf, f = pull_lets ~i ~m f in
      let i, letsg, g = pull_lets ~i ~m g in
      i, letsf @ letsg, { form with form = Imp (s, f, g) }
    | Label (s, f) ->
      (* Keep the label inline rather than lifting it into an enforced let-def.
         Enforcement (enforceability.ml `aux`) threads the label onto the clauses
         derived from `f`, so it ends up as the `@<source>` annotation on the
         produced rule — no synthetic `Label`/`Cau_Label` indirection. *)
      let i, lets, f = pull_lets ~i ~m f in
      i, lets, { form with form = Label (s, f) }
    | _ -> failwith ("unsupported constructor " ^ op_to_string form)
  in r

(* ------------------------------------------------------------------ *)
(* drop_dead_params                                                     *)
(*                                                                      *)
(* A parameter of a let that its body does not use — or uses only as a  *)
(* dead parameter of another let — does not affect the let's value: the *)
(* let holds for all values of it.  Drop it from the definition and the  *)
(* corresponding argument from every call.  Otherwise the let could not  *)
(* be enumerated (nothing binds that parameter), even when the rest of   *)
(* its body is guarded.  Lets with an enforcement type (+/-) keep their  *)
(* interface.  Runs after [convert_lets] (let names are unique) and      *)
(* before [unroll_let] (no Predicate'/Let' yet).                         *)
(* ------------------------------------------------------------------ *)

let drop_dead_params (f : Tyformula.t) : Tyformula.t =
  let rec aux (alive : (string, bool list, String.comparator_witness) Map.t) (f : Tyformula.t) =
    let go = aux alive in
    let keep_only keep xs = List.filteri xs ~f:(fun k _ -> List.nth_exn keep k) in
    let form = match f.form with
      | TT | FF | EqConst _ | Predicate' _ | Let' _ -> f.form
      | Predicate (r, trms) ->
        (match Map.find alive r with
         | Some keep -> Predicate (r, keep_only keep trms)
         | None -> f.form)
      | Let (r, enftype, vars, body, g) ->
        let body = go body in
        let keep =
          if Enftype.is_suppressable enftype || Enftype.is_causable enftype then
            List.map vars ~f:(fun _ -> true)
          else
            let used = fv body in
            List.map vars ~f:(fun (x, _) -> Set.exists used ~f:(Var.equal_ident x)) in
        Let (r, enftype, keep_only keep vars, body, aux (Map.set alive ~key:r ~data:keep) g)
      | Agg (s, op, x, y, g) -> Agg (s, op, x, y, go g)
      | Top (s, op, x, y, g) -> Top (s, op, x, y, go g)
      | Neg g -> Neg (go g)
      | And (s, gs) -> And (s, List.map gs ~f:go)
      | Or (s, gs) -> Or (s, List.map gs ~f:go)
      | Imp (s, g, h) -> Imp (s, go g, go h)
      | Exists (x, g) -> Exists (x, go g)
      | Forall (x, g) -> Forall (x, go g)
      | Prev (i, g) -> Prev (i, go g)
      | Next (i, g) -> Next (i, go g)
      | Once (i, g) -> Once (i, go g)
      | Eventually (i, g) -> Eventually (i, go g)
      | Historically (i, g) -> Historically (i, go g)
      | Always (i, g) -> Always (i, go g)
      | Since (s, i, g, h) -> Since (s, i, go g, go h)
      | Until (s, i, g, h) -> Until (s, i, go g, go h)
      | Type (g, ty) -> Type (go g, ty)
      | Label (s, g) -> Label (s, go g)
    in { f with form } in
  aux (Map.empty (module String)) f

let do_pull_lets (f : t) : let_def list * t =
  let _i, lets, f = pull_lets f in
  lets, f

(* ------------------------------------------------------------------ *)
(* Normalization phase output type                                      *)
(* ------------------------------------------------------------------ *)

type t = {
  lets    : let_def list;
  formula : Tyformula.t;
  origin  : Tyformula.t;   (* original typed formula, before normalization *)
}

let to_string (lf: t) =
  String.concat ~sep:"\n" (List.map ~f:let_def_to_string lf.lets)
  ^ "\n" ^ Tyformula.to_string lf.formula

(* ------------------------------------------------------------------ *)
(* normalize: Phase 4 — let-pulling normalization                      *)
(*                                                                      *)
(* Input:  a typed formula (output of Tyformula.of_formula')           *)
(* Output: a [result] with all temporal subformulas lifted to named    *)
(*         let-bound predicates, ready for enforceability type checking *)
(* ------------------------------------------------------------------ *)

let make ?(moderate=true) (f : Tyformula.t) : t =
  let origin = f in
  let f = f
    |> push_negs |> convert_vars |> convert_lets |> drop_dead_params
    |> unroll_let ~moderate |> push_quants |> simplify |> ac_simplify in
  let lets, f = do_pull_lets f in
  let f = ac_simplify f in
  let lets = List.map ~f:(fun le -> { le with le_body = ac_simplify le.le_body }) lets in
  let f = match f.form with
    | Always (itv, f) when Interval.is_full itv -> f
    | And (s, fs) ->
      let fs = List.map ~f:(function
          | { form = Always (itv, f) } when Interval.is_full itv -> f
          | f -> f) fs in
      make_dummy (And (s, fs))
    | _ -> f in
  { lets; formula = f; origin }
