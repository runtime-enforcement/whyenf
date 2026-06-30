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
    | Since (s, itv, f, g) ->
      let origin = form in
      let i, letsf, f = pull_lets ~i ~m f in
      let i, letsg, g = pull_lets ~i ~m g in
      let e = "Since" ^ string_of_int i in
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
    |> push_negs |> convert_vars |> convert_lets
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
