open Base
open MFOTL_lib

(* Save a reference to the library-level FormulaError exception before
   any local [Errors] module can shadow the name. *)
let raise_formula_error msg = raise (Errors.FormulaError msg)

open Tyformula
open Nformula

module Var = Tterm.TypedVar
module Term = Tterm

(* ------------------------------------------------------------------ *)
(* Guardedness helpers                                                  *)
(* ------------------------------------------------------------------ *)

(*
let non_monotone_predicates_of_trigger
    ~let_ctxt_mon:(let_ctxt_mon:(string, (string, Base.String.comparator_witness) Base.Set.t, Base.String.comparator_witness) Base.Map.t)
    ~let_ctxt_anti_mon:(let_ctxt_anti_mon:(string, (string, Base.String.comparator_witness) Base.Set.t, Base.String.comparator_witness) Base.Map.t)
    (p : bool) (trigger : Trigger.t) =
  let filter_mon, filter_anti_mon =
    non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon trigger.Trigger.filter in
  let guard_maps = List.map trigger.Trigger.guards ~f:(fun fs ->
      non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon (make_dummy (And (N, fs)))) in
  let guard_mon, guard_anti_mon =
    List.fold guard_maps
      ~f:(fun (init_mon, init_anti_mon) (mon, anti_mon) ->
          Set.union init_mon mon, Set.union init_anti_mon anti_mon)
      ~init:(Set.empty (module String), Set.empty (module String)) in
  match trigger.Trigger.guards with
  | [] ->
    if p then filter_mon, filter_anti_mon else filter_anti_mon, filter_mon
  | _ ->
    let guard_mon, guard_anti_mon =
      if p then guard_mon, guard_anti_mon else guard_anti_mon, guard_mon in
    Set.union guard_mon filter_mon,
    Set.union guard_anti_mon filter_anti_mon*)

let allow_table_guards = ref false
let table_guard_warnings : (string * string) list ref = ref []

let rec pull_guard (m : GuardInfo.map) (x : Var.t) (p : bool) (trigger : Trigger.t) : Trigger.t option =
  let npg = pull_guard m x in

  let guard_quality r =
    let ld_opt = Map.find m r in
    let is_unguardable =
      match ld_opt with
      | Some ld -> Option.is_none ld.switch_pos_opt
      | None -> false
    in
    let is_table =
      match ld_opt with
      | Some ld ->
        (match ld.switch_pos_opt with
         | Some (Switch.Once _) | Some (Switch.Prev _) | Some (Switch.Since _) -> true
         | _ -> false)
      | None -> false
    in
    is_unguardable, is_table, ld_opt in
  let try_pulling_guard allow_table =
    let with_existing_guard = (not (List.is_empty trigger.Trigger.guards)) &&
                              List.for_all trigger.Trigger.guards ~f:(
                                List.exists ~f:(fun guard -> match guard.form with
                                    | Predicate (r, trms) ->
                                      let is_unguardable, is_table, _ = guard_quality r in
                                      if is_unguardable || is_table && not allow_table then false
                                      else List.exists ~f:(Term.equal (Term.dummy_var x)) trms
                                    | _ -> false)) in
    if with_existing_guard
    then Some trigger
    else begin
      let base_guards = if List.is_empty trigger.Trigger.guards then [[]] else trigger.Trigger.guards in
      let rec aux p filter =
        let r =
          match filter.form, p with
          | TT, false -> Some trigger
          | FF, true  -> Some trigger
          | Predicate (r, trms), true when List.exists ~f:(Term.equal (Term.dummy_var x)) trms ->
            let is_unguardable, is_table, ld_opt = guard_quality r in
            if is_unguardable || (is_table && not allow_table) then None
            else begin
              (if is_table then
                 let body_str = match ld_opt with
                   | Some ld -> ld.body_str
                   | None -> "?" in
                 let entry = (r, body_str) in
                 if not (List.exists !table_guard_warnings ~f:(fun (n, _) -> String.equal n r)) then
                   table_guard_warnings := entry :: !table_guard_warnings);
              Some { Trigger.guards = List.map ~f:(fun fs -> filter :: fs) base_guards;
                     filter = make_dummy TT }
            end
          | EqConst (trm, _), true when Term.equal (Term.dummy_var x) trm ->
            Some { Trigger.guards = List.map ~f:(fun fs -> filter :: fs) base_guards;
                   filter = make_dummy TT }
          | Neg f, _ ->
            Option.map (aux (not p) f) ~f:(fun trigger ->
                { trigger with Trigger.filter = ac_simplify (make_dummy (Neg trigger.Trigger.filter)) })
          | And (_, fs), true ->
            Option.map ~f:(fun (i, trigger) ->
                let a, b = List.split_n fs i in
                let form = And (N, a @ trigger.Trigger.filter :: (List.tl_exn b)) in
                let filter = ac_simplify { filter with form } in
                { trigger with Trigger.filter })
              (List.find_mapi ~f:(fun i f ->
                   Option.map ~f:(fun trigger -> (i, trigger)) (aux true f)) fs)
          | And (_, fs), false ->
            Option.map (Option.all (List.map ~f:(aux false) fs)) ~f:(fun triggers ->
                let guards = List.concat_map ~f:(fun t -> t.Trigger.guards) triggers in
                let filter = ac_simplify (make_dummy (
                    And (N, List.map ~f:(Trigger.to_formula false) triggers))) in
                { Trigger.guards; filter })
          | Or (_, fs), false ->
            Option.map ~f:(fun (i, trigger) ->
                let a, b = List.split_n fs i in
                let form = Or (N, a @ trigger.Trigger.filter :: (List.tl_exn b)) in
                let filter = ac_simplify { filter with form } in
                { trigger with Trigger.filter })
              (List.find_mapi ~f:(fun i f ->
                   Option.map ~f:(fun trigger -> (i, trigger)) (aux false f)) fs)
          | Or (_, fs), true ->
            Option.map (Option.all (List.map ~f:(aux true) fs)) ~f:(fun triggers ->
                let guards = List.concat_map ~f:(fun t -> t.Trigger.guards) triggers in
                let filter = ac_simplify (make_dummy (
                    Or (N, List.map ~f:(Trigger.to_formula true) triggers))) in
                { Trigger.guards; filter })
          | Imp (_, f1, f2), false ->
            (match aux true f1, aux false f2 with
             | Some trigger, _ ->
               Some { trigger with Trigger.filter = ac_simplify (make_dummy (Imp (N, trigger.Trigger.filter, f2))) }
             | _, Some trigger ->
               Some { trigger with Trigger.filter = ac_simplify (make_dummy (Imp (N, f1, trigger.Trigger.filter))) }
             | _ -> None)
          | Imp (_, f1, f2), true ->
            (match aux false f1, aux true f2 with
             | Some trigger1, Some trigger2 ->
               Some { trigger with Trigger.guards = trigger1.guards @ trigger2.guards }
             | _ -> None)
          | Exists (y, f), _
          | Forall (y, f), _ when not (Var.equal_ident x y) ->
            Option.map ~f:(fun trigger -> { trigger with Trigger.filter = f }) (aux p f)
          | Label (s, f), _ ->
            Option.map (aux p f) ~f:(fun trigger ->
                { trigger with Trigger.filter = { filter with form = Label (s, trigger.Trigger.filter) } })
          | _ -> None
        in
        r in
      aux p trigger.Trigger.filter
    end in
  let _ = npg in
  let r_opt = try_pulling_guard false in
  match r_opt with
  | None when !allow_table_guards -> try_pulling_guard true
  | _ -> r_opt

let normalize_trigger ?(vars=None) (m : Nformula.GuardInfo.map) (trigger : Trigger.t) (p : bool) (orig_f : Tyformula.t) : Trigger.t Verdict.v =
  let vars = match vars with
    | None -> Set.elements (fvs (trigger.Trigger.filter :: List.concat trigger.Trigger.guards))
    | Some vars -> vars in
  List.fold_right
    ~f:(fun x ->
        function
        | Verdict.Impossible e -> Verdict.Impossible e
        | Verdict.Possible [trigger] ->
          (match pull_guard m x p trigger with
           | None -> Verdict.Impossible (Verdict.Errors.ERule
                                           ("Variable " ^ Var.to_string x ^
                                            " is not guarded in " ^ Tyformula.to_string orig_f
                                            ^ " (polarity: " ^ (if p then "+" else "-") ^ ")"
                                            ^ " (computed filter: " ^ Trigger.to_string trigger ^ ")"))
           | Some trigger -> Verdict.Possible [trigger])
        | other -> other)
    ~init:(Verdict.Possible [trigger]) vars

let normalize_trigger_best_effort ?(vars=None) (m : GuardInfo.map) (trigger : Trigger.t) (p : bool) (_orig_f : Tyformula.t) : Trigger.t =
  let vars = match vars with
    | None -> Set.elements (fvs (trigger.Trigger.filter :: List.concat trigger.Trigger.guards))
    | Some vars -> vars in
  List.fold_right
    ~f:(fun x trigger ->
        match pull_guard m x p trigger with
        | None -> trigger
        | Some trigger -> trigger)
    ~init:trigger vars

(*let maps_of_lets (lets : Lformula.let_def list) =
  let pred_map =
    List.fold_left lets
      ~init:(Map.empty (module String))
      ~f:(fun lets le -> Map.update lets le.Lformula.le_name (fun _ -> predicates ~lets le.Lformula.le_body)) in
  let mon_map, anti_mon_map =
    List.fold_left lets
      ~init:(Map.empty (module String), Map.empty (module String))
      ~f:(fun (let_ctxt_mon, let_ctxt_anti_mon) le ->
          let mon, anti_mon = non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon le.Lformula.le_body in
          Map.update let_ctxt_mon le.Lformula.le_name (fun _ -> mon),
          Map.update let_ctxt_anti_mon le.Lformula.le_name (fun _ -> anti_mon)) in
  pred_map, mon_map, anti_mon_map
*)
    
(* Normalize types used below: Lformula.let_extraction, Lformula.result *)

(* ------------------------------------------------------------------ *)
(* let_def / let_map types                                              *)
(* ------------------------------------------------------------------ *)

let guard_map_of_let_map (m : let_map) : GuardInfo.map =
  Map.map m ~f:(fun ld ->
      { GuardInfo.switch_pos_opt = ld.switch_pos_opt;
        body_str = Tyformula.to_string ld.body })

(* ------------------------------------------------------------------ *)
(* to_string helpers                                                    *)
(* ------------------------------------------------------------------ *)

let enf_sols_to_string enf_sols =
  Printf.sprintf "[%s]"
    (Etc.string_list_to_string (List.map enf_sols ~f:(fun (clauses, constr) ->
         Printf.sprintf "{ clauses = [%s];\n  constr = %s }"
           (Etc.string_list_to_string (List.map ~f:Clause.to_string clauses))
           (Constraints.to_string constr))))

let let_def_to_string let_def =
  let o default f x = Option.value (Option.map ~f x) ~default in
  Printf.sprintf "{ name = %s;\n  args = [%s];\n  body = %s;\n  cau_sols = %s;\n  sup_sols = %s;\n  trigger_pos_opt = %s;\n  trigger_neg_opt = %s }"
    let_def.name
    (Etc.string_list_to_string (List.map let_def.args ~f:(
         fun (v, tt_opt) -> Var.to_string v ^ o "" (fun tt -> ": " ^ Dom.tt_to_string tt) tt_opt)))
    (to_string let_def.body)
    (Verdict.verdict_to_string ~to_string:enf_sols_to_string let_def.cau_sols)
    (Verdict.verdict_to_string ~to_string:enf_sols_to_string let_def.sup_sols)
    (o "None" Switch.to_string let_def.switch_pos_opt)
    (o "None" Switch.to_string let_def.switch_neg_opt)

let let_map_to_string m =
  String.concat ~sep:"\n" (List.map ~f:(fun (key, let_def) -> key ^ " -> " ^ let_def_to_string let_def)
                             (Map.to_alist m))

(* ------------------------------------------------------------------ *)
(* merge_clauses_constr                                                 *)
(* ------------------------------------------------------------------ *)

let merge_clauses_constr clauses_constrs clauses_constrs' =
  let clauses_constrs' = Etc.cartesian [clauses_constrs; clauses_constrs'] in
  List.map clauses_constrs' ~f:(fun clauses_constrs ->
      let clauses, constrs = List.unzip clauses_constrs in
      (List.concat clauses, Constraints.ac_simplify (Constraints.CConj constrs)))

(* ------------------------------------------------------------------ *)
(* fix_predicate_names                                                  *)
(* ------------------------------------------------------------------ *)

let fix_predicate_names m pol e =
  match Map.find m e with
  | Some ({ switch_neg_opt = Some _ } as _let_def) ->
    e ^ (if pol then "_pos" else "_neg")
  | _ -> e

let fix_predicate_names_clauses_constr m =
  List.map ~f:(fun (clauses, constrs) ->
      List.map clauses ~f:(fun { Clause.trigger; effects } ->
          { Clause.trigger = { Trigger.guards = List.map ~f:(List.map ~f:(map_predicate ~pol:false ~f:(fix_predicate_names m))) trigger.guards;
                               filter = map_predicate ~pol:false ~f:(fix_predicate_names m) trigger.filter };
            effects = List.map ~f:(Effect.map_predicate ~f:(fix_predicate_names m)) effects }),
      constrs)

(* ------------------------------------------------------------------ *)
(* types: main enforceability type inference                            *)
(* ------------------------------------------------------------------ *)

let types (t: Enftype.t) (norm: Lformula.t) (b: Interval.v) : 'a Verdict.v =

  let set_b = function
    | Interval.U a -> Interval.B (a, b)
    | B _ as i -> i in

  let dummy_for_var x = Term.dummy_for_var x in

  let lets = norm.Lformula.lets in
  let f    = norm.Lformula.formula in

  (*let _pred_map, _mon_map, _anti_mon_map = maps_of_lets lets in*)

  (* Main auxiliary function: normalize enforceable formula *)
  let rec aux (m: let_map) (t: Enftype.t) (f: Tyformula.t) : enf_sols =
    let open Verdict in
    let r =
      match Enftype.is_causable t, Enftype.is_suppressable t with
      | true, true -> Impossible (Errors.EFormula (Some "no formula can be both causable and suppressable", f, t))
      | true, false -> begin
          match f.form with
          | TT -> Possible [([{ Clause.trigger = Trigger.make (make_dummy TT); effects = [] }], Constraints.CTT)]
          | Predicate (e, terms) -> begin
              match Map.find m e with
              | Some def ->
                let* solutions = def.cau_sols in
                List.map solutions ~f:(fun (clauses, constr) ->
                    [{ Clause.trigger = Trigger.make (make_dummy TT);
                       effects = [Effect.Cau ("Cau_" ^ e, terms)] }], constr)
              | None when Sig.mem e ->
                let enftype = Sig.enftype_of_pred e in
                if Enftype.geq enftype Enftype.cau then
                  Possible [([{ Clause.trigger = Trigger.make (make_dummy TT);
                                effects = [Effect.Cau (e, terms)] }],
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
                Possible [(List.concat clauses, Constraints.CConj constrs)]))
          | Or (L, f :: fs) ->
            let* solutions = aux m t f in
            List.map solutions ~f:(fun (clauses, constr) ->
                List.map clauses ~f:(fun { Clause.trigger; effects } ->
                    { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, trigger.filter :: List.map fs ~f:(fun g -> make_dummy (Neg g))))) };
                      effects }),
                constr)
          | Or (R, fs) ->
            let f = List.last_exn fs in
            let fs = fs |> List.rev |> List.tl_exn |> List.rev in
            let* solutions = aux m t f in
            List.map solutions ~f:(fun (clauses, constr) ->
                List.map clauses ~f:(fun { Clause.trigger; effects } ->
                    { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, trigger.filter :: List.map fs ~f:(fun g -> make_dummy (Neg g))))) };
                      effects }),
                constr)
          | Or (_, fs) ->
            let rec run (left: Tyformula.t list) = function
              | [] -> Impossible (EDisj [])
              | f :: right ->
                disj (let* solutions = aux m t f in
                      List.map solutions ~f:(fun (clauses, constr) ->
                          List.map clauses ~f:(fun { Clause.trigger; effects } ->
                              { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, trigger.filter :: List.map (left @ right) ~f:(fun g -> make_dummy (Neg g))))) };
                                effects }),
                          constr))
                  (run (f::left) right)
            in run [] fs
          | Imp (L, f, g) ->
            let* solutions = aux m (Enftype.neg t) f in
            List.map solutions
              ~f:(fun (clauses, constr) ->
                  List.map clauses ~f:(fun { Clause.trigger; effects } ->
                      { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, [trigger.filter; make_dummy (Neg g)]))) };
                        effects }),
                  constr)
          | Imp (R, f, g) ->
            let* solutions = aux m t g in
            List.map solutions ~f:(fun (clauses, constr) ->
                List.map clauses ~f:(fun { Clause.trigger; effects } ->
                    { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, [trigger.filter; f]))) };
                      effects }),
                constr)
          | Imp (_, f, g) ->
            disj
              (let* solutions = aux m (Enftype.neg t) f in
               List.map solutions ~f:(fun (clauses, constr) ->
                   List.map clauses ~f:(fun { Clause.trigger; effects } ->
                       { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, [trigger.filter; make_dummy (Neg g)]))) };
                         effects }),
                   constr))
              (let* solutions = aux m t g in
               List.map solutions ~f:(fun (clauses, constr) ->
                   List.map clauses ~f:(fun { Clause.trigger; effects } ->
                       { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, [trigger.filter; f]))) };
                         effects }),
                   constr))
          | Exists (x, f) ->
            aux m t (subst (Map.singleton (module Var) x (dummy_for_var x)) f)
          | Forall (x, f) ->
            let** solutions = aux m t f in
            disjs (List.map solutions ~f:(fun (clauses, constr) ->
                match all (List.map clauses ~f:(fun { Clause.trigger; effects } ->
                    let vars = Some (Set.elements (Effect.fvs effects)) in
                    match normalize_trigger ~vars (guard_map_of_let_map m) trigger false f with
                    | Possible [trigger] -> Possible [{ Clause.trigger; effects }]
                    | Impossible error -> Impossible error)) with
                | Possible clauses -> Possible [List.concat clauses, constr]
                | Impossible errors -> Impossible errors))
          | Eventually (i, f) ->
            let** solutions = aux m t f in
            let solutions =
              List.filter_map solutions ~f:(fun (clauses, constr) ->
                  match Option.all (List.map clauses ~f:(fun { Clause.trigger; effects } ->
                      let is_trigger_trivial = match trigger.Trigger.filter.form with TT -> true | _ -> false in
                      let are_effects_simple = List.for_all effects
                          ~f:(fun effect -> match effect with Cau _ | Sup _ -> true | _ -> false) in
                      if is_trigger_trivial && are_effects_simple then
                        Some { Clause.trigger; effects = List.map effects ~f:(Effect.eventualize (set_b i)) }
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
          | Until (_s, i, _, g) when Interval.has_zero i ->
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
                  match Option.all (List.map clauses ~f:(fun { Clause.trigger; effects } ->
                      let suppressed = List.filter_map effects
                          ~f:(fun effect -> match effect with
                              | (Sup (r, trms) as p) -> Some { form = Predicate (r, trms); info = () }
                              | _ -> None) in
                      let is_trigger_trivial = match trigger.Trigger.filter.form with
                        | TT -> true
                        | _ -> List.mem suppressed trigger.filter ~equal:core_equal in
                      let are_effects_simple = List.for_all effects
                          ~f:(function Cau _ | Sup _ -> true | _ -> false) in
                      if is_trigger_trivial && are_effects_simple then
                        begin
                          if not (List.is_empty effects) then
                            Some { Clause.trigger = Trigger.make (make_dummy TT);
                                   effects = List.map effects ~f:(Effect.nextize is) }
                          else
                            Some { Clause.trigger = Trigger.make (make_dummy TT);
                                   effects = [Effect.NextTT is] }
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
          | FF -> Possible [([{ Clause.trigger = Trigger.make (make_dummy TT); effects = [] }], Constraints.CTT)]
          | Predicate (e, terms) -> begin
              match Map.find m e with
              | Some def ->
                let* solutions = def.sup_sols in
                List.map solutions ~f:(fun (clauses, constr) ->
                    [{ Clause.trigger = Trigger.make f;
                       effects = [Effect.Sup ("Sup_" ^ e, terms)] }], constr)
              | None when Sig.mem e ->
                let enftype = Sig.enftype_of_pred e in
                if Enftype.geq enftype Enftype.sup then
                  Possible [[{ Clause.trigger = Trigger.make f;
                               effects = [Effect.Sup (e, terms)] }],
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
                    Some (List.concat clauses, Constraints.CConj constrs))) enf_sols
          | And (L, f :: fs) ->
            let* solutions = aux m t f in
            List.map solutions ~f:(fun (clauses, constr) ->
                List.map clauses ~f:(fun { Clause.trigger; effects } ->
                    { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, trigger.filter :: fs))) };
                      effects }),
                constr)
          | And (R, fs) ->
            let f = List.last_exn fs in
            let fs = fs |> List.rev |> List.tl_exn |> List.rev in
            let* solutions = aux m t f in
            List.map solutions ~f:(fun (clauses, constr) ->
                List.map clauses ~f:(fun { Clause.trigger; effects } ->
                    { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, trigger.filter :: fs))) };
                      effects }),
                constr)
          | And (_, fs) ->
            let rec run (left: Tyformula.t list) = function
              | [] -> Impossible (EDisj [])
              | f :: right ->
                disj (let* solutions = aux m t f in
                      List.map solutions ~f:(fun (clauses, constr) ->
                          List.map clauses ~f:(fun { Clause.trigger; effects } ->
                              { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, trigger.filter :: left @ right))) };
                                effects }),
                          constr))
                  (run (f::left) right)
            in run [] fs
          | Imp (L, f, g) ->
            let* solutions = aux m (Enftype.neg t) f in
            List.map solutions
              ~f:(fun (clauses, constr) ->
                  List.map clauses ~f:(fun { Clause.trigger; effects } ->
                      { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, [trigger.filter; make_dummy (Neg g)]))) };
                        effects }),
                  constr)
          | Imp (R, f, g) ->
            let* solutions = aux m t g in
            List.map solutions ~f:(fun (clauses, constr) ->
                List.map clauses ~f:(fun { Clause.trigger; effects } ->
                    { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, [trigger.filter; f]))) };
                      effects }),
                constr)
          | Imp (_, f, g) ->
            disj
              (let* solutions = aux m (Enftype.neg t) f in
               List.map solutions ~f:(fun (clauses, constr) ->
                   List.map clauses ~f:(fun { Clause.trigger; effects } ->
                       { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, [trigger.filter; make_dummy (Neg g)]))) };
                         effects }),
                   constr))
              (let* solutions = aux m t g in
               List.map solutions ~f:(fun (clauses, constr) ->
                   List.map clauses ~f:(fun { Clause.trigger; effects } ->
                       { Clause.trigger = { trigger with Trigger.filter = ac_simplify (make_dummy (And (N, [trigger.filter; f]))) };
                         effects }),
                   constr))
          | Forall (x, f) ->
            aux m t (subst (Map.singleton (module Var) x (dummy_for_var x)) f)
          | Exists (x, f) ->
            let** solutions = aux m t f in
            disjs (List.map solutions ~f:(fun (clauses, constr) ->
                match all (List.map clauses ~f:(fun { Clause.trigger; effects } ->
                    let vars = Some (Set.elements (Effect.fvs effects)) in
                    match normalize_trigger ~vars (guard_map_of_let_map m) trigger true f with
                    | Possible [trigger] -> Possible [{ Clause.trigger; effects }]
                    | Impossible error -> Impossible error)) with
                | Possible clauses -> Possible [List.concat clauses, constr]
                | Impossible errors -> Impossible errors))
          | Always (i, f) ->
            let* solutions = aux m t f in
            List.filter_map solutions ~f:(fun (clauses, constr) ->
                match Option.all (List.map clauses ~f:(fun { Clause.trigger; effects } ->
                    let is_trigger_trivial = match trigger.Trigger.filter.form with TT -> true | _ -> false in
                    let are_effects_simple = List.for_all effects
                        ~f:(fun effect -> match effect with Cau _ -> true | _ -> false) in
                    if is_trigger_trivial && are_effects_simple then
                      Some { Clause.trigger; effects = List.map effects ~f:(Effect.eventualize (set_b i)) }
                    else
                      None))
                with | Some clauses -> Some (clauses, constr)
                     | None -> None)
          | Until (s, i, f, g) when Interval.has_zero i ->
            aux m t { f with form = And (s, [f; g]) }
          | Until (_s, _i, f, _g) ->
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
                  match Option.all (List.map clauses ~f:(fun { Clause.trigger; effects } ->
                      let are_effects_simple = List.for_all effects
                          ~f:(function Cau _ | Sup _ -> true | _ -> false) in
                      let suppressed = List.filter_map effects
                          ~f:(fun effect -> match effect with
                              | (Sup (r, trms) as p) -> Some { form = Predicate (r, trms); info = () }
                              | _ -> None) in
                      let is_trigger_trivial = match trigger.Trigger.filter.form with
                        | TT -> true
                        | _ -> List.mem suppressed trigger.filter ~equal:core_equal in
                      if is_trigger_trivial && are_effects_simple then
                        begin
                          if not (List.is_empty effects) then
                            Some { Clause.trigger = Trigger.make (make_dummy TT);
                                   effects = List.map effects ~f:(Effect.nextize is) }
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
                     op_to_string (make_dummy (Eventually (i, f)))), f, t))
             | solutions -> Possible solutions)
          | Label (_, f) -> aux m t f
          | _ -> Impossible (Errors.EFormula (None, f, t))
        end
      | false, false -> assert false
    in
    let r = Verdict.map r ~f:(fix_predicate_names_clauses_constr m) in
    r
  in

  let type_let_aux_sols m let_def =
    let body = let_def.body in
    let args = let_def.args |> List.map ~f:fst |> List.map ~f:Term.dummy_var in
    let cau_sols = aux m Enftype.cau body in
    let sup_sols = aux m Enftype.sup body in
    let cau_sols = Verdict.map ~f:(fix_predicate_names_clauses_constr m) cau_sols in
    let sup_sols = Verdict.map ~f:(fix_predicate_names_clauses_constr m) sup_sols in
    let set_enftype e t (clauses, constr) =
      (List.map clauses ~f:(fun (clause : Clause.t) ->
           let n =
             if Enftype.is_causable t
             then "Cau_" ^ e
             else "Sup_" ^ e in
           let g = make_dummy (Predicate (n, args)) in
           let c = { clause with Clause.
                     trigger =
                       { Trigger.guards =
                           if List.is_empty clause.trigger.guards then [[g]]
                           else List.map ~f:(fun fs -> g :: fs) clause.trigger.guards;
                         filter = clause.trigger.filter } } in
           c
         ),
       Constraints.ac_simplify (Constraints.CConj [constr; Constraints.CGeq (e, t); Constraints.CLeq (e, t)])) in
    Verdict.map ~f:(List.map ~f:(set_enftype let_def.name Enftype.cau)) cau_sols,
    Verdict.map ~f:(List.map ~f:(set_enftype let_def.name Enftype.sup)) sup_sols in

  let type_let_aux m let_def (trigger : Trigger.t) =
    let cau_sols, sup_sols = type_let_aux_sols m let_def in
    let trigger_pos = ({ trigger with Trigger.filter = make_past_only true trigger.filter } : Trigger.t)
    and trigger_neg = ({ trigger with Trigger.filter = make_past_only false trigger.filter } : Trigger.t) in
    let trigger_neg_opt =
      if equal_core_t trigger_pos.filter.form trigger_neg.filter.form
      then None
      else Some trigger_neg in
    cau_sols, sup_sols, trigger_pos, trigger_neg_opt in

  (* Type a let-bound expression *)
  let type_let ((m: let_map), (errors: Verdict.Errors.error list)) (let_def: let_def)
    : let_map * (Verdict.Errors.error list) =
    let open Verdict in
    let body = let_def.body in
    let args = let_def.args |> List.map ~f:fst |> List.map ~f:Term.dummy_var in
    (* Strip existential quantifiers *)
    let g = Lformula.strip_exists body in
    (* Additional check for temporal operators *)
    match g.form with
    | Since (s, i, f, g) ->
      begin
        let ft = normalize_trigger (guard_map_of_let_map m) (Trigger.make f) false body in
        let gt = normalize_trigger (guard_map_of_let_map m) (Trigger.make g) true body in
        match ft, gt with
        | Impossible error_f, Impossible error_g -> (m, error_f :: error_g :: errors)
        | Impossible error_f, _ -> (m, error_f :: errors)
        | _, Impossible error_g -> (m, error_g :: errors)
        | Possible [trigger_f], Possible [trigger_g] ->
          let _, sup_sols_f, trigger_pos_f, trigger_neg_opt_f = type_let_aux m { let_def with body = f } trigger_f in
          let cau_sols_g, sup_sols_g, trigger_pos_g, trigger_neg_opt_g = type_let_aux m { let_def with body = g } trigger_g in
          let switch_pos = Switch.Since (trigger_pos_f, trigger_pos_g)
          and switch_neg_opt = Option.map2 ~f:(fun trigger_neg_f trigger_neg_g -> Switch.Since (trigger_neg_f, trigger_neg_g)) trigger_neg_opt_f trigger_neg_opt_g in
          let cau_sols, sup_sols =
            if Interval.has_zero i then
              cau_sols_g, conj ~f:merge_clauses_constr sup_sols_f sup_sols_g
            else
              Impossible (EFormula (Some "Since's interval does not contain 0", g, Enftype.cau)),
              sup_sols_g
          in
          let cau_sols = Verdict.map cau_sols ~f:(fun clauses_constrs ->
              List.map clauses_constrs ~f:(fun (clauses, constr) ->
                  List.map clauses ~f:(fun { Clause.trigger; effects } ->
                      let g = make_dummy (Predicate (let_def.name, args)) in
                      let filter = ac_simplify (make_dummy (
                          And (N, [trigger.filter; make_dummy (Neg g)]))) in
                      { Clause.trigger = { trigger with Trigger.filter }; effects }), constr)) in
          let sup_sols = Verdict.map sup_sols ~f:(fun clauses_constrs ->
              List.map clauses_constrs ~f:(fun (clauses, constr) ->
                  List.map clauses ~f:(fun { Clause.trigger; effects } ->
                      let g = make_dummy (Predicate (let_def.name, args)) in
                      let filter = ac_simplify (make_dummy (
                          And (N, [trigger.filter; g]))) in
                      { Clause.trigger = { trigger with Trigger.filter }; effects }), constr)) in
          let m = Map.update m let_def.name
              ~f:(fun _ -> { let_def with cau_sols = cau_sols;
                                          sup_sols = sup_sols;
                                          switch_pos_opt = Some switch_pos;
                                          switch_neg_opt }) in
          (m, errors)
        | _ -> (m, errors)
      end
    | Once (i, f) ->
      begin
        let ft = normalize_trigger (guard_map_of_let_map m) (Trigger.make f) true body in
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
          let switch_pos = Switch.Once trigger_pos
          and switch_neg_opt = Option.map ~f:(fun trigger_neg -> Switch.Now trigger_neg) trigger_neg_opt in
          let m = Map.update m let_def.name
              ~f:(fun _ -> { let_def with cau_sols = cau_sols;
                                          switch_pos_opt = Some switch_pos;
                                          switch_neg_opt }) in
          (m, errors)
        | _ -> (m, errors)
      end
    | Prev (i, f) ->
      begin
        let ft = normalize_trigger (guard_map_of_let_map m) (Trigger.make f) true body in
        match ft with
        | Impossible error_f -> (m, error_f :: errors)
        | Possible [trigger] ->
          let _, _, trigger_pos, trigger_neg_opt = type_let_aux m { let_def with body = f } trigger in
          let switch_pos = Switch.Prev trigger_pos in
          let _switch_neg_opt = Option.map ~f:(fun trigger_neg -> Switch.Now trigger_neg) trigger_neg_opt in
          let m = Map.update m let_def.name
              ~f:(fun _ -> { let_def with switch_pos_opt = Some switch_pos }) in
          (m, errors)
        | _ -> (m, errors)
      end
    | _ -> begin
        let arg_set = Set.of_list (module Var) (List.map ~f:fst let_def.args) in
        let vars = Set.elements (Set.union (fvs [g]) arg_set) in
        let gt = normalize_trigger ~vars:(Some vars) (guard_map_of_let_map m) (Trigger.make g) true body in
        match gt with
        | Impossible _error ->
          let filter_trigger =
            normalize_trigger_best_effort
              ~vars:(Some vars) (guard_map_of_let_map m) (Trigger.make g) true body in
          let _guarded_vars = fvs (List.concat filter_trigger.guards) in
          let _non_arg_fvs = Set.diff (fvs [g]) arg_set in
          let _unguarded_non_args = Set.diff _non_arg_fvs _guarded_vars in
          let filter_trigger_opt = Some filter_trigger in
          let m = Map.update m let_def.name
              ~f:(fun _ -> { let_def with filter_trigger_opt }) in
          (m, errors)
        | Possible [trigger] ->
          let cau_sols, sup_sols, trigger_pos, trigger_neg_opt = type_let_aux m let_def trigger in
          let switch_pos = Switch.Now trigger_pos
          and switch_neg_opt = Option.map ~f:(fun trigger_neg -> Switch.Now trigger_neg) trigger_neg_opt in
          let m = Map.update m let_def.name
              ~f:(fun _ -> { let_def with cau_sols = cau_sols;
                                          sup_sols = sup_sols;
                                          switch_pos_opt = Some switch_pos;
                                          switch_neg_opt }) in
          (m, errors)
        | _ -> (m, errors)
      end
  in

  let lets = List.map lets ~f:(fun le ->
      { name = le.le_name; enftype_opt = le.le_enftype; args = le.le_args;
        body = le.le_body; origin = le.le_origin;
        cau_sols = Impossible (Verdict.Errors.EFormula (None, le.le_body, Enftype.cau));
        sup_sols = Impossible (Verdict.Errors.EFormula (None, le.le_body, Enftype.sup));
        switch_pos_opt = None; switch_neg_opt = None;
        filter_trigger_opt = None }) in
  let m, errors = List.fold_left ~init:(Map.empty (module String), []) ~f:type_let lets in

  match errors with
  | [] -> Verdict.Possible [{ let_names = List.map lets ~f:(fun le -> le.name);
                              let_map = m;
                              sols = aux m Enftype.cau f}]
  | errors -> Verdict.Impossible (Verdict.Errors.EConj errors)


(* ------------------------------------------------------------------ *)
(* enforce: outer normalization + enforceability type inference        *)
(* ------------------------------------------------------------------ *)

let enforce ?(verbose=true) (norm : Lformula.t) (b : Time.Span.s) : Nformula.t =
  let f = norm.Lformula.formula in
  let error_msg f err =
    Stdio.print_endline ("The formula\n "
                         ^ to_string f
                         ^ "\nis not enforceable:\n"
                         ^ Verdict.Errors.to_string (Verdict.Errors.ac_simplify err));
    raise_formula_error "this formula is not enforceable" in
  if not (Set.is_empty (fv f)) && verbose then (
    Stdio.print_endline ("The formula\n "
                         ^ to_string f
                         ^ "\nis not closed: free variables are "
                         ^ String.concat ~sep:", " (List.map ~f:Var.to_string (Set.elements (fv f))));
    ignore (raise_formula_error "this formula is not closed"));
  allow_table_guards := false;
  table_guard_warnings := [];
  let verdict = match types Enftype.cau norm b with
    | Verdict.Impossible _ ->
      allow_table_guards := true;
      table_guard_warnings := [];
      types Enftype.cau norm b
    | ok -> ok
  in
  List.iter (List.rev !table_guard_warnings) ~f:(fun (name, body) ->
      Stdio.eprintf "WARNING: table %s used as guard (body: %s)\n" name body);
  match verdict with
  | Verdict.Impossible err -> error_msg f err
  | Possible [nf] -> nf
  | Possible _ -> assert false
