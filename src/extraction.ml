open Base
open MFOTL_lib
open Lformula    (* let_def, result *)
open Enforceability (* Clause, Trigger, Switch, Verdict, Constraints, make_past_only,
                       enf_sols, let_def, let_map, typing_result *)
open Tyformula    (* t, typed_t, fv, fvs, ac_simplify, make_dummy, map_info, TypedInfo *)
open Nformula

module Var = Tterm.TypedVar

let raise_formula_error msg = raise (Errors.FormulaError msg)

(* ------------------------------------------------------------------ *)
(* compile_clause                                                       *)
(*                                                                      *)
(* Converts one enforcement clause (trigger → effects) into a typed    *)
(* formula of the form:                                                 *)
(*   ALWAYS. ∀ free-vars. (guard ∧ past-filter) → (cau-effects)       *)
(* ------------------------------------------------------------------ *)

let compile_clause ({ Clause.trigger; effects } : Clause.t) =
  let f enftype = map_info ~f:(fun info -> { TypedInfo.dummy with info; enftype }) in
  let c = f Enftype.cau and s = f Enftype.sup and o = f Enftype.obs in
  let trigger = { trigger with Trigger.filter = make_past_only true trigger.Trigger.filter } in
  let effects : typed_t list = List.map effects ~f:Effect.to_typed in
  let init = ac_simplify
      { form = Imp (R, o (Trigger.to_formula true trigger),
                    { form = And (L, effects);
                      info = { TypedInfo.dummy with enftype = Enftype.cau } });
        info = { TypedInfo.dummy with enftype = Enftype.cau } } in
  let vars = Set.elements (fvs [init]) in
  let f = List.fold_right vars ~init
      ~f:(fun x f -> { form = Forall (x, f); info = { TypedInfo.dummy with enftype = Enftype.cau } }) in
  { f with form = Always (Interval.full, f) }

(* ------------------------------------------------------------------ *)
(* compile_formula                                                      *)
(*                                                                      *)
(* Wraps a list of enforcement clause formulas in the let bindings      *)
(* derived from extracted_lets, producing the final typed formula.       *)
(* ------------------------------------------------------------------ *)

let compile_formula (lets : Tnformula.let_def list) (fs : typed_t list) : typed_t =
  let init = ac_simplify { form = And (LR, fs); info = { TypedInfo.dummy with enftype = Enftype.cau } } in
  List.fold_right lets ~init
    ~f:(fun cl g ->
        match cl.body_neg_opt with
        | Some f_neg ->
          { form = Let (cl.name ^ "_pos", Enftype.obs, cl.args, cl.body_pos,
                        { form = Let (cl.name ^ "_neg", Enftype.obs, cl.args, f_neg, g);
                          info = { TypedInfo.dummy with enftype = Enftype.cau } });
            info = { TypedInfo.dummy with enftype = Enftype.cau } }
        | None ->
          { form = Let (cl.name, Enftype.obs, cl.args, cl.body_pos, g);
            info = { TypedInfo.dummy with enftype = Enftype.cau } })

(* ------------------------------------------------------------------ *)
(* find_let_clauses / compile_lets                                      *)
(*                                                                      *)
(* For each extracted let predicate, given the chosen constraint        *)
(* solution [sol], compute:                                             *)
(*   - body_pos / body_neg : the positive/negative switch formula       *)
(*   - clauses_opt         : enforcement clauses, if the predicate is   *)
(*                           purely causable or purely suppressable      *)
(*   - filter_trigger_opt  : fallback trigger when guardedness fails    *)
(* ------------------------------------------------------------------ *)

let find_let_clauses (m : let_map)
    (sol : (string, Enftype.Constraint.t, String.comparator_witness) Map.t)
    (key : string) (cau : bool) : Clause.t list  =
  match Map.find m key with
  | None -> []
  | Some def ->
    match (if cau then def.cau_sols else def.sup_sols) with
    | Verdict.Impossible _ -> []
    | Possible solutions ->
      match List.find solutions ~f:(fun (_, sub_constr) ->
          not (List.is_empty (
              List.filter_map
                (Constraints.solve (Constraints.ac_simplify sub_constr))
                ~f:(fun sub_sol -> Constraints.try_merge (sol, sub_sol))))) with
      | None -> []
      | Some (sub_clauses, _) -> sub_clauses

let compile_lets (m : let_map)
    (sol : (string, Enftype.Constraint.t, String.comparator_witness) Map.t) : Tnformula.let_map =
  Map.map m ~f:(fun (le : let_def) ->
      let enftype_opt = match Map.find sol le.name with
        | Some constr -> Some (Enftype.Constraint.solve constr)
        | None -> le.enftype_opt in
      let lift f =
        let vars = Set.elements (Set.diff (fv f) (Set.of_list (module Var) (List.map ~f:fst le.args))) in
        let f = List.fold_right vars ~init:f ~f:(fun x f -> make_dummy (Exists (x, f))) in
        map_info ~f:(fun info -> { TypedInfo.dummy with info }) f in
      let body_pos = match Option.bind (Map.find m le.name)
                               ~f:(fun def -> Option.map def.switch_pos_opt ~f:(fun s -> s, def.args)) with
        | Some (sw, _args) -> lift (Switch.to_formula true sw)
        | None -> map_info ~f:(fun info -> { TypedInfo.dummy with info }) le.body in
      let body_neg = Option.map
          (Option.bind (Map.find m le.name)
             ~f:(fun def -> Option.map def.switch_neg_opt ~f:(fun s -> s, def.args)))
          ~f:(fun (sw, _args) -> lift (Switch.to_formula true sw)) in
      let clauses = match enftype_opt with
        | Some et when Enftype.is_causable et && Enftype.is_suppressable et ->
          (* CauSup let-def: gather both the causing and suppressing clauses;
             the SMT check verifies their conditions are exclusive. *)
          find_let_clauses m sol le.name true @ find_let_clauses m sol le.name false
        | Some et when Enftype.is_causable et ->
          find_let_clauses m sol le.name true
        | Some et when Enftype.is_suppressable et ->
          find_let_clauses m sol le.name false
        | _ -> [] in
      let filter_trigger_opt = Option.bind (Map.find m le.name)
          ~f:(fun def -> def.filter_trigger_opt) in
      Tnformula.{ name = le.name; enftype_opt; args = le.args;
                  body_pos; body_neg_opt = body_neg;
                  switch_pos_opt = le.switch_pos_opt;
                  switch_neg_opt = le.switch_neg_opt;
                  clauses; filter_trigger_opt; force_filter = false })

(* ------------------------------------------------------------------ *)
(* downgrade_filter_lets                                                *)
(*                                                                      *)
(* A `Now` let whose predicate is only ever referenced in *filter*      *)
(* (membership-test) positions never has to enumerate its body, so it   *)
(* can be compiled as a `filter let` (a boolean test) instead of a      *)
(* materialised, enumerable `let`.  Collapsing such a let keeps the      *)
(* growing tables it would otherwise enumerate as guards out of the     *)
(* per-time-point complexity.                                           *)
(*                                                                      *)
(* We compute the set of lets that *must* stay enumerable ("full") by a  *)
(* backward fixpoint: a let is full iff it is referenced in a guard      *)
(* (enumeration) position of                                            *)
(*   (a) a top-level enforcement clause,                                 *)
(*   (b) the add/remove trigger of a table (always materialised, so the  *)
(*       predicates producing its tuples must stay enumerable), or       *)
(*   (c) another full `Now` let.                                         *)
(* Every other `Now` let has its guards folded into its filter, which    *)
(* leaves [Trigger.to_formula true] — and hence the body — unchanged.    *)
(* ------------------------------------------------------------------ *)

let downgrade_filter_lets (let_map : Tnformula.let_map) (clauses : Clause.t list)
  : Tnformula.let_map =
  let no_lets = Map.empty (module String) in
  let guard_refs (tr : Trigger.t) : string list =
    Set.to_list (Trigger.guard_predicates ~lets:no_lets tr) in
  let is_table_switch = function
    | Some (Switch.Once _ | Switch.Since _ | Switch.Prev _
           | Switch.Agg _ | Switch.Top _) -> true
    | _ -> false in
  let table_guard_refs : Switch.t option -> string list = function
    | Some (Switch.Once (_, tr)) | Some (Switch.Prev (_, tr))
    | Some (Switch.Agg (_, tr)) | Some (Switch.Top (_, tr)) -> guard_refs tr
    | Some (Switch.Since (_, lt, rt)) -> guard_refs lt @ guard_refs rt
    | _ -> [] in
  let now_guard_refs (def : Tnformula.let_def) : string list =
    let one = function Some (Switch.Now tr) -> guard_refs tr | _ -> [] in
    one def.switch_pos_opt @ one def.switch_neg_opt in
  (* A let can only become a filter let if every free variable of its body is one
     of its arguments.  A full let *enumerates* its body and projects the
     non-argument variables away; a filter let merely *tests membership* given
     its arguments, so any non-argument (existential) variable would be unbound
     and the test unsound.  A let that is not arg-closed must therefore stay a
     full (enumerating) let — and, like any full let, its guards must too, so it
     is seeded into [full] here rather than just skipped at emission. *)
  let arg_closed (def : Tnformula.let_def) : bool =
    let arg_vars = Set.of_list (module Var) (List.map def.args ~f:fst) in
    let body_forms =
      List.filter_map [def.switch_pos_opt; def.switch_neg_opt]
        ~f:(Option.map ~f:(Switch.to_formula true)) in
    Set.is_subset (fvs body_forms) ~of_:arg_vars in
  (* Seed: guards of the enforcement clauses, the producing predicates of every
     table (materialised whether or not it is enumerated), the guards of any
     [filter_trigger_opt] — an unguardable-fallback let is emitted with those as
     real guard patterns — and every let that is not arg-closed. *)
  let seed =
    List.concat_map clauses ~f:(fun c -> guard_refs c.Clause.trigger)
    @ List.filter_map (Map.data let_map) ~f:(fun def ->
        if arg_closed def then None else Some def.name)
    @ List.concat_map (Map.data let_map) ~f:(fun def ->
        (if is_table_switch def.switch_pos_opt
         then table_guard_refs def.switch_pos_opt else [])
        @ (match def.filter_trigger_opt with
           | Some tr -> guard_refs tr
           | None -> [])) in
  let full = ref (Set.of_list (module String)
                    (List.filter seed ~f:(Map.mem let_map))) in
  let changed = ref true in
  while !changed do
    changed := false;
    Set.iter !full ~f:(fun name ->
        match Map.find let_map name with
        | Some def ->
          List.iter (now_guard_refs def) ~f:(fun g ->
              if Map.mem let_map g && not (Set.mem !full g) then begin
                full := Set.add !full g; changed := true end)
        | None -> ())
  done;
  (* Mark every let that is never enumerated as a filter let.  ([full] already
     contains every not-arg-closed let, so anything outside it is a sound
     membership test.)  We keep the switch — and hence the guard structure the
     EDG / sectioning analyses rely on — untouched; only emission changes. *)
  Map.mapi let_map ~f:(fun ~key ~data ->
      Tnformula.{ data with force_filter = not (Set.mem !full key) })

(* ------------------------------------------------------------------ *)
(* extract                                                  *)
(*                                                                      *)
(* Phase 4: given the enforceability typing result, solve the           *)
(* constraint system, pick a strategy, and produce the compiled         *)
(* representation ready for the Enfflash backend.                       *)
(* ------------------------------------------------------------------ *)

let extract ?(orig : Tyformula.t option) (nf : Nformula.t) : Tnformula.t =
  let error err =
    (match orig with
     | Some f ->
       (* Report the original (pre-normalization) formula, matching the
          "not enforceable" message produced by [Enforceability.enforce]. *)
       Stdio.print_endline ("The formula\n "
                            ^ Tyformula.to_string f
                            ^ "\nis not enforceable:\n"
                            ^ Verdict.Errors.to_string (Verdict.Errors.ac_simplify err))
     | None ->
       Stdio.print_endline ("Constraint solving failed:\n"
                            ^ Verdict.Errors.to_string (Verdict.Errors.ac_simplify err)));
    raise_formula_error "no satisfying enforcement assignment" in
  match nf.sols with
  | Verdict.Impossible err -> error err
  | Possible solutions ->
    match Verdict.disjs (List.map solutions ~f:(fun (clauses, constr) ->
        let constr = Constraints.ac_simplify constr in
        match Constraints.solve constr with
        | sol :: _ ->
          let let_map = compile_lets nf.let_map sol in
          let let_clauses = List.concat (List.map (Map.data let_map) ~f:(fun cl -> cl.clauses)) in
          let clauses = clauses @ List.rev let_clauses in
          (* New enforceability analysis: build the Event Dependency Graph and,
             per SCC, (1) prove cause/suppress conditions incompatible via SMT
             and (2) prove the data-flow graph has no cycle through a non-stable
             edge.  A candidate solution is only accepted if both checks pass. *)
          let lets, _, _ = Splitting.maps_of_lets let_map in
          let edg = Edg.build ~lets clauses in
          let smt_conflicts = Smt_check.run edg in
          let flow_viol = Dataflow.run (Array.of_list clauses) in
          (match smt_conflicts, flow_viol with
           | [], [] ->
             (* Downgrade lets that are only ever filtered (never enumerated) to
                filter-lets, after the enforceability checks have validated the
                original structure (the collapse is semantics-preserving). *)
             let let_map = downgrade_filter_lets let_map clauses in
             let let_defs = List.map nf.let_names ~f:(fun name -> Map.find_exn let_map name) in
             let formula = compile_formula let_defs (List.map clauses ~f:compile_clause) in
             Verdict.Possible [Tnformula.{ let_names = nf.let_names; let_map; clauses; formula }]
           | _ ->
             let parts =
               (if List.is_empty smt_conflicts then []
                else ["cause/suppress conflict(s):\n" ^ Smt_check.conflicts_to_string smt_conflicts])
               @ (if List.is_empty flow_viol then []
                  else ["non-terminating data flow:\n" ^ Dataflow.violations_to_string flow_viol]) in
             Verdict.Impossible (Verdict.Errors.ERule
               ("Policy is not enforceable —\n" ^ String.concat ~sep:"\n" parts)))
        | [] ->
          Verdict.Impossible (Verdict.Errors.ERule
            ("Constraint system " ^ Constraints.to_string constr ^ " is not solvable")))) with
    | Possible (r :: _) -> r
    | Impossible err    -> error err

(* ------------------------------------------------------------------ *)
(* do_type_and_extract: phases 3 + 4 in one call                       *)
(* ------------------------------------------------------------------ *)

let do_type_and_extract ?(verbose=true) ?(moderate=true) f b =
  extract ~orig:f (enforce ~verbose (Lformula.make ~moderate f) b)

