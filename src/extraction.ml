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
        | Some et when Enftype.is_causable et && not (Enftype.is_suppressable et) ->
          find_let_clauses m sol le.name true
        | Some et when Enftype.is_suppressable et && not (Enftype.is_causable et) ->
          find_let_clauses m sol le.name false
        | _ -> [] in
      let filter_trigger_opt = Option.bind (Map.find m le.name)
          ~f:(fun def -> def.filter_trigger_opt) in
      Tnformula.{ name = le.name; enftype_opt; args = le.args;
                  body_pos; body_neg_opt = body_neg;
                  switch_pos_opt = le.switch_pos_opt;
                  switch_neg_opt = le.switch_neg_opt;
                  clauses; filter_trigger_opt })

(* ------------------------------------------------------------------ *)
(* extract                                                  *)
(*                                                                      *)
(* Phase 4: given the enforceability typing result, solve the           *)
(* constraint system, pick a strategy, and produce the compiled         *)
(* representation ready for the Enfflash backend.                       *)
(* ------------------------------------------------------------------ *)

let extract (nf : Nformula.t) : Tnformula.t =
  let error err =
    Stdio.print_endline ("Constraint solving failed:\n"
                         ^ Verdict.Errors.to_string (Verdict.Errors.ac_simplify err));
    raise_formula_error "no satisfying enforcement assignment" in
  match nf.sols with
  | Verdict.Impossible err -> error err
  | Possible solutions ->
    match Verdict.disjs (List.map solutions ~f:(fun (clauses, constr) ->
        let constr = Constraints.ac_simplify constr in
        match Constraints.solve constr with
        | sol :: _ ->
          let let_map = compile_lets nf.let_map sol in
          let let_defs = List.map nf.let_names ~f:(fun name -> Map.find_exn let_map name) in
          let let_clauses = List.concat (List.map (Map.data let_map) ~f:(fun cl -> cl.clauses)) in
          let clauses = clauses @ List.rev let_clauses in
          let formula = compile_formula let_defs (List.map clauses ~f:compile_clause) in
          Verdict.Possible [Tnformula.{ let_names = nf.let_names; let_map; clauses; formula }]
        | [] ->
          Verdict.Impossible (Verdict.Errors.ERule
            ("Constraint system " ^ Constraints.to_string constr ^ " is not solvable")))) with
    | Possible (r :: _) -> r
    | Impossible err    -> error err

(* ------------------------------------------------------------------ *)
(* do_type_and_extract: phases 3 + 4 in one call                       *)
(* ------------------------------------------------------------------ *)

let do_type_and_extract ?(verbose=true) ?(moderate=true) f b =
  extract (enforce ~verbose (Lformula.make ~moderate f) b)

