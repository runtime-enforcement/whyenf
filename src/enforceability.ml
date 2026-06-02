open Base
open MFOTL_lib

(* Save a reference to the library-level FormulaError exception before
   any local [Errors] module can shadow the name. *)
let raise_formula_error msg = raise (Errors.FormulaError msg)

open Normalize
open Tyformula

module Var = Tterm.TypedVar
module Term = Tterm

(* ------------------------------------------------------------------ *)
(* Rank                                                                 *)
(* ------------------------------------------------------------------ *)

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

(* ------------------------------------------------------------------ *)
(* Constraints module                                                   *)
(* ------------------------------------------------------------------ *)

module Constraints = struct

  open Enftype.Constraint

  type constr =
    | CTT
    | CFF
    | CGeq of string * Enftype.t
    | CLeq of string * Enftype.t
    | CConj of constr list
    | CDisj of constr list [@@deriving equal, compare, sexp_of]

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
           CDisj cs'
         | c -> c)
    | c -> c

  let rec cartesian a = function
      [] -> []
    | h::t -> (List.map a ~f:(fun x -> (x, h))) @ cartesian a t

  let try_merge (a, b) =
    try Some (Map.merge a b ~f:merge)
    with CannotMerge _k -> None

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
    let r = match c with
      | CTT -> [Map.empty (module String)]
      | CFF -> []
      | CGeq (s, t) -> [Map.singleton (module String) s (lower t)]
      | CLeq (s, t) -> [Map.singleton (module String) s (upper t)]
      | CConj [] -> [Map.empty (module String)]
      | CConj (c::cs) ->
        let f sol d = List.filter_map (cartesian sol (solve d)) ~f:try_merge in
        List.fold_left cs ~init:(solve c) ~f
      | CDisj cs -> List.concat_map cs ~f:solve
    in
    r

end

type enf_sols = (clause list * Constraints.constr) Verdict.v

(* ------------------------------------------------------------------ *)
(* let_def / let_map types                                              *)
(* ------------------------------------------------------------------ *)

type let_def = {
  name: string;
  args: (Var.t * Dom.tt option) list;
  body: t;
  cau_sols: enf_sols;
  sup_sols: enf_sols;
  switch_pos_opt: switch option;
  switch_neg_opt: switch option;
  filter_trigger_opt: trigger option;
}
type let_map = (string, let_def, String.comparator_witness) Map.t

let guard_map_of_let_map (m: let_map) : guard_map =
  Map.map m ~f:(fun ld ->
      { switch_pos_opt = ld.switch_pos_opt; body_str = to_string ld.body })

(* ------------------------------------------------------------------ *)
(* to_string helpers                                                    *)
(* ------------------------------------------------------------------ *)

let switch_to_string = function
  | SOnce trigger -> "⧫(" ^ trigger_to_string trigger ^ ")"
  | SPrev trigger -> "●(" ^ trigger_to_string trigger ^ ")"
  | SSince (ltrigger, rtrigger) -> "(" ^ trigger_to_string ltrigger ^ ") S (" ^ trigger_to_string rtrigger ^ ")"
  | SNow trigger -> trigger_to_string trigger

let clause_to_string clause =
  Printf.sprintf "{ trigger = %s;\n  effects = [%s] }"
    (trigger_to_string clause.trigger)
    (Etc.string_list_to_string (List.map ~f:to_string clause.effects))

let enf_sols_to_string enf_sols =
  Printf.sprintf "[%s]"
    (Etc.string_list_to_string (List.map enf_sols ~f:(fun (clauses, constr) ->
         Printf.sprintf "{ clauses = [%s];\n  constr = %s }"
           (Etc.string_list_to_string (List.map ~f:clause_to_string clauses))
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
    (o "None" switch_to_string let_def.switch_pos_opt)
    (o "None" switch_to_string let_def.switch_neg_opt)

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
(* make_past_only                                                       *)
(* ------------------------------------------------------------------ *)

let rec make_past_only (p: bool) form =
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
  | Until (s, i, _f, g) when p && Interval.has_zero i -> make_past_only p g
  | Until (_s, _i, _f, _g) when p -> make_dummy FF
  | Until (_s, _i, _f, _g) -> make_dummy TT
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
  | Next (_i, _f) when p -> make_dummy FF
  | Next (_i, _f) -> make_dummy TT
  | Once (i, f) ->
    let f = make_past_only p f in
    { form with form = Once (i, f) }
  | Eventually (i, f) when Interval.has_zero i -> make_past_only p f
  | Eventually (_i, _f) when p -> make_dummy FF
  | Eventually (_i, _f) -> make_dummy TT
  | Historically (i, f) ->
    let f = make_past_only p f in
    { form with form = Historically (i, f) }
  | Always (i, f) when p && Interval.has_zero i ->
    let f = make_past_only (not p) (make_dummy (Neg f)) in
    { form with form = Neg f }
  | Always (_i, _f) when p -> make_dummy FF
  | Always (_i, _f) -> make_dummy TT
  | Label (s, f) ->
    let f = make_past_only p f in
    { form with form = Label (s, f) }

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
      List.map clauses ~f:(fun { trigger; effects } ->
          { trigger = { guards = List.map ~f:(List.map ~f:(map_predicate ~pol:false ~f:(fix_predicate_names m))) trigger.guards;
                        filter = map_predicate ~pol:false ~f:(fix_predicate_names m) trigger.filter };
            effects = List.map ~f:(map_predicate ~f:(fix_predicate_names m)) effects }),
      constrs)

(* ------------------------------------------------------------------ *)
(* types: main enforceability type inference                            *)
(* ------------------------------------------------------------------ *)

let types (t: Enftype.t) (f: t) (b: Interval.v) : 'a Verdict.v =

  let set_b = function
    | Interval.U a -> Interval.B (a, b)
    | B _ as i -> i in

  let dummy_for_var x = Term.dummy_for_var x in

  let f = push_quants f in

  let lets, f = do_pull_lets f in

  let f = ac_simplify f in
  let lets = List.map ~f:(fun (s, enftype, args, f) -> (s, enftype, args, ac_simplify f)) lets in

  let f = match f.form with
    | Always (itv, f) when Interval.is_full itv -> f
    | And (s, fs) ->
      let fs = List.map ~f:(function
          | { form = Always (itv, f) } when Interval.is_full itv -> f
          | f -> f) fs in
      make_dummy (And (s, fs))
    | _ -> f in

  let pred_map, mon_map, anti_mon_map = maps_of_lets lets in

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
                    match normalize_trigger ~vars (guard_map_of_let_map m) trigger false f with
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
                  match Option.all (List.map clauses ~f:(fun { trigger; effects } ->
                      let _are_effects_simple = List.for_all effects
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
                                       make_dummy (construct_nexts is fs f.form)) }
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
                    Some (List.concat clauses, Constraints.CConj constrs))) enf_sols
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
                    match normalize_trigger ~vars (guard_map_of_let_map m) trigger true f with
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
                                       make_dummy (construct_nexts is fs f.form)) }
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
           c
         ),
       Constraints.ac_simplify (Constraints.CConj [constr; Constraints.CGeq (e, t); Constraints.CLeq (e, t)])) in
    Verdict.map ~f:(List.map ~f:(set_enftype let_def.name Enftype.cau)) cau_sols,
    Verdict.map ~f:(List.map ~f:(set_enftype let_def.name Enftype.sup)) sup_sols in

  let type_let_aux m let_def (trigger : trigger) =
    let cau_sols, sup_sols = type_let_aux_sols m let_def in
    let trigger_pos = ({ trigger with filter = make_past_only true trigger.filter } : trigger)
    and trigger_neg = ({ trigger with filter = make_past_only false trigger.filter } : trigger) in
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
    let g = strip_exists body in
    (* Additional check for temporal operators *)
    match g.form with
    | Since (s, i, f, g) ->
      begin
        let ft = normalize_trigger (guard_map_of_let_map m) (init_trigger f) false body in
        let gt = normalize_trigger (guard_map_of_let_map m) (init_trigger g) true body in
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
        | _ -> (m, errors)
      end
    | Once (i, f) ->
      begin
        let ft = normalize_trigger (guard_map_of_let_map m) (init_trigger f) true body in
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
        | _ -> (m, errors)
      end
    | Prev (i, f) ->
      begin
        let ft = normalize_trigger (guard_map_of_let_map m) (init_trigger f) true body in
        match ft with
        | Impossible error_f -> (m, error_f :: errors)
        | Possible [trigger] ->
          let _, _, trigger_pos, trigger_neg_opt = type_let_aux m { let_def with body = f } trigger in
          let switch_pos = SPrev trigger_pos in
          let _switch_neg_opt = Option.map ~f:(fun trigger_neg -> SNow trigger_neg) trigger_neg_opt in
          let m = Map.update m let_def.name
              ~f:(fun _ -> { let_def with switch_pos_opt = Some switch_pos }) in
          (m, errors)
        | _ -> (m, errors)
      end
    | _ -> begin
        let arg_set = Set.of_list (module Var) (List.map ~f:fst let_def.args) in
        let vars = Set.elements (Set.union (fvs [g]) arg_set) in
        let gt = normalize_trigger ~vars:(Some vars) (guard_map_of_let_map m) (init_trigger g) true body in
        match gt with
        | Impossible _error ->
          let filter_trigger =
            normalize_trigger_best_effort
              ~vars:(Some vars) (guard_map_of_let_map m) (init_trigger g) true body in
          let _guarded_vars = fvs (List.concat filter_trigger.guards) in
          let _non_arg_fvs = Set.diff (fvs [g]) arg_set in
          let _unguarded_non_args = Set.diff _non_arg_fvs _guarded_vars in
          let filter_trigger_opt = Some filter_trigger in
          let m = Map.update m let_def.name
              ~f:(fun _ -> { let_def with filter_trigger_opt }) in
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
        | _ -> (m, errors)
      end
  in

  let raw_lets = lets in
  let lets = List.map lets ~f:(fun (name, _enftype_opt, args, body) ->
      { name; args; body;
        cau_sols = Impossible (Verdict.Errors.EFormula (None, body, Enftype.cau));
        sup_sols = Impossible (Verdict.Errors.EFormula (None, body, Enftype.sup));
        switch_pos_opt = None; switch_neg_opt = None;
        filter_trigger_opt = None }) in
  let m, errors = List.fold_left ~init:(Map.empty (module String), []) ~f:type_let lets in

  match errors with
  | [] -> Verdict.Possible [raw_lets, m, aux m Enftype.cau f]
  | errors -> Verdict.Impossible (Verdict.Errors.EConj errors)

(* ------------------------------------------------------------------ *)
(* compile_clause / compile_formula / find_let_clauses / compile_lets  *)
(* ------------------------------------------------------------------ *)

let compile_clause ({ trigger; effects }: clause) =
  let f enftype = map_info ~f:(fun info -> { TypedInfo.dummy with info; enftype }) in
  let c = f Enftype.cau and s = f Enftype.sup and o = f Enftype.obs in
  let trigger = { trigger with filter = make_past_only true trigger.filter } in
  let effects : typed_t list = List.map effects ~f:(fun (effect: t) ->
      match effect.form with
      | Neg { form; info = _ } ->
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
    ~f:(fun (e, enftype, vars, f_pos, f_neg_opt, _, _) g ->
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
      let body_pos, body_neg_opt, clauses_opt, filter_trigger_opt =
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
         (match enftype with
          | Some et when Enftype.is_causable et && not (Enftype.is_suppressable et) ->
            find_let_clauses m sol e true
          | Some et when Enftype.is_suppressable et && not (Enftype.is_causable et) ->
            find_let_clauses m sol e false
          | _ -> None),
         Option.bind (Map.find m e) ~f:(fun def -> def.filter_trigger_opt))
      in
      (e, enftype, orig_args, body_pos, body_neg_opt, clauses_opt, filter_trigger_opt))

(* ------------------------------------------------------------------ *)
(* Type aliases for the public interface                                *)
(* ------------------------------------------------------------------ *)

type pg_map = (string, Etc.string_set_list, String.comparator_witness) Map.t
type t_map  = (string, Enftype.t * int list, String.comparator_witness) Map.t

type compiled_let =
  string
  * Enftype.t option
  * (Var.t * Dom.tt option) list
  * typed_t
  * typed_t option
  * clause list option
  * trigger option

(* ------------------------------------------------------------------ *)
(* do_type                                                              *)
(* ------------------------------------------------------------------ *)

let do_type ?(verbose=true) ?(moderate=true) f b =
  let _orig_f = f in
  let error err =
    Stdio.print_endline ("The formula\n "
                         ^ to_string f
                         ^ "\nis not enforceable:\n"
                         ^ Verdict.Errors.to_string (Verdict.Errors.ac_simplify err));
    raise_formula_error (Printf.sprintf "this formula is not enforceable") in
  let f = f |> push_negs |> convert_vars |> convert_lets |> unroll_let ~moderate |> simplify |> ac_simplify in
  if not (Set.is_empty (fv f)) && verbose then (
    Stdio.print_endline ("The formula\n "
                         ^ to_string f
                         ^ "\nis not closed: free variables are "
                         ^ String.concat ~sep:", " (List.map ~f:Var.to_string (Set.elements (fv f))));
    ignore (raise_formula_error (Printf.sprintf "this formula is not closed")));
  match types Enftype.cau f b with
  | Verdict.Impossible err -> error err
  | Possible [lets, m, sols] ->
    (match sols with
     | Verdict.Impossible err -> error err
     | Possible solutions ->
       match (Verdict.disjs (List.map solutions ~f:(fun (clauses, constr) ->
           let constr = Constraints.ac_simplify constr in
           match Constraints.solve constr with
           | sol::_ ->
             let lets = compile_lets m sol lets in

             let let_clauses = List.concat (List.filter_map lets ~f:(fun (_, _, _, _, _, clauses_opt, _) -> clauses_opt)) in
             let fs = List.map (clauses @ List.rev let_clauses) ~f:compile_clause in
             Verdict.Possible [compile_formula lets fs]
           | [] -> Verdict.Impossible (Verdict.Errors.ERule ("Constraint system " ^ Constraints.to_string constr ^ " is not solvable"))))) with
       | Possible (f::_) -> f
       | Impossible err -> error err)
  | Possible _ -> assert false

(* ------------------------------------------------------------------ *)
(* do_type_and_compile                                                  *)
(* ------------------------------------------------------------------ *)

let do_type_and_compile ?(verbose=true) ?(moderate=true) f b =
  let _orig_f = f in
  let error err =
    Stdio.print_endline ("The formula\n "
                         ^ to_string f
                         ^ "\nis not enforceable:\n"
                         ^ Verdict.Errors.to_string (Verdict.Errors.ac_simplify err));
    raise_formula_error (Printf.sprintf "this formula is not enforceable") in
  let f = f |> push_negs |> convert_vars |> convert_lets |> unroll_let ~moderate |> simplify |> ac_simplify in
  if not (Set.is_empty (fv f)) && verbose then (
    Stdio.print_endline ("The formula\n "
                         ^ to_string f
                         ^ "\nis not closed: free variables are "
                         ^ String.concat ~sep:", " (List.map ~f:Var.to_string (Set.elements (fv f))));
    ignore (raise_formula_error (Printf.sprintf "this formula is not closed")));
  (* Two-tier: first try without temporal tables as guards *)
  allow_table_guards := false;
  table_guard_warnings := [];
  let result = match types Enftype.cau f b with
    | Verdict.Impossible _ ->
      (* Retry with table guards allowed *)
      allow_table_guards := true;
      table_guard_warnings := [];
      types Enftype.cau f b
    | ok -> ok
  in
  (* Print warnings about table guards that were needed *)
  List.iter (List.rev !table_guard_warnings) ~f:(fun (name, body) ->
      Stdio.eprintf "WARNING: table %s used as guard (body: %s)\n" name body);
  match result with
  | Verdict.Impossible err -> error err
  | Possible [lets, m, sols] ->
    (match sols with
     | Verdict.Impossible err -> error err
     | Possible solutions ->
       match (Verdict.disjs (List.map solutions ~f:(fun (clauses, constr) ->
           let constr = Constraints.ac_simplify constr in
           match Constraints.solve constr with
           | sol::_ ->
             let lets = compile_lets m sol lets in

             let let_clauses = List.concat (List.filter_map lets ~f:(fun (_, _, _, _, _, clauses_opt, _) -> clauses_opt)) in
             let all_clauses = clauses @ List.rev let_clauses in
             let fs = List.map all_clauses ~f:compile_clause in
             Verdict.Possible [(lets, all_clauses, m, compile_formula lets fs)]
           | [] -> Verdict.Impossible (Verdict.Errors.ERule ("Constraint system " ^ Constraints.to_string constr ^ " is not solvable"))))) with
       | Possible ((lets, all_clauses, m, f)::_) -> (lets, all_clauses, m, f)
       | Impossible err -> error err)
  | Possible _ -> assert false

