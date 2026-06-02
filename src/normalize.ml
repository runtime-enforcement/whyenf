open Base
open MFOTL_lib
open Tyformula

module Var = Tterm.TypedVar
module Term = Tterm

(* Capture F.to_string before it can be shadowed by module Errors *)
let formula_to_string = to_string

(* Shared types *)

type trigger = {
  guards: t list list; (* DNF *)
  filter: t
} [@@deriving equal]

type clause = {
  trigger: trigger;
  effects: t list
}

type switch =
  | SOnce  of trigger
  | SPrev  of trigger
  | SSince of trigger * trigger
  | SNow   of trigger

(* Adapter type: the minimal let_def info that pull_guard needs *)
type let_guard_info = {
  switch_pos_opt : switch option;
  body_str       : string;       (* for error messages only *)
}
type guard_map = (string, let_guard_info, String.comparator_witness) Map.t

(* ------------------------------------------------------------------ *)
(* Trigger helpers                                                       *)
(* ------------------------------------------------------------------ *)

let trigger_to_string trigger =
  Printf.sprintf "{ guards = [%s];\n  filter = %s }"
    (Etc.string_list_to_string (List.map trigger.guards ~f:(
         fun fs -> "[" ^ Etc.string_list_to_string (List.map ~f:formula_to_string fs))))
    (formula_to_string trigger.filter)

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

let init_trigger filter =
  { guards = []; filter }

let of_switch p = function
  | SOnce trigger -> make_dummy (Once (Interval.full, of_trigger p trigger))
  | SPrev trigger -> make_dummy (Prev (Interval.full, of_trigger p trigger))
  | SSince (ltrigger, rtrigger) -> make_dummy (Since (N, Interval.full, of_trigger (not p) ltrigger, of_trigger p rtrigger))
  | SNow trigger -> of_trigger p trigger

(* ------------------------------------------------------------------ *)
(* strip_exists / add_back_exists                                        *)
(* ------------------------------------------------------------------ *)

let strip_exists f =
  match f |> all_exists |> snd |> List.last with
  | Some f -> f
  | _ -> f

let add_back_exists f xs fs =
  List.fold_right (List.zip_exn xs fs)
    ~f:(fun (x, f') f -> { f' with form = Exists (x, f) }) ~init:f

(* ------------------------------------------------------------------ *)
(* pull_lets / do_pull_lets                                              *)
(* ------------------------------------------------------------------ *)

let rec pull_lets ?(i=0) ?(m:(string, string list * t, String.comparator_witness) Map.t=Map.empty (module String)) form =
  let r =
    match form.form with
    | Predicate (r, trms) ->
      (match Map.find m r with
       | None -> (i, [], form)
       | Some (vars, e) -> (i, [], subst (Map.of_alist_exn (module Var) (List.zip_exn (List.map ~f:Var.of_ident vars) trms)) e))
    | TT | FF | EqConst _  -> (i, [], form)
    | Predicate' (_, _, f)
    | Let' (_, _, _, _, f)
    | Type (f, _) -> pull_lets ~i ~m f
    | Let (e, enftype, vars, f, g) ->
      let i, letsf, f = pull_lets ~i ~m f in
      (if Enftype.is_suppressable enftype || Enftype.is_causable enftype || height f > 1 then
         let i, letsg, g = pull_lets ~i ~m g in
         i, letsf @ (e, Some enftype, vars, f) :: letsg, g
       else
         let i, letsg, g = pull_lets ~i ~m:(Map.update m e ~f:(fun _ -> (List.map ~f:(fun (v, _) -> Var.ident v) vars, f))) g in
         i, letsf @ letsg, g)
    | Neg f ->
      let i, letsf, f = pull_lets ~i ~m f in
      i, letsf, { f with form = Neg f }
    | Exists (x, f)
    | Forall (x, f) when not (Set.mem (fvs [f]) x) ->
      pull_lets ~i ~m f
    | Exists (_x, _) ->
      let xs, fs = all_exists form in
      let i, lets, f = pull_lets ~i ~m (List.last_exn fs) in
      let e = "Exists" ^ string_of_int i in
      let fvs = Set.elements (fv form) in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      let g = add_back_exists f xs fs in
      i + 1, lets @ [e, None, vars, { f with form = g.form }],
      { f with form = Predicate (e, List.map ~f:Term.dummy_var fvs) }
    | Forall (x, f) ->
      pull_lets ~i ~m { form with form = Neg ({ form with form = Exists (x, { form with form = Neg f }) }) }
    | Prev (itv, f) ->
      let i, lets, f = pull_lets ~i ~m f in
      let e = "Prev" ^ string_of_int i in
      let fvs = Set.elements (fv f) in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      i + 1, lets @ [e, None, vars, { f with form = Prev (itv, f) }],
      { f with form = Predicate (e, List.map ~f:Term.dummy_var fvs) }
    | Once (itv, f) ->
      let i, lets, f = pull_lets ~i ~m f in
      let e = "Once" ^ string_of_int i in
      let fvs = Set.elements (fv f) in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      i + 1, lets @ [e, None, vars, { f with form = Once (itv, f) }],
      { f with form = Predicate (e, List.map ~f:Term.dummy_var fvs) }
    | Next (itv, f) ->
      let i, lets, f = pull_lets ~i ~m f in
      i, lets, { form with form = Next (itv, f) }
    | Eventually (itv, f) ->
      let i, lets, f = pull_lets ~i ~m f in
      i, lets, { form with form = Eventually (itv, f) }
    | Historically (itv, f) ->
      let i, lets, f = pull_lets ~i ~m f in
      let e = "Historically" ^ string_of_int i in
      let fvs = Set.elements (fv f) in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      i + 1, lets @ [e, None, vars, { f with form = Historically (itv, f) }],
      { f with form = Predicate (e, List.map ~f:Term.dummy_var fvs) }
    | Always (itv, f) ->
      let i, lets, f = pull_lets ~i ~m f in
      i, lets, { form with form = Always (itv, f) }
    | Since (s, itv, f, g) ->
      let i, letsf, f = pull_lets ~i ~m f in
      let i, letsg, g = pull_lets ~i ~m g in
      let e = "Since" ^ string_of_int i in
      (* Both sides of a Since must bind all table columns (for constant-time
         add/remove), so the columns are fv(f) ∩ fv(g), not their union. *)
      let fvs = Set.elements (Set.inter (fv f) (fv g)) in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      i + 1, letsf @ letsg @ [e, None, vars, { f with form = Since (s, itv, f, g) }],
      { f with form = Predicate (e, List.map ~f:Term.dummy_var fvs) }
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
      let i, lets, f = pull_lets ~i ~m f in
      let e = "Label" ^ string_of_int i ^ ":" ^ s in
      let fvs = Set.elements (fv f) in
      let vars = List.map ~f:(fun v -> (v, None)) fvs in
      i + 1, lets @ [e, None, vars, f],
      { f with form = Predicate (e, List.map ~f:Term.dummy_var fvs) }
    | _ -> failwith ("unsupported constructor " ^ op_to_string form)
  in r

let do_pull_lets f =
  let i, lets, f = pull_lets f in
  let _ = i in
  lets, f

(* ------------------------------------------------------------------ *)
(* non_monotone_predicates_of_trigger                                   *)
(* ------------------------------------------------------------------ *)

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

(* ------------------------------------------------------------------ *)
(* Two-tier guard control                                                *)
(* ------------------------------------------------------------------ *)

let allow_table_guards = ref false
let table_guard_warnings : (string * string) list ref = ref []

(* ------------------------------------------------------------------ *)
(* pull_guard                                                            *)
(* ------------------------------------------------------------------ *)

(* Given a formula f with a free variable x, find p_1, ..., p_k, g such that
   if p is true:  f = (p_1 | ... | p_k) & g
   if p is false: f =  p_1 | ... | p_k -> g
   in both cases: x is one of the arguments of each of p_1, ..., p_k.
   If this is not possible, the variable x is not present-guarded; return None *)
let rec pull_guard (m: guard_map) (x: Var.t) (p: bool) (trigger: trigger) : trigger option =
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
         | Some (SOnce _) | Some (SPrev _) | Some (SSince _) -> true
         | _ -> false)
      | None -> false
    in
    is_unguardable, is_table, ld_opt in
  let try_pulling_guard allow_table =
    (* First, check if one of the existing guards already does the job *)
    let with_existing_guard = (not (List.is_empty trigger.guards)) &&
                              List.for_all trigger.guards ~f:(
                                List.exists ~f:(fun guard -> match guard.form with
                                    | Predicate (r, trms) ->
                                      let is_unguardable, is_table, _ = guard_quality r in
                                      if is_unguardable || is_table && not allow_table then false
                                      else List.exists ~f:(Term.equal (Term.dummy_var x)) trms
                                    | _ -> false)) in
    if with_existing_guard
    then Some trigger
    (* If it not the case, look for a new guard *)
    else begin
      (* Treat empty guards (uninitialized) as [[]] (one empty disjunct) *)
      let base_guards = if List.is_empty trigger.guards then [[]] else trigger.guards in
      let rec aux p filter =
        let r =
          match filter.form, p with
          | TT, false -> Some trigger
          | FF, true  -> Some trigger
          | Predicate (r, trms), true when List.exists ~f:(Term.equal (Term.dummy_var x)) trms ->
            (* A predicate can serve as a guard unless it is:
               - a let-def with no switch (switch_pos_opt = None) [always rejected]
               - a table (SOnce, SPrev, SSince) [rejected unless allow_table_guards] *)
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
              Some { guards = List.map ~f:(fun fs -> filter :: fs) base_guards;
                     filter = make_dummy TT }
            end
          | EqConst (trm, _), true when Term.equal (Term.dummy_var x) trm ->
            Some { guards = List.map ~f:(fun fs -> filter :: fs) base_guards;
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
        r in
      aux p trigger.filter
    end in
  let _ = npg in
  (* Try without allowing tables to be guards *)
  let r_opt = try_pulling_guard false in
  (* If allow_table_guards is on, try again with tables *)
  match r_opt with
  | None when !allow_table_guards -> try_pulling_guard true
  | _ -> r_opt

(* ------------------------------------------------------------------ *)
(* normalize_trigger / normalize_trigger_best_effort                    *)
(* ------------------------------------------------------------------ *)

module Verdict = Verdict.Make(Tyformula)

(* Check that all variables in a formula are past-guarded and, if possible, normalize the formula *)
let normalize_trigger ?(vars=None) (m: guard_map) (trigger: trigger) (p: bool) (orig_f: t) : trigger Verdict.v =
  let vars = match vars with
    | None -> Set.elements (fvs (trigger.filter :: List.concat trigger.guards))
    | Some vars -> vars in
  List.fold_right
    ~f:(fun x ->
        function
        | Verdict.Impossible e -> Verdict.Impossible e
        | Verdict.Possible [trigger] ->
          (match pull_guard m x p trigger with
           | None -> Verdict.Impossible (Verdict.Errors.ERule
                                           ("Variable " ^ Var.to_string x ^
                                            " is not guarded in " ^ formula_to_string orig_f
                                            ^ " (polarity: " ^ (if p then "+" else "-") ^ ")"
                                            ^ " (computed filter: " ^ trigger_to_string trigger ^ ")"))
           | Some trigger -> Verdict.Possible [trigger])
        | other -> other)
    ~init:(Verdict.Possible [trigger]) vars

(* Check that all variables in a formula are past-guarded and, if possible, normalize the formula *)
let normalize_trigger_best_effort ?(vars=None) (m: guard_map) (trigger: trigger) (p: bool) (_orig_f: t) : trigger =
  let vars = match vars with
    | None -> Set.elements (fvs (trigger.filter :: List.concat trigger.guards))
    | Some vars -> vars in
  List.fold_right
    ~f:(fun x trigger ->
        match pull_guard m x p trigger with
        | None -> trigger
        | Some trigger -> trigger)
    ~init:trigger vars

(* ------------------------------------------------------------------ *)
(* maps_of_lets                                                          *)
(* ------------------------------------------------------------------ *)

let maps_of_lets lets =
  let pred_map =
    List.fold_left lets
      ~init:(Map.empty (module String))
      ~f:(fun lets (e, _, _, f) -> Map.update lets e (fun _ -> predicates ~lets f)) in
  let mon_map, anti_mon_map =
    List.fold_left lets
      ~init:(Map.empty (module String), Map.empty (module String))
      ~f:(fun (let_ctxt_mon, let_ctxt_anti_mon) (e, _, _, f) ->
          let mon, anti_mon = non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon f in
          Map.update let_ctxt_mon e (fun _ -> mon),
          Map.update let_ctxt_anti_mon e (fun _ -> anti_mon)) in
  pred_map, mon_map, anti_mon_map

