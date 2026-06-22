open Base
open MFOTL_lib

open Tyformula

module Var = Tterm.TypedVar
module Term = Tterm

(* ------------------------------------------------------------------ *)
(* Trigger, Clause, Switch, GuardInfo                                   *)
(* (shared IR between enforceability, extraction, and compilation)     *)
(* ------------------------------------------------------------------ *)

module Trigger = struct
  type t = {
    guards : Tyformula.t list list; (* DNF *)
    filter : Tyformula.t;
  } [@@deriving equal]

  let make (filter : Tyformula.t) : t = { guards = []; filter }

  (* Simplify the DNF guards (an OR of ANDs).  Both levels are idempotent and
     the disjunction subsumes supersets:
       - drop repeated conjuncts within a disjunct,
       - drop repeated disjuncts,
       - drop any disjunct whose conjuncts are a superset of another's
         ((A∧B) ∨ (A∧B∧C) ≡ (A∧B)).
     Order of first occurrence is preserved. *)
  let dedup (trig : t) : t =
    let stable_dedup ~equal xs =
      List.rev (List.fold xs ~init:[] ~f:(fun acc x ->
          if List.mem acc x ~equal then acc else x :: acc)) in
    let subsumes smaller larger =
      List.for_all smaller ~f:(fun c -> List.mem larger c ~equal:Tyformula.equal) in
    let guards =
      trig.guards
      |> List.map ~f:(stable_dedup ~equal:Tyformula.equal)
      |> stable_dedup ~equal:(List.equal Tyformula.equal) in
    let guards =
      List.filteri guards ~f:(fun i d ->
          not (List.existsi guards ~f:(fun j d' ->
              j <> i && subsumes d' d
              && (List.length d' < List.length d || j < i)))) in
    { trig with guards }

  let to_string (trig : t) : string =
    Printf.sprintf "{ guards = [%s];\n  filter = %s }"
      (Etc.string_list_to_string (List.map trig.guards ~f:(
           fun fs -> "[" ^ Etc.string_list_to_string (List.map ~f:Tyformula.to_string fs))))
      (Tyformula.to_string trig.filter)

  let to_formula (pos : bool) (trig : t) : Tyformula.t =
    let filter = trig.filter |> Tyformula.push_negs |> Tyformula.ac_simplify in
    match trig.guards with
    | [] -> filter
    | guards ->
      let guard_f = Tyformula.make_dummy (Or (N, List.map ~f:(
          fun fs -> Tyformula.make_dummy (And (N, fs))) guards)) in
      if pos then
        Tyformula.make_dummy (And (N, [guard_f; filter]))
      else
        Tyformula.make_dummy (Imp (N, guard_f, filter))

  let guard_predicates ?(lets=Map.empty (module String)) (t : t) =
    let fs = List.concat t.guards in
    Set.union_list (module String) (List.map ~f:(Tyformula.predicates ~lets) fs)

  let predicates ?(lets=Map.empty (module String)) (t : t) =
    let fs = t.filter :: List.concat t.guards in
    Set.union_list (module String) (List.map ~f:(Tyformula.predicates ~lets) fs)

  let non_monotone_predicates ?(let_ctxt_mon=Map.empty (module String)) ?(let_ctxt_anti_mon=Map.empty (module String)) (t : t) =
    let fs = t.filter :: List.concat t.guards in
    let mons, anti_mons = List.unzip (List.map ~f:(Tyformula.non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon) fs) in
    Set.union_list (module String) mons, Set.union_list (module String) anti_mons
    
    
end

module Effect = struct
  type t =
    | Cau of string * Tterm.t list
    | Sup of string * Tterm.t list
    | EventuallyCau of Interval.t * string * Tterm.t list
    | EventuallySup of Interval.t * string * Tterm.t list
    | NextCau of Interval.t list * string * Tterm.t list
    | NextTT  of Interval.t list
    | NextSup of Interval.t list * string * Tterm.t list

  let eventualize itv = function
    | Cau (r, trms) -> EventuallyCau (itv, r, trms)
    | Sup (r, trms) -> EventuallySup (itv, r, trms)

  let nextize itvs = function
    | Cau (r, trms) -> NextCau (itvs, r, trms)
    | Sup (r, trms) -> NextSup (itvs, r, trms)

  let to_string = function
    | Cau (r, trms) -> Printf.sprintf "%s(%s)" r (Tterm.list_to_string trms)
    | Sup (r, trms) -> Printf.sprintf "¬%s(%s)" r (Tterm.list_to_string trms)
    | EventuallyCau (itv, r, trms) -> Printf.sprintf "◊%s %s(%s)" (Interval.to_string itv) r (Tterm.list_to_string trms)
    | NextTT itvs -> Printf.sprintf "○%s ⊤" (Etc.string_list_to_string (List.map ~f:Interval.to_string itvs))
    | NextCau (itvs, r, trms) -> Printf.sprintf "○%s %s(%s)"
                                   (Etc.string_list_to_string (List.map ~f:Interval.to_string itvs))
                                   r (Tterm.list_to_string trms)
    | NextSup (itvs, r, trms) -> Printf.sprintf "○%s ¬%s(%s)"
                                   (Etc.string_list_to_string (List.map ~f:Interval.to_string itvs))
                                   r (Tterm.list_to_string trms)

  let rec to_typed =
    let info enftype = { Tyformula.TypedInfo.dummy with enftype = Enftype.cau } in
    let rec add_next f = function
      | [] -> f
      | itv::itvs -> { form = Next (itv, add_next f itvs); info = info Enftype.cau } in
    function
    | Cau (r, trms) -> { form = Predicate (r, trms)
                       ; info = info Enftype.cau }
    | Sup (r, trms) -> { form = Neg ({ form = Predicate (r, trms); info = info Enftype.sup })
                       ; info = info Enftype.cau }
    | EventuallyCau (itv, r, trms) -> { form = Eventually (itv, { form = Predicate (r, trms); info = info Enftype.cau })
                                      ; info = info Enftype.cau }
    | NextTT itvs -> add_next { form = TT; info = info Enftype.cau } itvs
    | NextCau (itvs, r, trms) -> add_next (to_typed (Cau (r, trms))) itvs
    | NextSup (itvs, r, trms) -> add_next (to_typed (Sup (r, trms))) itvs

  let map_predicate ~f = function
    | Cau (r, trms) -> Cau (f true r, trms)
    | Sup (r, trms) -> Sup (f false r, trms)
    | EventuallyCau (itv, r, trms) -> EventuallyCau (itv, f true r, trms)
    | EventuallySup (itv, r, trms) -> EventuallySup (itv, f false r, trms)
    | NextTT n -> NextTT n
    | NextCau (n, r, trms) -> NextCau (n, f true r, trms)
    | NextSup (n, r, trms) -> NextSup (n, f false r, trms)

  let fvs es = fvs (List.map ~f:to_typed es)

  let predicates = function
    | Cau (r, _)
    | Sup (r, _)
    | EventuallyCau (_, r, _)
    | EventuallySup (_, r, _)
    | NextCau (_, r, _)
    | NextSup (_, r, _) -> Set.singleton (module String) r
    | NextTT _ -> Set.empty (module String)
    
end

module Clause = struct
  type t = {
    trigger : Trigger.t;
    effects : Effect.t list;
    (* Source labels (e.g. "../Lex/.../gdpr.lex:1174:1-1183:45") active over this
       clause, innermost first.  Propagated from the [Label] formula wrapper to
       the rule it ultimately produces, instead of via a synthetic Cau_Label
       indirection. *)
    labels  : string list;
  }

  let make ?(labels = []) ~trigger ~effects () : t = { trigger; effects; labels }

  let to_string (c : t) : string =
    Printf.sprintf "{ trigger = %s;\n  effects = [%s]%s }"
      (Trigger.to_string c.trigger)
      (Etc.string_list_to_string (List.map ~f:Effect.to_string c.effects))
      (if List.is_empty c.labels then ""
       else ";\n  labels = [" ^ String.concat ~sep:"; " c.labels ^ "]")

  let trigger_predicates ?(lets=Map.empty (module String)) (c : t) =
    Trigger.predicates ~lets c.trigger

  let trigger_non_monotone_predicates ?(let_ctxt_mon=Map.empty (module String)) ?(let_ctxt_anti_mon=Map.empty (module String)) (c : t) =
    Trigger.non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon c.trigger

  let effect_predicates (c : t) =
    Set.union_list (module String) (List.map ~f:Effect.predicates c.effects)

  let predicates (c : t) =
    Set.union (trigger_predicates c) (effect_predicates c)
      
    
end

(* Metadata for an aggregation let (observable-only).  The enumerating trigger
   for the inner subformula is stored alongside in [Switch.Agg]. *)
type agg_info = {
  ai_op          : Aggregation.op;
  ai_term        : Term.t;              (* aggregated term *)
  ai_groups      : Var.t list;          (* grouping variables *)
  ai_result      : Var.t * Dom.tt;      (* result var and its type *)
  ai_incremental : string option;       (* Some once_let_name for the O(1) fast path *)
}

(* Metadata for a table-operation let: a Python `tfun` applied per group. *)
type top_info = {
  ti_fn      : string;
  ti_args    : Term.t list;
  ti_groups  : Var.t list;
  ti_results : (Var.t * Dom.tt) list;
}

module Switch = struct
  (* Past temporal operators carry their metric interval, so the engine can
     window the backing table (evict tuples older than the upper bound, hold
     back tuples not yet within the lower bound).  [Once]/[Prev]/[Since] all use
     [Interval.full] (i.e. [0,∞)) for the non-metric case, which preserves the
     previous accumulate-forever behaviour. *)
  type t =
    | Once  of Interval.t * Trigger.t
    | Prev  of Interval.t * Trigger.t
    | Since of Interval.t * Trigger.t * Trigger.t
    | Now   of Trigger.t
    | Agg   of agg_info * Trigger.t
    | Top   of top_info * Trigger.t

  let to_string : t -> string = function
    | Once  (i, trigger) -> "⧫" ^ Interval.to_string i ^ "(" ^ Trigger.to_string trigger ^ ")"
    | Prev  (i, trigger) -> "●" ^ Interval.to_string i ^ "(" ^ Trigger.to_string trigger ^ ")"
    | Since (i, ltrigger, rtrigger) ->
      "(" ^ Trigger.to_string ltrigger ^ ") S" ^ Interval.to_string i ^ " (" ^ Trigger.to_string rtrigger ^ ")"
    | Now   trigger -> Trigger.to_string trigger
    | Agg (ai, trigger) ->
      Printf.sprintf "%s(...) over %s" (Aggregation.op_to_string ai.ai_op)
        (Trigger.to_string trigger)
    | Top (ti, trigger) ->
      Printf.sprintf "%s(...) over %s" ti.ti_fn (Trigger.to_string trigger)

  let to_formula (pos : bool) : t -> Tyformula.t = function
    | Once  (i, trigger) -> Tyformula.make_dummy (Once  (i, Trigger.to_formula pos trigger))
    | Prev  (i, trigger) -> Tyformula.make_dummy (Prev  (i, Trigger.to_formula pos trigger))
    | Since (i, ltrigger, rtrigger) ->
      Tyformula.make_dummy (Since (
          N, i,
          Trigger.to_formula (not pos) ltrigger,
          Trigger.to_formula pos rtrigger))
    | Now   trigger -> Trigger.to_formula pos trigger
    | Agg (_, trigger) | Top (_, trigger) -> Trigger.to_formula pos trigger
end

module GuardInfo = struct
  type t = {
    switch_pos_opt : Switch.t option;
    body_str       : string;
  }
  type map = (string, t, String.comparator_witness) Map.t
end

(* ------------------------------------------------------------------ *)
(* Constraints                                                          *)
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

module Verdict = Verdict.Make(Tyformula)

type enf_sols = (Clause.t list * Constraints.constr) Verdict.v

type let_def = {
  name               : string;
  enftype_opt        : Enftype.t option;
  args               : (Var.t * Dom.tt option) list;
  body               : t;
  origin             : t;     (* original formula fragment before transformation *)
  cau_sols           : enf_sols;
  sup_sols           : enf_sols;
  switch_pos_opt     : Switch.t option;
  switch_neg_opt     : Switch.t option;
  filter_trigger_opt : Trigger.t option;
}

type let_map = (string, let_def, String.comparator_witness) Map.t

type t = {
  let_names : string list;
  let_map   : let_map;
  sols      : enf_sols;
}

  
