(* Data structures and serialization for the enfflash program format (.ef).
   These types mirror enfflash/src/ast.rs and can be parsed by
   enfflash/src/program_parser.lalrpop. *)

open Base
open MFOTL_lib

(* ─── Types ──────────────────────────────────────────────────────────────── *)

type ef_ty = EfInt | EfStr | EfFloat

type ef_value =
  | EfVInt of int
  | EfVStr of string
  | EfVFloat of float
  | EfVBool of bool

type cmp_op = CmpEq | CmpNeq | CmpLt | CmpLe | CmpGt | CmpGe

type term_expr =
  | TEVar of string
  | TELit of ef_value
  | TEFunCall of string * term_expr list

type pattern_arg =
  | PAVar of string
  | PALiteral of ef_value
  | PAWildcard

type event_pattern = {
  ep_name: string;
  ep_args: pattern_arg list;
}

type guard_pattern =
  | GEvent of event_pattern
  | GEqConst of string * ef_value

type filter_expr =
  | FBoolLit of bool
  | FTableLookup of string * term_expr list
  | FCompare of term_expr * cmp_op * term_expr
  | FAnd of filter_expr * filter_expr
  | FOr of filter_expr * filter_expr
  | FNot of filter_expr

type clause = {
  cl_patterns: guard_pattern list list;
  cl_filter: filter_expr;
}

type rule_action = RCause | RSuppress

type event_decl = {
  ed_name: string;
  ed_param_types: ef_ty list;
}

type fun_decl = {
  fd_name: string;
  fd_param_names: string list;
  fd_param_types: ef_ty list;
  fd_ret_type: ef_ty;
  fd_body: string;
}

type let_def = {
  ld_label: string option;
  ld_is_filter: bool;
  ld_name: string;
  ld_params: (string * ef_ty) list;
  ld_clause: clause;
}

type table_def = {
  td_label: string option;
  td_lagged: bool;
  td_name: string;
  td_columns: (string * ef_ty) list;
  td_add_clause: clause;
  td_remove_clause: clause option;
  (* Metric window [a, b] (seconds) for Once/Since/Prev tables.  A tuple added
     at time t is valid for queries at current time c iff c - t ∈ [a, b].
     [None] = the non-metric [0, ∞) case (accumulate forever, never evict).
     [Some (a, None)] = lower bound a, unbounded upper. *)
  td_window: (int * int option) option;
}

type rule_def = {
  rd_label: string option;
  rd_event: string;
  rd_params: term_expr list;
  rd_action: rule_action;
  rd_delay: int option;
  rd_tp_offset: int option;
  rd_trigger: clause;
  rd_validate: filter_expr option;
}

(* Aggregation operators (SQL-like reductions over a column). *)
type agg_op = AggSum | AggAvg | AggMed | AggCnt | AggMin | AggMax | AggStd

(* An aggregation let: evaluates [agg_clause] to a set of valuations, groups
   them by [agg_groups], and reduces the [agg_term] column with [agg_op] per
   group, producing rows over [agg_columns] (= groups ++ result).  When
   [agg_incremental] = Some t, the subformula is an unbounded Once whose rows
   live in table [t] and the engine maintains a running per-group accumulator. *)
type agg_let_def = {
  agg_label: string option;
  agg_name: string;
  agg_columns: (string * ef_ty) list;
  agg_op: agg_op;
  agg_term: term_expr;
  agg_groups: string list;
  agg_result: string * ef_ty;
  agg_clause: clause;
  agg_incremental: string option;
}

(* A table-operation let: per group, the rows' [top_args] tuples are passed to
   the Python table function [top_fn] (a `tfun`), which returns output tuples
   bound to [top_results]. *)
type top_let_def = {
  top_label: string option;
  top_name: string;
  top_columns: (string * ef_ty) list;
  top_fn: string;
  top_args: term_expr list;
  top_groups: string list;
  top_results: (string * ef_ty) list;
  top_clause: clause;
}

(* A Python table function: takes one argument `rows` (a list of value-lists)
   and returns a list of output value-lists. *)
type tfun_decl = {
  tfd_name: string;
  tfd_body: string;
}

type program_item =
  | PiLet of let_def
  | PiTable of table_def
  | PiAgg of agg_let_def
  | PiTop of top_let_def

type program = {
  pg_event_decls: event_decl list;
  (* Module-level Python preamble (imports + shared globals) from the --func
     file, exec'd once in the single shared module that hosts every function. *)
  pg_py_preamble: string;
  pg_fun_decls: fun_decl list;
  pg_tfun_decls: tfun_decl list;
  pg_let_defs: let_def list;
  pg_agg_lets: agg_let_def list;
  pg_top_lets: top_let_def list;
  pg_tables: table_def list;
  pg_rules: rule_def list;
  pg_items: program_item list;
  (* Precomputed EDG-ordered sections (recursive?, rule-indices); when non-empty,
     emitted verbatim by [program_to_string] instead of recomputing.  Filled by
     the compiler so the monotonicity-filtering choice is reflected. *)
  pg_sections: (bool * int list) list list;
  (* Same as pg_sections but computed with monotone edges dropped from the CDG. *)
  pg_sections_drop: (bool * int list) list list;
  (* Section-to-section dependency edges (global section indices) from the CDG. *)
  pg_section_edges: (int * int) list;
  pg_section_edges_drop: (int * int) list;
}

(* ─── Complexity of the compiled program ─────────────────────────────────── *)

(* Asymptotic per-time-point cost of the engine in [enfflash/src/engine.rs],
   under the assumption that the trace carries O(1) events per time-stamp.

   The engine evaluates a clause (a disjunction of conjunctions of guard
   patterns, plus a filter) by a left-to-right nested-loop join over the working
   set: starting from a single empty binding, each guard expands every current
   binding by the tuples of the relation it names that agree with the bindings
   so far (see [match_guard_conj_against_events]).  Hence the work of one
   conjunction is the size of its join — the product of the per-guard fan-outs —
   and a clause is the sum over its disjuncts.

   Per-guard fan-out, given the variables already bound to its left:
     - a guard all of whose variables are already bound is a membership lookup → 1
     - a guard introducing a fresh variable enumerates its relation, with size:
         · a declared trace event:        O(1) events per time-stamp        → 1
         · a lagged (Prev) table:          only the previous time-point's
                                            events (O(1))                    → 1
         · a metric table with a bounded
           upper window:                   ~one window of O(1)-per-stamp
                                            events (O(1))                    → 1
         · an unbounded table:             accumulates over the trace        → |t|
         · a filter-let:                   a boolean test                    → 1
         · a guard-let / agg / top:        its defining clause's join size
   Filter table-lookups are treated the same way (a membership check when all
   args are bound, an enumeration otherwise).  Recursion through lets is broken
   by [seen]. *)

let pattern_arg_var = function PAVar x -> [ x ] | PALiteral _ | PAWildcard -> []

let rec term_expr_vars = function
  | TEVar x -> [ x ]
  | TELit _ -> []
  | TEFunCall (_, args) -> List.concat_map args ~f:term_expr_vars

let guard_pattern_vars = function
  | GEqConst (x, _) -> [ x ]
  | GEvent ep -> List.concat_map ep.ep_args ~f:pattern_arg_var

(* A caused/suppressed argument is *value-generating* if it is a function of a
   variable (e.g. [B(x+1)]): unlike a plain projection or constant, it can
   produce values outside the trace's finite active domain.  A recursive section
   containing such a cause is a "bad cycle" — the number of derivable events is
   not bounded by the domain, so the fixpoint gets the crude square bound. *)
let term_generative = function
  | TEFunCall (_, args) -> not (List.is_empty (List.concat_map args ~f:term_expr_vars))
  | TEVar _ | TELit _ -> false

(* A measured cost analysis of clauses, parameterised by the program. *)
type analyzer = {
  (* Cost of evaluating a clause once: the size of its guard join (each guard
     counted once, so variables bound together by one guard stay correlated). *)
  join : clause -> Complexity.t;
  (* Cost of a rule inside a fixpoint section.  The caused relation grows to its
     closure, which the recursion *decorrelates*: each distinct variable of the
     caused event ranges independently over the domain of the relation that
     binds it, so those variables are counted *per variable* (a guard binding k
     of them contributes its size k times).  Guards that bind none of the caused
     variables are pure context and stay per-guard.  Hence
       recursive_rule_cost = (∏ distinct caused var v: dom v) · (∏ context guard) *)
  recursive_rule_cost : rule_def -> Complexity.t;
}

let make_analyzer (pg : program) : analyzer =
  let tbl  = Hashtbl.create (module String) in
  List.iter pg.pg_tables   ~f:(fun td -> Hashtbl.set tbl  ~key:td.td_name  ~data:td);
  let lets = Hashtbl.create (module String) in
  List.iter pg.pg_let_defs ~f:(fun ld -> Hashtbl.set lets ~key:ld.ld_name  ~data:ld);
  let aggs = Hashtbl.create (module String) in
  List.iter pg.pg_agg_lets ~f:(fun ad -> Hashtbl.set aggs ~key:ad.agg_name ~data:ad);
  let tops = Hashtbl.create (module String) in
  List.iter pg.pg_top_lets ~f:(fun td -> Hashtbl.set tops ~key:td.top_name ~data:td);
  let empty = Set.empty (module String) in
  (* size of a table relation under the O(1)-events-per-time-stamp assumption *)
  let table_card td : Complexity.t =
    if td.td_lagged then Complexity.One                       (* previous step only *)
    else match td.td_window with
      | Some (_, Some _) -> Complexity.One                    (* bounded window *)
      | _ -> Complexity.Card td.td_name                       (* accumulates *)
  in
  let rec relation_card seen name : Complexity.t =
    match Hashtbl.find tbl name with
    | Some td -> table_card td
    | None ->
      match Hashtbl.find lets name with
      | Some ld when ld.ld_is_filter -> Complexity.One
      | Some ld -> let_clause_card seen name ld.ld_clause
      | None ->
        match Hashtbl.find aggs name with
        | Some ad -> let_clause_card seen name ad.agg_clause
        | None ->
          match Hashtbl.find tops name with
          | Some td -> let_clause_card seen name td.top_clause
          | None -> Complexity.One   (* declared / builtin trace event: O(1) *)
  and let_clause_card seen name cl : Complexity.t =
    if Set.mem seen name then Complexity.Card name             (* cycle guard *)
    else clause_measure (Set.add seen name) (fun fresh -> not (List.is_empty fresh)) cl
  (* [clause_measure seen count cl] is the size of [cl]'s join, but a guard's
     cardinality is multiplied in only when [count] holds of the fresh variables
     it introduces.  With [count = (fresh ≠ ∅)] this is the full join size; with
     [count = (fresh ∩ output ≠ ∅)] it is the join projected onto [output] (an
     upper bound on the number of distinct output tuples, since projection never
     increases cardinality and a guard binding several output variables is
     counted once). *)
  and clause_measure seen count (cl : clause) : Complexity.t =
    match cl.cl_patterns with
    | [] -> filter_measure seen count empty cl.cl_filter
    | disjuncts ->
      Complexity.sum (List.map disjuncts ~f:(fun conj ->
          let jcost, bound = conj_measure seen count conj in
          Complexity.prod [ jcost; filter_measure seen count bound cl.cl_filter ]))
  and conj_measure seen count guards : Complexity.t * Set.M(String).t =
    let factors, bound =
      List.fold guards ~init:([], empty) ~f:(fun (factors, bound) g ->
          let gvars = guard_pattern_vars g in
          let fresh = List.filter gvars ~f:(fun v -> not (Set.mem bound v)) in
          let bound' = List.fold gvars ~init:bound ~f:Set.add in
          let card =
            if not (count fresh) then Complexity.One
            else match g with
              | GEqConst _ -> Complexity.One
              | GEvent ep -> relation_card seen ep.ep_name
          in
          (card :: factors, bound'))
    in
    (Complexity.prod factors, bound)
  and filter_measure seen count bound (f : filter_expr) : Complexity.t =
    match f with
    | FBoolLit _ | FCompare _ -> Complexity.One
    | FTableLookup (name, args) ->
      let fresh =
        List.filter (List.concat_map args ~f:term_expr_vars)
          ~f:(fun v -> not (Set.mem bound v))
      in
      if count fresh then relation_card seen name else Complexity.One
    | FAnd (a, b) -> Complexity.prod [ filter_measure seen count bound a; filter_measure seen count bound b ]
    | FOr  (a, b) -> Complexity.sum  [ filter_measure seen count bound a; filter_measure seen count bound b ]
    | FNot a -> filter_measure seen count bound a
  in
  let any_fresh fresh = not (List.is_empty fresh) in
  let join cl = Complexity.simplify (clause_measure empty any_fresh cl) in
  let is_relation name =
    Hashtbl.mem tbl name || Hashtbl.mem lets name
    || Hashtbl.mem aggs name || Hashtbl.mem tops name
  in
  (* Synthetic existential / effect events (`Sup_…`, `Cau_…`) introduced by the
     compiler are projections of the underlying tables, not genuine O(1) trace
     events, so they must not pin a variable's domain. *)
  let is_synthetic name =
    String.is_prefix name ~prefix:"Sup_" || String.is_prefix name ~prefix:"Cau_"
  in
  (* Cost of one rule under a fixpoint.  The caused relation grows to its closure,
     which the recursion decorrelates: it is bounded by the product, over the
     *distinct* variables of the caused event, of each variable's domain, times
     the per-guard cost of context guards (those binding no caused variable).
     A variable's domain [dom v] is O(1) if some real trace event or equality
     constant pins it; otherwise it is the size of a table/let that binds it
     (looking through synthetic existential events). *)
  let recursive_rule_cost (r : rule_def) =
    let output = Set.of_list (module String) (List.concat_map r.rd_params ~f:term_expr_vars) in
    let conj_cost guards =
      let pinned = Hashtbl.create (module String) in   (* var → bound to O(1) *)
      let tcard  = Hashtbl.create (module String) in   (* var → a binding table's size *)
      let aux = ref [] in                              (* context-guard factors *)
      List.iter guards ~f:(fun g ->
          let gvars = guard_pattern_vars g in
          let out_vars = List.filter gvars ~f:(Set.mem output) in
          match g with
          | GEqConst (v, _) -> if Set.mem output v then Hashtbl.set pinned ~key:v ~data:()
          | GEvent ep ->
            let name = ep.ep_name in
            if is_relation name then begin
              let c = relation_card empty name in
              List.iter out_vars ~f:(fun v ->
                  if not (Hashtbl.mem tcard v) then Hashtbl.set tcard ~key:v ~data:c);
              if List.is_empty out_vars && not (List.is_empty gvars) then aux := c :: !aux
            end
            else if is_synthetic name then ()             (* transparent: look through *)
            else List.iter out_vars ~f:(fun v -> Hashtbl.set pinned ~key:v ~data:())  (* real event pins *)
      );
      let dom v =
        if Hashtbl.mem pinned v then Complexity.One
        else match Hashtbl.find tcard v with Some c -> c | None -> Complexity.One
      in
      Complexity.prod (List.map (Set.to_list output) ~f:dom @ !aux)
    in
    let cost =
      match r.rd_trigger.cl_patterns with
      | [] -> Complexity.One
      | disjuncts -> Complexity.sum (List.map disjuncts ~f:conj_cost)
    in
    Complexity.simplify cost
  in
  { join; recursive_rule_cost }

let clause_complexity (pg : program) (cl : clause) : Complexity.t =
  (make_analyzer pg).join cl

(* Per-time-point cost of the whole program: maintaining every table (matching
   its add/remove clauses) plus evaluating the rule sections (in EDG/CDG
   dependency order).

   A `once` section is a single pass: the sum of its rules' trigger-join costs.

   A `fixpoint` section iterates until its derived relations reach closure.  The
   work is dominated by the size that closure grows to, which the recursion
   decorrelates — so it is [Σ_r recursive_rule_cost r] rather than the per-pass
   join times an iteration count.  For example
       ⧫C(x) ⟹ B(x)                         costs |Once0|     (one output var)
       ⧫A(x₁..xₙ) ⟹ A(xₙ,x₁..xₙ₋₁)          costs |OnceA|ⁿ    (n output vars).
   When a caused argument is value-generating (a "bad cycle" in the EDG — e.g.
   [B(x+1)] feeding back into the cycle), the closure is not bounded by the
   active domain, and we fall back to the crude [per_pass²]. *)
let program_complexity (pg : program) : Complexity.t =
  let a = make_analyzer pg in
  let table_cost =
    List.map pg.pg_tables ~f:(fun td ->
        Complexity.sum
          (a.join td.td_add_clause
           :: (match td.td_remove_clause with Some c -> [ a.join c ] | None -> [])))
  in
  let rules = Array.of_list pg.pg_rules in
  let bad_cycle idxs =
    List.exists idxs ~f:(fun i -> List.exists rules.(i).rd_params ~f:term_generative)
  in
  let fixpoint_cost idxs =
    if bad_cycle idxs then
      let per_pass = Complexity.sum (List.map idxs ~f:(fun i -> a.join rules.(i).rd_trigger)) in
      Complexity.pow per_pass 2
    else Complexity.sum (List.map idxs ~f:(fun i -> a.recursive_rule_cost rules.(i)))
  in
  let section_cost (recursive, idxs) =
    if recursive then fixpoint_cost idxs
    else Complexity.sum (List.map idxs ~f:(fun i -> a.join rules.(i).rd_trigger))
  in
  let sections = List.concat pg.pg_sections in
  let rule_cost =
    if List.is_empty sections && not (Array.is_empty rules) then
      (* no recorded sections: assume one global fixpoint over all rules *)
      [ fixpoint_cost (List.init (Array.length rules) ~f:Fn.id) ]
    else List.map sections ~f:section_cost
  in
  Complexity.sum (table_cost @ rule_cost)

let program_complexity_to_string (pg : program) : string =
  Complexity.to_string (program_complexity pg)

(* The relations whose cardinality appears in the program's per-time-point
   complexity — i.e. the unbounded tables/lets the engine actually enumerates
   (scans) at run time.  A table that only ever serves as a membership filter
   contributes [Complexity.One] and so is absent here. *)
let scanned_relation_names (pg : program) : Set.M(String).t =
  Set.of_list (module String) (Complexity.cards (program_complexity pg))

(* ─── Serialization to .ef text format ───────────────────────────────────── *)

let ef_ty_to_string = function
  | EfInt   -> "int"
  | EfStr   -> "str"
  | EfFloat -> "float"

let ef_value_to_string = function
  | EfVInt i   -> Int.to_string i
  | EfVStr s   -> Printf.sprintf "\"%s\"" s
  | EfVFloat f ->
    (* The Rust engine's float-literal grammar requires a decimal point
       (`<digits>.<digits>`).  `%g` drops it for integral values
       (10000.0 → "10000"), which would then be parsed as an int and clash
       with the float column type, so append ".0" when no point/exponent is
       present. *)
    let s = Printf.sprintf "%.12g" f in
    if String.contains s '.' || String.contains s 'e' || String.contains s 'E'
    then s
    else s ^ ".0"
  | EfVBool b  -> if b then "true" else "false"

let rec term_expr_to_string = function
  | TEVar x -> x
  | TELit v -> ef_value_to_string v
  | TEFunCall (f, args) ->
    Printf.sprintf "%s(%s)" f
      (String.concat ~sep:", " (List.map ~f:term_expr_to_string args))

let pattern_arg_to_string = function
  | PAVar x     -> x
  | PALiteral v -> ef_value_to_string v
  | PAWildcard  -> "_"

let event_pattern_to_string ep =
  Printf.sprintf "%s(%s)" ep.ep_name
    (String.concat ~sep:", " (List.map ~f:pattern_arg_to_string ep.ep_args))

let guard_pattern_to_string = function
  | GEvent ep -> event_pattern_to_string ep
  | GEqConst (x, v) -> Printf.sprintf "%s == %s" x (ef_value_to_string v)

let guard_pattern_list_to_string eps =
  String.concat ~sep:" & " (List.map ~f:guard_pattern_to_string eps)

let cmp_op_to_string = function
  | CmpEq  -> "=="
  | CmpNeq -> "!="
  | CmpLt  -> "<"
  | CmpLe  -> "<="
  | CmpGt  -> ">"
  | CmpGe  -> ">="

let rec filter_expr_to_string = function
  | FBoolLit true  -> "true"
  | FBoolLit false -> "false"
  | FTableLookup (name, args) ->
    Printf.sprintf "%s(%s)" name
      (String.concat ~sep:", " (List.map ~f:term_expr_to_string args))
  | FCompare (lhs, op, rhs) ->
    Printf.sprintf "%s %s %s"
      (term_expr_to_string lhs) (cmp_op_to_string op) (term_expr_to_string rhs)
  | FAnd (l, r) ->
    Printf.sprintf "%s & %s"
      (filter_expr_to_string_parens l)
      (filter_expr_to_string_parens r)
  | FOr (l, r) ->
    Printf.sprintf "(%s | %s)"
      (filter_expr_to_string l)
      (filter_expr_to_string r)
  | FNot f ->
    Printf.sprintf "!%s" (filter_expr_to_string_atom f)

and filter_expr_to_string_parens f =
  match f with
  | FOr _ -> Printf.sprintf "(%s)" (filter_expr_to_string f)
  | _     -> filter_expr_to_string f

and filter_expr_to_string_atom f =
  match f with
  | FBoolLit _ | FTableLookup _ -> filter_expr_to_string f
  | _ -> Printf.sprintf "(%s)" (filter_expr_to_string f)

let clause_to_string ?(indent="    ") cl =
  let pats_str = String.concat ~sep:(Printf.sprintf "\n%s or " indent)
      (List.map ~f:guard_pattern_list_to_string cl.cl_patterns) in
  match cl.cl_filter with
  | FBoolLit true when not (List.is_empty cl.cl_patterns) ->
    Printf.sprintf "%s%s" indent pats_str
  | _ when List.is_empty cl.cl_patterns ->
    (* No event patterns: emit "if <filter>" so the parser sees
       a filter-only clause body. *)
    Printf.sprintf "%sif %s" indent (filter_expr_to_string cl.cl_filter)
  | _ ->
    Printf.sprintf "%s%s\n%s  if %s" indent pats_str indent
      (filter_expr_to_string cl.cl_filter)

let label_prefix = function
  | None     -> ""
  | Some lbl ->
    let needs_brackets = String.exists lbl ~f:(fun c ->
      not (Char.is_alphanum c || Char.equal c '_' || Char.equal c '.')) in
    if needs_brackets then Printf.sprintf "@<%s> " lbl
    else Printf.sprintf "@%s " lbl

let typed_params_to_string params =
  String.concat ~sep:", "
    (List.map params ~f:(fun (n, t) ->
         Printf.sprintf "%s:%s" n (ef_ty_to_string t)))

let event_decl_to_string ed =
  Printf.sprintf "event %s(%s);" ed.ed_name
    (String.concat ~sep:", " (List.map ~f:ef_ty_to_string ed.ed_param_types))

let fun_decl_to_string fd =
  let params =
    List.map2_exn fd.fd_param_names fd.fd_param_types
      ~f:(fun n t -> Printf.sprintf "%s:%s" n (ef_ty_to_string t)) in
  let body_lines = String.split_lines fd.fd_body in
  let indented_body = String.concat ~sep:"\n"
      (List.map body_lines ~f:(fun l -> "    " ^ l)) in
  Printf.sprintf "fun %s(%s) : %s {\n%s\n}"
    fd.fd_name
    (String.concat ~sep:", " params)
    (ef_ty_to_string fd.fd_ret_type)
    indented_body

let let_def_to_string ld =
  let keyword = if ld.ld_is_filter then "filter let" else "let" in
  Printf.sprintf "%s%s %s(%s) := {\n%s\n}"
    (label_prefix ld.ld_label)
    keyword
    ld.ld_name
    (typed_params_to_string ld.ld_params)
    (clause_to_string ~indent:"  " ld.ld_clause)

let table_def_to_string td =
  let lagged_str = if td.td_lagged then "lagged " else "" in
  (* Emit a metric window only when non-trivial, so [0, ∞) tables print exactly
     as before.  Unbounded upper bound is written as `*`. *)
  let window_str = match td.td_window with
    | None | Some (0, None) -> ""
    | Some (a, b_opt) ->
      let b_str = match b_opt with Some b -> Int.to_string b | None -> "*" in
      Printf.sprintf " [window %d %s]" a b_str in
  let add_str = Printf.sprintf "  add {\n%s\n  }"
      (clause_to_string ~indent:"    " td.td_add_clause) in
  let remove_str = match td.td_remove_clause with
    | None    -> ""
    | Some cl -> Printf.sprintf "\n  remove {\n%s\n  }"
                   (clause_to_string ~indent:"    " cl) in
  Printf.sprintf "%s%stable %s(%s)%s :=\n%s%s;"
    (label_prefix td.td_label)
    lagged_str
    td.td_name
    (typed_params_to_string td.td_columns)
    window_str
    add_str
    remove_str

let agg_op_to_string = function
  | AggSum -> "SUM" | AggAvg -> "AVG" | AggMed -> "MED" | AggCnt -> "CNT"
  | AggMin -> "MIN" | AggMax -> "MAX" | AggStd -> "STD"

let agg_let_def_to_string ad =
  let incr = match ad.agg_incremental with
    | None -> "" | Some t -> Printf.sprintf " incremental %s" t in
  Printf.sprintf "%sagg let %s(%s) := %s(%s) group_by [%s]%s over {\n%s\n};"
    (label_prefix ad.agg_label)
    ad.agg_name
    (typed_params_to_string ad.agg_columns)
    (agg_op_to_string ad.agg_op)
    (term_expr_to_string ad.agg_term)
    (String.concat ~sep:", " ad.agg_groups)
    incr
    (clause_to_string ~indent:"  " ad.agg_clause)

let top_let_def_to_string td =
  Printf.sprintf "%stableop let %s(%s) := %s(%s) group_by [%s] over {\n%s\n};"
    (label_prefix td.top_label)
    td.top_name
    (typed_params_to_string td.top_columns)
    td.top_fn
    (String.concat ~sep:", " (List.map ~f:term_expr_to_string td.top_args))
    (String.concat ~sep:", " td.top_groups)
    (clause_to_string ~indent:"  " td.top_clause)

let tfun_decl_to_string t =
  let body_lines = String.split_lines t.tfd_body in
  let indented_body = String.concat ~sep:"\n"
      (List.map body_lines ~f:(fun l -> "    " ^ l)) in
  Printf.sprintf "tfun %s {\n%s\n}" t.tfd_name indented_body

let rule_def_to_string rd =
  let action_str = match rd.rd_action with
    | RCause    -> "+"
    | RSuppress -> "-" in
  let delay_str = match rd.rd_delay with
    | None   -> ""
    | Some d -> Printf.sprintf " [delay %d]" d in
  let next_str = match rd.rd_tp_offset with
    | None   -> ""
    | Some n -> Printf.sprintf " [next %d]" n in
  let trigger_str = clause_to_string ~indent:"    " rd.rd_trigger in
  let validate_str = match rd.rd_validate with
    | None   -> ""
    | Some f -> Printf.sprintf "\n  validate {\n    %s\n  }"
                  (filter_expr_to_string f) in
  Printf.sprintf "%srule %s%s(%s)%s%s :=\n  trigger {\n%s\n  }%s;"
    (label_prefix rd.rd_label)
    action_str
    rd.rd_event
    (String.concat ~sep:", " (List.map ~f:term_expr_to_string rd.rd_params))
    delay_str
    next_str
    trigger_str
    validate_str

(* ─── Single-use let compression ─────────────────────────────────────────────
   Post-processing pass that folds alias chains left over from normalization,
   e.g.
     let Exists526(e_17) := { Exists524(e_17, rs_20) if !Exists525(e_17, rs_20) }
     let Exists527()     := { Exists526(e_17) }
   into a single
     let Exists527()     := { Exists524(e_17, rs_20) if !Exists525(e_17, rs_20) }.

   We target *pure aliases*: a let B whose clause is exactly one guard
   `A(x…)` (no filter), where A is another let referenced nowhere else.  Since
   B ≡ A with its parameters renamed to B's call variables, B's clause can be
   replaced by A's (renamed) clause and A dropped.  This is purely syntactic and
   runs after all enforceability analysis, so guardedness is unaffected. *)

let rename_var m v = match Map.find m v with Some v' -> v' | None -> v

let rec rename_term m = function
  | TEVar v            -> TEVar (rename_var m v)
  | TELit l            -> TELit l
  | TEFunCall (f, args) -> TEFunCall (f, List.map ~f:(rename_term m) args)

let rename_pattern_arg m = function
  | PAVar v -> PAVar (rename_var m v)
  | other   -> other

let rename_guard m = function
  | GEvent { ep_name; ep_args } ->
    GEvent { ep_name; ep_args = List.map ~f:(rename_pattern_arg m) ep_args }
  | GEqConst (v, c) -> GEqConst (rename_var m v, c)

let rec rename_filter m = function
  | FBoolLit b            -> FBoolLit b
  | FTableLookup (n, args) -> FTableLookup (n, List.map ~f:(rename_term m) args)
  | FCompare (a, op, b)   -> FCompare (rename_term m a, op, rename_term m b)
  | FAnd (a, b)           -> FAnd (rename_filter m a, rename_filter m b)
  | FOr (a, b)            -> FOr (rename_filter m a, rename_filter m b)
  | FNot a               -> FNot (rename_filter m a)

let rename_clause m (cl : clause) : clause =
  { cl_patterns = List.map ~f:(List.map ~f:(rename_guard m)) cl.cl_patterns;
    cl_filter   = rename_filter m cl.cl_filter }

(* Count, per name, how many times each let/event is referenced across every
   clause and validate filter in the program. *)
let count_let_refs (prog : program) : (string, int) Hashtbl.t =
  let tbl = Hashtbl.create (module String) in
  let rec cf = function
    | FTableLookup (n, _)  -> Hashtbl.incr tbl n
    | FBoolLit _ | FCompare _ -> ()
    | FAnd (a, b) | FOr (a, b) -> cf a; cf b
    | FNot a -> cf a in
  let cg = function GEvent { ep_name; _ } -> Hashtbl.incr tbl ep_name | GEqConst _ -> () in
  let cc (cl : clause) =
    List.iter cl.cl_patterns ~f:(List.iter ~f:cg); cf cl.cl_filter in
  List.iter prog.pg_let_defs ~f:(fun ld -> cc ld.ld_clause);
  List.iter prog.pg_agg_lets ~f:(fun ad -> cc ad.agg_clause);
  List.iter prog.pg_top_lets ~f:(fun td -> cc td.top_clause);
  List.iter prog.pg_tables ~f:(fun td ->
      cc td.td_add_clause; Option.iter td.td_remove_clause ~f:cc);
  List.iter prog.pg_rules ~f:(fun rd ->
      cc rd.rd_trigger; Option.iter rd.rd_validate ~f:cf);
  tbl

let conj_filters = List.fold ~init:(FBoolLit true)
    ~f:(fun acc f -> match acc, f with
        | FBoolLit true, _ -> f
        | _, FBoolLit true -> acc
        | _ -> FAnd (acc, f))

(* Variables bound (enumerated) by the guard patterns of a clause. *)
let guard_bound_vars (cl : clause) : (string, String.comparator_witness) Set.t =
  List.fold cl.cl_patterns ~init:(Set.empty (module String)) ~f:(fun acc disj ->
      List.fold disj ~init:acc ~f:(fun acc -> function
          | GEvent { ep_args; _ } ->
            List.fold ep_args ~init:acc ~f:(fun acc -> function
                | PAVar v -> Set.add acc v | _ -> acc)
          | GEqConst (v, _) -> Set.add acc v))

(* Splice let [a] into a host clause: replace each guard `a(x…)` by a's own
   guards (parameters renamed to the call variables) and conjoin a's filter.
   Only valid when a's parameters are themselves guard-bound, so binding is
   preserved. *)
let inline_in_clause (a : let_def) (cl : clause) : clause =
  let a_guards = match a.ld_clause.cl_patterns with [] -> [] | g :: _ -> g in
  let extra_filters = ref [] in
  let cl_patterns = List.map cl.cl_patterns ~f:(fun disj ->
      List.concat_map disj ~f:(function
          | GEvent { ep_name; ep_args } when String.equal ep_name a.ld_name ->
            let argvars = List.map ep_args ~f:(function PAVar v -> v | _ -> "_") in
            let m = Map.of_alist_exn (module String)
                (List.zip_exn (List.map ~f:fst a.ld_params) argvars) in
            extra_filters := rename_filter m a.ld_clause.cl_filter :: !extra_filters;
            List.map a_guards ~f:(rename_guard m)
          | g -> [g])) in
  { cl_patterns;
    cl_filter = conj_filters (cl.cl_filter :: List.rev !extra_filters) }

(* Fold a stateless derived let A into every site that references it, then drop
   A.  Restricted to the guard-preserving case so the backend's guardedness
   requirement is never violated:
     - A has a single guard-disjunct and is not self-recursive;
     - every one of A's parameters is bound by A's own guard patterns;
     - A is referenced only in guard positions (never inside a filter, where it
       would become an unenumerable free variable);
     - each host disjunct that mentions A is the host's only disjunct and passes
       plain variables.
   Temporal predicates are realised as tables, not lets, so every
   [pg_let_defs] entry is otherwise safe to inline. *)
let compress_alias_lets (prog : program) : program =
  let max_uses = 4 in
  (* True when [a] never appears inside a filter expression anywhere. *)
  let no_filter_refs (a : let_def) (prog : program) : bool =
    let rec ff = function
      | FTableLookup (n, _) -> not (String.equal n a.ld_name)
      | FBoolLit _ | FCompare _ -> true
      | FAnd (x, y) | FOr (x, y) -> ff x && ff y
      | FNot x -> ff x in
    let cc (cl : clause) = ff cl.cl_filter in
    List.for_all prog.pg_let_defs ~f:(fun ld -> cc ld.ld_clause)
    && List.for_all prog.pg_agg_lets ~f:(fun ad -> cc ad.agg_clause)
    && List.for_all prog.pg_top_lets ~f:(fun td -> cc td.top_clause)
    && List.for_all prog.pg_tables ~f:(fun td ->
        cc td.td_add_clause && Option.for_all td.td_remove_clause ~f:cc)
    && List.for_all prog.pg_rules ~f:(fun rd ->
        cc rd.rd_trigger && Option.for_all rd.rd_validate ~f:ff) in
  let guard_sites_safe (a : let_def) (prog : program) : bool =
    let clause_ok (cl : clause) =
      let refs_in_guards =
        List.exists cl.cl_patterns ~f:(List.exists ~f:(function
            | GEvent { ep_name; _ } -> String.equal ep_name a.ld_name | _ -> false)) in
      (not refs_in_guards)
      || ((match cl.cl_patterns with [] | [_] -> true | _ -> false)
          && List.for_all cl.cl_patterns ~f:(List.for_all ~f:(function
              | GEvent { ep_name; ep_args } when String.equal ep_name a.ld_name ->
                Int.equal (List.length ep_args) (List.length a.ld_params)
                && List.for_all ep_args ~f:(function PAVar _ -> true | _ -> false)
              | _ -> true))) in
    List.for_all prog.pg_let_defs ~f:(fun ld ->
        String.equal ld.ld_name a.ld_name || clause_ok ld.ld_clause)
    && List.for_all prog.pg_agg_lets ~f:(fun ad -> clause_ok ad.agg_clause)
    && List.for_all prog.pg_top_lets ~f:(fun td -> clause_ok td.top_clause)
    && List.for_all prog.pg_tables ~f:(fun td ->
        clause_ok td.td_add_clause && Option.for_all td.td_remove_clause ~f:clause_ok)
    && List.for_all prog.pg_rules ~f:(fun rd -> clause_ok rd.rd_trigger) in
  let self_recursive (a : let_def) =
    Hashtbl.mem (count_let_refs
        { prog with pg_let_defs = [a]; pg_agg_lets = []; pg_top_lets = [];
                    pg_tables = []; pg_rules = []; pg_items = [] })
      a.ld_name in
  let single_disjunct (a : let_def) =
    match a.ld_clause.cl_patterns with [] | [_] -> true | _ -> false in
  let params_guard_bound (a : let_def) =
    let bound = guard_bound_vars a.ld_clause in
    List.for_all a.ld_params ~f:(fun (p, _) -> Set.mem bound p) in
  let rec loop prog =
    let refs = count_let_refs prog in
    let uses a = Option.value (Hashtbl.find refs a) ~default:0 in
    let candidate = List.find prog.pg_let_defs ~f:(fun a ->
        uses a.ld_name >= 1 && uses a.ld_name <= max_uses
        && single_disjunct a
        && not (self_recursive a)
        && params_guard_bound a
        && no_filter_refs a prog
        && guard_sites_safe a prog) in
    match candidate with
    | None -> prog
    | Some a ->
      let upd cl = inline_in_clause a cl in
      let pg_let_defs = List.filter_map prog.pg_let_defs ~f:(fun ld ->
          if String.equal ld.ld_name a.ld_name then None
          else Some { ld with ld_clause = upd ld.ld_clause }) in
      let pg_agg_lets = List.map prog.pg_agg_lets ~f:(fun ad ->
          { ad with agg_clause = upd ad.agg_clause }) in
      let pg_top_lets = List.map prog.pg_top_lets ~f:(fun td ->
          { td with top_clause = upd td.top_clause }) in
      let pg_tables = List.map prog.pg_tables ~f:(fun td ->
          { td with td_add_clause = upd td.td_add_clause;
                    td_remove_clause = Option.map td.td_remove_clause ~f:upd }) in
      let pg_rules = List.map prog.pg_rules ~f:(fun rd ->
          { rd with rd_trigger = upd rd.rd_trigger }) in
      let pg_items = List.filter_map prog.pg_items ~f:(function
          | PiLet ld when String.equal ld.ld_name a.ld_name -> None
          | PiLet ld -> Some (PiLet { ld with ld_clause = upd ld.ld_clause })
          | PiTable td -> Some (PiTable
              { td with td_add_clause = upd td.td_add_clause;
                        td_remove_clause = Option.map td.td_remove_clause ~f:upd })
          | PiAgg ad -> Some (PiAgg { ad with agg_clause = upd ad.agg_clause })
          | PiTop td -> Some (PiTop { td with top_clause = upd td.top_clause })) in
      loop { prog with pg_let_defs; pg_agg_lets; pg_top_lets; pg_tables; pg_rules; pg_items }
  in
  loop prog

(* ─── Rule Dependency Graph (RDG) + EDG-ordered evaluation sections ─────────── *)

(* The Rule Dependency Graph: nodes are rules, edge i→j when the event produced
   by rule i can appear in rule j's trigger (directly, or through a let/table the
   trigger references).  Its SCCs are the evaluation sections. *)
type rdg = {
  rdg_n         : int;
  rdg_graph     : unit Graph_util.Graph.t;
  rdg_self      : bool array;       (* self-loop per rule *)
  rdg_labels    : string array;     (* "+Event" / "-Event" per rule *)
  rdg_events    : string array;     (* produced event per rule *)
  rdg_scc_count : int;
  rdg_scc_of    : int array;
}

let build_rdg ?(drop_monotone = false) (pg : program) : rdg =
  let module G = Graph_util.Graph in
  let rec filter_names f acc = match f with
    | FTableLookup (n, _) -> Set.add acc n
    | FAnd (a, b) | FOr (a, b) -> filter_names b (filter_names a acc)
    | FNot a -> filter_names a acc
    | FBoolLit _ | FCompare _ -> acc in
  let clause_names (c : clause) =
    let acc =
      List.fold c.cl_patterns ~init:(Set.empty (module String)) ~f:(fun acc conj ->
          List.fold conj ~init:acc ~f:(fun acc g ->
              match g with GEvent ep -> Set.add acc ep.ep_name | GEqConst _ -> acc)) in
    filter_names c.cl_filter acc in
  let ref_map =
    let m = List.fold pg.pg_let_defs ~init:(Map.empty (module String))
        ~f:(fun m ld -> Map.set m ~key:ld.ld_name ~data:(clause_names ld.ld_clause)) in
    let m = List.fold pg.pg_agg_lets ~init:m
        ~f:(fun m ad -> Map.set m ~key:ad.agg_name ~data:(clause_names ad.agg_clause)) in
    let m = List.fold pg.pg_top_lets ~init:m
        ~f:(fun m td -> Map.set m ~key:td.top_name ~data:(clause_names td.top_clause)) in
    List.fold pg.pg_tables ~init:m ~f:(fun m td ->
        let s = clause_names td.td_add_clause in
        let s = match td.td_remove_clause with
          | Some c -> Set.union s (clause_names c) | None -> s in
        Map.set m ~key:td.td_name ~data:s) in
  let rec expand name seen =
    match Map.find ref_map name with
    | None -> seen
    | Some refs -> Set.fold refs ~init:seen ~f:(fun seen r ->
        if Set.mem seen r then seen else expand r (Set.add seen r)) in
  let rules = Array.of_list pg.pg_rules in
  let n = Array.length rules in
  let trig = Array.map rules ~f:(fun r ->
      let direct = clause_names r.rd_trigger in
      Set.fold direct ~init:direct ~f:(fun acc nm ->
          Set.union acc (expand nm (Set.empty (module String))))) in
  let producers = Array.foldi rules ~init:(Map.empty (module String))
      ~f:(fun i m r -> Map.add_multi m ~key:r.rd_event ~data:i) in
  (* When [drop_monotone], drop a dependency edge i→j whose effect event is
     monotone-harmless for the consumer's trigger (CDG*-style): if rule j's
     trigger is *monotone* in the produced event (it occurs only positively) a
     cause edge is droppable; if *anti-monotone* (only negatively) a suppress
     edge is droppable.  Computed directly on the compiled triggers so it also
     covers the synthetic Cau_/Sup_ chains that form the big fixpoint sections.
     This is sound (monotone deps don't need a fixpoint) but less transparent. *)
  let trigger_polarity (c : clause) =
    let pos = ref (Set.empty (module String))
    and neg = ref (Set.empty (module String)) in
    List.iter c.cl_patterns ~f:(fun conj ->
        List.iter conj ~f:(function
            | GEvent ep -> pos := Set.add !pos ep.ep_name
            | GEqConst _ -> ()));
    let rec walk pol = function
      | FTableLookup (p, _) -> if pol then pos := Set.add !pos p else neg := Set.add !neg p
      | FAnd (a, b) | FOr (a, b) -> walk pol a; walk pol b
      | FNot a -> walk (not pol) a
      | FBoolLit _ | FCompare _ -> () in
    walk true c.cl_filter;
    (* purely-monotone = positive only; purely-anti = negative only *)
    (Set.diff !pos !neg, Set.diff !neg !pos) in
  let pol = Array.map rules ~f:(fun r -> trigger_polarity r.rd_trigger) in
  let droppable ~producer ~consumer ~event =
    drop_monotone
    && (let monp, antip = pol.(consumer) in
        match rules.(producer).rd_action with
        | RCause    -> Set.mem monp  event
        | RSuppress -> Set.mem antip event) in
  let g = ref (G.empty n) and self_loop = Array.create ~len:n false in
  for j = 0 to n - 1 do
    Set.iter trig.(j) ~f:(fun nm ->
        match Map.find producers nm with
        | None -> ()
        | Some ps -> List.iter ps ~f:(fun i ->
            if not (droppable ~producer:i ~consumer:j ~event:nm) then
              (if i = j then self_loop.(j) <- true
               else g := G.add_edge !g ~src:i ~lbl:() ~dst:j)))
  done;
  let scc_count, scc_of = Graph_util.tarjan !g in
  let labels = Array.map rules ~f:(fun r ->
      (match r.rd_action with RCause -> "+" | RSuppress -> "-") ^ r.rd_event) in
  let events = Array.map rules ~f:(fun r -> r.rd_event) in
  { rdg_n = n; rdg_graph = !g; rdg_self = self_loop; rdg_labels = labels;
    rdg_events = events; rdg_scc_count = scc_count; rdg_scc_of = scc_of }

(* ─── RDG visualisations ───────────────────────────────────────────────────── *)

let rdg_esc s = String.substr_replace_all s ~pattern:"\"" ~with_:"'"
let rdg_is_helper name =
  String.is_prefix name ~prefix:"Sup_" || String.is_prefix name ~prefix:"Cau_"
  || List.exists ["Once"; "Exists"; "Since"; "Prev"; "Scope"; "Label"]
       ~f:(fun p -> String.is_prefix name ~prefix:p)

(* ─── Wave/section execution graph ────────────────────────────────────────── *)

(* Generates a DOT graph showing the wave decomposition.
   Each wave is a cluster; sections within a wave are nodes coloured by kind:
     pink  = fixpoint (iterated to local fixpoint)
     blue  = once (sequential)
   Edges are the CDG section-level dependencies stored in pg_section_edges. *)
let waves_dot ?(drop_monotone = false) (pg : program) : string =
  let waves    = if drop_monotone then pg.pg_sections_drop else pg.pg_sections in
  let sec_edges = if drop_monotone then pg.pg_section_edges_drop else pg.pg_section_edges in
  if List.is_empty waves then "digraph waves { label=\"(no sections)\"; }\n"
  else begin
    let rules  = Array.of_list pg.pg_rules in
    let n_rules = Array.length rules in
    let rep_event idxs =
      let evs  = List.filter_map idxs ~f:(fun i ->
          if i < n_rules then Some rules.(i).rd_event else None) in
      let real = List.filter evs ~f:(fun e -> not (rdg_is_helper e)) in
      let pick = if List.is_empty real then evs else real in
      Option.value (List.min_elt pick
            ~compare:(fun a b -> Int.compare (String.length a) (String.length b)))
        ~default:"?" in
    let buf = Buffer.create 2048 in
    Buffer.add_string buf
      "digraph waves {\n  rankdir=TB;\n  compound=true;\n  \
       node [shape=box, style=\"filled,rounded\", fontsize=10];\n  \
       edge [color=\"#555555\", arrowsize=0.6];\n\n";
    Buffer.add_string buf
      "  subgraph cluster_legend {\n    label=\"Legend\"; rank=sink;\n    \
       style=dashed; fontsize=9; color=\"#aaaaaa\"; bgcolor=\"white\";\n    \
       lfix  [label=\"fixpoint (sequential)\", fillcolor=\"#ff9999\"];\n    \
       lonce [label=\"once (sequential)\",     fillcolor=\"#cfe8ff\"];\n    \
       lfix -> lonce [style=invis];\n  }\n\n";
    let cur_gi = ref 0 in
    List.iteri waves ~f:(fun wi wave ->
        Buffer.add_string buf
          (Printf.sprintf "  subgraph cluster_w%d {\n    label=%S;\n    \
            style=rounded; color=\"#999999\"; bgcolor=\"#f8f8ff\";\n"
             wi (Printf.sprintf "Wave %d" wi));
        List.iter wave ~f:(fun (recursive, idxs) ->
            let g    = !cur_gi in Int.incr cur_gi;
            let color = if recursive then "#ff9999" else "#cfe8ff" in
            let ev   = rdg_esc (rep_event idxs) in
            let kind = if recursive then "fixpoint" else "once" in
            let nr   = List.length idxs in
            let lbl  = Printf.sprintf "%s\\n%s  (%d rule%s)"
                ev kind nr (if nr = 1 then "" else "s") in
            Buffer.add_string buf
              (Printf.sprintf "    s%d [label=\"%s\", fillcolor=\"%s\"];\n"
                 g lbl color));
        Buffer.add_string buf "  }\n");
    List.iter sec_edges ~f:(fun (a, b) ->
        Buffer.add_string buf (Printf.sprintf "  s%d -> s%d;\n" a b));
    Buffer.add_string buf "}\n";
    Buffer.contents buf
  end

(* Returns named DOT contents: the full RDG (rules, SCC-clustered), the focused
   condensation (one node per SCC = one evaluation section, the section
   dependency DAG), and one expanded graph per recursive (fixpoint) section. *)
let rdg_export ?(drop_monotone = false) (pg : program) : (string * string) list =
  let module G = Graph_util.Graph in
  let r = build_rdg ~drop_monotone pg in
  let sc = r.rdg_scc_count and scc_of = r.rdg_scc_of and n = r.rdg_n in
  if n = 0 then [] else begin
    let sizes = Array.create ~len:sc 0 in
    Array.iter scc_of ~f:(fun s -> sizes.(s) <- sizes.(s) + 1);
    let recursive = Array.create ~len:sc false in
    Array.iteri scc_of ~f:(fun i s -> if r.rdg_self.(i) then recursive.(s) <- true);
    for s = 0 to sc - 1 do if sizes.(s) > 1 then recursive.(s) <- true done;
    let members_ev = Array.create ~len:sc [] in
    for i = n - 1 downto 0 do members_ev.(scc_of.(i)) <- r.rdg_events.(i) :: members_ev.(scc_of.(i)) done;
    let rep s =
      let ms = members_ev.(s) in
      let real = List.filter ms ~f:(fun e -> not (rdg_is_helper e)) in
      let pick = if List.is_empty real then ms else real in
      Option.value (List.min_elt pick
                      ~compare:(fun a b -> Int.compare (String.length a) (String.length b)))
        ~default:"?" in
    (* full RDG, clustered by SCC *)
    let full =
      G.to_dot ~name:"RDG" ~scc_of
        ~node_label:(fun v -> rdg_esc r.rdg_labels.(v))
        ~label_to_string:(fun () -> "") r.rdg_graph in
    (* focused condensation = section dependency DAG *)
    let focus =
      let buf = Buffer.create 1024 in
      Buffer.add_string buf
        "digraph RDG_focus {\n  rankdir=LR;\n  node [shape=box, style=filled, fontsize=10];\n\
        \  edge [color=\"#999999\", arrowsize=0.5];\n";
      for s = 0 to sc - 1 do
        let color =
          if recursive.(s) then "#ff9999"
          else match members_ev.(s) with
            | e :: _ when String.is_prefix e ~prefix:"Sup_" -> "#ffe0b3"
            | e :: _ when String.is_prefix e ~prefix:"Cau_" -> "#d9f2d9"
            | _ -> "#cfe8ff" in
        let lbl =
          if sizes.(s) > 1
          then Printf.sprintf "%s\\nsec%d (%d rules)" (rdg_esc (rep s)) s sizes.(s)
          else Printf.sprintf "%s\\nsec%d" (rdg_esc (rep s)) s in
        Buffer.add_string buf
          (Printf.sprintf "  s%d [label=\"%s\", fillcolor=\"%s\"];\n" s lbl color)
      done;
      let cond =
        List.filter_map (G.edges r.rdg_graph) ~f:(fun (u, _, v) ->
            let a = scc_of.(u) and b = scc_of.(v) in
            if a <> b then Some (a, b) else None)
        |> List.dedup_and_sort ~compare:[%compare: int * int] in
      List.iter cond ~f:(fun (a, b) ->
          Buffer.add_string buf (Printf.sprintf "  s%d -> s%d;\n" a b));
      Buffer.add_string buf "}\n";
      Buffer.contents buf in
    (* one expanded graph per recursive (fixpoint) section *)
    let scc_dot s =
      let buf = Buffer.create 256 in
      Buffer.add_string buf
        (Printf.sprintf "digraph RDG_sec%d {\n  rankdir=LR;\n  node [shape=box, fontsize=8];\n" s);
      Array.iteri scc_of ~f:(fun i si ->
          if si = s then
            Buffer.add_string buf
              (Printf.sprintf "  n%d [label=\"%s\"];\n" i (rdg_esc r.rdg_labels.(i))));
      List.iter (G.edges r.rdg_graph) ~f:(fun (u, _, v) ->
          if scc_of.(u) = s && scc_of.(v) = s then
            Buffer.add_string buf (Printf.sprintf "  n%d -> n%d;\n" u v));
      Buffer.add_string buf "}\n";
      Buffer.contents buf in
    let scc_files =
      List.filter_map (List.init sc ~f:Fn.id) ~f:(fun s ->
          if recursive.(s) then Some (Printf.sprintf "rdg_sec_%d.dot" s, scc_dot s) else None) in
    ("rdg.dot", full) :: ("rdg_focus.dot", focus)
    :: ("waves.dot",      waves_dot ~drop_monotone:false pg)
    :: ("waves_drop.dot", waves_dot ~drop_monotone:true  pg)
    :: scc_files
  end

(* ─── Explaining a complexity bound ──────────────────────────────────────── *)

(* Names of relations (tables / lets / aggs / tops / events) a clause reads. *)
let clause_refs (cl : clause) : string list =
  let acc = ref [] in
  List.iter cl.cl_patterns ~f:(List.iter ~f:(function
      | GEvent ep -> acc := ep.ep_name :: !acc
      | GEqConst _ -> ()));
  let rec f = function
    | FTableLookup (n, _) -> acc := n :: !acc
    | FAnd (a, b) | FOr (a, b) -> f a; f b
    | FNot a -> f a
    | FBoolLit _ | FCompare _ -> ()
  in
  f cl.cl_filter;
  !acc

type definition =
  [ `Table of table_def | `Let of let_def | `Agg of agg_let_def | `Top of top_let_def ]

let find_definition (pg : program) (name : string) : definition option =
  match List.find pg.pg_tables ~f:(fun td -> String.equal td.td_name name) with
  | Some td -> Some (`Table td)
  | None ->
    match List.find pg.pg_let_defs ~f:(fun ld -> String.equal ld.ld_name name) with
    | Some ld -> Some (`Let ld)
    | None ->
      match List.find pg.pg_agg_lets ~f:(fun ad -> String.equal ad.agg_name name) with
      | Some ad -> Some (`Agg ad)
      | None ->
        match List.find pg.pg_top_lets ~f:(fun td -> String.equal td.top_name name) with
        | Some td -> Some (`Top td)
        | None -> None

let definition_clauses : definition -> clause list = function
  | `Table td -> td.td_add_clause :: (match td.td_remove_clause with Some c -> [ c ] | None -> [])
  | `Let ld -> [ ld.ld_clause ]
  | `Agg ad -> [ ad.agg_clause ]
  | `Top td -> [ td.top_clause ]

let definition_to_string : definition -> string = function
  | `Table td -> table_def_to_string td
  | `Let ld -> let_def_to_string ld
  | `Agg ad -> agg_let_def_to_string ad
  | `Top td -> top_let_def_to_string td

(* Pretty-print, in dependency order, every relation the complexity bound
   mentions, together with the transitive closure of the relations they read —
   so one can see what each accumulating [Once…] table (and each let it depends
   on) actually collects, down to the trace events. *)
let relevant_definitions_to_string (pg : program) : string =
  let roots =
    Complexity.cards (program_complexity pg)
    |> List.dedup_and_sort ~compare:String.compare
  in
  let seen = Hashtbl.create (module String) in
  let order = ref [] in
  let rec visit name =
    if not (Hashtbl.mem seen name) then begin
      Hashtbl.set seen ~key:name ~data:();
      match find_definition pg name with
      | None -> ()                               (* a trace event: nothing to unfold *)
      | Some def ->
        order := name :: !order;                 (* pre-order: dependents before deps *)
        List.iter (definition_clauses def) ~f:(fun cl ->
            List.iter (clause_refs cl) ~f:visit)
    end
  in
  List.iter roots ~f:visit;
  List.rev !order
  |> List.filter_map ~f:(fun name ->
      Option.map (find_definition pg name) ~f:definition_to_string)
  |> String.concat ~sep:"\n\n"

let program_to_string pg =
  let buf = Buffer.create 4096 in
  let emit s = Buffer.add_string buf s; Buffer.add_char buf '\n' in
  let emit_blank () = Buffer.add_char buf '\n' in
  (* Estimated per-time-point cost, as a `//` comment (skipped by the parser). *)
  emit (Printf.sprintf "// complexity (per time-point, O(1) events/stamp): %s"
          (program_complexity_to_string pg));
  emit_blank ();
  (* Event declarations *)
  List.iter pg.pg_event_decls ~f:(fun ed -> emit (event_decl_to_string ed));
  if not (List.is_empty pg.pg_event_decls) then emit_blank ();
  (* Module-level Python preamble (imports + shared globals), if any. *)
  if not (String.is_empty pg.pg_py_preamble) then begin
    emit (Printf.sprintf "pyinit {\n%s\n}" pg.pg_py_preamble);
    emit_blank ()
  end;
  (* Function declarations (scalar funs, then table funs) *)
  List.iter pg.pg_fun_decls ~f:(fun fd -> emit (fun_decl_to_string fd));
  if not (List.is_empty pg.pg_fun_decls) then emit_blank ();
  List.iter pg.pg_tfun_decls ~f:(fun t -> emit (tfun_decl_to_string t); emit_blank ());
  (* Let definitions, table definitions, aggregation/table-op lets in order *)
  List.iter pg.pg_items ~f:(fun item ->
      match item with
      | PiLet ld -> emit (let_def_to_string ld); emit_blank ()
      | PiTable td -> emit (table_def_to_string td); emit_blank ()
      | PiAgg ad -> emit (agg_let_def_to_string ad); emit_blank ()
      | PiTop td -> emit (top_let_def_to_string td); emit_blank ());
  (* Rule definitions, grouped into EDG-ordered sections.  Each section is
     introduced by a `section fixpoint;` / `section once;` marker (a first-class
     statement in the .ef grammar) that the engine parses to drive evaluation:
     a `fixpoint` section is iterated to a local fixpoint, a `once` section is
     evaluated in a single pass.  Rules are emitted in section (dependency)
     order. *)
  let waves = pg.pg_sections in
  let rules = Array.of_list pg.pg_rules in
  List.iteri waves ~f:(fun wi wave ->
      if wi > 0 then (emit "sync;"; emit_blank ());
      List.iter wave ~f:(fun (recursive, idxs) ->
          emit (Printf.sprintf "section %s;" (if recursive then "fixpoint" else "once"));
          emit_blank ();
          List.iter idxs ~f:(fun i -> emit (rule_def_to_string rules.(i)); emit_blank ())));
  Buffer.contents buf

let write_program_to_file ~(filename: string) (pg: program) =
  let text = program_to_string pg in
  Stdio.Out_channel.write_all filename ~data:text
