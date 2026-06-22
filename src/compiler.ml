(* Compiler from the enforcement strategy extraction result into an Enfflash.program.

   Pipeline:
     Parsing         → Sformula.t
     Init + alpha    → Formula.t          (Formula.init, Formula.convert_vars)
     Term typing     → Tyformula.t        (Tyformula.of_formula')
     Normalization   → Normalize.result   (Normalize.normalize)
     Enforceability  → typing_result      (Enforceability.enforce)
     Extraction      → Extraction.result  (Extraction.extract)
     Compilation     → Enfflash.program   (Compiler.compile, this module)
     Linearization   → .ef file           (Enfflash.write_program_to_file)

   The top-level [run] function orchestrates all steps from a parsed formula.

   Mapping summary:
     SNow   trigger  →  let Name(…) := { filter }
     SOnce  trigger  →  table Name(…) := add { clause };
     SPrev  trigger  →  lagged table Name(…) := add { clause };
     SSince (l, r)   →  table Name(…) := add { r } remove { l };
     clause (trigger → effects) →  one rule per (effect × guard disjunct)

   Notes on NEXT:
     Next is eliminated by make_past_only before reaching the compiler
     (Next in positive polarity → FF, in negative → TT). No engine extension needed.
*)

open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm
module Ctxt = Ctxt.Make(Dom)

open Nformula

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Type / value conversions                                                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

let tt_to_ef : Dom.tt -> Enfflash.ef_ty = function
  | Dom.TInt   -> EfInt
  | Dom.TStr   -> EfStr
  | Dom.TFloat -> EfFloat

let dom_to_ef : Dom.t -> Enfflash.ef_value = function
  | Dom.Int i   -> EfVInt i
  | Dom.Str s   -> EfVStr s
  | Dom.Float f -> EfVFloat f

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Term compilation                                                           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Sanitize a name to be a valid enfflash identifier (alphanumeric + _). *)
let sanitize_name name =
  String.map name ~f:(fun c ->
      if Char.is_alphanum c || Char.equal c '_' then c else '_')

let san = sanitize_name

let rec term_to_ef (t: Tterm.t) : Enfflash.term_expr =
  match t.trm with
  | Var x         -> TEVar (san (fst x))
  | Const d       -> TELit (dom_to_ef d)
  | App (f, args) -> TEFunCall (f, List.map ~f:term_to_ef args)
  | _             -> TEVar "__unsupported_term__"

let term_to_pattern_arg (t: Tterm.t) : Enfflash.pattern_arg =
  match t.trm with
  | Var x   -> PAVar (san (fst x))
  | Const d -> PALiteral (dom_to_ef d)
  | _       -> PAWildcard

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Recognize relational operations encoded as EqConst(App("op",[a,b]), 1)     *)
(* (Formula.init encodes  a < b  as  EqConst(App("lt",[a,b]), Int 1) )       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

let try_relop (t: Tterm.t) (c: Dom.t) : (Enfflash.term_expr * Enfflash.cmp_op * Enfflash.term_expr) option =
  match t.trm, c with
  | App ("eq",  [a; b]), Dom.Int 1 -> Some (term_to_ef a, CmpEq,  term_to_ef b)
  | App ("neq", [a; b]), Dom.Int 1 -> Some (term_to_ef a, CmpNeq, term_to_ef b)
  | App ("lt",  [a; b]), Dom.Int 1 -> Some (term_to_ef a, CmpLt,  term_to_ef b)
  | App ("leq", [a; b]), Dom.Int 1 -> Some (term_to_ef a, CmpLe,  term_to_ef b)
  | App ("gt",  [a; b]), Dom.Int 1 -> Some (term_to_ef a, CmpGt,  term_to_ef b)
  | App ("geq", [a; b]), Dom.Int 1 -> Some (term_to_ef a, CmpGe,  term_to_ef b)
  | _ -> None

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Formula → FilterExpr                                                       *)
(*                                                                            *)
(* Works on the _core_t constructors which are shared between Formula.t       *)
(* (info = unit) and Formula.typed_t (info = TypedInfo.t).  The function      *)
(* takes just the .form field and recurses via .form on children.             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

let rec compile_filter_form
    (form: (_, Tterm.TypedVar.t, Dom.t, Tterm.t) Tyformula._core_t)
  : Enfflash.filter_expr =
  let open Enfflash in
  match form with
  | TT -> FBoolLit true
  | FF -> FBoolLit false
  | EqConst (t, c) ->
    (match try_relop t c with
     | Some (l, op, r) -> FCompare (l, op, r)
     | None -> FCompare (term_to_ef t, CmpEq, TELit (dom_to_ef c)))
  | Predicate (name, args) ->
    FTableLookup (name, List.map ~f:term_to_ef args)
  | Predicate' (name, args, _) ->
    FTableLookup (name, List.map ~f:term_to_ef args)
  | Neg f -> FNot (compile_filter_form f.form)
  | And (_, fs) ->
    (match fs with
     | []   -> FBoolLit true
     | [f]  -> compile_filter_form f.form
     | f :: rest ->
       List.fold_left rest
         ~init:(compile_filter_form f.form)
         ~f:(fun acc g -> FAnd (acc, compile_filter_form g.form)))
  | Or (_, fs) ->
    (match fs with
     | []   -> FBoolLit false
     | [f]  -> compile_filter_form f.form
     | f :: rest ->
       List.fold_left rest
         ~init:(compile_filter_form f.form)
         ~f:(fun acc g -> FOr (acc, compile_filter_form g.form)))
  | Imp (_, f, g) ->
    FOr (FNot (compile_filter_form f.form), compile_filter_form g.form)
  | Exists (_, f) ->
    (* Existential quantification is implicit in enfflash:
       free variables in TableLookup patterns get existentially bound. *)
    compile_filter_form f.form
  | Forall (_, f) ->
    (* NOTE: Universal quantification is not directly expressible in enfflash.
       This compiles the body but the universal semantics is lost. *)
    compile_filter_form f.form
  | Let (name, _, vars, body, _) ->
    (* Inline the let reference as a lookup. *)
    let args = List.map vars ~f:(fun (v, _) -> Enfflash.TEVar (san (fst v))) in
    FTableLookup (sanitize_name name, args)
  | Let' (name, _, vars, _, _) ->
    let args = List.map vars ~f:(fun (v, _) -> Enfflash.TEVar (san (fst v))) in
    FTableLookup (sanitize_name name, args)
  | Eventually (i, f) when Interval.has_zero i ->
    (* ◊[0,…) body: the interval includes the current timepoint,
       so the body can be satisfied NOW.  In a filter context we
       check the body at the present time. *)
    compile_filter_form f.form
  | Eventually _ | Next _ ->
    (* Future-only obligations (interval starts > 0, or Next).
       In a filter context (present-time check) they evaluate
       to false: the obligation is not yet met. *)
    FBoolLit false
  | Label (_, f) ->
    (* Labels are metadata; compile the inner formula. *)
    compile_filter_form f.form
  | _ ->
    (* Temporal operators (Once, Since, Prev, Always, etc.) cannot be expressed
       as filter expressions.  They should have been compiled into tables by the
       let compilation pass.  If we reach here, something is unexpected. *)
    FBoolLit true

(* Convenience wrappers *)
let formula_to_filter (f: Tyformula.t) : Enfflash.filter_expr =
  compile_filter_form f.form

let typed_formula_to_filter (f: Tyformula.typed_t) : Enfflash.filter_expr =
  compile_filter_form f.form

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Helpers                                                                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

let merge_filters (parts: Enfflash.filter_expr list) : Enfflash.filter_expr =
  match parts with
  | []   -> FBoolLit true
  | [f]  -> f
  | f :: rest ->
    List.fold_left rest ~init:f ~f:(fun acc g -> Enfflash.FAnd (acc, g))

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Conjunct reordering                                                        *)
(*                                                                            *)
(* Check whether a predicate name corresponds to a trace event in the
   signature (Sig module), or is a synthetic Cau_/Sup_ event generated
   by the enforcement compiler. *)
let is_trace_event name =
  String.is_prefix name ~prefix:"Cau_"
  || String.is_prefix name ~prefix:"Sup_"
  || (try Sig.equal_pred_kind (Sig.kind_of_pred name) Sig.Trace
      with _ -> false)

(* A predicate is allowed in a guard pattern if it is a trace event
   or a let-def.  Tables (Func with kind=Table) must NOT appear in
   guard patterns. *)
let is_pattern_event name =
  is_trace_event name
  || (try Sig.equal_pred_kind (Sig.kind_of_pred name) Sig.Let
      with _ -> false)

(* Parse label-prefixed names like "Label0:myname" into
   (Some "myname", "Label0_myname"). *)
let parse_label_name name =
  match String.lsplit2 name ~on:':' with
  | Some (prefix, label) ->
    (Some label, prefix ^ "_" ^ label)
  | None ->
    (None, name)

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Trigger → Clause(s)                                                        *)
(*                                                                            *)
(* A trigger has guards (DNF list of conjunctive formula lists) and a filter. *)
(* Each guard disjunct produces one enfflash clause.                           *)
(* Within each conjunct, we separate trace events (→ EventPatterns) from      *)
(* other formulas (→ folded into the filter).                                 *)
(*                                                                            *)
(* Non-filter let-bound predicates (those whose SNow trigger has guards) are  *)
(* inlined: their trigger's guards and filter are substituted with the actual  *)
(* arguments and merged into the current clause.  This ensures that trace      *)
(* events inside let-def bodies become proper EventPatterns in the clause.     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Check whether a let-def is a non-filter SNow (its trigger has event guards).
   If so, return Some (formal_args, trigger).  Otherwise return None. *)
let get_inlineable_trigger (let_map: Nformula.let_map) (name: string)
  : ((Tterm.TypedVar.t * Dom.tt option) list * Trigger.t) option =
  match Map.find let_map name with
  | Some def ->
    (match def.switch_pos_opt with
     | Some (Switch.Now trigger) when not (List.is_empty trigger.guards) ->
       Some (def.args, trigger)
     | _ -> None)
  | None -> None

(* Build a substitution map from formal parameters to actual arguments. *)
let build_subst
    (formals: (Tterm.TypedVar.t * Dom.tt option) list)
    (actuals: Tterm.t list)
  : (Tterm.TypedVar.t, Tterm.t, Tterm.TypedVar.comparator_witness) Map.t =
  List.fold2_exn formals actuals
    ~init:(Map.empty (module Tterm.TypedVar))
    ~f:(fun acc (formal_var, _) actual_term ->
        Map.set acc ~key:formal_var ~data:actual_term)

(* Inline non-filter let-def guards: given a list of guard conjuncts,
   expand any non-filter let-bound predicates into their trigger's guards
   and filter, substituting formal parameters with actual arguments.
   Returns (expanded_guards, extra_filter_formulas). *)
let rec inline_let_guards
    (let_map: Nformula.let_map)
    (guards: Tyformula.t list)
  : Tyformula.t list * Tyformula.t list =
  List.fold_right guards ~init:([], [])
    ~f:(fun g (acc_guards, acc_filters) ->
        match g.form with
        | Predicate (name, actuals) when not (is_trace_event name) ->
          (match get_inlineable_trigger let_map name with
           | Some (formals, inner_trigger) ->
             (* Build substitution: formal param → actual arg *)
             let subst_map = build_subst formals actuals in
             (* Substitute in the inner trigger's guards (take first disjunct) *)
             let inlined_guards =
               match inner_trigger.guards with
               | [] -> []
               | disjunct :: _ ->
                 List.map disjunct ~f:(Tyformula.subst subst_map) in
             (* Substitute in the inner trigger's filter *)
             let inlined_filter = Tyformula.subst subst_map inner_trigger.filter in
             let extra_filter =
               match inlined_filter.form with
               | Tyformula.TT -> acc_filters
               | _ -> inlined_filter :: acc_filters in
             (* Recursively inline the expanded guards *)
             let re_inlined_guards, re_inlined_filters =
               inline_let_guards let_map inlined_guards in
             (re_inlined_guards @ acc_guards, re_inlined_filters @ extra_filter)
           | None ->
             (* Not inlineable: keep as-is *)
             (g :: acc_guards, acc_filters))
        | _ ->
          (g :: acc_guards, acc_filters))

(* Convert a guard conjunct to a guard pattern.
   MFOTL.ml ensures only valid guards appear here (trace events,
   non-filter let-defs, EqConst).  Compile straightforwardly. *)
let guard_to_pattern (g: Tyformula.t) : Enfflash.guard_pattern =
  match g.form with
  | Predicate (name, args) ->
    Enfflash.(GEvent { ep_name = sanitize_name name;
                       ep_args = List.map ~f:term_to_pattern_arg args })
  | EqConst ({ trm = Tterm.Var x }, v) ->
    Enfflash.(GEqConst (san (Tterm.TypedVar.ident x), dom_to_ef v))
  | _ -> failwith (Printf.sprintf "guard_to_pattern: unexpected guard form")

let decompose_guard_disj (guards: Tyformula.t list list)
  : Enfflash.guard_pattern list list =
  List.map guards ~f:(fun conj ->
      List.map conj ~f:guard_to_pattern)

let trigger_to_clause
    ~(let_map: Tnformula.let_map)
    (trigger: Trigger.t)
  : Enfflash.clause =
  let patterns = decompose_guard_disj trigger.guards in
  Enfflash.{ cl_patterns = patterns;
             cl_filter   = formula_to_filter trigger.filter }

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SNow trigger → Clause with event extraction                                *)
(*                                                                            *)
(* For present-time (SNow) let-defs, `trigger.guards` may be empty because    *)
(* `pull_guard` only promotes predicates that guard an unguarded variable.     *)
(* When all free variables are already the let-def's parameters, no guards     *)
(* are pulled and trace events like Declaration(x) end up in the filter.      *)
(*                                                                            *)
(* This function additionally scans the filter's top-level conjunction for     *)
(* trace-event predicates and promotes them to event patterns.                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Flatten a formula's top-level conjunction into a list of conjuncts. *)
let rec flatten_conj (f: Tyformula.t) : Tyformula.t list =
  match f.form with
  | And (_, fs) -> List.concat_map fs ~f:flatten_conj
  | _ -> [f]

(* Build a conjunction from a list of formulas. *)
let rebuild_conj (fs: Tyformula.t list) : Tyformula.t =
  match fs with
  | []  -> Tyformula.make_dummy Tyformula.TT
  | [f] -> f
  | _   -> Tyformula.make_dummy (Tyformula.And (Side.N, fs))

(* For an SNow trigger: extract trace-event predicates from the filter
   and combine with any existing guards to form a proper clause. *)

(* Fresh-variable counter for event-pattern wildcard slots. *)
let fresh_var_counter = ref 0
let fresh_var () =
  let n = !fresh_var_counter in
  Int.incr fresh_var_counter;
  Printf.sprintf "_ep%d" n

(* Convert a predicate conjunct to an event pattern, handling complex args.
   For each argument that is not a simple Var or Const, we bind a fresh
   variable in the pattern and return a filter equality constraint:
     fresh_var == complex_expr
   Returns (guard_pattern, extra_filter_exprs). *)
let predicate_to_event_pattern (name: string) (args: Tterm.t list)
  : Enfflash.guard_pattern * Enfflash.filter_expr list =
  let open Enfflash in
  let extra_filters = ref [] in
  let pattern_args = List.map args ~f:(fun t ->
      match t.trm with
      | Var x   -> PAVar (san (fst x))
      | Const d -> PALiteral (dom_to_ef d)
      | _       ->
        (* Complex expression: bind to a fresh variable and add filter *)
        let v = fresh_var () in
        extra_filters := FCompare (TEVar v, CmpEq, term_to_ef t) :: !extra_filters;
        PAVar v) in
  let gp = GEvent { ep_name = sanitize_name name; ep_args = pattern_args } in
  (gp, List.rev !extra_filters)

let snow_trigger_to_clause
    ~(let_map: Tnformula.let_map)
    (trigger: Trigger.t)
  : Enfflash.clause =
  (* Start with any guards already present (usually empty for SNow) *)
  let base_patterns = decompose_guard_disj trigger.guards in
  (* Flatten the filter into conjuncts *)
  let conjuncts = flatten_conj trigger.filter in
  (* Separate event predicates from non-event parts *)
  let events, rest = List.partition_tf conjuncts ~f:(fun f ->
      match f.form with
      | Tyformula.Predicate (name, _) -> is_pattern_event name
      | _ -> false) in
  (* Convert event predicates to guard patterns, collecting extra filters *)
  let event_patterns = ref [] in
  let extra_filters = ref [] in
  List.iter events ~f:(fun f ->
      match f.form with
      | Tyformula.Predicate (name, args) ->
        let gp, ef = predicate_to_event_pattern name args in
        event_patterns := gp :: !event_patterns;
        extra_filters := ef @ !extra_filters
      | _ -> ());
  let event_patterns = List.rev !event_patterns in
  let extra_filters = List.rev !extra_filters in
  (* Merge: if base_patterns has disjuncts, add events to each;
     otherwise create a single disjunct with just the events. *)
  let patterns = match base_patterns, event_patterns with
    | _, [] -> base_patterns
    | [], eps -> [eps]
    | disjs, eps ->
      List.map disjs ~f:(fun conj -> conj @ eps) in
  (* Remaining conjuncts become the filter, plus any extra equality filters *)
  let remaining_filter = formula_to_filter (rebuild_conj rest) in
  let cl_filter = merge_filters (remaining_filter :: extra_filters) in
  Enfflash.{ cl_patterns = patterns; cl_filter }


(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Compile event declarations from the Sig table                              *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

let compile_event_decls () : Enfflash.event_decl list =
  let events =
    Hashtbl.fold Sig.table ~init:[]
      ~f:(fun ~key ~data acc ->
          match data with
          | Sig.Pred pred
            when Sig.equal_pred_kind pred.kind Sig.Trace
              && not (String.equal key "~tp")
              && not (String.equal key "tick") ->
            let types =
              List.map pred.arg_ttts ~f:(fun (_, ttt) ->
                  match ttt with
                  | Ctxt.TConst tt -> tt_to_ef tt
                  | _ -> Enfflash.EfInt (* default for non-concrete types *)) in
            Enfflash.{ ed_name = key; ed_param_types = types } :: acc
          | _ -> acc) in
  List.sort events ~compare:(fun a b -> String.compare a.Enfflash.ed_name b.ed_name)

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Compile function declarations from the Sig table                           *)
(*                                                                            *)
(* External (user-defined) functions in the signature are compiled into        *)
(* Enfflash fun_decl entries.  The Python source file is parsed to extract     *)
(* function bodies.                                                            *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Parse a Python source file and extract function bodies.
   Returns a map from function name to the body (lines after "def fname(...):")
   with leading indentation removed. *)
(* Module-level "preamble" of a --func Python file: every top-level (unindented)
   statement that is not a `def` — imports and shared global initialisations
   (e.g. `import numpy as np`, `consent = set()`).  These are shared by all the
   functions (the [fun]/[afun] bodies reference them, and stateful globals must
   persist across calls), so the engine execs the preamble once in the single
   shared module that hosts every Python function.  Mirrors the way the legacy
   tool loads the whole --func file as one module. *)
let python_preamble (py_source: string) : string =
  let lines = String.split_lines py_source in
  let rec collect lines acc =
    match lines with
    | [] -> List.rev acc
    | line :: rest ->
      let stripped = String.lstrip line in
      if String.is_prefix stripped ~prefix:"def " then
        (* Skip the function's (indented / blank) body lines. *)
        let rec skip rest =
          match rest with
          | [] -> []
          | next :: more ->
            if String.is_empty (String.lstrip next)
            || (String.length next > 0 && Char.is_whitespace (String.get next 0))
            then skip more
            else next :: more in
        collect (skip rest) acc
      else if String.is_empty stripped then collect rest acc
      else collect rest (line :: acc) in
  String.concat ~sep:"\n" (collect lines [])

(* Parse a --func Python file into a map [name -> (params, body)].  The body is
   the dedented function body verbatim (no rewriting); [params] are the parameter
   names exactly as written in the Python def, so the engine can emit each
   function with its original signature. *)
let parse_python_functions (py_source: string)
  : (string, (string list * string), String.comparator_witness) Map.t =
  let lines = String.split_lines py_source in
  (* Remove common leading whitespace from non-empty lines (like textwrap.dedent) *)
  let dedent body_lines =
    let non_empty = List.filter body_lines ~f:(fun l -> not (String.is_empty (String.lstrip l))) in
    let min_indent = List.fold non_empty ~init:Int.max_value
        ~f:(fun acc l ->
            let trimmed = String.lstrip l in
            let indent = String.length l - String.length trimmed in
            Int.min acc indent) in
    let min_indent = if Int.equal min_indent Int.max_value then 0 else min_indent in
    List.map body_lines ~f:(fun l ->
        if String.is_empty (String.lstrip l) then ""
        else if String.length l >= min_indent then String.drop_prefix l min_indent
        else String.lstrip l) in
  let rec collect_functions lines acc =
    match lines with
    | [] -> acc
    | line :: rest ->
      (* Match "def fname(...)  -> ... :" or "def fname(...) :" *)
      let stripped = String.lstrip line in
      if String.is_prefix stripped ~prefix:"def " then
        let after_def = String.drop_prefix stripped 4 in
        match String.lsplit2 after_def ~on:'(' with
        | Some (fname, after_paren) ->
          let fname = String.strip fname in
          (* Parameter names exactly as written in the Python def (stripped of
             any `: type` annotation or `= default`), so the engine can emit the
             function with its original signature — the body refers to these. *)
          let params =
            match String.lsplit2 after_paren ~on:')' with
            | Some (args, _) ->
              String.split args ~on:','
              |> List.map ~f:(fun p ->
                  let p = match String.lsplit2 p ~on:':' with Some (n, _) -> n | None -> p in
                  let p = match String.lsplit2 p ~on:'=' with Some (n, _) -> n | None -> p in
                  String.strip p)
              |> List.filter ~f:(fun p -> not (String.is_empty p))
            | None -> [] in
          (* Collect body lines: all indented lines that follow *)
          let rec collect_body rest body_lines =
            match rest with
            | [] -> (List.rev body_lines, [])
            | next :: more ->
              let next_stripped = String.lstrip next in
              if String.is_empty next_stripped then
                (* blank line inside function, include it *)
                collect_body more (next :: body_lines)
              else if String.length next > 0 && Char.is_whitespace (String.get next 0) then
                collect_body more (next :: body_lines)
              else
                (* next non-indented line: function is done *)
                (List.rev body_lines, next :: more)
          in
          let raw_body_lines, remaining = collect_body rest [] in
          let body_lines = dedent raw_body_lines in
          let body = String.rstrip (String.concat ~sep:"\n" body_lines) in
          collect_functions remaining (Map.set acc ~key:fname ~data:(params, body))
        | None -> collect_functions rest acc
      else
        collect_functions rest acc
  in
  collect_functions lines (Map.empty (module String))

let ttt_to_ef (ttt: Ctxt.ttt) : Enfflash.ef_ty =
  match ttt with
  | Ctxt.TConst tt -> tt_to_ef tt
  | _ -> Enfflash.EfInt

(* Map built-in MFOTL function names to equivalent Python bodies *)
let builtin_to_python (name: string) (param_names: string list) : string option =
  match name, param_names with
  (* Arithmetic (int) *)
  | "add", [a; b]             -> Some (Printf.sprintf "return %s + %s" a b)
  | "sub", [a; b]             -> Some (Printf.sprintf "return %s - %s" a b)
  | "usub", [a]               -> Some (Printf.sprintf "return -%s" a)
  | "mul", [a; b]             -> Some (Printf.sprintf "return %s * %s" a b)
  | "div", [a; b]             -> Some (Printf.sprintf "return %s // %s" a b)
  | "pow", [a; b]             -> Some (Printf.sprintf "return %s ** %s" a b)
  (* Arithmetic (float) *)
  | "fadd", [a; b]            -> Some (Printf.sprintf "return %s + %s" a b)
  | "fsub", [a; b]            -> Some (Printf.sprintf "return %s - %s" a b)
  | "ufsub", [a]              -> Some (Printf.sprintf "return -%s" a)
  | "fmul", [a; b]            -> Some (Printf.sprintf "return %s * %s" a b)
  | "fdiv", [a; b]            -> Some (Printf.sprintf "return %s / %s" a b)
  | "fpow", [a; b]            -> Some (Printf.sprintf "return %s ** %s" a b)
  (* Comparison *)
  | "eq", [a; b]              -> Some (Printf.sprintf "return 1 if %s == %s else 0" a b)
  | "neq", [a; b]             -> Some (Printf.sprintf "return 1 if %s != %s else 0" a b)
  | "lt", [a; b]              -> Some (Printf.sprintf "return 1 if %s < %s else 0" a b)
  | "leq", [a; b]             -> Some (Printf.sprintf "return 1 if %s <= %s else 0" a b)
  | "gt", [a; b]              -> Some (Printf.sprintf "return 1 if %s > %s else 0" a b)
  | "geq", [a; b]             -> Some (Printf.sprintf "return 1 if %s >= %s else 0" a b)
  (* Logic *)
  | "not", [a]                -> Some (Printf.sprintf "return 0 if %s else 1" a)
  (* String *)
  | "conc", [a; b]            -> Some (Printf.sprintf "return %s + %s" a b)
  | "substr", [s; a; b]       -> Some (Printf.sprintf "return %s[%s:%s]" s a b)
  | "match", [x; r]           -> Some (Printf.sprintf "import re\nreturn 1 if re.match(%s, %s) else 0" r x)
  (* Conversions *)
  | "string_of_int", [x]      -> Some (Printf.sprintf "return str(%s)" x)
  | "string_of_float", [x]    -> Some (Printf.sprintf "return str(%s)" x)
  | "int_of_float", [x]       -> Some (Printf.sprintf "return int(%s)" x)
  | "float_of_int", [x]       -> Some (Printf.sprintf "return float(%s)" x)
  | _ -> None

let compile_fun_decls ~(py_source: string option) () : Enfflash.fun_decl list =
  let py_bodies = match py_source with
    | Some src -> parse_python_functions src
    | None -> Map.empty (module String) in
  let funs =
    Hashtbl.fold Sig.table ~init:[]
      ~f:(fun ~key ~data acc ->
          match data with
          | Sig.Func func ->
            (match func.kind with
             | Funcs.External ->
               let mfotl_param_names = List.map func.arg_ttts ~f:fst in
               let param_types = List.map func.arg_ttts ~f:(fun (_, ttt) -> ttt_to_ef ttt) in
               let ret_type = match func.ret_ttts with
                 | [ttt] -> ttt_to_ef ttt
                 | _ -> Enfflash.EfInt in
               let py_params, body = match Map.find py_bodies key with
                 | Some (params, b) -> (Some params, b)
                 | None ->
                   (* Generate a fallback body based on the function signature *)
                   (None, Printf.sprintf "return %s" (String.concat ~sep:" + " (
                       match mfotl_param_names with
                       | [] -> ["0"]
                       | [p] -> [p]
                       | _ -> [List.hd_exn mfotl_param_names]))) in
               (* Use the Python def's own parameter names (so the body resolves)
                  when they line up positionally with the signature; otherwise
                  fall back to the MFOTL signature names. *)
               let param_names = match py_params with
                 | Some ps when List.length ps = List.length param_types -> ps
                 | _ -> mfotl_param_names in
               Enfflash.{ fd_name = key;
                          fd_param_names = param_names;
                          fd_param_types = param_types;
                          fd_ret_type = ret_type;
                          fd_body = body } :: acc
             | Funcs.Builtin _ ->
               let param_names = List.map func.arg_ttts ~f:fst in
               (match builtin_to_python key param_names with
                | Some body ->
                  let param_types = List.map func.arg_ttts ~f:(fun (_, ttt) -> ttt_to_ef ttt) in
                  let ret_type = match func.ret_ttts with
                    | [ttt] -> ttt_to_ef ttt
                    | _ -> Enfflash.EfInt in
                  Enfflash.{ fd_name = key;
                             fd_param_names = param_names;
                             fd_param_types = param_types;
                             fd_ret_type = ret_type;
                             fd_body = body } :: acc
                | None -> acc)
             | _ -> acc)
          | _ -> acc) in
  List.sort funs ~compare:(fun a b -> String.compare a.Enfflash.fd_name b.fd_name)

(* Compile the Python table functions referenced by `tableop let`s.  Each named
   function takes one argument `rows` (a list of value-lists) and returns a list
   of output value-lists; its body comes from the --func Python file. *)
let compile_tfun_decls ~(py_source: string option) (names: string list) : Enfflash.tfun_decl list =
  let py_bodies = match py_source with
    | Some src -> parse_python_functions src
    | None -> Map.empty (module String) in
  List.dedup_and_sort names ~compare:String.compare
  |> List.map ~f:(fun name ->
      let tfd_body = match Map.find py_bodies name with
        | Some (params, b) ->
          (* The engine invokes a table function as `def name(rows): …`.  Bind
             the function's own (single) parameter to `rows` when it differs, so
             a body written against the original parameter name still resolves. *)
          (match params with
           | [param] when not (String.equal param "rows") -> param ^ " = rows\n" ^ b
           | _ -> b)
        | None -> "return rows" in
      Enfflash.{ tfd_name = name; tfd_body })

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Compile let definitions using switch structures from the let_map           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Check whether a compiled filter_expr references any trace event.
   A let whose body contains event references is "sufficiently guarded"
   and can itself serve as a guard; otherwise it is a "filter let". *)
(*let rec filter_has_event_ref (f: Enfflash.filter_expr) : bool =
  match f with
  | FBoolLit _ -> false
  | FTableLookup (name, _) ->
    (match Hashtbl.find Sig.table name with
     | Some (Sig.Pred p) -> Sig.equal_pred_kind p.kind Sig.Trace
     | _ -> false)
  | FCompare _ -> false
  | FAnd (a, b) | FOr (a, b) -> filter_has_event_ref a || filter_has_event_ref b
  | FNot a -> filter_has_event_ref a*)

(* Convert a metric interval into the table window passed to the engine.
   [0, ∞) maps to [None] (the non-metric accumulate-forever case), so plain
   Once/Since/Prev compile exactly as before. *)
let interval_to_window (i: Interval.t) : (int * int option) option =
  let a = Time.Span.min_seconds (Interval.left i) in
  let b = Option.map (Interval.right i) ~f:Time.Span.min_seconds in
  match a, b with
  | 0, None -> None
  | _       -> Some (a, b)

let compile_let_from_switch
    ~(let_map: Tnformula.let_map)
    ~(name: string)
    ~(label: string option)
    ~(args: (Tterm.TypedVar.t * Dom.tt option) list)
    ~(switch: Switch.t)
  : [`Let of Enfflash.let_def | `Table of Enfflash.table_def
    | `Agg of Enfflash.agg_let_def | `Top of Enfflash.top_let_def] =
  let columns =
    List.map args ~f:(fun (v, tt_opt) ->
        (san (fst v), match tt_opt with Some tt -> tt_to_ef tt | None -> tt_to_ef (snd v))) in
  let sanitized = sanitize_name name in
  match switch with
  | Switch.Now trigger ->
    (* Present-time predicate → let-def with a proper clause.
       Guard events (trace events, let-defs) become event patterns;
       non-event guards and the trigger filter become the clause filter. *)
    let clause = snow_trigger_to_clause ~let_map trigger in
    let has_patterns = not (List.is_empty clause.cl_patterns)
                       || not (List.for_all clause.cl_patterns
                                ~f:List.is_empty) in
    `Let Enfflash.{
        ld_label = label;
        ld_is_filter = not has_patterns;
        ld_name  = sanitized;
        ld_params = columns;
        ld_clause = clause;
      }
  | Switch.Once (i, trigger) ->
    (* Monotone accumulation: table with add, no remove.  A metric interval
       windows the table (evict tuples older than the upper bound, hold back
       tuples not yet within the lower bound). *)
    `Table Enfflash.{
        td_label = label;
        td_lagged = false;
        td_name = sanitized;
        td_columns = columns;
        td_add_clause = trigger_to_clause ~let_map trigger;
        td_remove_clause = None;
        td_window = interval_to_window i;
      }
  | Switch.Prev (i, trigger) ->
    (* Previous-step predicate: lagged table (updated after rules fire).  A
       metric interval bounds the gap to the previous time-point. *)
    `Table Enfflash.{
        td_label = label;
        td_lagged = true;
        td_name = sanitized;
        td_columns = columns;
        td_add_clause = trigger_to_clause ~let_map trigger;
        td_remove_clause = None;
        td_window = interval_to_window i;
      }
  | Switch.Since (i, left_trigger, right_trigger) ->
    (* Table with add (right trigger) and remove (negated left trigger).
       Since semantics: φ SINCE ψ — add row when ψ fires (right trigger),
       remove when ¬φ holds (the continuation condition is violated).
       The left trigger encodes φ; we always negate it for the remove
       clause.  simplify_neg handles both directions:
         ¬revoke(x) → revoke(x)   (double-neg elimination)
         C(2)       → ¬C(2)       (wrap in Neg)
       In the engine, if both add and remove match, add wins. *)
    let rec simplify_neg (f: Tyformula.t) : Tyformula.t =
      match f.form with
      | Neg g -> g    (* ¬¬φ → φ *)
      | TT -> { f with form = FF }  (* ¬⊤ → ⊥ *)
      | FF -> { f with form = TT }  (* ¬⊥ → ⊤ (drops a spurious `if !false`) *)
      | And (s, fs) -> { f with form = Or (s, List.map ~f:simplify_neg fs) }
      | Or (s, fs) -> { f with form = And (s, List.map ~f:simplify_neg fs) }
      | _ -> Tyformula.make_dummy (Tyformula.Neg f)
    in
    let neg_filter = simplify_neg left_trigger.filter in
    let neg_trigger = Trigger.{
        guards = left_trigger.guards;
        filter = neg_filter;
      } in
    let rm_clause = trigger_to_clause ~let_map neg_trigger in
    `Table Enfflash.{
        td_label = label;
        td_lagged = false;
        td_name = sanitized;
        td_columns = columns;
        td_add_clause = trigger_to_clause ~let_map right_trigger;
        td_remove_clause = Some rm_clause;
        td_window = interval_to_window i;
      }
  | Switch.Agg (ai, trigger) ->
    let agg_op = match ai.Nformula.ai_op with
      | Aggregation.ASum -> Enfflash.AggSum
      | Aggregation.AAvg -> Enfflash.AggAvg
      | Aggregation.AMed -> Enfflash.AggMed
      | Aggregation.ACnt -> Enfflash.AggCnt
      | Aggregation.AMin | Aggregation.AAssign -> Enfflash.AggMin
      | Aggregation.AMax -> Enfflash.AggMax
      | Aggregation.AStd -> Enfflash.AggStd in
    let (rv, rtt) = ai.ai_result in
    `Agg Enfflash.{
        agg_label = label;
        agg_name  = sanitized;
        agg_columns = columns;
        agg_op;
        agg_term = term_to_ef ai.ai_term;
        agg_groups = List.map ai.ai_groups ~f:(fun v -> san (fst v));
        agg_result = (san (fst rv), tt_to_ef rtt);
        agg_clause = trigger_to_clause ~let_map trigger;
        agg_incremental = Option.map ai.ai_incremental ~f:sanitize_name;
      }
  | Switch.Top (ti, trigger) ->
    `Top Enfflash.{
        top_label = label;
        top_name  = sanitized;
        top_columns = columns;
        top_fn = ti.Nformula.ti_fn;
        top_args = List.map ti.ti_args ~f:term_to_ef;
        top_groups = List.map ti.ti_groups ~f:(fun v -> san (fst v));
        top_results = List.map ti.ti_results ~f:(fun (v, tt) -> (san (fst v), tt_to_ef tt));
        top_clause = trigger_to_clause ~let_map trigger;
      }

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Compile enforcement clauses → rules                                        *)
(*                                                                            *)
(* Each clause { trigger; effects } becomes one rule per (effect, disjunct).  *)
(* Effects:                                                                   *)
(*   Predicate(name, args)      → rule +name(…)   (cause)                    *)
(*   Neg(Predicate(name, args)) → rule -name(…)   (suppress)                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Infer ef_ty from a typed term.  Variables carry Dom.tt; constants carry
   Dom.t from which we can read the type; for applications we default to EfInt. *)
let term_to_ef_ty (t: Tterm.t) : Enfflash.ef_ty =
  match t.trm with
  | Var (_, tt)  -> tt_to_ef tt
  | Const (Dom.Int _)   -> Enfflash.EfInt
  | Const (Dom.Str _)   -> Enfflash.EfStr
  | Const (Dom.Float _) -> Enfflash.EfFloat
  | App _        -> Enfflash.EfInt   (* conservative default *)
  | _            -> Enfflash.EfInt

(* Collect synthetic (Cau_/Sup_) event declarations from enforcement clauses.
   Scans both effects (cause/suppress actions) and trigger guards/filters
   for Predicate references whose sanitized name starts with "Cau_" or "Sup_".
   For each we record (sanitized_name, param_types).
   We keep only the first occurrence of each name. *)
let collect_synthetic_event_decls
    ~(existing: Enfflash.event_decl list)
    (clauses: Clause.t list)
  : Enfflash.event_decl list =
  let existing_names =
    Set.of_list (module String) (List.map existing ~f:(fun ed -> ed.Enfflash.ed_name)) in
  let seen = Hashtbl.create (module String) in
  let register_pred name args =
    let sname = sanitize_name name in
    if not (Set.mem existing_names sname)
    && not (Hashtbl.mem seen sname) then begin
      let param_types = List.map args ~f:term_to_ef_ty in
      Hashtbl.set seen ~key:sname ~data:param_types
    end
  in
  (* Recursively scan a formula for Predicate references starting with Cau_/Sup_ *)
  let rec scan_formula (f: Tyformula.t) =
    match f.form with
    | Predicate (name, args) ->
      let sname = sanitize_name name in
      if String.is_prefix sname ~prefix:"Cau_" || String.is_prefix sname ~prefix:"Sup_" then
        register_pred name args
    | Neg g -> scan_formula g
    | And (_, fs) | Or (_, fs) -> List.iter fs ~f:scan_formula
    | Imp (_, f, g) -> scan_formula f; scan_formula g
    | Exists (_, f) | Forall (_, f) -> scan_formula f
    | Eventually (_, f) | Always (_, f) | Next (_, f) -> scan_formula f
    | _ -> ()
  in
  List.iter clauses ~f:(fun clause ->
      (* Scan effects *)
      List.iter clause.effects ~f:(fun effect ->
          let name_args_opt = match effect with
            | Cau (name, args) -> Some (name, args)
            | Sup (name, args) -> Some (name, args)
            | EventuallyCau (_, name, args) -> Some (name, args)
            | EventuallySup (_, name, args) -> Some (name, args)
            | NextCau (_, name, args) -> Some (name, args)
            | NextSup (_, name, args) -> Some (name, args)
            | _ -> None
          in
          Option.iter name_args_opt ~f:(fun (name, args) ->
              register_pred name args));
      (* Scan trigger guards *)
      List.iter clause.trigger.guards ~f:(fun guard_conj ->
          List.iter guard_conj ~f:scan_formula);
      (* Scan trigger filter *)
      scan_formula clause.trigger.filter);
  Hashtbl.fold seen ~init:[] ~f:(fun ~key ~data acc ->
      Enfflash.{ ed_name = key; ed_param_types = data } :: acc)
  |> List.sort ~compare:(fun a b -> String.compare a.Enfflash.ed_name b.Enfflash.ed_name)

let interval_to_delay (i: Interval.t) : int option =
  match Interval.right i with
  | Some ts -> Some (Time.Span.min_seconds ts)
  | None    -> None

(* Extract a label from an effect predicate name, if it encodes a label.
   Names like "Cau_Label1:Main rule" or "Sup_Label2:Foo" carry labels
   that were introduced by the enforcement typing. *)
let extract_label_from_effect_name name =
  let try_strip prefix =
    if String.is_prefix name ~prefix then
      Some (String.drop_prefix name (String.length prefix))
    else None
  in
  let suffix = match try_strip "Cau_" with
    | Some s -> Some s
    | None -> try_strip "Sup_"
  in
  match suffix with
  | Some s -> fst (parse_label_name s)
  | None -> None

let compile_clause_to_rules ~(let_map: Tnformula.let_map) (clause: Clause.t) : Enfflash.rule_def list =
  let trigger_clause = trigger_to_clause ~let_map clause.trigger in
  (* Source label propagated from a [Label] wrapper (innermost first).  Takes
     precedence over any label encoded in a synthetic effect name. *)
  let clause_label = match clause.Clause.labels with
    | [] -> None
    | ls -> Some (String.concat ~sep:", " ls) in
  let label_of name = match clause_label with
    | Some _ -> clause_label
    | None   -> extract_label_from_effect_name name in
  let effects_info =
    List.filter_map clause.effects ~f:(fun effect ->
        match effect with
        | Cau (name, args) ->
          let params = List.map args ~f:term_to_ef in
          let label = label_of name in
          Some (sanitize_name name, params, Enfflash.RCause, None, None, label)
        | Sup (name, args) ->
          let params = List.map args ~f:term_to_ef in
          let label = label_of name in
          Some (sanitize_name name, params, Enfflash.RSuppress, None, None, label)
        | EventuallyCau (i, name, args) ->
          let params = List.map args ~f:term_to_ef in
          let label = label_of name in
          Some (sanitize_name name, params, Enfflash.RCause, interval_to_delay i, None, label)
        | EventuallySup (i, name, args) ->
          let params = List.map args ~f:term_to_ef in
          let label = label_of name in
          Some (sanitize_name name, params, Enfflash.RSuppress, interval_to_delay i, None, label)
        | NextCau (itvs, name, args) ->
          (* A chain of n nested NEXT operators fires the obligation n real
             time-points ahead; [itvs] holds one interval per NEXT, so the
             time-point offset is its length (≥ 1). *)
          let params = List.map args ~f:term_to_ef in
          let label = label_of name in
          Some (sanitize_name name, params, Enfflash.RCause, None, Some (List.length itvs), label)
        | NextSup (itvs, name, args) ->
          let params = List.map args ~f:term_to_ef in
          let label = label_of name in
          Some (sanitize_name name, params, Enfflash.RSuppress, None, Some (List.length itvs), label)
        | _ -> None) in
  List.map effects_info ~f:(fun (ev_name, params, action, delay, tp_offset, label) ->
      Enfflash.{
        rd_label      = label;
        rd_event      = ev_name;
        rd_params     = params;
        rd_action     = action;
        rd_delay      = delay;
        rd_tp_offset  = tp_offset;
        rd_trigger    = trigger_clause;
        rd_validate   = None;
      })

(* Fix default Int(0) values in rule params when the target event expects a
   different type.  E.g., Contains(str,str) with args [0; 0] → [""; ""].     *)
let fix_rule_defaults
    (event_decl_map: (string, Enfflash.ef_ty list) Hashtbl.t)
    (rules: Enfflash.rule_def list)
  : Enfflash.rule_def list =
  let default_for_ty : Enfflash.ef_ty -> Enfflash.ef_value = function
    | EfInt   -> EfVInt 0
    | EfStr   -> EfVStr ""
    | EfFloat -> EfVFloat 0.0
  in
  List.map rules ~f:(fun rule ->
      match Hashtbl.find event_decl_map rule.rd_event with
      | Some param_types when List.length param_types = List.length rule.rd_params ->
        let rd_params =
          List.map2_exn rule.rd_params param_types ~f:(fun te expected_ty ->
              match te with
              | Enfflash.TELit (EfVInt 0) when not (Poly.equal expected_ty Enfflash.EfInt) ->
                Enfflash.TELit (default_for_ty expected_ty)
              | _ -> te) in
        { rule with rd_params }
      | _ -> rule)

(* Reorder guards *)
let reorder_guard_pattern_list (conj: Enfflash.guard_pattern list) =
    let is_once_since = function
      | Enfflash.GEvent { ep_name; _ } ->
        String.is_prefix ep_name ~prefix:"Once"
        || String.is_prefix ep_name ~prefix:"Since"
      | _ -> false
    in
    let rest, once_since = List.partition_tf conj ~f:(fun gp -> not (is_once_since gp)) in
    let r = rest @ once_since in
    (*print_endline (Printf.sprintf "reorder([%s]) = [%s]"
                     (String.concat ~sep:", " (List.map ~f:Enfflash.guard_pattern_to_string conj))
                     (String.concat ~sep:", " (List.map ~f:Enfflash.guard_pattern_to_string r)));*)
    r

let reorder_clause (clause: Enfflash.clause) =
  { clause with cl_patterns = List.map ~f:reorder_guard_pattern_list clause.cl_patterns }

let reorder_let_def (let_def: Enfflash.let_def) =
  { let_def with ld_clause = reorder_clause let_def.ld_clause }

let reorder_table_def (table_def: Enfflash.table_def) =
  { table_def with td_add_clause = reorder_clause table_def.td_add_clause;
                   td_remove_clause = Option.map ~f:reorder_clause table_def.td_remove_clause }

let reorder_rule_def (rule_def: Enfflash.rule_def) =
  { rule_def with rd_trigger = reorder_clause rule_def.rd_trigger }

let reorder_agg_let_def (ad: Enfflash.agg_let_def) =
  { ad with agg_clause = reorder_clause ad.agg_clause }

let reorder_top_let_def (td: Enfflash.top_let_def) =
  { td with top_clause = reorder_clause td.top_clause }

let reorder_item = function
  | Enfflash.PiLet let_def   -> Enfflash.PiLet (reorder_let_def let_def)
  | PiTable        table_def -> PiTable        (reorder_table_def table_def)
  | PiAgg          ad        -> PiAgg          (reorder_agg_let_def ad)
  | PiTop          td        -> PiTop          (reorder_top_let_def td)

let reorder_program (prog: Enfflash.program) =
  { prog with pg_let_defs = List.map ~f:reorder_let_def   prog.pg_let_defs;
              pg_agg_lets = List.map ~f:reorder_agg_let_def prog.pg_agg_lets;
              pg_top_lets = List.map ~f:reorder_top_let_def prog.pg_top_lets;
              pg_tables   = List.map ~f:reorder_table_def prog.pg_tables;
              pg_rules    = List.map ~f:reorder_rule_def  prog.pg_rules;
              pg_items    = List.map ~f:reorder_item      prog.pg_items }
              

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Section computation via the CDG algorithm from splitting.ml                *)
(*                                                                             *)
(* Builds the Clause Dependency Graph on [tnf] (using the proper monotonicity *)
(* analysis from Splitting.EventSplit.build_cdg), computes its SCCs, and maps *)
(* each SCC to the rule indices (into [prog.pg_rules]) produced by the clauses*)
(* in that SCC.  Returns sections in dependency (topological) order.          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

let compute_sections ~drop_monotone (tnf : Tnformula.t)
    (clause_to_rule_indices : int list array)
    : (bool * int list) list list * (int * int) list =
  let lets, let_ctxt_mon, let_ctxt_anti_mon = Splitting.maps_of_lets tnf.let_map in
  let clauses = Array.of_list tnf.clauses in
  let n = Array.length clauses in
  let g = Splitting.EventSplit.build_cdg ~filtered:drop_monotone
      ~lets ~let_ctxt_mon ~let_ctxt_anti_mon clauses in
  let clause_to_sec = Array.create ~len:n (-1) in
  let gi = ref 0 in
  let sections =
    Graph_util.sccs_in_waves g
    |> List.filter_map ~f:(fun wave ->
        let scc_entries =
          List.filter_map wave ~f:(fun (recursive, clause_indices) ->
              let rule_indices =
                List.concat_map clause_indices ~f:(fun i -> clause_to_rule_indices.(i)) in
              if List.is_empty rule_indices then None
              else Some (recursive, clause_indices, rule_indices)) in
        if List.is_empty scc_entries then None
        else begin
          (* Merge all once SCCs into one section (they are CDG-independent
             within a wave).  Assign global section indices in output order:
             once section first (if any), then each fixpoint section. *)
          let once_clauses =
            List.concat_map scc_entries ~f:(fun (r, cis, _) -> if r then [] else cis) in
          let once_rules =
            List.concat_map scc_entries ~f:(fun (r, _, ris) -> if r then [] else ris) in
          let once_sec = match once_rules with
            | [] -> []
            | _  ->
              let sec = !gi in Int.incr gi;
              List.iter once_clauses ~f:(fun ci -> clause_to_sec.(ci) <- sec);
              [(false, once_rules)] in
          let fix_secs =
            List.filter_map scc_entries ~f:(fun (r, cis, ris) ->
                if not r then None
                else begin
                  let sec = !gi in Int.incr gi;
                  List.iter cis ~f:(fun ci -> clause_to_sec.(ci) <- sec);
                  Some (true, ris)
                end) in
          Some (once_sec @ fix_secs)
        end) in
  let edges =
    Graph_util.Graph.edges g
    |> List.filter_map ~f:(fun (u, _, v) ->
        let a = clause_to_sec.(u) and b = clause_to_sec.(v) in
        if a >= 0 && b >= 0 && a <> b then Some (a, b) else None)
    |> List.dedup_and_sort ~compare:[%compare: int * int] in
  (sections, edges)

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Top-level compilation                                                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)


let compile
    ?(drop_monotone: bool = false)
    ~(py_source: string option)
    (r: Tnformula.t)
  : Enfflash.program =
  let let_map = r.let_map in
  let lets    = List.map r.let_names ~f:(Map.find_exn let_map) in
  let clauses = r.clauses in
  let event_decls = compile_event_decls () in
  let fun_decls = compile_fun_decls ~py_source () in
  let let_defs  = ref [] in
  let tables    = ref [] in
  let agg_lets  = ref [] in
  let top_lets  = ref [] in
  let items     = ref [] in
  (* ── Process each compiled let ────────────────────────────────────────── *)
  List.iter lets ~f:(fun (cl : Tnformula.let_def) ->
      let name = cl.name and args = cl.args
      and body_pos = cl.body_pos and body_neg_opt = cl.body_neg_opt
      and filter_trigger_opt = cl.filter_trigger_opt in
      let label, _sanitized = parse_label_name name in
      let emit_variant vname vlabel switch_opt fallback_body =
        match switch_opt with
        | Some switch ->
          (match compile_let_from_switch ~let_map ~name:vname ~label:vlabel ~args ~switch with
           | `Let ld  -> let_defs := ld :: !let_defs; items := Enfflash.PiLet ld :: !items
           | `Table td -> tables := td :: !tables; items := Enfflash.PiTable td :: !items
           | `Agg ad -> agg_lets := ad :: !agg_lets; items := Enfflash.PiAgg ad :: !items
           | `Top td -> top_lets := td :: !top_lets; items := Enfflash.PiTop td :: !items)
        | None ->
          (* No switch info available: compile the body formula as a let definition.
             It is a filter let unless the body references trace events. *)
          let columns =
            List.map args ~f:(fun (v, tt_opt) ->
                (san (fst v), match tt_opt with Some tt -> tt_to_ef tt | None -> tt_to_ef (snd v))) in
          let body = typed_formula_to_filter fallback_body in
          let ld = Enfflash.{
              ld_label  = vlabel;
              ld_is_filter = true;(*not (filter_has_event_ref body);*)
              ld_name   = sanitize_name vname;
              ld_params = columns;
              ld_clause = trigger_to_clause ~let_map (Option.value_exn filter_trigger_opt)
            } in
          let_defs := ld :: !let_defs;
          items := Enfflash.PiLet ld :: !items
      in
      let def_opt = Map.find let_map name in
      match body_neg_opt with
      | Some body_neg ->
        (* Both positive and negative variants needed.
           Also emit the original name as an alias for _pos so that
           references to the unsuffixed name (e.g., inside _neg body) resolve. *)
        emit_variant
          name label
          (Option.bind def_opt ~f:(fun (d: Tnformula.let_def) -> d.switch_pos_opt))
          body_pos;
        emit_variant
          (name ^ "_pos") label
          (Option.bind def_opt ~f:(fun (d: Tnformula.let_def) -> d.switch_pos_opt))
          body_pos;
        emit_variant
          (name ^ "_neg") label
          (Option.bind def_opt ~f:(fun (d: Tnformula.let_def) -> d.switch_neg_opt))
          body_neg
      | None ->
        emit_variant
          name label
          (Option.bind def_opt ~f:(fun (d: Tnformula.let_def) -> d.switch_pos_opt))
          body_pos);
  (* ── Process enforcement clauses, tracking clause→rule-index mapping ─── *)
  let rules_per_clause = List.map clauses ~f:(compile_clause_to_rules ~let_map) in
  let rules = List.concat rules_per_clause in
  let clause_to_rule_indices =
    let idx = ref 0 in
    Array.of_list (List.map rules_per_clause ~f:(fun rs ->
        let start = !idx in
        idx := !idx + List.length rs;
        List.range start !idx)) in
  (* ── Add synthetic event declarations for Cau_/Sup_ events ──────────── *)
  let synthetic_decls = collect_synthetic_event_decls ~existing:event_decls clauses in
  let all_event_decls = event_decls @ synthetic_decls in
  (* ── Fix default Int(0) in rule params when event expects str/float ─── *)
  let ed_map = Hashtbl.create (module String) in
  List.iter all_event_decls ~f:(fun ed ->
      Hashtbl.set ed_map ~key:ed.Enfflash.ed_name ~data:ed.Enfflash.ed_param_types);
  let rules = fix_rule_defaults ed_map rules in
  (* ── Add !T(args) guards to Cau_T rules for precision ────────────────── *)
  (* When the enforcement typing produces a rule +Cau_T(args) for a table
     or let-definition T, the rule's trigger may not include the guard
     ¬T(args).  Without it, the rule fires for every matching event even if
     T is already satisfied, leading to imprecise (redundant) causation.
     For tables (SOnce), the guard persists across time-points.
     For let-definitions, the guard prevents redundant iterations within
     a single fixpoint.  We inject the guard here. *)
  let table_names =
    Set.of_list (module String)
      (List.map (List.rev !tables) ~f:(fun td -> td.Enfflash.td_name)) in
  let let_def_names =
    Set.of_list (module String)
      (List.map (List.rev !let_defs) ~f:(fun ld -> ld.Enfflash.ld_name)) in
  let known_names = Set.union table_names let_def_names in
  let rules =
    List.map rules ~f:(fun (rule : Enfflash.rule_def) ->
        match rule.rd_action with
        | Enfflash.RCause
          when String.is_prefix rule.rd_event ~prefix:"Cau_" ->
          let target_name = String.drop_prefix rule.rd_event 4 in
          if Set.mem known_names target_name then
            let guard = Enfflash.FNot (
                Enfflash.FTableLookup (target_name, rule.rd_params)) in
            let new_filter = match rule.rd_trigger.cl_filter with
              | Enfflash.FBoolLit true -> guard
              | f -> Enfflash.FAnd (f, guard) in
            { rule with rd_trigger =
                          { rule.rd_trigger with cl_filter = new_filter } }
          else rule
        | _ -> rule) in
  let agg_lets = List.rev !agg_lets in
  let top_lets = List.rev !top_lets in
  let tfun_decls =
    compile_tfun_decls ~py_source (List.map top_lets ~f:(fun td -> td.Enfflash.top_fn)) in
  let prog =
    Enfflash.{
      pg_event_decls = all_event_decls;
      pg_py_preamble = (match py_source with Some src -> python_preamble src | None -> "");
      pg_fun_decls   = fun_decls;
      pg_tfun_decls  = tfun_decls;
      pg_let_defs    = List.rev !let_defs;
      pg_agg_lets    = agg_lets;
      pg_top_lets    = top_lets;
      pg_tables      = List.rev !tables;
      pg_rules       = rules;
      pg_items       = List.rev !items;
      pg_sections           = [];
      pg_sections_drop      = [];
      pg_section_edges      = [];
      pg_section_edges_drop = [];
    } in
  let prog = Enfflash.compress_alias_lets prog in
  let prog = reorder_program prog in
  let secs, edges           = compute_sections ~drop_monotone:false r clause_to_rule_indices in
  let secs_drop, edges_drop = compute_sections ~drop_monotone:true  r clause_to_rule_indices in
  { prog with
    pg_sections           = secs;
    pg_sections_drop      = secs_drop;
    pg_section_edges      = edges;
    pg_section_edges_drop = edges_drop;
  }

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Convenience: compile and write to file                                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

let compile_and_write
    ~(filename: string)
    ~(py_source: string option)
    (r: Tnformula.t)
  =
  let program = compile ~py_source r in
  Enfflash.write_program_to_file ~filename program;
  program

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Parallel splitting: multi-program compilation                               *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(** Info about one sub-enforcer produced by [split_and_compile]. *)
type split_group_info = {
  sgi_program_file   : string;
  (** Predicate names that must be forwarded to this sub-enforcer. *)
  sgi_trigger_events : string list;
}

(** Compile [tnf] into [k] sub-programs, one per split group.
    Writes:
      [output_dir/base_name_subN.ef]           for each group N
      [output_dir/base_name_manifest.json]     machine-readable index

    When the split yields only one group (no useful split), a single file
    [output_dir/base_name.ef] is written instead.

    [filtered] and [aggressivity] are forwarded to [Splitting.split]. *)
let split_and_compile
    ?(filtered    = false)
    ?(aggressivity = 0)
    ?(num_groups   = 0)
    ?(data_axes : Splitting.DataSplit.data_axis list = [])
    ?(broadcast_events : string list = [])
    ~(py_source   : string option)
    ~(output_dir  : string)
    ~(base_name   : string)
    (tnf : Tnformula.t)
  : split_group_info list =
  let groups      = Splitting.EventSplit.split ~filtered ~aggressivity ~num_groups tnf in
  let clauses_arr = Array.of_list tnf.clauses in
  (* Build the let-context predicate map once, shared across all groups. *)
  let pred_map, _, _ = Splitting.maps_of_lets tnf.let_map in
  let trigger_events_of indices =
    Set.to_list (
      Set.union_list (module String)
        (List.map indices ~f:(fun i ->
           Clause.trigger_predicates ~lets:pred_map clauses_arr.(i))))
  in
  (* One [.ef] per *event* group; data shards reuse the same program. *)
  let compile_group idx indices =
    let filename =
      if List.length groups = 1 then
        Filename.concat output_dir (base_name ^ ".ef")
      else
        Filename.concat output_dir
          (Printf.sprintf "%s_sub%d.ef" base_name idx) in
    let sub_clauses = List.map indices ~f:(fun i -> clauses_arr.(i)) in
    let sub_tnf = Tnformula.clean_unused_lets { tnf with Tnformula.clauses = sub_clauses } in
    let _ = compile_and_write ~filename ~py_source sub_tnf in
    { sgi_program_file   = filename;
      sgi_trigger_events = trigger_events_of indices }
  in
  let event_infos = List.mapi groups ~f:compile_group in

  (* ---- JSON rendering ---- *)
  let json_str_list xs =
    String.concat ~sep:", " (List.map xs ~f:(fun s -> Printf.sprintf "\"%s\"" s)) in
  (* All bucket tuples (one bucket per axis) — the Cartesian product. *)
  let bucket_tuples =
    List.fold_right data_axes ~init:[[]] ~f:(fun axis acc ->
        List.concat_map (List.range 0 axis.Splitting.DataSplit.da_modulo) ~f:(fun b ->
            List.map acc ~f:(fun t -> b :: t))) in
  let data_routes_json tuple =
    List.map2_exn data_axes tuple ~f:(fun axis b ->
        let fields =
          String.concat ~sep:", "
            (List.map axis.Splitting.DataSplit.da_fields ~f:(fun (ev, i) ->
                 Printf.sprintf "\"%s\": %d" ev i)) in
        Printf.sprintf "{ \"modulo\": %d, \"bucket\": %d, \"fields\": { %s } }"
          axis.Splitting.DataSplit.da_modulo b fields)
    |> String.concat ~sep:", " in
  let group_json sgi tuple =
    let evts = json_str_list sgi.sgi_trigger_events in
    if List.is_empty data_axes then
      Printf.sprintf
        "    { \"program\": \"%s\", \"trigger_events\": [%s] }"
        sgi.sgi_program_file evts
    else
      Printf.sprintf
        "    { \"program\": \"%s\", \"trigger_events\": [%s], \"data_routes\": [%s], \"broadcast_events\": [%s] }"
        sgi.sgi_program_file evts (data_routes_json tuple) (json_str_list broadcast_events)
  in
  (* Manifest = event groups × data shards. *)
  let entries =
    List.concat_map event_infos ~f:(fun sgi ->
        List.map bucket_tuples ~f:(fun tuple -> sgi, tuple)) in
  let manifest_file =
    Filename.concat output_dir (base_name ^ "_manifest.json") in
  let manifest =
    Printf.sprintf "{\n  \"groups\": [\n%s\n  ]\n}\n"
      (String.concat ~sep:",\n"
         (List.map entries ~f:(fun (sgi, tuple) -> group_json sgi tuple))) in
  Stdio.Out_channel.write_all manifest_file ~data:manifest;
  List.map entries ~f:fst

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Pipeline orchestration                                                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Shared pipeline front-end: parse → normalise → extract → Tnformula.t *)
let extract_tnf
    ~(b: Time.Span.s)
    ?(verbose: bool = true)
    ?(moderate: bool = true)
    (sformula: Sformula.t)
  : Tnformula.t =
  let formula = Formula.init sformula in
  let f       = Formula.convert_vars formula in
  let tyf     = Tyformula.of_formula' f in
  let lf      = Lformula.make ~moderate tyf in
  let nf      = Enforceability.enforce ~verbose lf b in
  Extraction.extract ~orig:tyf nf

(* Data-splitting analysis: build the base-event field graph and print its
   connected components (the available data-parallel axes) plus the
   un-partitionable (tainted) fields. Runs only the typed front-end (no
   enforceability/extraction needed). *)
let analyze_data (sformula : Sformula.t) : unit =
  let f   = Formula.convert_vars (Formula.init sformula) in
  let tyf = Tyformula.of_formula' f in
  let comps, tainted = Splitting.DataSplit.analyze tyf in
  Stdio.printf "Data-split analysis: %d connected component(s)\n" (List.length comps);
  List.iteri comps ~f:(fun i fields ->
    Stdio.printf "  [%d] (%d field%s) %s\n"
      i (List.length fields) (if List.length fields = 1 then "" else "s")
      (String.concat ~sep:", " fields));
  if not (List.is_empty tainted) then
    Stdio.printf "Un-partitionable (tainted) fields: %s\n"
      (String.concat ~sep:", " tainted)

(* Build the Event Dependency Graph for the (accepted) policy and return it as
   Graphviz DOT.  Prints a short SCC summary to stderr.  Runs the full
   enforceability front-end, so it only succeeds for enforceable policies. *)
let edg_dot ?(moderate : bool = true) ~(b : Time.Span.s) (sformula : Sformula.t) : string =
  let tnf = extract_tnf ~b ~verbose:false ~moderate sformula in
  let lets, _, _ = Splitting.maps_of_lets tnf.Tnformula.let_map in
  let edg = Edg.build ~lets tnf.Tnformula.clauses in
  Stdio.eprintf "%s" (Edg.summary_to_string edg);
  Edg.to_dot edg

(* Write a full bundle of EDG visualisations into [dir]: the full graph, the
   focused condensation, and one graph per recursive SCC.  Each `.dot` is also
   rendered to `.svg` via Graphviz `dot` when it is on PATH (best-effort). *)
let edg_dir ?(moderate : bool = true) ?(py_source : string option = None)
    ?(drop_monotone : bool = false)
    ~(b : Time.Span.s) (sformula : Sformula.t) (dir : string) : unit =
  let tnf = extract_tnf ~b ~verbose:false ~moderate sformula in
  let lets, _, _ = Splitting.maps_of_lets tnf.Tnformula.let_map in
  let edg = Edg.build ~lets tnf.Tnformula.clauses in
  ignore (Stdlib.Sys.command (Printf.sprintf "mkdir -p %s" (Filename.quote dir)));
  (* also emit the compiled enforcement program (.ef) for this policy *)
  let program = compile ~drop_monotone ~py_source tnf in
  Enfflash.write_program_to_file ~filename:(Filename.concat dir "policy.ef") program;
  let have_dot = Int.equal 0 (Stdlib.Sys.command "command -v dot >/dev/null 2>&1") in
  (* Always write the .dot; only render to SVG when the graph is small enough to
     be readable (≤ this many nodes).  Laying out the full graphs and the big
     fixpoint sections with `dot` is slow and yields an unreadable hairball, so
     those are left as .dot for manual/zoomed rendering. *)
  let render_node_cap = 260 in
  let emit name content =
    let path = Filename.concat dir name in
    Stdio.Out_channel.write_all path ~data:content;
    (* node lines carry "[label=" but not "->" (edge lines do) *)
    let nodes =
      List.count (String.split_lines content)
        ~f:(fun l -> String.is_substring l ~substring:"[label="
                     && not (String.is_substring l ~substring:"->")) in
    let svg = (Filename.chop_extension path) ^ ".svg" in
    let q = Filename.quote in
    if have_dot then begin
      if nodes <= render_node_cap then
        (* small graphs: hierarchical layout (readable) *)
        ignore (Stdlib.Sys.command
                  (Printf.sprintf "timeout 90 dot -Tsvg %s -o %s 2>/dev/null" (q path) (q svg)))
      else if String.is_substring name ~substring:"focus" then
        (* the focused condensations are the overview to keep; when they are
           large (e.g. after -drop-monotone-deps) dot's hierarchical layout is
           too slow, so render them with the scalable force-directed engine. *)
        ignore (Stdlib.Sys.command
                  (Printf.sprintf "sfdp -Tsvg -Goverlap=prism %s -o %s 2>/dev/null" (q path) (q svg)))
      (* else: the full graphs / big fixpoint sections stay .dot-only (hairballs) *)
    end in
  emit "edg.dot"   (Edg.to_dot edg);
  emit "focus.dot" (Edg.focused_dot edg);
  List.iter (Edg.cyclic_sccs edg) ~f:(fun s ->
      emit (Printf.sprintf "scc_%d.dot" s) (Edg.scc_subgraph_dot edg s));
  (* Rule Dependency Graph (the graph the runtime sections are built from):
     full RDG, focused condensation (= the section dependency DAG), and one
     expanded graph per recursive (fixpoint) section. *)
  List.iter (Enfflash.rdg_export ~drop_monotone program) ~f:(fun (name, content) -> emit name content);
  Stdio.eprintf "%s" (Edg.summary_to_string edg);
  Stdio.eprintf "[enfguard] EDG graphs + policy.ef written to %s/ (%s)\n" dir
    (if have_dot then "DOT + rendered SVG" else "DOT only — install graphviz for SVG")

let run
    ~(py_source: string option)
    ~(b: Time.Span.s)
    ?(verbose: bool = true)
    ?(moderate: bool = true)
    ?(drop_monotone: bool = false)
    ~(filename: string)
    (sformula: Sformula.t)
  : Enfflash.program =
  let tnf     = extract_tnf ~b ~verbose ~moderate sformula in
  let program = compile ~drop_monotone ~py_source tnf in
  Enfflash.write_program_to_file ~filename program;
  program

(** Full pipeline for the parallel splitting variant.
    Returns the path to the written manifest and the list of group infos. *)
let run_parallel
    ?(filtered    = false)
    ?(aggressivity = 0)
    ?(num_groups   = 0)
    ?(data_groups : (string * int) list = [])
    ~(py_source   : string option)
    ~(b           : Time.Span.s)
    ?(verbose     : bool = true)
    ?(moderate    : bool = true)
    ~(output_dir  : string)
    ~(base_name   : string)
    (sformula: Sformula.t)
  : string * split_group_info list =
  let tnf        = extract_tnf ~b ~verbose ~moderate sformula in
  (* Resolve data-split selections (if any) against the typed formula. *)
  let data_axes, broadcast_events =
    if List.is_empty data_groups then [], []
    else
      let tyf = Tyformula.of_formula' (Formula.convert_vars (Formula.init sformula)) in
      Splitting.DataSplit.resolve_selection tyf data_groups in
  (* When data splitting is requested but no event split was asked for, keep the
     whole policy as a single event group (otherwise the default largest-covering
     would multiply the data shards by ~every clause). *)
  let num_groups =
    if (not (List.is_empty data_axes)) && num_groups = 0 && aggressivity = 0
    then 1 else num_groups in
  let group_infos =
    split_and_compile ~filtered ~aggressivity ~num_groups ~data_axes ~broadcast_events
      ~py_source ~output_dir ~base_name tnf in
  let manifest   = Filename.concat output_dir (base_name ^ "_manifest.json") in
  manifest, group_infos

