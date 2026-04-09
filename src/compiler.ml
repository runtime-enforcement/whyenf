(* Compiler from MFOTL enforcement typing intermediate representation
   (the lets and clauses from MFOTL.ml do_type) into an Enfflash.program.

   Data flow:
     MFOTL.do_type produces:
       lets   : (name * enftype option * args * body_pos * body_neg_opt * clauses_opt) list
       clauses: Formula.clause list   (raw, before compile_clause)
       m      : Formula.let_map       (switch + enforcement info per let)

     This module converts that into Enfflash.program, which can be serialized
     to the .ef text format understood by the enfflash engine.

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

(* Access the enforcement types (trigger, clause, switch, let_def, let_map)
   which are defined inside MFOTL_Enforceability(Sig). *)
module Enforcement = Tyformula.MFOTL_Enforceability(Sig)

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
let get_inlineable_trigger (let_map: Enforcement.let_map) (name: string)
  : ((Tterm.TypedVar.t * Dom.tt option) list * Enforcement.trigger) option =
  match Map.find let_map name with
  | Some def ->
    (match def.switch_pos_opt with
     | Some (Enforcement.SNow trigger) when not (List.is_empty trigger.guards) ->
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
    (let_map: Enforcement.let_map)
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
    ~(let_map: Enforcement.let_map)
    (trigger: Enforcement.trigger)
  : Enfflash.clause =
  Enfflash.{ cl_patterns = decompose_guard_disj trigger.guards;
             cl_filter   = formula_to_filter trigger.filter }


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
let parse_python_functions (py_source: string) : (string, string, String.comparator_witness) Map.t =
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
        | Some (fname, _) ->
          let fname = String.strip fname in
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
          collect_functions remaining (Map.set acc ~key:fname ~data:body)
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
               let param_names = List.map func.arg_ttts ~f:fst in
               let param_types = List.map func.arg_ttts ~f:(fun (_, ttt) -> ttt_to_ef ttt) in
               let ret_type = match func.ret_ttts with
                 | [ttt] -> ttt_to_ef ttt
                 | _ -> Enfflash.EfInt in
               let body = match Map.find py_bodies key with
                 | Some b -> b
                 | None ->
                   (* Generate a fallback body based on the function signature *)
                   Printf.sprintf "return %s" (String.concat ~sep:" + " (
                       match param_names with
                       | [] -> ["0"]
                       | [p] -> [p]
                       | _ -> [List.hd_exn param_names])) in
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

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Compile let definitions using switch structures from the let_map           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Check whether a compiled filter_expr references any trace event.
   A let whose body contains event references is "sufficiently guarded"
   and can itself serve as a guard; otherwise it is a "filter let". *)
let rec filter_has_event_ref (f: Enfflash.filter_expr) : bool =
  match f with
  | FBoolLit _ -> false
  | FTableLookup (name, _) ->
    (match Hashtbl.find Sig.table name with
     | Some (Sig.Pred p) -> Sig.equal_pred_kind p.kind Sig.Trace
     | _ -> false)
  | FCompare _ -> false
  | FAnd (a, b) | FOr (a, b) -> filter_has_event_ref a || filter_has_event_ref b
  | FNot a -> filter_has_event_ref a

let compile_let_from_switch
    ~(let_map: Enforcement.let_map)
    ~(name: string)
    ~(label: string option)
    ~(args: (Tterm.TypedVar.t * Dom.tt option) list)
    ~(switch: Enforcement.switch)
  : [`Let of Enfflash.let_def | `Table of Enfflash.table_def] =
  let columns =
    List.map args ~f:(fun (v, tt_opt) ->
        (san (fst v), match tt_opt with Some tt -> tt_to_ef tt | None -> tt_to_ef (snd v))) in
  let sanitized = sanitize_name name in
  match switch with
  | SNow trigger ->
    (* Present-time predicate → let-def.
       We incorporate BOTH the guards (DNF of event/predicate lookups)
       and the filter into the let body.  This way the engine can
       recursively evaluate the body — iterating events and other
       let-defs to bind free variables — while preserving fixpoint
       semantics (let-defs are re-evaluated each time they are
       referenced, unlike tables which are snapshot-based). *)
    let base_filter = formula_to_filter trigger.filter in
    (* Convert guard DNF into a filter expression:
       guards = [[g1;g2]; [g3;g4]] → (g1 ∧ g2) ∨ (g3 ∧ g4) *)
    let guard_filter =
      match trigger.guards with
      | [] -> Enfflash.FBoolLit true
      | disjuncts ->
        let conj_to_filter conj =
          let parts = List.filter_map conj ~f:(fun g ->
              let f = formula_to_filter g in
              match f with Enfflash.FBoolLit true -> None | _ -> Some f) in
          merge_filters parts in
        let disj_filters = List.map disjuncts ~f:conj_to_filter in
        (match disj_filters with
         | []       -> Enfflash.FBoolLit true
         | [f]      -> f
         | f :: rest ->
           List.fold_left rest ~init:f
             ~f:(fun acc g -> Enfflash.FOr (acc, g)))
    in
    let body = match guard_filter, base_filter with
      | Enfflash.FBoolLit true, f -> f
      | f, Enfflash.FBoolLit true -> f
      | g, f -> Enfflash.FAnd (g, f) in
    `Let Enfflash.{
        ld_label = label;
        ld_is_filter = not (filter_has_event_ref body);
        ld_name  = sanitized;
        ld_params = columns;
        ld_body  = body;
      }
  | SOnce trigger ->
    (* Monotone accumulation: table with add, no remove. *)
    `Table Enfflash.{
        td_label = label;
        td_lagged = false;
        td_name = sanitized;
        td_columns = columns;
        td_add_clause = trigger_to_clause ~let_map trigger;
        td_remove_clause = None;
      }
  | SPrev trigger ->
    (* Previous-step predicate: lagged table (updated after rules fire). *)
    `Table Enfflash.{
        td_label = label;
        td_lagged = true;
        td_name = sanitized;
        td_columns = columns;
        td_add_clause = trigger_to_clause ~let_map trigger;
        td_remove_clause = None;
      }
  | SSince (left_trigger, right_trigger) ->
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
      | And (s, fs) -> { f with form = Or (s, List.map ~f:simplify_neg fs) }
      | Or (s, fs) -> { f with form = And (s, List.map ~f:simplify_neg fs) }
      | _ -> Tyformula.make_dummy (Tyformula.Neg f)
    in
    let neg_filter = simplify_neg left_trigger.filter in
    let neg_trigger = Enforcement.{
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
    (clauses: Enforcement.clause list)
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
          let name_args_opt = match effect.form with
            | Predicate (name, args)                     -> Some (name, args)
            | Neg { form = Predicate (name, args); _ }   -> Some (name, args)
            | Eventually (_, { form = Predicate (name, args); _ }) -> Some (name, args)
            | Eventually (_, { form = Neg { form = Predicate (name, args); _ }; _ }) -> Some (name, args)
            | Next (_, { form = Predicate (name, args); _ }) -> Some (name, args)
            | Next (_, { form = Neg { form = Predicate (name, args); _ }; _ }) -> Some (name, args)
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

let compile_clause_to_rules ~(let_map: Enforcement.let_map) (clause: Enforcement.clause) : Enfflash.rule_def list =
  let trigger_clause = trigger_to_clause ~let_map clause.trigger in
  let effects_info =
    List.filter_map clause.effects ~f:(fun effect ->
        match effect.form with
        | Predicate (name, args) ->
          let params = List.map args ~f:term_to_ef in
          let label = extract_label_from_effect_name name in
          Some (sanitize_name name, params, Enfflash.RCause, None, None, label)
        | Neg { form = Predicate (name, args); _ } ->
          let params = List.map args ~f:term_to_ef in
          let label = extract_label_from_effect_name name in
          Some (sanitize_name name, params, Enfflash.RSuppress, None, None, label)
        | Eventually (i, { form = Predicate (name, args); _ }) ->
          let params = List.map args ~f:term_to_ef in
          let label = extract_label_from_effect_name name in
          Some (sanitize_name name, params, Enfflash.RCause, interval_to_delay i, None, label)
        | Eventually (i, { form = Neg { form = Predicate (name, args); _ }; _ }) ->
          let params = List.map args ~f:term_to_ef in
          let label = extract_label_from_effect_name name in
          Some (sanitize_name name, params, Enfflash.RSuppress, interval_to_delay i, None, label)
        | Next (i, { form = Predicate (name, args); _ }) ->
          let params = List.map args ~f:term_to_ef in
          let label = extract_label_from_effect_name name in
          Some (sanitize_name name, params, Enfflash.RCause, None, Some 1, label)
        | Next (i, { form = Neg { form = Predicate (name, args); _ }; _ }) ->
          let params = List.map args ~f:term_to_ef in
          let label = extract_label_from_effect_name name in
          Some (sanitize_name name, params, Enfflash.RSuppress, None, Some 1, label)
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
(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Top-level compilation                                                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

type compiled_let =
  string                                  (* name *)
  * Enftype.t option                      (* enforcement type *)
  * (Tterm.TypedVar.t * Dom.tt option) list  (* parameters *)
  * Tyformula.typed_t                     (* body_pos *)
  * Tyformula.typed_t option              (* body_neg_opt *)
  * Enforcement.clause list option        (* enforcement clauses *)

let compile
    ~(py_source: string option)
    ~(let_map: Enforcement.let_map)
    ~(lets: compiled_let list)
    ~(clauses: Enforcement.clause list)
  : Enfflash.program =
  let event_decls = compile_event_decls () in
  let fun_decls = compile_fun_decls ~py_source () in
  let let_defs  = ref [] in
  let tables    = ref [] in
  (* ── Process each compiled let ────────────────────────────────────────── *)
  List.iter lets ~f:(fun (name, _enftype, args, body_pos, body_neg_opt, _clauses_opt) ->
      let label, _sanitized = parse_label_name name in
      let emit_variant vname vlabel switch_opt fallback_body =
        match switch_opt with
        | Some switch ->
          (match compile_let_from_switch ~let_map ~name:vname ~label:vlabel ~args ~switch with
           | `Let ld  -> let_defs := ld :: !let_defs
           | `Table td -> tables := td :: !tables)
        | None ->
          (* No switch info available: compile the body formula as a let definition.
             It is a filter let unless the body references trace events. *)
          let columns =
            List.map args ~f:(fun (v, tt_opt) ->
                (san (fst v), match tt_opt with Some tt -> tt_to_ef tt | None -> tt_to_ef (snd v))) in
          let body = typed_formula_to_filter fallback_body in
          let_defs := Enfflash.{
              ld_label  = vlabel;
              ld_is_filter = not (filter_has_event_ref body);
              ld_name   = sanitize_name vname;
              ld_params = columns;
              ld_body   = body;
            } :: !let_defs
      in
      let def_opt = Map.find let_map name in
      match body_neg_opt with
      | Some body_neg ->
        (* Both positive and negative variants needed.
           Also emit the original name as an alias for _pos so that
           references to the unsuffixed name (e.g., inside _neg body) resolve. *)
        emit_variant
          name label
          (Option.bind def_opt ~f:(fun (d: Enforcement.let_def) -> d.switch_pos_opt))
          body_pos;
        emit_variant
          (name ^ "_pos") label
          (Option.bind def_opt ~f:(fun (d: Enforcement.let_def) -> d.switch_pos_opt))
          body_pos;
        emit_variant
          (name ^ "_neg") label
          (Option.bind def_opt ~f:(fun (d: Enforcement.let_def) -> d.switch_neg_opt))
          body_neg
      | None ->
        emit_variant
          name label
          (Option.bind def_opt ~f:(fun (d: Enforcement.let_def) -> d.switch_pos_opt))
          body_pos);
  (* ── Process enforcement clauses ──────────────────────────────────────── *)
  let rules = List.concat_map clauses ~f:(compile_clause_to_rules ~let_map) in
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
  Enfflash.{
    pg_event_decls = all_event_decls;
    pg_fun_decls   = fun_decls;
    pg_let_defs    = List.rev !let_defs;
    pg_tables      = List.rev !tables;
    pg_rules       = rules;
  }

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* Convenience: compile and write to file                                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

let compile_and_write
    ~(filename: string)
    ~(py_source: string option)
    ~(let_map: Enforcement.let_map)
    ~(lets: compiled_let list)
    ~(clauses: Enforcement.clause list)
  =
  let program = compile ~py_source ~let_map ~lets ~clauses in
  Enfflash.write_program_to_file ~filename program;
  program
