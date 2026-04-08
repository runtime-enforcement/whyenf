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
  | Eventually _ | Next _ ->
    (* Eventually/Next represent future obligations that have not yet been
       discharged.  In a filter context (present-time check), they evaluate
       to false: the obligation is not yet met. *)
    FBoolLit false
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

(* Check whether a predicate name corresponds to a trace event in the
   signature (Sig module), or is a synthetic Cau_/Sup_ event generated
   by the enforcement compiler. *)
let is_trace_event name =
  String.is_prefix name ~prefix:"Cau_"
  || String.is_prefix name ~prefix:"Sup_"
  || (try Sig.equal_pred_kind (Sig.kind_of_pred name) Sig.Trace
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
(* ═══════════════════════════════════════════════════════════════════════════ *)

let decompose_guard_conj (guards: Tyformula.t list) =
  let events, conditions =
    List.partition_tf guards ~f:(fun g ->
        match g.form with
        | Predicate (name, _) -> is_trace_event name
        | Neg f ->
          (match f.form with
           | Predicate (name, _) -> is_trace_event name
           | _ -> false)
        | _ -> false) in
  let patterns =
    List.map events ~f:(fun g ->
        match g.form with
        | Predicate (name, args) ->
          Enfflash.{ ep_name = name;
                     ep_args = List.map ~f:term_to_pattern_arg args }
        | Neg f ->
          (match f.form with
           | Predicate (name, args) ->
             Enfflash.{ ep_name = name;
                        ep_args = List.map ~f:term_to_pattern_arg args }
           | _ -> assert false)
        | _ -> assert false) in
  let filter_parts =
    List.filter_map conditions ~f:(fun c ->
        let f = formula_to_filter c in
        match f with Enfflash.FBoolLit true -> None | _ -> Some f) in
  (patterns, filter_parts)

let trigger_to_clauses (trigger: Enforcement.trigger) : Enfflash.clause list =
  (* Flatten an And-conjunction into a list of conjuncts so that we can
     separate trace-event predicates (→ patterns) from other conditions
     (→ if-filter).  This matters when guards = [] and the entire formula
     sits in trigger.filter. *)
  let rec flatten_conj (f: Tyformula.t) : Tyformula.t list =
    match f.form with
    | And (_, fs) -> List.concat_map fs ~f:flatten_conj
    | _ -> [f] in
  (* Flatten an Or into a list of disjuncts. *)
  let rec flatten_disj (f: Tyformula.t) : Tyformula.t list =
    match f.form with
    | Or (_, fs) -> List.concat_map fs ~f:flatten_disj
    | _ -> [f] in
  (* Convert a filter formula into DNF: a list of conjunct-lists.
     Each inner list represents a conjunction; the outer list represents
     the disjunction. We only expand Ors that contain trace events so
     as not to blow up the clause count unnecessarily. *)
  let rec filter_to_dnf (f: Tyformula.t) : Tyformula.t list list =
    match f.form with
    | And (_, fs) ->
      (* Cartesian product of the sub-DNFs *)
      List.fold_left fs ~init:[[]]
        ~f:(fun acc sub ->
            let sub_dnf = filter_to_dnf sub in
            List.concat_map acc ~f:(fun conj ->
                List.map sub_dnf ~f:(fun d -> conj @ d)))
    | Or (_, _) ->
      let disjuncts = flatten_disj f in
      (* Only expand into DNF if at least one disjunct is a trace event.
         Otherwise keep it as an opaque filter. *)
      let has_event = List.exists disjuncts ~f:(fun d ->
          match d.form with
          | Predicate (name, _) -> is_trace_event name
          | _ ->
            let conjs = flatten_conj d in
            List.exists conjs ~f:(fun c ->
                match c.form with
                | Predicate (name, _) -> is_trace_event name
                | _ -> false)) in
      if has_event then
        List.concat_map disjuncts ~f:filter_to_dnf
      else
        [[f]]
    | _ -> [[f]]
  in
  match trigger.guards with
  | [] ->
    (* No event guards: decompose the filter formula itself into
       trace-event patterns and residual filter conditions,
       expanding Ors that contain trace events into separate clauses. *)
    let dnf = filter_to_dnf trigger.filter in
    List.map dnf ~f:(fun conjuncts ->
        let patterns, filter_parts = decompose_guard_conj conjuncts in
        Enfflash.{ cl_patterns = patterns;
                   cl_filter = merge_filters filter_parts })
  | disjuncts ->
    (* Expand the filter into DNF to pull trace events into patterns.
       Then cross-product each guard disjunct with each filter disjunct. *)
    let filter_dnf = filter_to_dnf trigger.filter in
    List.concat_map disjuncts ~f:(fun guard_conj ->
        List.map filter_dnf ~f:(fun filter_conj ->
            let guard_patterns, guard_filter_parts = decompose_guard_conj guard_conj in
            let filter_patterns, filter_filter_parts = decompose_guard_conj filter_conj in
            Enfflash.{ cl_patterns = guard_patterns @ filter_patterns;
                       cl_filter = merge_filters (guard_filter_parts @ filter_filter_parts) }))

(* Pick the first clause from a trigger (for table add/remove which require
   a single clause).  Multiple guard disjuncts would need engine support for
   OR in clauses; for now we take the first and note. *)
let trigger_to_single_clause (trigger: Enforcement.trigger) : Enfflash.clause =
  match trigger_to_clauses trigger with
  | []     -> { cl_patterns = []; cl_filter = FBoolLit true }
  | [c]    -> c
  | c :: _ -> c  (* NOTE: only first guard disjunct used *)

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
    (* Present-time predicate: compile trigger guards + filter into one FilterExpr.
       If the compiled body references trace events, the let is
       "sufficiently guarded"; otherwise it is a "filter let". *)
    let guard_filter =
      match trigger.guards with
      | [] -> None
      | disjuncts ->
        let disj_parts =
          List.map disjuncts ~f:(fun conj ->
              let parts = List.map conj ~f:formula_to_filter in
              merge_filters parts) in
        Some (match disj_parts with
            | [f] -> f
            | f :: rest ->
              List.fold_left rest ~init:f ~f:(fun acc g -> Enfflash.FOr (acc, g))
            | [] -> FBoolLit true) in
    let base_filter = formula_to_filter trigger.filter in
    let all_parts =
      (Option.to_list guard_filter)
      @ (match base_filter with FBoolLit true -> [] | f -> [f]) in
    let body = merge_filters all_parts in
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
        td_add_clause = trigger_to_single_clause trigger;
        td_remove_clause = None;
      }
  | SPrev trigger ->
    (* Previous-step predicate: lagged table (updated after rules fire). *)
    `Table Enfflash.{
        td_label = label;
        td_lagged = true;
        td_name = sanitized;
        td_columns = columns;
        td_add_clause = trigger_to_single_clause trigger;
        td_remove_clause = None;
      }
  | SSince (left_trigger, right_trigger) ->
    (* Table with add (right trigger) and remove (left trigger).
       Since semantics: add row when right fires, remove when left fires.
       If the remove trigger has no event patterns (e.g., it references only
       let-defined predicates), we drop the remove clause; the table becomes
       monotone, which is a safe over-approximation. *)
    let rm_clause = trigger_to_single_clause left_trigger in
    let rm_opt = if List.is_empty rm_clause.cl_patterns then None
                 else Some rm_clause in
    `Table Enfflash.{
        td_label = label;
        td_lagged = false;
        td_name = sanitized;
        td_columns = columns;
        td_add_clause = trigger_to_single_clause right_trigger;
        td_remove_clause = rm_opt;
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

let compile_clause_to_rules (clause: Enforcement.clause) : Enfflash.rule_def list =
  let trigger_clauses = trigger_to_clauses clause.trigger in
  let effects_info =
    List.filter_map clause.effects ~f:(fun effect ->
        match effect.form with
        | Predicate (name, args) ->
          let params = List.map args ~f:term_to_ef in
          Some (sanitize_name name, params, Enfflash.RCause, None, None)
        | Neg { form = Predicate (name, args); _ } ->
          let params = List.map args ~f:term_to_ef in
          Some (sanitize_name name, params, Enfflash.RSuppress, None, None)
        | Eventually (i, { form = Predicate (name, args); _ }) ->
          let params = List.map args ~f:term_to_ef in
          Some (sanitize_name name, params, Enfflash.RCause, interval_to_delay i, None)
        | Eventually (i, { form = Neg { form = Predicate (name, args); _ }; _ }) ->
          let params = List.map args ~f:term_to_ef in
          Some (sanitize_name name, params, Enfflash.RSuppress, interval_to_delay i, None)
        | Next (i, { form = Predicate (name, args); _ }) ->
          let params = List.map args ~f:term_to_ef in
          Some (sanitize_name name, params, Enfflash.RCause, None, Some 1)
        | Next (i, { form = Neg { form = Predicate (name, args); _ }; _ }) ->
          let params = List.map args ~f:term_to_ef in
          Some (sanitize_name name, params, Enfflash.RSuppress, None, Some 1)
        | _ -> None) in
  List.concat_map effects_info ~f:(fun (ev_name, params, action, delay, tp_offset) ->
      List.map trigger_clauses ~f:(fun trigger_clause ->
          Enfflash.{
            rd_label      = None;
            rd_event      = ev_name;
            rd_params     = params;
            rd_action     = action;
            rd_delay      = delay;
            rd_tp_offset  = tp_offset;
            rd_trigger    = trigger_clause;
            rd_validate   = None;
          }))

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
          (match compile_let_from_switch ~name:vname ~label:vlabel ~args ~switch with
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
  let rules = List.concat_map clauses ~f:compile_clause_to_rules in
  (* ── Add synthetic event declarations for Cau_/Sup_ events ──────────── *)
  let synthetic_decls = collect_synthetic_event_decls ~existing:event_decls clauses in
  let all_event_decls = event_decls @ synthetic_decls in
  (* ── Fix default Int(0) in rule params when event expects str/float ─── *)
  let ed_map = Hashtbl.create (module String) in
  List.iter all_event_decls ~f:(fun ed ->
      Hashtbl.set ed_map ~key:ed.Enfflash.ed_name ~data:ed.Enfflash.ed_param_types);
  let rules = fix_rule_defaults ed_map rules in
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
