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

type filter_expr =
  | FBoolLit of bool
  | FTableLookup of string * term_expr list
  | FCompare of term_expr * cmp_op * term_expr
  | FAnd of filter_expr * filter_expr
  | FOr of filter_expr * filter_expr
  | FNot of filter_expr

type clause = {
  cl_patterns: event_pattern list;
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
  ld_body: filter_expr;
}

type table_def = {
  td_label: string option;
  td_lagged: bool;
  td_name: string;
  td_columns: (string * ef_ty) list;
  td_add_clause: clause;
  td_remove_clause: clause option;
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

type program = {
  pg_event_decls: event_decl list;
  pg_fun_decls: fun_decl list;
  pg_let_defs: let_def list;
  pg_tables: table_def list;
  pg_rules: rule_def list;
}

(* ─── Serialization to .ef text format ───────────────────────────────────── *)

let ef_ty_to_string = function
  | EfInt   -> "int"
  | EfStr   -> "str"
  | EfFloat -> "float"

let ef_value_to_string = function
  | EfVInt i   -> Int.to_string i
  | EfVStr s   -> Printf.sprintf "\"%s\"" s
  | EfVFloat f -> Printf.sprintf "%g" f
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
  let pats_str = String.concat ~sep:" & "
      (List.map ~f:event_pattern_to_string cl.cl_patterns) in
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
  | Some lbl -> Printf.sprintf "@%s " lbl

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
  Printf.sprintf "%s%s %s(%s) := {\n  %s\n}"
    (label_prefix ld.ld_label)
    keyword
    ld.ld_name
    (typed_params_to_string ld.ld_params)
    (filter_expr_to_string ld.ld_body)

let table_def_to_string td =
  let lagged_str = if td.td_lagged then "lagged " else "" in
  let add_str = Printf.sprintf "  add {\n%s\n  }"
      (clause_to_string ~indent:"    " td.td_add_clause) in
  let remove_str = match td.td_remove_clause with
    | None    -> ""
    | Some cl -> Printf.sprintf "\n  remove {\n%s\n  }"
                   (clause_to_string ~indent:"    " cl) in
  Printf.sprintf "%s%stable %s(%s) :=\n%s%s;"
    (label_prefix td.td_label)
    lagged_str
    td.td_name
    (typed_params_to_string td.td_columns)
    add_str
    remove_str

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

let program_to_string pg =
  let buf = Buffer.create 4096 in
  let emit s = Buffer.add_string buf s; Buffer.add_char buf '\n' in
  let emit_blank () = Buffer.add_char buf '\n' in
  (* Event declarations *)
  List.iter pg.pg_event_decls ~f:(fun ed -> emit (event_decl_to_string ed));
  if not (List.is_empty pg.pg_event_decls) then emit_blank ();
  (* Function declarations *)
  List.iter pg.pg_fun_decls ~f:(fun fd -> emit (fun_decl_to_string fd));
  if not (List.is_empty pg.pg_fun_decls) then emit_blank ();
  (* Let definitions *)
  List.iter pg.pg_let_defs ~f:(fun ld ->
      emit (let_def_to_string ld); emit_blank ());
  (* Table definitions *)
  List.iter pg.pg_tables ~f:(fun td ->
      emit (table_def_to_string td); emit_blank ());
  (* Rule definitions *)
  List.iter pg.pg_rules ~f:(fun rd ->
      emit (rule_def_to_string rd); emit_blank ());
  Buffer.contents buf

let write_program_to_file ~(filename: string) (pg: program) =
  let text = program_to_string pg in
  Stdio.Out_channel.write_all filename ~data:text
