/// Static type checker for enfflash programs.
///
/// Checks:
/// - Event arities and argument types in patterns, filters, table clauses, rules
/// - Function call arities and argument/return types
/// - Let definition arities and argument types
/// - Table lookup arities and column types
/// - Variables are defined before use in `if` filters (pattern vars must cover all needed vars)
/// - Comparison operands have compatible types
/// - All rule output params are bound by trigger patterns

use std::collections::{HashMap, HashSet};
use crate::ast::*;
use crate::monotonicity::*;

/// Collected type information about the program's declarations.
struct TyEnv {
    /// event name → param types
    events: HashMap<String, (Vec<Ty>, RuleAction)>,
    /// fun name → (param types, return type)
    functions: HashMap<String, (Vec<(String, Ty)>, Ty)>,
    /// table name → column (name, type) list
    tables: HashMap<String, Vec<(String, Ty)>>,
    /// let name → param (name, type) list
    lets: HashMap<String, Vec<(String, Ty)>>,
    /// Names of filter lets (insufficiently guarded, cannot bind variables in patterns)
    filter_lets: HashSet<String>,
    /// event name → (event name → monotonicity)
    monotonicities: HashMap<String, HashMap<String, Monotonicity>>,
}

/// A typing context: variable name → type.
type VarCtx = HashMap<String, Ty>;

/// All errors accumulated during type checking.
pub struct CheckErrors {
    pub errors: Vec<String>,
}

impl CheckErrors {
    fn new() -> Self {
        CheckErrors { errors: Vec::new() }
    }
    fn err(&mut self, msg: String) {
        self.errors.push(msg);
    }
    pub fn is_empty(&self) -> bool {
        self.errors.is_empty()
    }
}

/// Run the type checker on a parsed program. Returns a list of error messages (empty = OK).
pub fn check_program(program: &Program) -> CheckErrors {
    let mut errs = CheckErrors::new();

    // Build the declaration environment
    let mut te = TyEnv {
        events: HashMap::new(),
        functions: HashMap::new(),
        tables: HashMap::new(),
        lets: HashMap::new(),
        filter_lets: HashSet::new(),
        monotonicities: HashMap::new(),
    };

    // Duplicate-name checks + collect declarations
    for ed in &program.event_decls {
        if te.events.contains_key(&ed.name) {
            errs.err(format!("Duplicate event declaration: '{}'", ed.name));
        }
        te.events.insert(ed.name.clone(), (ed.param_types.clone(), RuleAction::Observe));
    }
    for fd in &program.fun_decls {
        if te.functions.contains_key(&fd.name) {
            errs.err(format!("Duplicate function declaration: '{}'", fd.name));
        }
        let params: Vec<(String, Ty)> = fd.param_names.iter().zip(fd.param_types.iter())
            .map(|(n, t)| (n.clone(), t.clone()))
            .collect();
        te.functions.insert(fd.name.clone(), (params, fd.ret_type.clone()));
    }
    for ld in &program.let_defs {
        if te.lets.contains_key(&ld.name) {
            errs.err(format!("Duplicate let definition: '{}'", ld.name));
        }
        te.lets.insert(ld.name.clone(), ld.params.clone());
        if ld.is_filter {
            te.filter_lets.insert(ld.name.clone());
        }
        te.monotonicities.insert(ld.name.clone(), compute_let_monotonicity(ld, &te.monotonicities));
    }
    for td in &program.tables {
        if te.tables.contains_key(&td.name) {
            errs.err(format!("Duplicate table definition: '{}'", td.name));
        }
        te.tables.insert(td.name.clone(), td.columns.clone());
        te.monotonicities.insert(td.name.clone(), compute_table_monotonicity(td, &te.monotonicities));
    }

    // Check let bodies
    for ld in &program.let_defs {
        let mut ctx = VarCtx::new();
        for (pname, pty) in &ld.params {
            ctx.insert(pname.clone(), pty.clone());
        }
        check_filter(&te, &ctx, &ld.body, &format!("let '{}'", ld.name), &mut errs);
    }

    // Check table clauses
    for td in &program.tables {
        // For add, patterns + filter conditions must bind all columns
        let mut add_var_names = collect_pattern_var_names(&td.add_clause.patterns);
        add_var_names.extend(collect_filter_var_names(&td.add_clause.filter));
        for (col_name, _) in &td.columns {
            if !add_var_names.contains(col_name) {
                errs.err(format!(
                    "table '{}' add: column '{}' not bound by patterns",
                    td.name, col_name
                ));
            }
        }
        check_clause(&te, &td.add_clause, Some(td), &format!("table '{}' add", td.name), &mut errs);
        if let Some(ref rm) = td.remove_clause {
            // For remove, patterns + filter conditions must bind all columns
            let mut rm_var_names = collect_pattern_var_names(&rm.patterns);
            rm_var_names.extend(collect_filter_var_names(&rm.filter));
            for (col_name, _) in &td.columns {
                if !rm_var_names.contains(col_name) {
                    errs.err(format!(
                        "table '{}' remove: column '{}' not bound by patterns",
                        td.name, col_name
                    ));
                }
            }
            check_clause(&te, rm, Some(td), &format!("table '{}' remove", td.name), &mut errs);
        }
    }

    // Check rules
    for rd in &program.rules {
        let action_sym = match rd.action {
            RuleAction::Cause => "+",
            RuleAction::Suppress => "-",
            RuleAction::Observe => "",
        };
        let loc = format!("rule {}{}", action_sym, rd.event);

        // Rule event must be declared
        if let Some((ev_types, _)) = te.events.get(&rd.event) {
            if rd.params.len() != ev_types.len() {
                errs.err(format!(
                    "{}: expected {} params (from event decl), got {}",
                    loc, ev_types.len(), rd.params.len()
                ));
            }
        } else {
            errs.err(format!("{}: unknown event '{}'", loc, rd.event));
        }

        // Compute monotonicity for this rule (used for analysis, no error emitted
        // since an event may be both caused and suppressed by different rules;
        // the engine handles this via fixpoint iteration).
        let _monotonicity = compute_rule_monotonicity(rd, &te.monotonicities);

        // Update the event rule action.  An event may now be both caused and
        // suppressed by different rules (the engine resolves this via fixpoint),
        // so we no longer treat a Cause/Suppress mix as an error.
        if let Some((_, existing_action)) = te.events.get_mut(&rd.event) {
            if *existing_action == RuleAction::Observe {
                *existing_action = rd.action; // first rule for this event, set the action
            }
            // (previously this was an error when existing != rd.action)
        }

        // Check trigger clause
        check_clause(&te, &rd.trigger, None, &format!("{} trigger", loc), &mut errs);

        // All rule output params must be bound by trigger patterns or filter conditions
        let mut bound_var_names = collect_pattern_var_names(&rd.trigger.patterns);
        bound_var_names.extend(collect_filter_var_names(&rd.trigger.filter));
        for p in &rd.params {
            for v in &p.clone().fvs() {
                if !bound_var_names.contains(v) {
                    errs.err(format!(
                        "{}: output param '{}' not bound by trigger patterns",
                        loc, v
                    ));
                }
            }
        }

        // Type-check output params against event decl
        if let Some((ev_types, _)) = te.events.get(&rd.event) {
            let mut ctx = build_ctx_from_patterns(&te, &rd.trigger.patterns);
            extend_ctx_from_filter(&te, &mut ctx, &rd.trigger.filter);
            for (param, expected_ty) in rd.params.iter().zip(ev_types.iter()) {
                let ty = infer_term(&te, &ctx, param, &loc, &mut errs);
                if let Some(actual_ty) = &ty {
                    if actual_ty != expected_ty {
                        errs.err(format!(
                            "{}: param '{:?}' has type {} but event '{}' expects {}",
                            loc, param, actual_ty, rd.event, expected_ty
                        ));
                    }
                }
            }
        }

        // Check validate filter if present
        if let Some(ref vf) = rd.validate {
            // validate runs with the same env as trigger
            let mut ctx = build_ctx_from_patterns(&te, &rd.trigger.patterns);
            extend_ctx_from_filter(&te, &mut ctx, &rd.trigger.filter);
            check_filter(&te, &ctx, vf, &format!("{} validate", loc), &mut errs);
        }
        
    }

    errs
}

/// Collect variable names bound by a list of event patterns (no types, just names).
fn collect_pattern_var_names(patterns: &[EventPattern]) -> HashSet<String> {
    let mut names = HashSet::new();
    for pat in patterns {
        for arg in &pat.args {
            if let PatternArg::Var(name) = arg {
                names.insert(name.clone());
            }
        }
    }
    names
}

/// Collect variable names referenced in filter expressions.
/// These variables can be existentially bound at runtime via table/let/event lookups.
fn collect_filter_var_names(filter: &FilterExpr) -> HashSet<String> {
    let mut names = HashSet::new();
    match filter {
        FilterExpr::TableLookup { args, .. } => {
            for arg in args {
                for v in arg.clone().fvs() {
                    names.insert(v);
                }
            }
        }
        FilterExpr::Compare { lhs, rhs, .. } => {
            for v in lhs.clone().fvs() { names.insert(v); }
            for v in rhs.clone().fvs() { names.insert(v); }
        }
        FilterExpr::And(l, r) | FilterExpr::Or(l, r) => {
            names.extend(collect_filter_var_names(l));
            names.extend(collect_filter_var_names(r));
        }
        FilterExpr::Not(inner) => {
            names.extend(collect_filter_var_names(inner));
        }
        FilterExpr::BoolLit(_) => {}
    }
    names
}

/// Build a typed variable context from patterns using event declarations.
fn build_ctx_from_patterns(te: &TyEnv, patterns: &[EventPattern]) -> VarCtx {
    let mut ctx = VarCtx::new();
    for pat in patterns {
        if let Some((ev_types, _)) = te.events.get(&pat.name) {
            for (arg, ty) in pat.args.iter().zip(ev_types.iter()) {
                if let PatternArg::Var(name) = arg {
                    ctx.insert(name.clone(), ty.clone());
                }
            }
        }
    }
    ctx
}

/// Extend a variable context with variable types inferred from filter expressions.
/// For TableLookup references to tables/lets/events, we infer argument types from
/// the declaration's parameter types.
fn extend_ctx_from_filter(te: &TyEnv, ctx: &mut VarCtx, filter: &FilterExpr) {
    match filter {
        FilterExpr::TableLookup { name, args } => {
            // Find param types from table, let, or event declaration
            let param_types: Option<Vec<Ty>> = if let Some(cols) = te.tables.get(name) {
                Some(cols.iter().map(|(_, t)| t.clone()).collect())
            } else if let Some(params) = te.lets.get(name) {
                Some(params.iter().map(|(_, t)| t.clone()).collect())
            } else if let Some((ev_types, _)) = te.events.get(name) {
                Some(ev_types.clone())
            } else {
                None
            };
            if let Some(ptypes) = param_types {
                for (arg, ty) in args.iter().zip(ptypes.iter()) {
                    if let TermExpr::Var(vname) = arg {
                        ctx.entry(vname.clone()).or_insert_with(|| ty.clone());
                    }
                }
            }
        }
        FilterExpr::And(l, r) | FilterExpr::Or(l, r) => {
            extend_ctx_from_filter(te, ctx, l);
            extend_ctx_from_filter(te, ctx, r);
        }
        FilterExpr::Not(inner) => {
            extend_ctx_from_filter(te, ctx, inner);
        }
        _ => {}
    }
}



/// Check a clause: patterns + filter.
fn check_clause(
    te: &TyEnv,
    clause: &Clause,
    parent_table: Option<&TableDef>,
    loc: &str,
    errs: &mut CheckErrors,
) {
    // Check patterns: each pattern must reference a declared event with correct arity
    for pat in &clause.patterns {
        if let Some((ev_types, _)) = te.events.get(&pat.name) {
            if pat.args.len() != ev_types.len() {
                errs.err(format!(
                    "{}: pattern '{}' has {} args, event expects {}",
                    loc, pat.name, pat.args.len(), ev_types.len()
                ));
            }
            // Check literal types in patterns
            for (i, (arg, expected_ty)) in pat.args.iter().zip(ev_types.iter()).enumerate() {
                if let PatternArg::Literal(val) = arg {
                    let val_ty = value_type(val);
                    if &val_ty != expected_ty {
                        errs.err(format!(
                            "{}: pattern '{}' arg {} is {} but event expects {}",
                            loc, pat.name, i, val_ty, expected_ty
                        ));
                    }
                }
            }
        } else {
            errs.err(format!("{}: unknown event '{}' in pattern", loc, pat.name));
        }
    }

    // Check that pattern variables used for table columns have correct types
    if let Some(td) = parent_table {
        let mut ctx = build_ctx_from_patterns(te, &clause.patterns);
        extend_ctx_from_filter(te, &mut ctx, &clause.filter);
        for (col_name, col_ty) in &td.columns {
            if let Some(var_ty) = ctx.get(col_name) {
                if var_ty != col_ty {
                    errs.err(format!(
                        "{}: variable '{}' has type {} from pattern but table column expects {}",
                        loc, col_name, var_ty, col_ty
                    ));
                }
            }
        }
    }

    // Build typed context from patterns + filter, then check filter
    let mut ctx = build_ctx_from_patterns(te, &clause.patterns);
    extend_ctx_from_filter(te, &mut ctx, &clause.filter);
    check_filter(te, &ctx, &clause.filter, loc, errs);
}

/// Check a filter expression. `ctx` has the variables definitely in scope.
/// Extra variables in filters (not in ctx) are allowed — they'll be existentially quantified at runtime.
fn check_filter(
    te: &TyEnv,
    ctx: &VarCtx,
    filter: &FilterExpr,
    loc: &str,
    errs: &mut CheckErrors,
) {
    match filter {
        FilterExpr::BoolLit(_) => {}

        FilterExpr::And(l, r) | FilterExpr::Or(l, r) => {
            check_filter(te, ctx, l, loc, errs);
            check_filter(te, ctx, r, loc, errs);
        }

        FilterExpr::Not(f) => {
            check_filter(te, ctx, f, loc, errs);
        }

        FilterExpr::Compare { lhs, op: _, rhs } => {
            let lt = infer_term(te, ctx, lhs, loc, errs);
            let rt = infer_term(te, ctx, rhs, loc, errs);
            if let (Some(lt), Some(rt)) = (&lt, &rt) {
                if lt != rt {
                    errs.err(format!(
                        "{}: comparison between incompatible types {} and {}",
                        loc, lt, rt
                    ));
                }
            }
        }

        FilterExpr::TableLookup { name, args } => {
            // Could be table, let, or event
            if let Some(cols) = te.tables.get(name) {
                // Table lookup
                if args.len() != cols.len() {
                    errs.err(format!(
                        "{}: table '{}' expects {} args, got {}",
                        loc, name, cols.len(), args.len()
                    ));
                }
                for (i, (arg, (_, col_ty))) in args.iter().zip(cols.iter()).enumerate() {
                    let at = infer_term(te, ctx, arg, loc, errs);
                    if let Some(at) = &at {
                        if at != col_ty {
                            errs.err(format!(
                                "{}: table '{}' arg {} has type {} but column expects {}",
                                loc, name, i, at, col_ty
                            ));
                        }
                    }
                }
            } else if let Some(params) = te.lets.get(name) {
                // Let definition call
                if args.len() != params.len() {
                    errs.err(format!(
                        "{}: let '{}' expects {} args, got {}",
                        loc, name, params.len(), args.len()
                    ));
                }
                for (i, (arg, (_, param_ty))) in args.iter().zip(params.iter()).enumerate() {
                    let at = infer_term(te, ctx, arg, loc, errs);
                    if let Some(at) = &at {
                        if at != param_ty {
                            errs.err(format!(
                                "{}: let '{}' arg {} has type {} but param expects {}",
                                loc, name, i, at, param_ty
                            ));
                        }
                    }
                }
            } else if let Some((ev_types, _)) = te.events.get(name) {
                // Event check in filter
                if args.len() != ev_types.len() {
                    errs.err(format!(
                        "{}: event '{}' expects {} args, got {}",
                        loc, name, ev_types.len(), args.len()
                    ));
                }
                for (i, (arg, expected_ty)) in args.iter().zip(ev_types.iter()).enumerate() {
                    let at = infer_term(te, ctx, arg, loc, errs);
                    if let Some(at) = &at {
                        if at != expected_ty {
                            errs.err(format!(
                                "{}: event '{}' arg {} has type {} but expects {}",
                                loc, name, i, at, expected_ty
                            ));
                        }
                    }
                }
            } else {
                errs.err(format!("{}: unknown name '{}' (not a table, let, or event)", loc, name));
            }
        }
    }
}

/// Infer the type of a term expression. Returns None if unknown (error already reported).
fn infer_term(
    te: &TyEnv,
    ctx: &VarCtx,
    term: &TermExpr,
    loc: &str,
    errs: &mut CheckErrors,
) -> Option<Ty> {
    match term {
        TermExpr::Var(name) => {
            if let Some(ty) = ctx.get(name) {
                Some(ty.clone())
            } else {
                // Not in the pattern context — this is fine, it will be
                // existentially quantified at runtime. We can't infer a type
                // for it here, so return None (no error).
                None
            }
        }
        TermExpr::Lit(val) => Some(value_type(val)),
        TermExpr::FunCall { name, args } => {
            if let Some((params, ret_ty)) = te.functions.get(name) {
                if args.len() != params.len() {
                    errs.err(format!(
                        "{}: function '{}' expects {} args, got {}",
                        loc, name, params.len(), args.len()
                    ));
                }
                for (i, (arg, (_, expected_ty))) in args.iter().zip(params.iter()).enumerate() {
                    let at = infer_term(te, ctx, arg, loc, errs);
                    if let Some(at) = &at {
                        if at != expected_ty {
                            errs.err(format!(
                                "{}: function '{}' arg {} has type {} but expects {}",
                                loc, name, i, at, expected_ty
                            ));
                        }
                    }
                }
                Some(ret_ty.clone())
            } else {
                errs.err(format!("{}: unknown function '{}'", loc, name));
                None
            }
        }
    }
}

/// Get the type of a literal value.
fn value_type(val: &Value) -> Ty {
    match val {
        Value::Int(_) => Ty::Int,
        Value::Float(_) => Ty::Float,
        Value::Str(_) => Ty::Str,
        Value::Bool(_) => Ty::Bool,
    }
}
