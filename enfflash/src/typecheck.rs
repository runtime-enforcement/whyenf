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

        if ld.is_filter {
            // Compiler-generated filter lets may legitimately carry guard patterns
            // when the best-effort trigger was able to pull some event guards for
            // free variables.  We therefore allow patterns in filter lets.
            //
            // Free variables in a filter let body (variables beyond the declared
            // parameters) must each be enumerable at runtime, i.e. they must
            // appear either:
            //   (a) as a variable in a guard pattern (event match → row iteration), or
            //   (b) as an argument to a positive table/event/let lookup in the filter.
            // A free variable that only appears in a bare comparison (`x == 5`)
            // cannot be enumerated and the filter will silently evaluate to false.
            let param_names: HashSet<String> =
                ld.params.iter().map(|(n, _)| n.clone()).collect();
            // Variables enumerable via guard patterns
            let pattern_vars = collect_pattern_var_names(&ld.clause.patterns);
            // Variables enumerable via positive lookups in the filter body
            let filter_lookup_vars = collect_filter_lookup_var_names(&ld.clause.filter);
            let enumerable_vars: HashSet<String> = pattern_vars
                .union(&filter_lookup_vars)
                .cloned()
                .collect();
            let used_vars = collect_filter_used_var_names(&ld.clause.filter);
            let free_vars: HashSet<String> =
                used_vars.difference(&param_names).cloned().collect();
            for v in free_vars.difference(&enumerable_vars) {
                errs.err(format!(
                    "filter let '{}': free variable '{}' does not appear in any \
                     guard pattern or table/event/let lookup and cannot be enumerated at runtime",
                    ld.name, v
                ));
            }
        }

        if !ld.is_filter {
            let guarded = collect_pattern_var_names(&ld.clause.patterns);

            for (param_name, _) in &ld.params {
                if !guarded.contains(param_name) {
                    errs.err(format!(
                        "let '{}': parameter '{}' is not guarded by let patterns",
                        ld.name, param_name
                    ));
                }
            }

            let used = collect_filter_used_var_names(&ld.clause.filter);
            for v in used.difference(&guarded) {
                errs.err(format!(
                    "let '{}': variable '{}' is not guarded by let patterns",
                    ld.name, v
                ));
            }
        }

        check_clause(&te, &ld.clause, None, &format!("let '{}'", ld.name), &mut errs);
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

/// Collect variable names bound by disjunctive guard patterns.
/// Within each conjunction (disjunct), take the union of bound vars.
/// Across disjuncts, take the intersection (a var is only guaranteed
/// bound if ALL disjuncts bind it).
fn collect_pattern_var_names(patterns: &[Vec<GuardPattern>]) -> HashSet<String> {
    if patterns.is_empty() {
        return HashSet::new();
    }
    let mut iter = patterns.iter();
    let first = iter.next().unwrap();
    let mut result: HashSet<String> = collect_conj_var_names(first);
    for conj in iter {
        let conj_vars = collect_conj_var_names(conj);
        result = result.intersection(&conj_vars).cloned().collect();
    }
    result
}

fn collect_conj_var_names(guards: &[GuardPattern]) -> HashSet<String> {
    let mut names = HashSet::new();
    for guard in guards {
        match guard {
            GuardPattern::Event(pat) => {
                for arg in &pat.args {
                    if let PatternArg::Var(name) = arg {
                        names.insert(name.clone());
                    }
                }
            }
            GuardPattern::EqConst(name, _) => {
                names.insert(name.clone());
            }
        }
    }
    names
}

/// Collect variable names that are *definitely* bound by a filter expression
/// at runtime via table/let/event lookups.
///
/// For `And`, both branches execute so we take the union.
/// For `Or`, only one branch executes so we take the *intersection* —
/// a variable is only guaranteed bound if both branches bind it.
/// For `Not`, no new bindings are introduced (negation only tests, it
/// doesn't bind variables in the outer scope).
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
        FilterExpr::And(l, r) => {
            // Both branches execute: union of bound vars
            names.extend(collect_filter_var_names(l));
            names.extend(collect_filter_var_names(r));
        }
        FilterExpr::Or(l, r) => {
            // Only one branch executes: intersection of bound vars
            let left = collect_filter_var_names(l);
            let right = collect_filter_var_names(r);
            names.extend(left.intersection(&right).cloned());
        }
        FilterExpr::Not(_) => {
            // Negation does not introduce bindings into the outer scope
        }
        FilterExpr::BoolLit(_) => {}
    }
    names
}

/// Collect all variable names that appear as arguments to any TableLookup
/// (table, let, or event reference) at any depth in a filter expression,
/// ignoring And/Or/Not structure.  These variables can be enumerated at
/// runtime by iterating over the corresponding table or event set.
fn collect_filter_lookup_var_names(filter: &FilterExpr) -> HashSet<String> {
    let mut names = HashSet::new();
    match filter {
        FilterExpr::TableLookup { args, .. } => {
            for arg in args {
                names.extend(arg.clone().fvs());
            }
        }
        FilterExpr::And(l, r) | FilterExpr::Or(l, r) => {
            names.extend(collect_filter_lookup_var_names(l));
            names.extend(collect_filter_lookup_var_names(r));
        }
        FilterExpr::Not(_) => {
            // Variables inside a negated lookup cannot be positively enumerated.
        }
        _ => {}
    }
    names
}

/// Collect variable names that occur syntactically in a filter expression.
/// Unlike `collect_filter_var_names`, this does not model runtime binding;
/// it simply returns all variables that appear in terms.
fn collect_filter_used_var_names(filter: &FilterExpr) -> HashSet<String> {
    let mut names = HashSet::new();
    match filter {
        FilterExpr::BoolLit(_) => {}
        FilterExpr::TableLookup { args, .. } => {
            for arg in args {
                collect_term_used_var_names(arg, &mut names);
            }
        }
        FilterExpr::Compare { lhs, rhs, .. } => {
            collect_term_used_var_names(lhs, &mut names);
            collect_term_used_var_names(rhs, &mut names);
        }
        FilterExpr::And(l, r) | FilterExpr::Or(l, r) => {
            names.extend(collect_filter_used_var_names(l));
            names.extend(collect_filter_used_var_names(r));
        }
        FilterExpr::Not(inner) => {
            names.extend(collect_filter_used_var_names(inner));
        }
    }
    names
}

fn collect_term_used_var_names(term: &TermExpr, out: &mut HashSet<String>) {
    match term {
        TermExpr::Var(v) => {
            out.insert(v.clone());
        }
        TermExpr::Lit(_) => {}
        TermExpr::FunCall { args, .. } => {
            for arg in args {
                collect_term_used_var_names(arg, out);
            }
        }
    }
}

/// Build a typed variable context from disjunctive guard patterns.
fn build_ctx_from_patterns(te: &TyEnv, patterns: &[Vec<GuardPattern>]) -> VarCtx {
    if patterns.is_empty() {
        return VarCtx::new();
    }
    let first_ctx = build_conj_ctx(te, &patterns[0]);
    if patterns.len() == 1 {
        return first_ctx;
    }
    let mut common_vars = collect_conj_var_names(&patterns[0]);
    for conj in &patterns[1..] {
        let conj_vars = collect_conj_var_names(conj);
        common_vars = common_vars.intersection(&conj_vars).cloned().collect();
    }
    first_ctx.into_iter().filter(|(k, _)| common_vars.contains(k)).collect()
}

fn build_conj_ctx(te: &TyEnv, guards: &[GuardPattern]) -> VarCtx {
    let mut ctx = VarCtx::new();
    for guard in guards {
        match guard {
            GuardPattern::Event(pat) => {
                let param_types: Option<Vec<Ty>> = if let Some((ev_types, _)) = te.events.get(&pat.name) {
                    Some(ev_types.clone())
                } else if let Some(params) = te.lets.get(&pat.name) {
                    Some(params.iter().map(|(_, t)| t.clone()).collect())
                } else if let Some(cols) = te.tables.get(&pat.name) {
                    Some(cols.iter().map(|(_, t)| t.clone()).collect())
                } else {
                    None
                };
                if let Some(types) = param_types {
                    for (arg, ty) in pat.args.iter().zip(types.iter()) {
                        if let PatternArg::Var(name) = arg {
                            ctx.insert(name.clone(), ty.clone());
                        }
                    }
                }
            }
            GuardPattern::EqConst(name, val) => {
                ctx.insert(name.clone(), value_type(val));
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
        FilterExpr::And(l, r) => {
            // Both branches execute: extend from both
            extend_ctx_from_filter(te, ctx, l);
            extend_ctx_from_filter(te, ctx, r);
        }
        FilterExpr::Or(l, r) => {
            // Only one branch executes: only add variables that both branches bind
            let mut left_ctx = VarCtx::new();
            let mut right_ctx = VarCtx::new();
            extend_ctx_from_filter(te, &mut left_ctx, l);
            extend_ctx_from_filter(te, &mut right_ctx, r);
            for (name, ty) in &left_ctx {
                if right_ctx.contains_key(name) {
                    ctx.entry(name.clone()).or_insert_with(|| ty.clone());
                }
            }
        }
        FilterExpr::Not(_) => {
            // Negation does not introduce bindings into the outer scope
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
    // Check patterns: each guard must reference a declared event/let-def with correct arity
    for disj in &clause.patterns {
        for guard in disj {
            match guard {
                GuardPattern::EqConst(_, _) => {
                    // EqConst binds a variable to a literal — always valid
                }
                GuardPattern::Event(pat) => {
                    if let Some((ev_types, _)) = te.events.get(&pat.name) {
                        if pat.args.len() != ev_types.len() {
                            errs.err(format!(
                                "{}: pattern '{}' has {} args, event expects {}",
                                loc, pat.name, pat.args.len(), ev_types.len()
                            ));
                        }
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
                    } else if let Some(params) = te.lets.get(&pat.name) {
                        if te.filter_lets.contains(&pat.name) {
                            errs.err(format!(
                                "{}: filter let '{}' cannot be used as a guard pattern",
                                loc, pat.name
                            ));
                        }
                        if pat.args.len() != params.len() {
                            errs.err(format!(
                                "{}: pattern '{}' has {} args, let-def expects {}",
                                loc, pat.name, pat.args.len(), params.len()
                            ));
                        }
                        for (i, (arg, (_, expected_ty))) in pat.args.iter().zip(params.iter()).enumerate() {
                            if let PatternArg::Literal(val) = arg {
                                let val_ty = value_type(val);
                                if &val_ty != expected_ty {
                                    errs.err(format!(
                                        "{}: pattern '{}' arg {} is {} but let-def expects {}",
                                        loc, pat.name, i, val_ty, expected_ty
                                    ));
                                }
                            }
                        }
                    } else if let Some(cols) = te.tables.get(&pat.name) {
                        // Table used as a guard pattern (lookup by row)
                        if pat.args.len() != cols.len() {
                            errs.err(format!(
                                "{}: pattern '{}' has {} args, table expects {}",
                                loc, pat.name, pat.args.len(), cols.len()
                            ));
                        }
                        for (i, (arg, (_, expected_ty))) in pat.args.iter().zip(cols.iter()).enumerate() {
                            if let PatternArg::Literal(val) = arg {
                                let val_ty = value_type(val);
                                if &val_ty != expected_ty {
                                    errs.err(format!(
                                        "{}: pattern '{}' arg {} is {} but table expects {}",
                                        loc, pat.name, i, val_ty, expected_ty
                                    ));
                                }
                            }
                        }
                    } else {
                        errs.err(format!("{}: unknown event '{}' in pattern", loc, pat.name));
                    }
                }
            }
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
