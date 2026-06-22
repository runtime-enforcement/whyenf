/// The enforcement engine: evaluates programs against logs.

use std::collections::BTreeSet;
use std::sync::Arc;
// Fast non-cryptographic hashing for all internal maps/sets.  SipHash (the std
// default) showed up as ~12% of runtime; FxHash is several times faster for the
// short string / small tuple keys used here and needs no DoS resistance.
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::io::Write;
use std::time::Instant;
use serde::{Serialize, Deserialize};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList};
use crate::ast::*;
use crate::table::{Table, Row};

// ─── Public output type ──────────────────────────────────────────────────────

/// The enforcement decision for one timepoint from one engine instance.
/// Returned by [`Engine::process_one`] and [`Engine::finish`]; callers
/// decide how to print or aggregate these values.
#[derive(Debug, Clone)]
pub struct EnfOutput {
    pub ts:             u64,
    pub proactive:      bool,
    /// Cause actions — filtered (no `Cau_` / `Sup_` synthetics).
    pub cause:          Vec<(EventInstance, Vec<String>)>,
    /// Suppress actions — filtered.
    pub suppress:       Vec<(EventInstance, Vec<String>)>,
    /// Wall-clock processing time for reactive output; `None` for proactive.
    pub dur_nanos:      Option<u64>,
    /// Wall-clock microseconds elapsed since the engine was created.
    pub latency_micros: u64,
}

impl EnfOutput {
    pub fn print(&self, json_mode: bool, label_mode: bool) {
        if json_mode {
            self.print_json();
        } else {
            self.print_textual(label_mode);
        }
    }

    fn print_json(&self) {
        let ts = self.ts;
        let cause_json = format!("[ {} ]",
            self.cause.iter().map(|(e, _)| e.to_json()).collect::<Vec<_>>().join(", "));
        let suppress_json = format!("[ {} ]",
            self.suppress.iter().map(|(e, _)| e.to_json()).collect::<Vec<_>>().join(", "));
        if self.proactive {
            if !self.cause.is_empty() {
                println!("{{ \"ts\": {}, \"cause\": {}, \"proactive\": true, \"latency\": {} }}",
                         ts, cause_json, self.latency_micros);
            } else {
                println!("{{ \"ts\": {}, \"proactive\": true, \"latency\": {} }}",
                         ts, self.latency_micros);
            }
        } else {
            let dur_field = self.dur_nanos
                .map_or(String::new(), |n| format!(", \"dur_nanos\": {}", n));
            let has_c = !self.cause.is_empty();
            let has_s = !self.suppress.is_empty();
            if has_c && has_s {
                println!("{{ \"ts\": {}{}, \"cause\": {}, \"suppress\": {}, \"latency\": {} }}",
                         ts, dur_field, cause_json, suppress_json, self.latency_micros);
            } else if has_c {
                println!("{{ \"ts\": {}{}, \"cause\": {}, \"latency\": {} }}",
                         ts, dur_field, cause_json, self.latency_micros);
            } else if has_s {
                println!("{{ \"ts\": {}{}, \"suppress\": {}, \"latency\": {} }}",
                         ts, dur_field, suppress_json, self.latency_micros);
            } else {
                println!("{{ \"ts\": {}{}, \"latency\": {} }}", ts, dur_field, self.latency_micros);
            }
        }
        let _ = std::io::stdout().flush();
    }

    fn print_textual(&self, label_mode: bool) {
        let ts = self.ts;
        if self.proactive {
            if !self.cause.is_empty() {
                if label_mode {
                    for (ev, labels) in &self.cause {
                        let fmt = labels.iter().map(|l| format!("\"{}\"", l)).collect::<Vec<_>>().join(", ");
                        println!("[Enforcer:Label] Cause {}: {}", ev, fmt);
                    }
                }
                println!("[Enforcer] @{} proactively commands:\nCause:\n{}\nOK.", ts,
                    self.cause.iter().map(|(e, _)| e.to_string()).collect::<Vec<_>>().join(", "));
            } else {
                println!("[Enforcer] @{} nothing to do proactively.", ts);
            }
        } else {
            if label_mode {
                for (ev, labels) in &self.suppress {
                    let fmt = labels.iter().map(|l| format!("\"{}\"", l)).collect::<Vec<_>>().join(", ");
                    println!("[Enforcer:Label] Suppress {}: {}", ev, fmt);
                }
                for (ev, labels) in &self.cause {
                    let fmt = labels.iter().map(|l| format!("\"{}\"", l)).collect::<Vec<_>>().join(", ");
                    println!("[Enforcer:Label] Cause {}: {}", ev, fmt);
                }
            }
            if !self.suppress.is_empty() || !self.cause.is_empty() {
                println!("[Enforcer] @{} reactively commands:", ts);
                if !self.suppress.is_empty() {
                    println!("Suppress:\n{}", self.suppress.iter().map(|(e,_)| e.to_string()).collect::<Vec<_>>().join(", "));
                }
                if !self.cause.is_empty() {
                    println!("Cause:\n{}", self.cause.iter().map(|(e,_)| e.to_string()).collect::<Vec<_>>().join(", "));
                }
                println!("OK.");
            } else {
                println!("[Enforcer] @{} OK.", ts);
            }
        }
    }
}

/// Convenience macro: prints to stderr only when `self.verbose_mode` is true.
macro_rules! vlog {
    ($self:expr, $($arg:tt)*) => {
        if $self.verbose_mode {
            eprintln!($($arg)*);
        }
    };
}

/// Level-2 verbose macro: prints only when verbose_level >= 2.
macro_rules! vlog2 {
    ($self:expr, $($arg:tt)*) => {
        if $self.verbose_level >= 2 {
            eprintln!($($arg)*);
        }
    };
}

// ─── Event → table/let dependency precomputation ─────────────────────────────

fn collect_clause_refs(
    clause: &Clause,
    event_names: &BTreeSet<String>,
) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut events = BTreeSet::new();
    let mut others = BTreeSet::new();
    for conj in &clause.patterns {
        for guard in conj {
            if let GuardPattern::Event(pat) = guard {
                if event_names.contains(&pat.name) {
                    events.insert(pat.name.clone());
                } else {
                    others.insert(pat.name.clone());
                }
            }
        }
    }
    collect_filter_refs(&clause.filter, event_names, &mut events, &mut others);
    (events, others)
}

fn collect_filter_refs(
    filter: &FilterExpr,
    event_names: &BTreeSet<String>,
    events: &mut BTreeSet<String>,
    others: &mut BTreeSet<String>,
) {
    match filter {
        FilterExpr::TableLookup { name, .. } => {
            if event_names.contains(name) { events.insert(name.clone()); }
            else { others.insert(name.clone()); }
        }
        FilterExpr::And(l, r) | FilterExpr::Or(l, r) => {
            collect_filter_refs(l, event_names, events, others);
            collect_filter_refs(r, event_names, events, others);
        }
        FilterExpr::Not(f) => collect_filter_refs(f, event_names, events, others),
        FilterExpr::BoolLit(_) | FilterExpr::Compare { .. } => {}
    }
}

/// Transitive closure: all event types that let-def `name` depends on.
fn transitive_event_deps(
    name: &str,
    direct_events: &HashMap<String, BTreeSet<String>>,
    direct_deps:   &HashMap<String, BTreeSet<String>>,
    cache:         &mut HashMap<String, BTreeSet<String>>,
) -> BTreeSet<String> {
    if let Some(c) = cache.get(name) { return c.clone(); }
    cache.insert(name.to_string(), BTreeSet::new()); // break cycles
    let mut all = direct_events.get(name).cloned().unwrap_or_default();
    for dep in direct_deps.get(name).cloned().unwrap_or_default() {
        all.extend(transitive_event_deps(&dep, direct_events, direct_deps, cache));
    }
    cache.insert(name.to_string(), all.clone());
    all
}

/// Build `event → tables`, `event → lets` and `event → rules` dependency maps.
/// The first two drive incremental table/let updates when new events are caused
/// at runtime; the third drives delta evaluation in the fixpoint loop (only
/// rules whose trigger transitively reads a newly-caused event type need
/// re-evaluation).
fn build_event_dep_maps(
    program:     &Program,
    event_names: &BTreeSet<String>,
) -> (HashMap<String, Vec<String>>, HashMap<String, Vec<String>>, HashMap<String, Vec<usize>>) {
    // Direct deps for each let-def
    let mut let_direct_ev:  HashMap<String, BTreeSet<String>> = HashMap::default();
    let mut let_direct_dep: HashMap<String, BTreeSet<String>> = HashMap::default();
    for ld in &program.let_defs {
        let (evs, deps) = collect_clause_refs(&ld.clause, event_names);
        let_direct_ev.insert(ld.name.clone(), evs);
        let_direct_dep.insert(ld.name.clone(), deps);
    }

    // Transitive event deps per let-def
    let mut tc: HashMap<String, BTreeSet<String>> = HashMap::default();
    let mut let_all_ev: HashMap<String, BTreeSet<String>> = HashMap::default();
    for ld in &program.let_defs {
        let all = transitive_event_deps(&ld.name, &let_direct_ev, &let_direct_dep, &mut tc);
        let_all_ev.insert(ld.name.clone(), all);
    }

    // event → lets
    let mut event_to_lets: HashMap<String, Vec<String>> = HashMap::default();
    for (let_name, evs) in &let_all_ev {
        for ev in evs {
            event_to_lets.entry(ev.clone()).or_default().push(let_name.clone());
        }
    }

    // event → tables (direct + via lets)
    let mut event_to_tables: HashMap<String, Vec<String>> = HashMap::default();
    let mut table_all_ev: HashMap<String, BTreeSet<String>> = HashMap::default();
    for td in &program.tables {
        let mut tev: BTreeSet<String> = BTreeSet::new();
        for clause in std::iter::once(&td.add_clause).chain(td.remove_clause.iter()) {
            let (direct_evs, direct_deps) = collect_clause_refs(clause, event_names);
            tev.extend(direct_evs);
            for dep in &direct_deps {
                if let Some(le) = let_all_ev.get(dep) { tev.extend(le.iter().cloned()); }
            }
        }
        for ev in &tev {
            event_to_tables.entry(ev.clone()).or_default().push(td.name.clone());
        }
        table_all_ev.insert(td.name.clone(), tev);
    }

    // event → rules: a rule transitively reads an event type if its trigger
    // names it directly, or references a table/let whose contents depend on it.
    let mut event_to_rules: HashMap<String, Vec<usize>> = HashMap::default();
    for (idx, rule) in program.rules.iter().enumerate() {
        let (mut all_ev, others) = collect_clause_refs(&rule.trigger, event_names);
        for dep in &others {
            if let Some(le) = let_all_ev.get(dep)   { all_ev.extend(le.iter().cloned()); }
            if let Some(te) = table_all_ev.get(dep) { all_ev.extend(te.iter().cloned()); }
        }
        for ev in &all_ev {
            event_to_rules.entry(ev.clone()).or_default().push(idx);
        }
    }

    (event_to_tables, event_to_lets, event_to_rules)
}

// ─── Precomputed let-dep helpers ─────────────────────────────────────────────

/// Collect direct let-def names referenced by a clause (patterns + filter).
/// Used at init time to build per-rule and per-let-def dependency lists so
/// that the hot-path `ensure_let_computed` skips AST traversal.
/// Collect the names of let-like definitions (plain lets, aggregation lets, and
/// table-op lets) that `clause` references, so they can be computed before it.
/// `let_names` must contain every such name (agg/top lets included), since all of
/// them are computed on demand via `ensure_let_computed`.
fn compute_clause_let_refs(clause: &Clause, let_names: &HashSet<String>) -> Vec<String> {
    let mut refs = Vec::new();
    for conj in &clause.patterns {
        for guard in conj {
            if let GuardPattern::Event(pat) = guard {
                if let_names.contains(&pat.name) {
                    refs.push(pat.name.clone());
                }
            }
        }
    }
    compute_filter_let_refs(&clause.filter, let_names, &mut refs);
    refs
}

fn compute_filter_let_refs(filter: &FilterExpr, let_names: &HashSet<String>, refs: &mut Vec<String>) {
    match filter {
        FilterExpr::TableLookup { name, .. } => {
            if let_names.contains(name) { refs.push(name.clone()); }
        }
        FilterExpr::And(l, r) | FilterExpr::Or(l, r) => {
            compute_filter_let_refs(l, let_names, refs);
            compute_filter_let_refs(r, let_names, refs);
        }
        FilterExpr::Not(f) => compute_filter_let_refs(f, let_names, refs),
        FilterExpr::BoolLit(_) | FilterExpr::Compare { .. } => {}
    }
}

// ─── Native built-in function dispatch ──────────────────────────────────────

/// Evaluate standard-library functions in pure Rust, bypassing the Python GIL.
/// Returns None for unknown/user-defined functions so the caller can fall back
/// to Python.
fn dispatch_builtin(name: &str, args: &[Value]) -> Option<Value> {
    use Value::{Int, Float, Str};
    use crate::ast::OrderedFloat as OF;
    Some(match (name, args) {
        // ── Integer arithmetic ──────────────────────────────────────────────
        ("add",          [Int(x), Int(y)])       => Int(x.wrapping_add(*y)),
        ("sub",          [Int(x), Int(y)])       => Int(x.wrapping_sub(*y)),
        ("mul",          [Int(x), Int(y)])       => Int(x.wrapping_mul(*y)),
        ("div",          [Int(x), Int(y)])       => Int(x.wrapping_div(*y)),
        ("pow",          [Int(x), Int(y)])       => Int(x.wrapping_pow(*y as u32)),
        ("usub",         [Int(x)])               => Int(x.wrapping_neg()),
        ("add_time_span",[Int(x), Int(y)])       => Int(x.wrapping_add(*y)),
        // ── Integer comparisons (return 0 / 1) ─────────────────────────────
        ("eq",  [Int(x), Int(y)]) => Int(if x == y { 1 } else { 0 }),
        ("neq", [Int(x), Int(y)]) => Int(if x != y { 1 } else { 0 }),
        ("leq", [Int(x), Int(y)]) => Int(if x <= y { 1 } else { 0 }),
        ("geq", [Int(x), Int(y)]) => Int(if x >= y { 1 } else { 0 }),
        ("lt",  [Int(x), Int(y)]) => Int(if x <  y { 1 } else { 0 }),
        ("gt",  [Int(x), Int(y)]) => Int(if x >  y { 1 } else { 0 }),
        // ── Boolean ─────────────────────────────────────────────────────────
        ("not", [Int(x)])  => Int(if *x == 0 { 1 } else { 0 }),
        ("not", [Value::Bool(b)]) => Int(if !b { 1 } else { 0 }),
        // ── Float arithmetic ────────────────────────────────────────────────
        ("fadd",  [Float(OF(x)), Float(OF(y))]) => Float(OF(x + y)),
        ("fsub",  [Float(OF(x)), Float(OF(y))]) => Float(OF(x - y)),
        ("fmul",  [Float(OF(x)), Float(OF(y))]) => Float(OF(x * y)),
        ("fdiv",  [Float(OF(x)), Float(OF(y))]) => Float(OF(x / y)),
        ("fpow",  [Float(OF(x)), Float(OF(y))]) => Float(OF(x.powf(*y))),
        ("ufsub", [Float(OF(x))])               => Float(OF(-x)),
        // ── Type conversions ────────────────────────────────────────────────
        ("float_of_int",    [Int(x)])    => Float(OF(*x as f64)),
        ("int_of_float",    [Float(OF(x))]) => Int(*x as i64),
        ("string_of_int",   [Int(x)])    => Str(x.to_string().into()),
        ("string_of_float", [Float(OF(x))]) => Str(x.to_string().into()),
        // ── String operations ───────────────────────────────────────────────
        ("conc",   [Str(x), Str(y)]) => Str(format!("{}{}", x, y).into()),
        ("substr", [Str(x), Int(s), Int(e)]) => {
            let s = (*s as usize).min(x.len());
            let e = (*e as usize).min(x.len());
            Str(x[s..e.max(s)].into())
        }
        // Anything else (user-defined or unknown) falls back to Python.
        _ => return None,
    })
}

// ─── Runtime environment ─────────────────────────────────────────────────────

/// Binding environment: variable name → Value.
///
/// Backed by a `Vec` rather than `HashMap` because rules typically bind 2–8
/// variables.  For small `n`, linear scan avoids hashing overhead, per-entry
/// heap allocation and the larger memory footprint of a hash table.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
struct Env(Vec<(Arc<str>, Value)>);

impl Env {
    #[inline] fn new() -> Self { Env(Vec::new()) }

    #[inline]
    fn get(&self, name: &str) -> Option<&Value> {
        // Iterate in reverse so the most-recently-bound shadow wins.
        self.0.iter().rev().find_map(|(k, v)| if k.as_ref() == name { Some(v) } else { None })
    }

    /// Insert a binding.  Keys are `Arc<str>` so that `Env::clone` (which happens
    /// far more often than insert, once per candidate row in the matching
    /// cross-product) is a refcount bump rather than a string allocation.
    #[inline]
    fn insert(&mut self, name: impl Into<Arc<str>>, val: Value) {
        let name = name.into();
        if let Some(slot) = self.0.iter_mut().find(|(k, _)| *k == name) {
            slot.1 = val;
        } else {
            self.0.push((name, val));
        }
    }

    /// Clone with room for `extra` more bindings, so the common
    /// clone-then-insert pattern allocates once instead of clone + regrow.
    #[inline]
    fn clone_with_room(&self, extra: usize) -> Env {
        let mut v = Vec::with_capacity(self.0.len() + extra);
        v.extend_from_slice(&self.0);
        Env(v)
    }

    #[inline]
    fn contains_key(&self, name: &str) -> bool {
        self.0.iter().any(|(k, _)| k.as_ref() == name)
    }

    #[inline]
    fn iter(&self) -> impl Iterator<Item = (&Arc<str>, &Value)> {
        self.0.iter().map(|(k, v)| (k, v))
    }
}

/// Pending obligation from a delayed rule.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct Obligation {
    /// The event to cause / suppress
    event: EventInstance,
    action: RuleAction,
    /// Deadline timestamp (current_ts + delay)
    deadline: u64,
    /// Optional validation filter (must hold at deadline)
    validate: Option<FilterExpr>,
    /// Binding environment captured when the obligation was created
    env: Env,
    /// The rule index that generated this
    rule_idx: usize,
    /// Labels of rules involved (only populated when label_mode is true)
    labels: Vec<String>,
}

pub struct Engine {
    pub program: Program,
    pub tables: HashMap<String, Table>,
    pub let_tables: HashMap<String, Table>,
    /// Let-defs where at least one row had an unbound parameter
    /// → the let-def is universally true (matches any lookup).
    let_full: HashSet<String>,
    /// Names of let-defs already (re)computed during the current evaluation
    /// round.  Used to memoize the lazy let-binding evaluation inside the
    /// fixpoint loop: cleared at the start of every iteration so that a let is
    /// computed at most once per iteration, and only when actually reached by a
    /// table or rule.  Transient state — not part of [`EngineState`].
    let_computed: HashSet<String>,
    /// Set of event names declared as events (for disambiguation)
    event_names: HashSet<String>,
    /// Named boolean predicates: `let` definitions
    let_defs: HashMap<String, LetDef>,
    /// Compiled Python functions: name → (param_names, compiled code object module)
    py_functions: HashMap<String, (Vec<String>, Py<PyAny>)>,
    /// Pending obligations
    obligations: HashMap<u64, Vec<Obligation>>,
    /// Obligations that fire at the next real time-point (from Next operator)
    next_tp_obligations: Vec<Obligation>,
    /// Current timestamp
    current_ts: Option<u64>,
    /// Monotonic time-point index, incremented once per processed time-point
    /// (tick or real).  Injected as the argument of the builtin `tp(i)` event.
    tp_counter: u64,
    /// Events of the most recently processed real time-point.  Obligation
    /// `validate` filters are discharged later (by `emit_proactive`) without an
    /// event context of their own; they compute any let-bindings they reach
    /// on demand against these events — matching the previous eager semantics,
    /// where let-tables held the latest processed time-point's values.
    last_events: Vec<EventInstance>,
    /// The timestamp for which we last emitted proactive output
    /// (to avoid duplicates when multiple TPs share the same ts).
    last_proactive_ts: Option<u64>,
    /// Whether to print rule labels on enforcement actions
    label_mode: bool,
    /// Whether to output enforcement actions in JSON format
    json_mode: bool,
    /// Whether to emit {"sync":true} after each reactive timepoint (subprocess parallel mode)
    sync_mode: bool,
    /// Buffered outputs from the current process_one / finish call.
    output_buffer: Vec<EnfOutput>,
    /// Whether to print verbose debug info
    verbose_mode: bool,
    /// Verbose detail level: 0 = off, 1 = basic (same as verbose_mode), 2 = full detail
    verbose_level: u8,
    /// EDG-ordered evaluation waves and sections (from wave decomposition of the
    /// CDG condensation).  Each wave is a list of independent sections; sections
    /// within the same wave have no dependency between them.
    waves: Vec<Vec<crate::sections::Section>>,
    /// If true, ignore wave/section structure and run all rules as one sequential fixpoint.
    flat_mode: bool,
    /// event_name → table names that need updating when that event type is caused
    event_to_tables: HashMap<String, Vec<String>>,
    /// event_name → let-def names to invalidate when that event type is caused
    event_to_lets: HashMap<String, Vec<String>>,
    /// event_name → rule indices whose trigger transitively reads that event type
    event_to_rules: HashMap<String, Vec<usize>>,
    /// Precomputed: direct let-def names each rule's trigger clause references.
    rule_let_deps: Vec<Vec<String>>,
    /// Precomputed: direct let-def names each let-def's body clause references.
    let_let_deps: HashMap<String, Vec<String>>,
    /// Aggregation lets (`agg let`): name → definition.
    agg_lets: HashMap<String, AggLetDef>,
    /// Table-operation lets (`tableop let`): name → definition.
    top_lets: HashMap<String, TopLetDef>,
    /// Compiled Python table functions (`tfun`): name → callable taking one
    /// argument `rows` (a list of value-lists) and returning a list of lists.
    tfun_functions: HashMap<String, Py<PyAny>>,
    /// Persistent state for incremental (O(1)) aggregations over unbounded Once:
    /// agg-let name → (per-group accumulator, set of already-folded Once rows).
    agg_state: HashMap<String, AggAccumState>,
    /// Current time (verbose mode)
    current_time: std::time::SystemTime
}

/// Running accumulator for one group of an incremental aggregation.
#[derive(Debug, Clone, Default)]
struct GroupAccum {
    count: i64,
    sum_i: i64,
    sum_f: f64,
    is_float: bool,
    min: Option<Value>,
    max: Option<Value>,
}

/// Incremental aggregation state for one `agg let`.
#[derive(Debug, Clone, Default)]
struct AggAccumState {
    groups: HashMap<Vec<Value>, GroupAccum>,
    seen: HashSet<Row>,
}

#[inline]
fn value_to_f64(v: &Value) -> f64 {
    match v { Value::Int(i) => *i as f64, Value::Float(OrderedFloat(f)) => *f, Value::Bool(b) => *b as i64 as f64, _ => 0.0 }
}
#[inline]
fn value_to_i64(v: &Value) -> i64 {
    match v { Value::Int(i) => *i, Value::Float(OrderedFloat(f)) => *f as i64, Value::Bool(b) => *b as i64, _ => 0 }
}

impl GroupAccum {
    fn fold(&mut self, v: &Value) {
        self.count += 1;
        if matches!(v, Value::Float(_)) { self.is_float = true; }
        self.sum_i = self.sum_i.wrapping_add(value_to_i64(v));
        self.sum_f += value_to_f64(v);
        self.min = Some(match self.min.take() { Some(m) => m.min(v.clone()), None => v.clone() });
        self.max = Some(match self.max.take() { Some(m) => m.max(v.clone()), None => v.clone() });
    }
    fn result(&self, op: AggOp) -> Option<Value> {
        if self.count == 0 { return None; }
        match op {
            AggOp::Cnt => Some(Value::Int(self.count)),
            AggOp::Sum => if self.is_float { Some(Value::Float(OrderedFloat(self.sum_f))) }
                          else { Some(Value::Int(self.sum_i)) },
            AggOp::Avg => if self.is_float { Some(Value::Float(OrderedFloat(self.sum_f / self.count as f64))) }
                          else { Some(Value::Int(self.sum_i / self.count)) },
            AggOp::Min => self.min.clone(),
            AggOp::Max => self.max.clone(),
            AggOp::Med | AggOp::Std => None, // not incrementally maintainable
        }
    }
}

/// Reduce a multiset of values with an aggregation op.  Returns None for an
/// empty multiset (so empty groups produce no row, per the spec).
fn agg_reduce(op: AggOp, vals: &[Value]) -> Option<Value> {
    if vals.is_empty() { return None; }
    let is_float = vals.iter().any(|v| matches!(v, Value::Float(_)));
    let n = vals.len() as i64;
    match op {
        AggOp::Cnt => Some(Value::Int(n)),
        AggOp::Sum => if is_float { Some(Value::Float(OrderedFloat(vals.iter().map(value_to_f64).sum()))) }
                      else { Some(Value::Int(vals.iter().map(value_to_i64).sum())) },
        AggOp::Avg => if is_float { Some(Value::Float(OrderedFloat(vals.iter().map(value_to_f64).sum::<f64>() / n as f64))) }
                      else { Some(Value::Int(vals.iter().map(value_to_i64).sum::<i64>() / n)) },
        AggOp::Min => vals.iter().cloned().min(),
        AggOp::Max => vals.iter().cloned().max(),
        AggOp::Med => { let mut s = vals.to_vec(); s.sort(); Some(s[s.len() / 2].clone()) }
        AggOp::Std => {
            let mean = vals.iter().map(value_to_f64).sum::<f64>() / n as f64;
            let var = vals.iter().map(|v| { let d = value_to_f64(v) - mean; d * d }).sum::<f64>() / n as f64;
            Some(Value::Float(OrderedFloat(var.sqrt())))
        }
    }
}

/// Assemble a result row over `columns` from a group key and a result value,
/// looking up each column by name (group var or result var).
fn build_agg_row(columns: &[(String, Ty)], groups: &[String], key: &[Value],
                 result_name: &str, result: &Value) -> Row {
    columns.iter().map(|(n, _)| {
        if n == result_name { result.clone() }
        else {
            match groups.iter().position(|g| g == n) {
                Some(i) => key.get(i).cloned().unwrap_or(Value::Bool(false)),
                None => Value::Bool(false),
            }
        }
    }).collect()
}

/// Assemble a Top result row from a group key and one output tuple.
fn build_top_row(columns: &[(String, Ty)], groups: &[String], key: &[Value],
                 results: &[(String, Ty)], out: &[Value]) -> Row {
    columns.iter().map(|(n, _)| {
        if let Some(i) = groups.iter().position(|g| g == n) {
            key.get(i).cloned().unwrap_or(Value::Bool(false))
        } else if let Some(i) = results.iter().position(|(rn, _)| rn == n) {
            out.get(i).cloned().unwrap_or(Value::Bool(false))
        } else {
            Value::Bool(false)
        }
    }).collect()
}

/// Extract a [`Value`] from a Python object (int / float / bool / str).
fn py_to_value(py: Python, obj: &Py<PyAny>) -> Value {
    if let Ok(b) = obj.extract::<bool>(py) { Value::Bool(b) }
    else if let Ok(i) = obj.extract::<i64>(py) { Value::Int(i) }
    else if let Ok(f) = obj.extract::<f64>(py) { Value::Float(OrderedFloat(f)) }
    else if let Ok(s) = obj.extract::<String>(py) { Value::Str(s.into()) }
    else { Value::Bool(false) }
}

// ─── State persistence ───────────────────────────────────────────────────────

/// Serializable snapshot of mutable engine state.
#[derive(Serialize, Deserialize)]
pub struct EngineState {
    pub tables: HashMap<String, Table>,
    pub let_tables: HashMap<String, Table>,
    pub let_full: BTreeSet<String>,
    pub obligations: HashMap<u64, Vec<Obligation>>,
    pub next_tp_obligations: Vec<Obligation>,
    pub current_ts: Option<u64>,
    pub last_proactive_ts: Option<u64>,
    #[serde(default)]
    pub tp_counter: u64,
}

impl Engine {
    pub fn new(program: Program, label_mode: bool, json_mode: bool, sync_mode: bool, verbose_mode: bool, verbose_level: u8, flat_mode: bool) -> Self {
        let mut event_names: BTreeSet<String> = program
            .event_decls
            .iter()
            .map(|d| d.name.clone())
            .collect();
        // Builtin time-point / time-stamp events.  These are not declared in the
        // program (the OCaml compiler emits `tp(i)` / `ts(t)` as bare predicates);
        // `process_timepoint` injects a singleton tuple for each into every real
        // time-point.  Register them as events here, before the dependency maps
        // are built, so clause feasibility and incremental updates treat them as
        // proper trace events.
        event_names.insert("tp".to_string());
        event_names.insert("ts".to_string());

        let mut tables = HashMap::default();
        
        for td in &program.tables {
            let cols: Vec<String> = td.columns.iter().map(|(n, _)| n.clone()).collect();
            let mut table = Table::new(td.name.clone(), cols);
            table.window = td.window;
            table.lagged = td.lagged;
            tables.insert(td.name.clone(), table);
        }

        let mut let_tables = HashMap::default();

        for ld in &program.let_defs {
            if !ld.is_filter {
                let cols: Vec<String> = ld.params.iter().map(|(n, _)| n.clone()).collect();
                let_tables.insert(ld.name.clone(), Table::new(ld.name.clone(), cols));
            }
        }
        // Aggregation / table-op lets are backed by a result table too.
        for ad in &program.agg_lets {
            let cols: Vec<String> = ad.columns.iter().map(|(n, _)| n.clone()).collect();
            let_tables.insert(ad.name.clone(), Table::new(ad.name.clone(), cols));
        }
        for td in &program.top_lets {
            let cols: Vec<String> = td.columns.iter().map(|(n, _)| n.clone()).collect();
            let_tables.insert(td.name.clone(), Table::new(td.name.clone(), cols));
        }
        let agg_lets: HashMap<String, AggLetDef> =
            program.agg_lets.iter().map(|d| (d.name.clone(), d.clone())).collect();
        let top_lets: HashMap<String, TopLetDef> =
            program.top_lets.iter().map(|d| (d.name.clone(), d.clone())).collect();

        // Collect let definitions
        let let_defs: HashMap<String, LetDef> = program
            .let_defs
            .iter()
            .map(|d| (d.name.clone(), d.clone()))
            .collect();

        // Compile all Python functions (scalar `fun` + table `tfun`) into a
        // SINGLE shared module, preceded by the module-level preamble (imports +
        // shared globals).  Hosting them together means they share one global
        // namespace: imports are visible to every function, stateful globals
        // (e.g. `consent = set()`) persist across calls, and functions can call
        // one another — matching how the legacy tool loads the whole --func file.
        let escape_py_kw = |name: &str| -> String {
            match name {
                "match" | "class" | "def" | "return" | "import" | "from"
                | "if" | "else" | "elif" | "for" | "while" | "with" | "as"
                | "try" | "except" | "finally" | "raise" | "pass" | "break"
                | "continue" | "and" | "or" | "not" | "is" | "in" | "lambda"
                | "global" | "nonlocal" | "del" | "yield" | "assert" | "True"
                | "False" | "None" | "async" | "await" | "type" | "case"
                    => format!("_ef_{}", name),
                _ => name.to_string(),
            }
        };
        let indent = |body: &str| -> String {
            body.lines().map(|l| format!("    {}", l)).collect::<Vec<_>>().join("\n")
        };
        let needs_module = !program.fun_decls.is_empty() || !program.tfun_decls.is_empty();
        let (py_functions, tfun_functions): (
            HashMap<String, (Vec<String>, Py<PyAny>)>,
            HashMap<String, Py<PyAny>>,
        ) = if !needs_module {
            (HashMap::default(), HashMap::default())
        } else {
            Python::with_gil(|py| {
                // Build the single module source: preamble, then every def.
                let mut src = String::new();
                if !program.py_preamble.is_empty() {
                    src.push_str(&program.py_preamble);
                    src.push('\n');
                }
                for fd in &program.fun_decls {
                    src.push_str(&format!(
                        "def {}({}):\n{}\n",
                        escape_py_kw(&fd.name), fd.param_names.join(", "), indent(&fd.body)
                    ));
                }
                for td in &program.tfun_decls {
                    src.push_str(&format!(
                        "def _eftf_{}(rows):\n{}\n", td.name, indent(&td.body)
                    ));
                }
                let module = PyModule::from_code_bound(py, &src, "funcs.py", "funcs")
                    .unwrap_or_else(|e| panic!("Python compilation error in --func module: {}", e));
                let mut py_fns = HashMap::default();
                for fd in &program.fun_decls {
                    let func = module.getattr(escape_py_kw(&fd.name).as_str())
                        .unwrap_or_else(|e| panic!("Cannot find Python function '{}': {}", fd.name, e));
                    py_fns.insert(fd.name.clone(), (fd.param_names.clone(), func.into_any().unbind()));
                }
                let mut tfun_fns = HashMap::default();
                for td in &program.tfun_decls {
                    let func = module.getattr(format!("_eftf_{}", td.name).as_str())
                        .unwrap_or_else(|e| panic!("Cannot find tfun '{}': {}", td.name, e));
                    tfun_fns.insert(td.name.clone(), func.into_any().unbind());
                }
                (py_fns, tfun_fns)
            })
        };

        // Prefer the EDG wave/section structure declared in the .ef
        // (`section …;` / `sync;` markers, parsed into program.waves);
        // fall back to recomputing (each section in its own single-element
        // wave) only when the program carries no markers (older .ef format).
        let waves = if program.waves.is_empty() {
            crate::sections::compute_sections(&program)
        } else {
            program.waves.iter()
                .map(|wave| wave.iter()
                    .map(|s| crate::sections::Section { rules: s.rules.clone(), recursive: s.recursive })
                    .collect())
                .collect()
        };
        let (event_to_tables, event_to_lets, event_to_rules) = build_event_dep_maps(&program, &event_names);

        // Precompute let deps so the hot-path rule loop avoids per-iteration AST traversal.
        // Every on-demand-computed definition: plain lets + aggregation lets +
        // table-op lets.  A clause referencing any of these must trigger its
        // computation first, so dependency scans use this combined name set.
        let let_names: HashSet<String> = let_defs.keys().cloned()
            .chain(agg_lets.keys().cloned())
            .chain(top_lets.keys().cloned())
            .collect();
        let rule_let_deps: Vec<Vec<String>> = program.rules.iter()
            .map(|r| compute_clause_let_refs(&r.trigger, &let_names))
            .collect();
        let mut let_let_deps: HashMap<String, Vec<String>> = program.let_defs.iter()
            .map(|ld| (ld.name.clone(), compute_clause_let_refs(&ld.clause, &let_names)))
            .collect();
        for ad in &program.agg_lets {
            let_let_deps.insert(ad.name.clone(), compute_clause_let_refs(&ad.clause, &let_names));
        }
        for td in &program.top_lets {
            let_let_deps.insert(td.name.clone(), compute_clause_let_refs(&td.clause, &let_names));
        }

        Engine {
            program,
            tables,
            let_tables,
            let_full: HashSet::default(),
            let_computed: HashSet::default(),
            event_names: event_names.into_iter().collect(),
            let_defs,
            py_functions,
            waves,
            flat_mode,
            event_to_tables,
            event_to_lets,
            event_to_rules,
            rule_let_deps,
            let_let_deps,
            agg_lets,
            top_lets,
            tfun_functions,
            agg_state: HashMap::default(),
            obligations: HashMap::default(),
            next_tp_obligations: Vec::new(),
            current_ts: None,
            tp_counter: 0,
            last_events: Vec::new(),
            last_proactive_ts: None,
            label_mode,
            json_mode,
            sync_mode,
            output_buffer: Vec::new(),
            verbose_mode,
            verbose_level,
            current_time: std::time::SystemTime::now()
        }
    }

    /// Prints statistics about the size of tables, number of obligations, etc.
    pub fn print_stats(&mut self) {
        let elapsed = self.current_time.elapsed().unwrap_or_default();
        eprintln!("=== Engine state at timestamp {} ===", self.current_ts.unwrap());
        eprintln!("Tables:");
        for (name, table) in &self.tables {
            eprintln!("  {}: {} rows", name, table.len());
        }
        let pending_obligations: usize = self.obligations.values().map(|v| v.len()).sum();
        eprintln!("Pending obligations: {}", pending_obligations);
        eprintln!("Elapsed time: {:?}", elapsed);
        eprintln!("===============================");
        self.current_time = std::time::SystemTime::now();
    }

    /// Print program summary: let definitions, table definitions, rules overview.
    /// Called once at engine start when verbose_mode is on.
    #[allow(dead_code)]
    pub fn print_program_summary(&self) {
        eprintln!("╔══════════════════════════════════════════════════════════");
        eprintln!("║ Program Summary");
        eprintln!("╠══════════════════════════════════════════════════════════");
        eprintln!("║ Events: {}", self.program.event_decls.len());
        eprintln!("║ Tables: {}", self.program.tables.len());
        eprintln!("║ Let definitions: {}", self.program.let_defs.len());
        eprintln!("║ Rules: {}", self.program.rules.len());
        eprintln!("╠── Let definitions ────────────────────────────────────────");
        for def in &self.program.let_defs {
            let params_str: String = def.params.iter()
                .map(|(n, t)| format!("{}:{}", n, t))
                .collect::<Vec<_>>().join(", ");
            let filter_tag = if def.is_filter { " [filter]" } else { "" };
            let pats: Vec<String> = def.clause.patterns.iter().map(|conj| {
                conj.iter().map(|g| format!("{}", g)).collect::<Vec<_>>().join(" & ")
            }).collect();
            if pats.is_empty() {
                eprintln!("║ let {}({}){} := if {}", def.name, params_str, filter_tag, def.clause.filter);
            } else {
                eprintln!("║ let {}({}){} := {} if {}", def.name, params_str, filter_tag, pats.join(" or "), def.clause.filter);
            }
        }
        eprintln!("╠── Tables ────────────────────────────────────────────────");
        for td in &self.program.tables {
            let cols_str: String = td.columns.iter()
                .map(|(n, t)| format!("{}:{}", n, t))
                .collect::<Vec<_>>().join(", ");
            let lag_tag = if td.lagged { " [lagged]" } else { "" };
            eprintln!("║ table {}({}){}", td.name, cols_str, lag_tag);
            // Show add clause patterns
            let add_pats: Vec<String> = td.add_clause.patterns.iter().map(|conj| {
                conj.iter().map(|g| format!("{}", g)).collect::<Vec<_>>().join(" & ")
            }).collect();
            if !add_pats.is_empty() {
                eprintln!("║   add: {} if {}", add_pats.join(" or "), td.add_clause.filter);
            }
            if let Some(ref rm) = td.remove_clause {
                let rm_pats: Vec<String> = rm.patterns.iter().map(|conj| {
                    conj.iter().map(|g| format!("{}", g)).collect::<Vec<_>>().join(" & ")
                }).collect();
                eprintln!("║   rm:  {} if {}", rm_pats.join(" or "), rm.filter);
            }
        }
        eprintln!("╠── Rules ─────────────────────────────────────────────────");
        for (i, rule) in self.program.rules.iter().enumerate() {
            let action_sym = match rule.action { RuleAction::Cause => "+", RuleAction::Suppress => "-", RuleAction::Observe => "?" };
            let params_str: String = rule.params.iter()
                .map(|p| format!("{}", p))
                .collect::<Vec<_>>().join(", ");
            let trig_pats: Vec<String> = rule.trigger.patterns.iter().map(|conj| {
                conj.iter().map(|g| format!("{}", g)).collect::<Vec<_>>().join(" & ")
            }).collect();
            let delay_str = if let Some(d) = rule.delay { format!(" @+{}", d) } else if rule.tp_offset.is_some() { " @next".into() } else { String::new() };
            eprintln!("║ #{}: {}{}({}){} when {} if {}",
                i, action_sym, rule.event, params_str, delay_str,
                trig_pats.join(" or "), rule.trigger.filter);
        }
        eprintln!("╚══════════════════════════════════════════════════════════");
    }

    /// Process a single time-point.  Returns all [`EnfOutput`]s produced
    /// (proactive output for the previous timestamp + reactive for this one).
    pub fn process_one(&mut self, tp: &TimePoint) -> Vec<EnfOutput> {
        self.process_timepoint(tp);
        std::mem::take(&mut self.output_buffer)
    }

    /// Flush all remaining delayed obligations (call after the last time-point).
    /// Returns any final proactive outputs.
    pub fn finish(&mut self) -> Vec<EnfOutput> {
        if let Some(ts) = self.current_ts {
            self.emit_proactive(ts);
        }
        if let Some(max_ts) = self.obligations.keys().max().cloned() {
            let start = self.current_ts.map_or(0, |t| t + 1);
            if start <= max_ts {
                self.flush_obligations_range(start, max_ts + 1);
            }
        }
        std::mem::take(&mut self.output_buffer)
    }

    // ─── State persistence ───────────────────────────────────────────────────

    /// Save mutable engine state to a JSON file (atomic: write tmp then rename).
    pub fn save_state(&self, path: &str) {
        let state = EngineState {
            tables: self.tables.clone(),
            let_tables: self.let_tables.clone(),
            let_full: self.let_full.iter().cloned().collect(),
            obligations: self.obligations.clone(),
            next_tp_obligations: self.next_tp_obligations.clone(),
            current_ts: self.current_ts,
            last_proactive_ts: self.last_proactive_ts,
            tp_counter: self.tp_counter,
        };
        let json = serde_json::to_string(&state)
            .unwrap_or_else(|e| panic!("Failed to serialize state: {}", e));
        let tmp = format!("{}.tmp", path);
        std::fs::write(&tmp, &json)
            .unwrap_or_else(|e| panic!("Failed to write state file '{}': {}", tmp, e));
        std::fs::rename(&tmp, path)
            .unwrap_or_else(|e| panic!("Failed to rename state file: {}", e));
        eprintln!("[enfflash] State saved to {}", path);
    }

    /// Load mutable engine state from a JSON file (if it exists).
    pub fn load_state(&mut self, path: &str) {
        if !std::path::Path::new(path).exists() {
            eprintln!("[enfflash] No state file found at {}, starting fresh", path);
            return;
        }
        let json = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("Failed to read state file '{}': {}", path, e));
        let state: EngineState = serde_json::from_str(&json)
            .unwrap_or_else(|e| panic!("Failed to deserialize state from '{}': {}", path, e));
        self.tables = state.tables;
        self.let_tables = state.let_tables;
        self.let_full = state.let_full.into_iter().collect();
        self.obligations = state.obligations;
        self.next_tp_obligations = state.next_tp_obligations;
        self.current_ts = state.current_ts;
        self.last_proactive_ts = state.last_proactive_ts;
        self.tp_counter = state.tp_counter;
        eprintln!("[enfflash] State loaded from {}", path);
    }

    fn is_tick_timepoint(&self, tp: &TimePoint) -> bool {
        tp.events.len() == 1 && tp.events[0].name == "tick" && tp.events[0].args.is_empty()
    }

    /// Read-only evaluation of a single rule against a fixed working set.
    /// Produces outcomes (immediate cause/suppress, delayed obligation, or
    /// next-tp obligation) without mutating `self` or the working set, so it can
    /// run in parallel across the rules of a recursive section.  Callers must
    /// have populated the let-tables the trigger reaches (via
    /// `ensure_lets_for_clause`) beforehand.

    fn process_timepoint(&mut self, tp: &TimePoint) {
        self.current_time = std::time::SystemTime::now();
        let new_ts = tp.timestamp;

        // Assign this time-point its index and advance the counter.  Real
        // (non-tick) time-points get the builtin `tp(i)` and `ts(t)` events
        // injected so policies can refer to the current time-point index and
        // timestamp; tick time-points are left untouched (they carry no events
        // and skip reactive processing below).
        let cur_tp = self.tp_counter;
        self.tp_counter += 1;
        let augmented;
        let tp: &TimePoint = if self.is_tick_timepoint(tp) {
            tp
        } else {
            let mut a = tp.clone();
            a.events.push(EventInstance {
                name: "tp".to_string(),
                args: vec![Value::Int(cur_tp as i64)],
            });
            a.events.push(EventInstance {
                name: "ts".to_string(),
                args: vec![Value::Int(new_ts as i64)],
            });
            augmented = a;
            &augmented
        };

        vlog!(self, "\n╔══════════════════════════════════════════════════════════");
        vlog!(self, "║ Timepoint @{} — {} event(s)", new_ts, tp.events.len());
        for ev in &tp.events {
            vlog!(self, "║   {}", ev);
        }
        vlog!(self, "╚══════════════════════════════════════════════════════════");

        // If timestamp advanced, flush obligations for intermediate timestamps
        // and emit proactive output for the previous timestamp.
        match self.current_ts {
            None => {
                self.current_ts = Some(new_ts);
            }
            Some(prev_ts) if new_ts > prev_ts => {
                // Timestamp advanced: emit proactive for prev_ts (if not yet done),
                // then flush obligations for the gap (prev_ts+1 .. new_ts-1).
                self.emit_proactive(prev_ts);
                if new_ts > prev_ts + 1 {
                    // Flush obligations in the gap (prev_ts+1 .. new_ts-1)
                    self.flush_obligations_range(prev_ts + 1, new_ts);
                }
                self.current_ts = Some(new_ts);
            }
            _ => {
                // Same timestamp — just continue accumulating
            }
        }

        // If tick, do not do anything reactive
        if self.is_tick_timepoint(tp) {
            vlog!(self, "  → tick time-point: skipping reactive processing");
            return;
        }

        // Record this time-point's events so that obligations discharged later
        // (after the timestamp advances) can compute their validate lets against
        // the latest real time-point.  Set after the emit/flush above, so those
        // discharges still see the *previous* time-point's events.
        self.last_events = tp.events.clone();

        // Advance metric (windowed) tables to the current timestamp before any
        // reads: activate tuples that have entered their lower bound, evict
        // those past the upper bound, and apply the gap window of lagged (Prev)
        // tables.  Sets each windowed table's anchor clock for this time-point.
        for table in self.tables.values_mut() {
            if table.lagged {
                table.apply_lag_gap(new_ts);
            } else if table.window.is_some() {
                table.advance(new_ts);
            }
        }

        // 1. Update non-lagged tables in original formula order.  Let-defs are
        //    evaluated lazily on demand (and memoized) as tables reach them.
        vlog!(self, "── Phase 1: update non-lagged tables and let-defs ──");
        let phase1_start = Instant::now();
        self.let_computed.clear();
        self.update_tables_and_lets(&tp.events, false);
        let phase1_elapsed = phase1_start.elapsed();

        // 2. Evaluate rules → produce suppress / cause lists
        let phase2_start = Instant::now();
        //    We use a fixpoint loop: caused events are added to the event set
        //    and rules are re-evaluated until no new events are produced.
        let mut all_suppress: Vec<(EventInstance, Vec<String>)> = Vec::new();
        let mut all_cause: Vec<(EventInstance, Vec<String>)> = Vec::new();

        // The working set of events starts with the timepoint's events and grows
        // as new events are caused in each iteration.
        let mut working_events: Vec<EventInstance> = tp.events.clone();
        // Track labels per event in the working set so that labels propagate
        // through the causal chain (label stack).
        let mut working_labels: HashMap<(String, Vec<Value>), Vec<String>> =
            HashMap::default();
        // Track which (event_name, args) pairs we've already produced to detect
        // new additions.  Pre-populate with the timepoint's own events so that
        // we never cause an event that already exists.
        let mut caused_set: HashSet<(String, Vec<Value>)> = HashSet::default();
        for ev in &tp.events {
            caused_set.insert((ev.name.clone(), ev.args.clone()));
        }
        let mut suppressed_set: HashSet<(String, Vec<Value>)> = HashSet::default();

        // Drain next-tp obligations (from Next operator) — they fire reactively
        // when the appropriate real time-point arrives.  A chain of `n` nested
        // NEXT operators fires `n` real time-points ahead; `ob.deadline` holds
        // the number of real time-points still to wait.  Obligations not yet due
        // are decremented and re-queued (into the now-emptied vector, so they are
        // not re-processed this round); only those reaching 0 fire here.
        let pending_next: Vec<Obligation> = std::mem::take(&mut self.next_tp_obligations);
        for mut ob in pending_next {
            if ob.deadline > 1 {
                ob.deadline -= 1;
                self.next_tp_obligations.push(ob);
                continue;
            }
            let valid = match &ob.validate {
                Some(f) => {
                    // On-demand: compute any let-bindings the validate filter
                    // reaches, against this time-point's events.
                    self.ensure_lets_for_filter(f, &tp.events);
                    self.eval_filter(f, &ob.env, &[])
                }
                None => true,
            };
            if valid {
                match ob.action {
                    RuleAction::Cause => {
                        let key = (ob.event.name.clone(), ob.event.args.clone());
                        if !caused_set.contains(&key) {
                            caused_set.insert(key);
                            working_events.push(ob.event.clone());
                            all_cause.push((ob.event, ob.labels));
                        }
                    }
                    RuleAction::Suppress => {
                        // Suppress only applies if the event is actually present
                        // in the incoming time-point's events.
                        let key = (ob.event.name.clone(), ob.event.args.clone());
                        if caused_set.contains(&key) && !suppressed_set.contains(&key) {
                            suppressed_set.insert(key);
                            all_suppress.push((ob.event, ob.labels));
                        }
                    }
                    RuleAction::Observe => {}
                }
            }
        }

        // Phase 1 updated tables with tp.events.  `last_processed` tracks how many
        // working_events have been reflected in tables/lets; incremental updates only
        // process the slice working_events[last_processed..] against affected tables.
        let mut last_processed = tp.events.len();

        const MAX_ITERATIONS: usize = 100;

        // ── Build the section list to evaluate ───────────────────────────────
        // flat_mode: one big sequential fixpoint over all rules, ignoring waves.
        let waves = std::mem::take(&mut self.waves);
        let flat_sections: Vec<crate::sections::Section>;
        let eval_waves: &[Vec<crate::sections::Section>];
        let flat_wrap: Vec<Vec<crate::sections::Section>>;
        if self.flat_mode {
            let all_rules: Vec<usize> = waves.iter()
                .flat_map(|w| w.iter())
                .flat_map(|s| s.rules.iter().copied())
                .collect();
            flat_sections = vec![crate::sections::Section { rules: all_rules, recursive: true }];
            flat_wrap = vec![flat_sections.clone()];
            eval_waves = &flat_wrap;
        } else {
            eval_waves = &waves;
            flat_sections = vec![];
            flat_wrap = vec![];
        }

        for wave in eval_waves {
          for sec in wave {
          let max_passes = if sec.recursive { MAX_ITERATIONS } else { 1 };
          for _iteration in 0..max_passes {
            let iter_start = Instant::now();

            // Incremental update: only process events added since last update.
            // Look up which tables/lets are affected by each new event type and
            // update only those — instead of rescanning all 100+ tables each time.
            // Delta evaluation: after the first pass, only rules whose trigger
            // transitively reads one of the newly-added event types can produce
            // new bindings — unaffected rules would re-derive the exact same
            // events, which the caused/suppressed dedup sets discard anyway.
            let mut affected_rules: Option<HashSet<usize>> = None;
            if working_events.len() > last_processed {
                let mut aff_tables: HashSet<String> = HashSet::default();
                let mut aff_lets:   HashSet<String> = HashSet::default();
                let mut aff_rules:  HashSet<usize>  = HashSet::default();
                for ev in &working_events[last_processed..] {
                    if let Some(ts) = self.event_to_tables.get(&ev.name) {
                        for t in ts { aff_tables.insert(t.clone()); }
                    }
                    if let Some(ls) = self.event_to_lets.get(&ev.name) {
                        for l in ls { aff_lets.insert(l.clone()); }
                    }
                    if let Some(rs) = self.event_to_rules.get(&ev.name) {
                        aff_rules.extend(rs.iter().copied());
                    }
                }
                for l in &aff_lets { self.let_computed.remove(l); }
                if !aff_tables.is_empty() {
                    self.update_tables_and_lets_filtered(&working_events, false, Some(&aff_tables));
                }
                last_processed = working_events.len();
                if _iteration > 0 {
                    affected_rules = Some(aff_rules);
                }
            }

            vlog!(self, "── Phase 2: fixpoint iteration {} ({} events in working set) ──",
                  _iteration, working_events.len());
            let mut new_suppress: Vec<(EventInstance, Vec<String>)> = Vec::new();
            let mut new_cause: Vec<(EventInstance, Vec<String>)> = Vec::new();

            // Event names present in the working set, for the per-rule
            // feasibility pre-check (rebuilt per iteration as the set grows).
            let present_names: HashSet<String> =
                working_events.iter().map(|e| e.name.clone()).collect();

            for &rule_idx in &sec.rules {
                if let Some(aff) = &affected_rules {
                    if !aff.contains(&rule_idx) { continue; }
                }
                // SAFETY: program.rules is not modified during rule evaluation;
                // raw ptr bypasses the borrow checker so we can still call &mut self
                // methods (e.g. self.obligations.push) while holding a rule reference.
                let rule: &RuleDef = unsafe { &*self.program.rules.as_ptr().add(rule_idx) };
                // Cheap name-level pre-check: skip the rule (including its let
                // computation) when its trigger demands an event that isn't there.
                if !self.clause_feasible(&rule.trigger, &present_names) {
                    continue;
                }
                // Ensure lets via precomputed dep list — avoids AST traversal and rule clone.
                // SAFETY: rule_let_deps is built once in `new` and never mutated during
                // evaluation; the raw ptr lets us iterate it while calling &mut self.
                let deps: *const Vec<String> = &self.rule_let_deps[rule_idx];
                for dep in unsafe { &*deps } { self.ensure_let_computed(dep, &working_events); }
                let bindings = self.match_clause_against_events(&rule.trigger, &working_events);

                let action_sym = match rule.action { RuleAction::Cause => "+", RuleAction::Suppress => "-", RuleAction::Observe => "?" };

                if self.verbose_mode && bindings.is_empty() {
                    // Diagnose *why* the rule did not fire: distinguish guard miss vs filter miss.
                    let diagnosis = self.diagnose_no_match(&rule.trigger, &working_events);
                    eprintln!("  rule #{} {}{}  → NO MATCH:\n{}",
                        rule_idx, action_sym, rule.event, diagnosis);
                }

                if self.verbose_level >= 2 && !bindings.is_empty() {
                    eprintln!("  [v2] rule #{} {}{}({}) → {} binding(s)",
                        rule_idx, action_sym, rule.event,
                        rule.params.iter().map(|p| format!("{:?}", p)).collect::<Vec<_>>().join(", "),
                        bindings.len());
                    for (bi, env) in bindings.iter().enumerate() {
                        let env_str: String = env.iter()
                            .map(|(k,v)| format!("{}={}", k, v))
                            .collect::<Vec<_>>().join(", ");
                        eprintln!("  [v2]   binding {}: {{{}}}", bi, env_str);
                    }
                }

                let rule_label: Vec<String> = if self.label_mode {
                    rule.label.iter().cloned().collect()
                } else {
                    vec![]
                };

                for env in &bindings {
                    // Collect inherited labels from matched trigger pattern events
                    let inherited_labels: Vec<String> = if self.label_mode {
                        let mut inh = Vec::new();
                        for disj in &rule.trigger.patterns {
                            for guard in disj {
                                if let GuardPattern::Event(pat) = guard {
                                    let resolved_args: Vec<Value> = pat.args.iter().map(|a| {
                                        match a {
                                            PatternArg::Var(name) => {
                                                env.get(name).cloned().unwrap_or(Value::Bool(false))
                                            }
                                            PatternArg::Literal(v) => v.clone(),
                                            PatternArg::Wildcard => Value::Bool(false),
                                        }
                                    }).collect();
                                    let key = (pat.name.clone(), resolved_args);
                                    if let Some(labels) = working_labels.get(&key) {
                                        for l in labels {
                                            if !inh.contains(l) {
                                                inh.push(l.clone());
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        inh
                    } else {
                        vec![]
                    };

                    // ── Regular event rule ───────────────────────────────
                    let args: Vec<Value> = rule
                        .params
                        .iter()
                        .map(|p| self.try_eval_term(p, env).clone().unwrap_or(Value::Bool(false)))
                        .collect();
                    let ev = EventInstance { name: rule.event.clone(), args };
                    vlog!(self, "  rule #{} {}{}  → MATCHED → {}",
                            rule_idx, action_sym, rule.event, ev);

                    // Combine rule's own label with inherited labels
                    let combined_labels: Vec<String> = if self.label_mode {
                        let mut all: Vec<String> = Vec::new();
                        for l in rule_label.iter().chain(inherited_labels.iter()) {
                            if !all.contains(l) {
                                all.push(l.clone());
                            }
                        }
                        all
                    } else {
                        vec![]
                    };

                    if let Some(tp_off) = rule.tp_offset {
                        // Next-tp obligation: fires `tp_off` real time-points ahead
                        // (tp_off == 1 for a single NEXT; n for n nested NEXTs).
                        // `deadline` carries the remaining number of real
                        // time-points to wait; the drain loop decrements it.
                        let tp_off = tp_off.max(1);
                        vlog!(self, "    → next-tp obligation (+{} tp): {} {}", tp_off, action_sym, ev);
                        self.next_tp_obligations.push(Obligation {
                            event: ev,
                            action: rule.action,
                            deadline: tp_off,
                            validate: rule.validate.clone(),
                            env: env.clone(),
                            rule_idx,
                            labels: combined_labels,
                        });
                    } else if let Some(delay) = rule.delay {
                        vlog!(self, "    → obligation: {} {} at ts+{}", action_sym, ev, delay);
                        self.obligations
                            .entry(self.current_ts.unwrap() + delay)
                            .or_default()
                            .push(Obligation {
                                event: ev,
                                action: rule.action,
                                deadline: self.current_ts.unwrap() + delay,
                                validate: rule.validate.clone(),
                                env: env.clone(),
                                rule_idx,
                                labels: combined_labels,
                            });
                    } else {
                        match rule.action {
                            RuleAction::Suppress => {
                                let key = (ev.name.clone(), ev.args.clone());
                                if !suppressed_set.contains(&key) {
                                    suppressed_set.insert(key);
                                    if !combined_labels.is_empty() {
                                        working_labels.insert((ev.name.clone(), ev.args.clone()), combined_labels.clone());
                                    }
                                    working_events.push(ev.clone());
                                    new_suppress.push((ev, combined_labels));
                                }
                            }
                            RuleAction::Cause => {
                                let key = (ev.name.clone(), ev.args.clone());
                                if !caused_set.contains(&key) {
                                    caused_set.insert(key);
                                    if !combined_labels.is_empty() {
                                        working_labels.insert((ev.name.clone(), ev.args.clone()), combined_labels.clone());
                                    }
                                    working_events.push(ev.clone());
                                    new_cause.push((ev, combined_labels));
                                }
                            }
                            RuleAction::Observe => {}
                        }
                    }
                }
            }

            let iter_elapsed = iter_start.elapsed();

            // Check if we reached the fixpoint (no new events)
            if new_cause.is_empty() && new_suppress.is_empty() {
                if self.verbose_mode {
                    eprintln!("    iter {}: {:.1?} (fixpoint)", _iteration, iter_elapsed);
                }
                vlog!(self, "  → fixpoint reached after {} iteration(s)", _iteration + 1);
                break;
            }

            if self.verbose_mode {
                eprintln!("    iter {}: {:.1?} (+{} cause, +{} suppress)",
                    _iteration, iter_elapsed, new_cause.len(), new_suppress.len());
            }

            // Level-2: show summary of this iteration's new events
            if self.verbose_level >= 2 {
                eprintln!("  ┌─ Iteration {} results ─", _iteration);
                for (ev, _) in &new_cause {
                    eprintln!("  │ + {}", ev);
                }
                for (ev, _) in &new_suppress {
                    eprintln!("  │ - {}", ev);
                }
                eprintln!("  └─────────────────────────────");
            }

            all_suppress.extend(new_suppress);
            all_cause.extend(new_cause);
          }
          } // end sec in wave
        } // end wave in waves
        self.waves = waves;

        // Final incremental update: events caused in the last section of the last
        // wave haven't triggered a table update yet (the check runs at iteration
        // start, so the last-emitted batch is never processed inside the loop).
        // Update now so that persistent tables (e.g. Once0) remember caused events
        // and don't fire again at the next timepoint.
        if working_events.len() > last_processed {
            let mut aff_tables: HashSet<String> = HashSet::default();
            let mut aff_lets:   HashSet<String> = HashSet::default();
            for ev in &working_events[last_processed..] {
                if let Some(ts) = self.event_to_tables.get(&ev.name) {
                    for t in ts { aff_tables.insert(t.clone()); }
                }
                if let Some(ls) = self.event_to_lets.get(&ev.name) {
                    for l in ls { aff_lets.insert(l.clone()); }
                }
            }
            for l in &aff_lets { self.let_computed.remove(l); }
            if !aff_tables.is_empty() {
                self.update_tables_and_lets_filtered(&working_events, false, Some(&aff_tables));
            }
        }

        let phase2_elapsed = phase2_start.elapsed();

        // Level-2: print full summary of reactive enforcement decisions
        if self.verbose_level >= 2 {
            eprintln!("  ┌─ Reactive summary @{} ─", new_ts);
            if all_suppress.is_empty() && all_cause.is_empty() {
                eprintln!("  │ (no enforcement actions)");
            }
            for (ev, _) in &all_suppress {
                if !ev.name.starts_with("Cau_") && !ev.name.starts_with("Sup_") {
                    eprintln!("  │ SUPPRESS {}", ev);
                }
            }
            for (ev, _) in &all_cause {
                if !ev.name.starts_with("Cau_") && !ev.name.starts_with("Sup_") {
                    eprintln!("  │ CAUSE {}", ev);
                }
            }
            // Internal Cau_/Sup_ events (condensed)
            let n_internal_cau = all_cause.iter().filter(|(ev, _)| ev.name.starts_with("Cau_") || ev.name.starts_with("Sup_")).count();
            let n_internal_sup = all_suppress.iter().filter(|(ev, _)| ev.name.starts_with("Cau_") || ev.name.starts_with("Sup_")).count();
            if n_internal_cau > 0 || n_internal_sup > 0 {
                eprintln!("  │ ({} internal cause, {} internal suppress)", n_internal_cau, n_internal_sup);
            }
            eprintln!("  └─────────────────────────────");
        }

        // (Tables are now updated during the fixpoint, no separate Phase 2a needed)

        // Proactive output is deferred: it will be emitted when the timestamp
        // actually advances (or at finish()), so that multiple TPs at the same
        // timestamp produce only one proactive line.
        let phase2b_start = Instant::now();
        let phase2b_elapsed = phase2b_start.elapsed();

        // 3. Update lagged tables
        vlog!(self, "── Phase 3: update lagged tables ──");
        let phase3_start = Instant::now();
        // Lagged tables compute any let-bindings they reach on demand; lets
        // already memoized during the fixpoint above are reused as-is.
        // A lagged (Prev) table reflects only the immediately-preceding
        // time-point, so clear it before repopulating with this time-point's
        // events, and record this timestamp as the anchor for the next
        // time-point's gap check.
        for table in self.tables.values_mut() {
            if table.lagged {
                table.clear();
                table.prev_ts = Some(new_ts);
            }
        }
        self.update_tables_and_lets(&tp.events, true);
        let phase3_elapsed = phase3_start.elapsed();

        // Emit reactive output now that all phases are done, so we can include accurate timing.
        let total_elapsed = phase1_elapsed + phase2_elapsed + phase2b_elapsed + phase3_elapsed;
        self.collect_output(&all_suppress, &all_cause, false, Some(total_elapsed.as_nanos() as u64));
        if self.sync_mode {
            // Print the buffered reactive output immediately, then the sync marker.
            // (Subprocess mode: output must reach the orchestrator before we block.)
            let outputs = std::mem::take(&mut self.output_buffer);
            self.print_outputs(&outputs);
            println!("{{\"sync\":true}}");
        }

        if self.verbose_mode {
            eprintln!("── Timing @{}: total {:.1?} │ P1(tables+lets) {:.1?} │ P2(fixpoint) {:.1?} │ P2b(obligations) {:.1?} │ P3(lagged) {:.1?}",
                new_ts, total_elapsed, phase1_elapsed, phase2_elapsed, phase2b_elapsed, phase3_elapsed);
            self.print_stats();
        }
    }

    /// Emit proactive output for a given timestamp (discharge obligations + print).
    /// Does nothing if proactive was already emitted for this ts.
    fn emit_proactive(&mut self, ts: u64) {
        if self.last_proactive_ts == Some(ts) {
            return; // already emitted
        }
        self.last_proactive_ts = Some(ts);
        let saved_ts = self.current_ts;
        self.current_ts = Some(ts);
        let mut proactive_cause: Vec<(EventInstance, Vec<String>)> = Vec::new();
        let mut proactive_suppress: Vec<(EventInstance, Vec<String>)> = Vec::new();
        let mut seen_cause: HashSet<(String, Vec<Value>)> = HashSet::default();
        let mut seen_suppress: HashSet<(String, Vec<Value>)> = HashSet::default();
        // Validate filters reach let-bindings on demand, against the most
        // recently processed time-point's events (cloned to satisfy the borrow
        // checker — `ensure_lets_for_filter` mutates the let-tables).
        let validate_events = self.last_events.clone();
        for ob in self.obligations.remove(&ts).unwrap_or_default() {
            let valid = match &ob.validate {
                Some(f) => {
                    self.ensure_lets_for_filter(f, &validate_events);
                    self.eval_filter(f, &ob.env, &[])
                }
                None => true,
            };
            if valid {
                let key = (ob.event.name.clone(), ob.event.args.clone());
                match ob.action {
                    RuleAction::Cause => {
                        if seen_cause.insert(key) {
                            proactive_cause.push((ob.event, ob.labels));
                        }
                    }
                    RuleAction::Suppress => {
                        if seen_suppress.insert(key) {
                            proactive_suppress.push((ob.event, ob.labels));
                        }
                    }
                    RuleAction::Observe  => {}
                }
            }
        }
        self.collect_output(&proactive_suppress, &proactive_cause, true, None);
        self.current_ts = saved_ts;
    }

    /// Discharge obligations for timestamps in [from_ts, up_to_ts).
    fn flush_obligations_range(&mut self, from_ts: u64, up_to_ts: u64) {
        vlog!(self, "── Flushing obligations in [{}, {}) ──", from_ts, up_to_ts);
        for ts in from_ts..up_to_ts {
            self.emit_proactive(ts);
        }
    }


    /// Build an [`EnfOutput`] from raw cause/suppress lists and push it onto
    /// `self.output_buffer`.  Synthetic `Cau_` / `Sup_` events are filtered out.
    fn collect_output(
        &mut self,
        suppress: &[(EventInstance, Vec<String>)],
        cause:    &[(EventInstance, Vec<String>)],
        proactive: bool,
        dur_nanos: Option<u64>,
    ) {
        let ts = self.current_ts.unwrap();
        let latency_micros = self.current_time.elapsed().unwrap_or_default().as_micros() as u64;
        let cause_filtered: Vec<_> = cause.iter()
            .filter(|(ev, _)| !ev.name.starts_with("Cau_") && !ev.name.starts_with("Sup_"))
            .cloned().collect();
        let suppress_filtered: Vec<_> = suppress.iter()
            .filter(|(ev, _)| !ev.name.starts_with("Cau_") && !ev.name.starts_with("Sup_"))
            .cloned().collect();
        self.output_buffer.push(EnfOutput {
            ts,
            proactive,
            cause:    cause_filtered,
            suppress: suppress_filtered,
            dur_nanos,
            latency_micros,
        });
    }

    /// Print a slice of [`EnfOutput`] values using this engine's display mode.
    pub fn print_outputs(&self, outputs: &[EnfOutput]) {
        for out in outputs {
            out.print(self.json_mode, self.label_mode);
        }
    }

    // ─── Unified table + let-def updates (in original formula order) ────────

    /// Like `update_tables_and_lets` but only processes the tables whose names
    /// are in `only_tables` (used for incremental updates).
    fn update_tables_and_lets_filtered(
        &mut self,
        events: &[EventInstance],
        lagged: bool,
        only_tables: Option<&HashSet<String>>,
    ) {
        let present_names: HashSet<String> = events.iter().map(|e| e.name.clone()).collect();
        let items = std::mem::take(&mut self.program.items);
        for item in &items {
            match item {
                ProgramItem::Table(td) => {
                    if td.lagged != lagged {
                        continue;
                    }
                    if let Some(filter) = only_tables {
                        if !filter.contains(&td.name) {
                            continue;
                        }
                    }
                    // Name-level pre-check: skip the table (and its let
                    // computation) when neither clause can match these events.
                    let add_feasible = self.clause_feasible(&td.add_clause, &present_names);
                    let rm_feasible = td.remove_clause.as_ref()
                        .map_or(false, |c| self.clause_feasible(c, &present_names));
                    if !add_feasible && !rm_feasible {
                        continue;
                    }
                    if let Some(ref rm_clause) = td.remove_clause {
                        if rm_feasible { self.ensure_lets_for_clause(rm_clause, events); }
                    }
                    if add_feasible { self.ensure_lets_for_clause(&td.add_clause, events); }
                    if rm_feasible {
                        if let Some(ref rm_clause) = td.remove_clause {
                        let rm_envs = if rm_clause.patterns.is_empty() || rm_clause.patterns.iter().all(|d| d.is_empty()) {
                            if let Some(table) = self.tables.get(&td.name) {
                                let mut envs = Vec::new();
                                for row in table.iter() {
                                    let mut env = Env::new();
                                    for ((col_name, _), val) in td.columns.iter().zip(row.iter()) {
                                        env.insert(col_name.as_str(), val.clone());
                                    }
                                    envs.push(env);
                                }
                                envs
                            } else {
                                vec![]
                            }
                        } else {
                            self.match_disjunctive_patterns_against_events(&rm_clause.patterns, events)
                        };
                        for env in &rm_envs {
                            let row: Row = td.columns.iter()
                                .map(|(col_name, _)| {
                                    env.get(col_name).unwrap_or_else(|| {
                                        panic!(
                                            "Table '{}' remove clause: column '{}' not bound by patterns",
                                            td.name, col_name
                                        )
                                    }).clone()
                                })
                                .collect();
                            if self.eval_filter(&rm_clause.filter, env, events) {
                                if let Some(table) = self.tables.get_mut(&td.name) {
                                    table.remove(&row);
                                }
                            }
                        }
                        }
                    }
                    if add_feasible {
                        let add_bindings = self.match_clause_against_events(&td.add_clause, events);
                        for env in &add_bindings {
                            let row: Row = td.columns.iter()
                                .map(|(col_name, _)| env.get(col_name).cloned().unwrap_or(Value::Bool(false)))
                                .collect();
                            if let Some(table) = self.tables.get_mut(&td.name) {
                                table.add(row);
                            }
                        }
                    }
                }
                ProgramItem::Let(_) | ProgramItem::Agg(_) | ProgramItem::Top(_) => {}
                ProgramItem::Rule(_) => {}
                ProgramItem::SectionMark(_) | ProgramItem::WaveSync => {}
            }
        }
        self.program.items = items;
    }

    /// Update tables in program order.  Let-defs are never recomputed eagerly
    /// here; instead each table clause first triggers on-demand, memoized
    /// computation of just the let-bindings it reaches (see
    /// [`Self::ensure_lets_for_clause`]).
    fn update_tables_and_lets(&mut self, events: &[EventInstance], lagged: bool) {
        // Take items out temporarily — none of the called methods access program.items,
        // so self can be mutably borrowed inside the loop without cloning the full Vec.
        let present_names: HashSet<String> = events.iter().map(|e| e.name.clone()).collect();
        let items = std::mem::take(&mut self.program.items);
        for item in &items {
            match item {
                ProgramItem::Table(td) => {
                    if td.lagged != lagged {
                        continue;
                    }
                    // Name-level pre-check: skip the table (and its let
                    // computation) when neither clause can match these events.
                    let add_feasible = self.clause_feasible(&td.add_clause, &present_names);
                    let rm_feasible = td.remove_clause.as_ref()
                        .map_or(false, |c| self.clause_feasible(c, &present_names));
                    if !add_feasible && !rm_feasible {
                        continue;
                    }
                    // On-demand: compute any let-bindings this table's clauses reach.
                    if let Some(ref rm_clause) = td.remove_clause {
                        if rm_feasible { self.ensure_lets_for_clause(rm_clause, events); }
                    }
                    if add_feasible { self.ensure_lets_for_clause(&td.add_clause, events); }
                    // Process remove clause FIRST, then add.
                    // If both match the same row, add wins (matches Since semantics).
                    if let Some(ref rm_clause) = td.remove_clause.as_ref().filter(|_| rm_feasible) {
                        let rm_envs = if rm_clause.patterns.is_empty() || rm_clause.patterns.iter().all(|d| d.is_empty()) {
                            if let Some(table) = self.tables.get(&td.name) {
                                let mut envs = Vec::new();
                                for row in table.iter() {
                                    let mut env = Env::new();
                                    for ((col_name, _), val) in td.columns.iter().zip(row.iter()) {
                                        env.insert(col_name.as_str(), val.clone());
                                    }
                                    envs.push(env);
                                }
                                envs
                            } else {
                                vec![]
                            }
                        } else {
                            self.match_disjunctive_patterns_against_events(&rm_clause.patterns, events)
                        };
                        for env in &rm_envs {
                            let row: Row = td.columns.iter()
                                .map(|(col_name, _)| {
                                    env.get(col_name).unwrap_or_else(|| {
                                        panic!(
                                            "Table '{}' remove clause: column '{}' not bound by patterns",
                                            td.name, col_name
                                        )
                                    }).clone()
                                })
                                .collect();
                            if self.eval_filter(&rm_clause.filter, env, events) {
                                if let Some(table) = self.tables.get_mut(&td.name) {
                                    let existed = table.remove(&row);
                                    if existed {
                                        vlog!(self, "  table {} -= [{}]", td.name,
                                              row.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "));
                                    }
                                }
                            }
                        }
                    }

                    // Process add clause (after remove, so add wins on conflict)
                    if add_feasible {
                        let add_bindings = self.match_clause_against_events(&td.add_clause, events);
                        if self.verbose_level >= 2 && !add_bindings.is_empty() {
                            eprintln!("  [v2] table {} add clause: {} binding(s) from {} events",
                                td.name, add_bindings.len(), events.len());
                        }
                        if self.verbose_level >= 2 && add_bindings.is_empty() && td.name.starts_with("Once") {
                            eprintln!("  [v2] table {} add clause: NO bindings (filter unsatisfied) with {} events",
                                td.name, events.len());
                        }
                        for env in &add_bindings {
                            let row: Row = td
                                .columns
                                .iter()
                                .map(|(col_name, _)| {
                                    env.get(col_name).cloned().unwrap_or(Value::Bool(false))
                                })
                                .collect();
                            if let Some(table) = self.tables.get_mut(&td.name) {
                                let is_new = table.add(row.clone());
                                if is_new {
                                    vlog!(self, "  table {} += [{}]", td.name,
                                          row.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "));
                                }
                            }
                        }
                    }
                }
                // Let-defs are computed on demand (and memoized) the moment a
                // table or rule reaches them — never eagerly here.
                ProgramItem::Let(_) | ProgramItem::Agg(_) | ProgramItem::Top(_) => {}
                ProgramItem::Rule(_) => {} // rules handled separately
                ProgramItem::SectionMark(_) | ProgramItem::WaveSync => {} // markers, not tables/lets
            }
        }
        self.program.items = items;

        // Level-2: dump all non-empty table and let-table contents after update
        if self.verbose_level >= 2 {
            eprintln!("  ┌─ Table contents after update ─");
            let mut any = false;
            for (name, table) in &self.tables {
                if table.len() > 0 {
                    any = true;
                    eprintln!("  │ {} ({} rows):", name, table.len());
                    for row in table.iter() {
                        eprintln!("  │   [{}]",
                            row.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "));
                    }
                }
            }
            for (name, table) in &self.let_tables {
                if table.len() > 0 {
                    any = true;
                    eprintln!("  │ {} ({} rows):", name, table.len());
                    for row in table.iter() {
                        eprintln!("  │   [{}]",
                            row.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "));
                    }
                }
            }
            if !any {
                eprintln!("  │ (all tables empty)");
            }
            eprintln!("  └─────────────────────────────");
        }
    }

    // ─── Lazy let-binding evaluation ───────────────────────────────────────────

    /// Recompute one (non-filter) let-def's table from scratch against `events`.
    /// This is the body that used to run eagerly in the `ProgramItem::Let` arm;
    /// callers are responsible for first computing any let-bindings it depends on.
    fn compute_let_table(&mut self, ld: &LetDef, events: &[EventInstance]) {
        // Clear previous rows — let-defs are re-evaluated from scratch.
        if let Some(let_table) = self.let_tables.get_mut(&ld.name) {
            let_table.clear();
        }
        self.let_full.remove(&ld.name);
        // Name-level pre-check: with these events the clause cannot match, so
        // the (already cleared) table is final.
        let present_names: HashSet<String> = events.iter().map(|e| e.name.clone()).collect();
        if !self.clause_feasible(&ld.clause, &present_names) {
            return;
        }
        let add_bindings = self.match_clause_against_events(&ld.clause, events);
        if self.verbose_level >= 2 && !add_bindings.is_empty() {
            eprintln!("  [v2] let table {} clause: {} binding(s) from {} events",
                ld.name, add_bindings.len(), events.len());
        }
        for env in &add_bindings {
            // Check if all parameters are bound in the env
            let all_bound = ld.params.iter().all(|(col_name, _)| env.contains_key(col_name));
            if !all_bound {
                // At least one parameter is unbound → the let-def
                // is universally true (matches any argument tuple).
                self.let_full.insert(ld.name.clone());
            }
            let row: Row = ld
                .params
                .iter()
                .map(|(col_name, _)| {
                    env.get(col_name).cloned().unwrap_or(Value::Bool(false))
                })
                .collect();
            if self.verbose_mode {
                if let Some(let_table) = self.let_tables.get_mut(&ld.name) {
                    if let_table.add(row.clone()) {
                        vlog!(self, "  let table {} += [{}]", ld.name,
                              row.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "));
                    }
                }
            } else if let Some(let_table) = self.let_tables.get_mut(&ld.name) {
                let_table.add(row);
            }
        }
    }

    /// Evaluate an aggregation let as a trace transducer: enumerate the
    /// subformula's valuations, group by the grouping vars, reduce the term
    /// column with the op, and (re)fill the result table.
    fn compute_agg_let(&mut self, ad: &AggLetDef, events: &[EventInstance]) {
        if ad.incremental.is_some() {
            return self.compute_agg_incremental(ad, events);
        }
        if let Some(t) = self.let_tables.get_mut(&ad.name) { t.clear(); }
        let bindings = self.match_clause_against_events(&ad.clause, events);
        let mut groups: HashMap<Vec<Value>, Vec<Value>> = HashMap::default();
        for env in &bindings {
            let key: Vec<Value> = ad.groups.iter()
                .map(|g| env.get(g).cloned().unwrap_or(Value::Bool(false)))
                .collect();
            if let Some(v) = self.try_eval_term(&ad.term, env) {
                groups.entry(key).or_default().push(v);
            }
        }
        let rows: Vec<Row> = groups.iter().filter_map(|(key, vals)| {
            agg_reduce(ad.op, vals)
                .map(|result| build_agg_row(&ad.columns, &ad.groups, key, &ad.result.0, &result))
        }).collect();
        if let Some(t) = self.let_tables.get_mut(&ad.name) {
            for row in rows { t.add(row); }
        }
    }

    /// Incremental aggregation over an unbounded Once table: fold only the rows
    /// added since the last pass into per-group accumulators (O(new rows)).
    fn compute_agg_incremental(&mut self, ad: &AggLetDef, _events: &[EventInstance]) {
        let once_name = match &ad.incremental { Some(n) => n.clone(), None => return };
        // Variable names bound to each column of the Once table, read off the
        // single guard pattern `once_name(v1, v2, …)` in the agg clause.
        let argvars: Vec<String> = ad.clause.patterns.iter().flatten()
            .find_map(|g| match g {
                GuardPattern::Event(ep) if ep.name == once_name =>
                    Some(ep.args.iter().map(|a| match a {
                        PatternArg::Var(v) => v.clone(),
                        _ => String::new(),
                    }).collect::<Vec<_>>()),
                _ => None,
            })
            .unwrap_or_default();
        // New Once rows not yet folded (immutable reads only).
        let new_rows: Vec<Row> = {
            let once_table = self.tables.get(&once_name)
                .or_else(|| self.let_tables.get(&once_name));
            match once_table {
                Some(t) => match self.agg_state.get(&ad.name) {
                    Some(st) => t.iter().filter(|r| !st.seen.contains(*r)).cloned().collect(),
                    None => t.iter().cloned().collect(),
                },
                None => Vec::new(),
            }
        };
        // Compute (group key, term value) per new row while holding only &self.
        let folds: Vec<(Vec<Value>, Value)> = new_rows.iter().filter_map(|row| {
            let mut env = Env::new();
            for (v, val) in argvars.iter().zip(row.iter()) {
                if !v.is_empty() { env.insert(v.as_str(), val.clone()); }
            }
            let key: Vec<Value> = ad.groups.iter()
                .map(|g| env.get(g).cloned().unwrap_or(Value::Bool(false)))
                .collect();
            self.try_eval_term(&ad.term, &env).map(|tv| (key, tv))
        }).collect();
        // Fold into the persistent accumulators.
        {
            let st = self.agg_state.entry(ad.name.clone()).or_default();
            for row in &new_rows { st.seen.insert(row.clone()); }
            for (key, tv) in folds {
                st.groups.entry(key).or_default().fold(&tv);
            }
        }
        // Rebuild the result table from the accumulators.
        let rows: Vec<Row> = {
            let st = self.agg_state.get(&ad.name).unwrap();
            st.groups.iter().filter_map(|(key, acc)| {
                acc.result(ad.op).map(|result| build_agg_row(&ad.columns, &ad.groups, key, &ad.result.0, &result))
            }).collect()
        };
        if let Some(t) = self.let_tables.get_mut(&ad.name) {
            t.clear();
            for row in rows { t.add(row); }
        }
    }

    /// Evaluate a table-operation let: per group, pass the rows' arg tuples to
    /// the Python `tfun` and bind its output tuples to the result columns.
    fn compute_top_let(&mut self, td: &TopLetDef, events: &[EventInstance]) {
        if let Some(t) = self.let_tables.get_mut(&td.name) { t.clear(); }
        let bindings = self.match_clause_against_events(&td.clause, events);
        let mut groups: HashMap<Vec<Value>, Vec<Vec<Value>>> = HashMap::default();
        for env in &bindings {
            let key: Vec<Value> = td.groups.iter()
                .map(|g| env.get(g).cloned().unwrap_or(Value::Bool(false)))
                .collect();
            let argtuple: Vec<Value> = td.args.iter()
                .map(|a| self.try_eval_term(a, env).unwrap_or(Value::Bool(false)))
                .collect();
            groups.entry(key).or_default().push(argtuple);
        }
        let mut rows: Vec<Row> = Vec::new();
        for (key, arg_rows) in &groups {
            for out in self.call_tfun(&td.fn_name, arg_rows) {
                rows.push(build_top_row(&td.columns, &td.groups, key, &td.results, &out));
            }
        }
        if let Some(t) = self.let_tables.get_mut(&td.name) {
            for row in rows { t.add(row); }
        }
    }

    /// Call a Python table function with a table of rows; returns output rows.
    fn call_tfun(&self, name: &str, rows: &[Vec<Value>]) -> Vec<Vec<Value>> {
        let func = match self.tfun_functions.get(name) { Some(f) => f, None => return Vec::new() };
        Python::with_gil(|py| {
            let py_rows = PyList::empty_bound(py);
            for r in rows {
                let cells = PyList::empty_bound(py);
                for v in r {
                    match v {
                        Value::Int(i) => cells.append(*i).unwrap(),
                        Value::Float(OrderedFloat(f)) => cells.append(*f).unwrap(),
                        Value::Str(s) => cells.append(&**s).unwrap(),
                        Value::Bool(b) => cells.append(*b).unwrap(),
                    }
                }
                py_rows.append(cells).unwrap();
            }
            let result = func.call1(py, (py_rows,))
                .unwrap_or_else(|e| panic!("Python error in tfun '{}': {}", name, e));
            // Expect a list of lists.
            let outer: Vec<Py<PyAny>> = match result.extract(py) {
                Ok(v) => v,
                Err(_) => return Vec::new(),
            };
            outer.iter().map(|row_obj| {
                match row_obj.extract::<Vec<Py<PyAny>>>(py) {
                    Ok(cells) => cells.iter().map(|c| py_to_value(py, c)).collect(),
                    Err(_) => vec![py_to_value(py, row_obj)],
                }
            }).collect()
        })
    }

    /// Ensure that `name`, if it is a let-def, has been computed this round.
    /// No-ops for events/tables and for let-defs already memoized in
    /// `self.let_computed`.  Dependencies (other let-defs referenced by the
    /// body) are computed first so that the table-backed lookup they perform
    /// during [`Self::compute_let_table`] sees up-to-date rows.
    fn ensure_let_computed(&mut self, name: &str, events: &[EventInstance]) {
        if self.let_computed.contains(name) {
            return;
        }
        let is_agg = self.agg_lets.contains_key(name);
        let is_top = self.top_lets.contains_key(name);
        if !is_agg && !is_top && !self.let_defs.contains_key(name) {
            return; // not a let-def (event or table) — nothing to do
        }
        // Mark up-front so a (degenerate) self-reference does not recurse forever.
        self.let_computed.insert(name.to_string());
        // Use precomputed dep list — no per-call AST traversal.
        // SAFETY: let_let_deps / let_defs / agg_lets / top_lets are built once in
        // `new` and not mutated during evaluation, so these raw refs stay valid
        // across the &mut self calls below.
        if let Some(deps) = self.let_let_deps.get(name) {
            let deps: *const Vec<String> = deps;
            for dep in unsafe { &*deps } {
                self.ensure_let_computed(dep, events);
            }
        }
        if is_agg {
            let ad: *const AggLetDef = &self.agg_lets[name];
            self.compute_agg_let(unsafe { &*ad }, events);
            return;
        }
        if is_top {
            let td: *const TopLetDef = &self.top_lets[name];
            self.compute_top_let(unsafe { &*td }, events);
            return;
        }
        let ld: *const LetDef = &self.let_defs[name];
        let ld = unsafe { &*ld };
        // Filter-lets are evaluated inline at use sites; they have no table.
        if ld.is_filter {
            return;
        }
        self.compute_let_table(ld, events);
    }

    /// Ensure every let-binding reached by `clause` (in its patterns or filter)
    /// is computed and memoized for the current round.
    fn ensure_lets_for_clause(&mut self, clause: &Clause, events: &[EventInstance]) {
        for name in self.collect_let_refs_in_clause(clause) {
            self.ensure_let_computed(&name, events);
        }
    }

    /// Ensure every let-binding reached by `filter` is computed and memoized.
    fn ensure_lets_for_filter(&mut self, filter: &FilterExpr, events: &[EventInstance]) {
        let mut refs = Vec::new();
        self.collect_let_refs_in_filter(filter, &mut refs);
        for name in refs {
            self.ensure_let_computed(&name, events);
        }
    }

    /// True if `name` is an on-demand-computed definition (plain let, aggregation
    /// let, or table-op let) that must be ensured before a referencing clause.
    fn is_let_like(&self, name: &str) -> bool {
        self.let_defs.contains_key(name)
            || self.agg_lets.contains_key(name)
            || self.top_lets.contains_key(name)
    }

    /// Names of let-defs directly referenced by a clause (patterns + filter).
    fn collect_let_refs_in_clause(&self, clause: &Clause) -> Vec<String> {
        let mut refs = Vec::new();
        for conj in &clause.patterns {
            for guard in conj {
                if let GuardPattern::Event(pat) = guard {
                    if self.is_let_like(&pat.name) {
                        refs.push(pat.name.clone());
                    }
                }
            }
        }
        self.collect_let_refs_in_filter(&clause.filter, &mut refs);
        refs
    }

    /// Names of let-defs directly referenced by a filter expression.
    fn collect_let_refs_in_filter(&self, filter: &FilterExpr, refs: &mut Vec<String>) {
        match filter {
            FilterExpr::TableLookup { name, .. } => {
                if self.is_let_like(name) {
                    refs.push(name.clone());
                }
            }
            FilterExpr::And(l, r) | FilterExpr::Or(l, r) => {
                self.collect_let_refs_in_filter(l, refs);
                self.collect_let_refs_in_filter(r, refs);
            }
            FilterExpr::Not(f) => self.collect_let_refs_in_filter(f, refs),
            FilterExpr::BoolLit(_) | FilterExpr::Compare { .. } => {}
        }
    }

    // ─── Pattern matching ────────────────────────────────────────────────────

    /// Match a conjunction of guard patterns (events, let-defs, eq-consts) against events.
    /// Returns all valid binding environments.
    /// Name-level feasibility check: can `clause` possibly match, given the set
    /// of event names present in the working set?  Guard patterns are positive
    /// conjuncts, so a disjunct containing an event guard whose event name is
    /// absent cannot match; the clause is feasible only if some disjunct
    /// survives.  Filter-only clauses and table/let guards always pass (filters
    /// may be satisfied by event *absence*, e.g. under Not, so they are never
    /// consulted here).
    fn clause_feasible(&self, clause: &Clause, present: &HashSet<String>) -> bool {
        if clause.patterns.is_empty() {
            return true;
        }
        clause.patterns.iter().any(|conj| {
            conj.iter().all(|g| match g {
                GuardPattern::Event(pat) => {
                    !self.event_names.contains(&pat.name) || present.contains(&pat.name)
                }
                _ => true,
            })
        })
    }

    fn match_guard_conj_against_events(
        &self,
        guards: &[GuardPattern],
        events: &[EventInstance],
    ) -> Vec<Env> {
        let mut envs = vec![Env::new()];
        for guard in guards {
            let mut new_envs = Vec::new();
            match guard {
                GuardPattern::EqConst(var_name, val) => {
                    // Bind variable to constant or check consistency
                    for env in &envs {
                        if let Some(existing) = env.get(var_name) {
                            if existing == val {
                                new_envs.push(env.clone());
                            }
                            // else: conflict, skip
                        } else {
                            let mut ext = env.clone();
                            ext.insert(var_name.as_str(), val.clone());
                            new_envs.push(ext);
                        }
                    }
                }
                GuardPattern::Event(pat) => {
                    // Resolve whether this name is a table/let once per guard — it
                    // depends only on `pat.name`, not on the binding env, so doing it
                    // inside the per-env loop re-hashed the name for every env.
                    let is_table_or_let = self.is_table_backed(&pat.name);
                    for env in &envs {
                        if is_table_or_let {
                            new_envs.extend(self.match_lookup_envs(&pat.lookup, env, events));
                            continue;
                        }
                        // Regular event pattern matching
                        for event in events {
                            if event.name == pat.name && event.args.len() == pat.args.len() {
                                if let Some(extended) = self.try_match_pattern(pat, event, env) {
                                    new_envs.push(extended);
                                }
                            }
                        }
                    }
                }
            }
            envs = new_envs;
            // Short-circuiting: stop if the environment is empty
            if envs.is_empty() {
                break;
            }
        }
        envs
    }

    /// Diagnose why a clause had no matches.  Returns a human-readable description
    /// of the first guard (per disjunct) that eliminated all bindings, or which
    /// filter expression caused the rejection.
    fn diagnose_no_match(&self, clause: &Clause, events: &[EventInstance]) -> String {
        let mut lines: Vec<String> = Vec::new();

        if clause.patterns.is_empty() {
            // No guard patterns at all — only a filter to check
            let filter_holds = self.eval_filter(&clause.filter, &Env::new(), events);
            if !filter_holds {
                lines.push(format!("  (no guard patterns; filter `{}` did not hold)", clause.filter));
            }
            return lines.join("\n");
        }

        for (di, conj) in clause.patterns.iter().enumerate() {
            let disj_prefix = if clause.patterns.len() > 1 {
                format!("  disjunct #{}: ", di)
            } else {
                "  ".to_string()
            };

            let mut envs: Vec<Env> = vec![Env::new()];
            let mut failed_guard: Option<String> = None;

            for guard in conj {
                let mut new_envs: Vec<Env> = Vec::new();
                match guard {
                    GuardPattern::EqConst(var_name, val) => {
                        for env in &envs {
                            if let Some(existing) = env.get(var_name) {
                                if existing == val {
                                    new_envs.push(env.clone());
                                }
                            } else {
                                let mut ext = env.clone();
                                ext.insert(var_name.as_str(), val.clone());
                                new_envs.push(ext);
                            }
                        }
                        if new_envs.is_empty() {
                            failed_guard = Some(format!("{}guard `{} = {}` conflicted with earlier bindings",
                                disj_prefix, var_name, val));
                            break;
                        }
                    }
                    GuardPattern::Event(pat) => {
                        for env in &envs {
                            if self.is_table_backed(&pat.name) {
                                new_envs.extend(self.match_lookup_envs(&pat.lookup, env, events));
                            } else {
                                for event in events {
                                    if event.name == pat.name && event.args.len() == pat.args.len() {
                                        if let Some(extended) = self.try_match_pattern(pat, event, env) {
                                            new_envs.push(extended);
                                        }
                                    }
                                }
                            }
                        }
                        if new_envs.is_empty() {
                            // Provide a more detailed reason
                            let is_table = self.is_table_backed(&pat.name);
                            let reason = if is_table {
                                let table_size = self.tables.get(&pat.name)
                                    .map(|t| t.len())
                                    .or_else(|| self.let_tables.get(&pat.name).map(|t| t.len()))
                                    .unwrap_or(0);
                                format!("table/let `{}` has {} row(s), none matched args [{}]",
                                    pat.name, table_size,
                                    pat.args.iter().map(|a| format!("{}", a)).collect::<Vec<_>>().join(", "))
                            } else {
                                let matching_events: Vec<String> = events.iter()
                                    .filter(|e| e.name == pat.name)
                                    .map(|e| format!("{}", e))
                                    .collect();
                                if matching_events.is_empty() {
                                    format!("no event named `{}` in working set ({} event(s) total)",
                                        pat.name, events.len())
                                } else {
                                    format!("event `{}` present ({}) but args [{}] did not unify with: {}",
                                        pat.name,
                                        matching_events.len(),
                                        pat.args.iter().map(|a| format!("{}", a)).collect::<Vec<_>>().join(", "),
                                        matching_events.join(", "))
                                }
                            };
                            failed_guard = Some(format!("{}guard `{}(...)` failed: {}",
                                disj_prefix, pat.name, reason));
                            break;
                        }
                    }
                }
                envs = new_envs;
            }

            if let Some(msg) = failed_guard {
                lines.push(msg);
            } else {
                // Guards passed — filter must have rejected the bindings
                let n_before = envs.len();
                let after: Vec<Env> = envs.iter()
                    .flat_map(|env| self.eval_filter_envs(&clause.filter, env, events))
                    .collect();
                if after.is_empty() {
                    lines.push(format!("{}guards produced {} binding(s), but filter `{}` rejected all",
                        disj_prefix, n_before, clause.filter));
                }
            }
        }

        if lines.is_empty() {
            "(unknown reason)".to_string()
        } else {
            lines.join("\n")
        }
    }

    /// Match disjunctive guard patterns (OR of AND-conjunctions) against events.
    /// Returns the union of all bindings from any matching disjunct.
    fn match_disjunctive_patterns_against_events(
        &self,
        pattern_disj: &[Vec<GuardPattern>],
        events: &[EventInstance],
    ) -> Vec<Env> {
        if pattern_disj.is_empty() {
            return vec![Env::new()];
        }
        let mut all_envs = Vec::new();
        for conj in pattern_disj {
            all_envs.extend(self.match_guard_conj_against_events(conj, events));
        }
        all_envs
    }

    /// Match a clause (disjunctive patterns + filter) against a set of events.
    /// Returns all valid binding environments, extended by any bindings from the filter.
    fn match_clause_against_events(
        &self,
        clause: &Clause,
        events: &[EventInstance],
    ) -> Vec<Env> {
        let envs = self.match_disjunctive_patterns_against_events(&clause.patterns, events);
        // Apply filter, collecting extended environments (for existential bindings)
        let mut result = Vec::new();
        for env in &envs {
            result.extend(self.eval_filter_envs(&clause.filter, env, events));
        }
        result
    }

    /// Try to match a single event pattern against a single event instance,
    /// extending an existing environment. Returns None on mismatch.
    fn try_match_pattern(
        &self,
        pat: &EventPattern,
        event: &EventInstance,
        env: &Env,
    ) -> Option<Env> {
        let mut new_env = env.clone_with_room(pat.args.len());
        for (arg, val) in pat.args.iter().zip(event.args.iter()) {
            match arg {
                PatternArg::Var(name) => {
                    if let Some(existing) = new_env.get(name) {
                        if existing != val {
                            return None; // Conflict
                        }
                    } else {
                        new_env.insert(name.as_str(), val.clone());
                    }
                }
                PatternArg::Literal(lit) => {
                    if lit != val {
                        return None;
                    }
                }
                PatternArg::Wildcard => {}
            }
        }
        Some(new_env)
    }

    /// Verify FunCall terms that were treated as wildcards during unification.
    /// For each arg that is a FunCall, if all its variables are bound in env,
    /// evaluate it and check it equals the matched value. If variables are
    /// still unbound, skip (will be verified at a higher And-level).
    fn verify_funcall_args(&self, args: &[TermExpr], vals: &[Value], env: &Env) -> bool {
        for (arg, val) in args.iter().zip(vals.iter()) {
            if let TermExpr::FunCall { .. } = arg {
                if let Some(computed) = self.try_eval_term(arg, env) {
                    if &computed != val {
                        return false;
                    }
                }
                // If can't evaluate (still has unbound vars), skip for now
            }
        }
        true
    }

    fn match_lookup_envs(&self, lookup: &FilterExpr, env: &Env, events: &[EventInstance]) -> Vec<Env> {
        let FilterExpr::TableLookup { name, args } = lookup else {
            return vec![];
        };

        let constraints: Vec<(usize, Value)> = args.iter().enumerate()
            .filter_map(|(i, arg)| self.try_eval_term(arg, env).map(|v| (i, v)))
            .collect();

        let mut result = Vec::new();

        // Collect raw row pointers so that we can call &self methods (verify_funcall_args)
        // while iterating over rows — the borrow checker can't see that self.tables and
        // self.py_functions are disjoint fields.
        // SAFETY: self is &self (immutable) for the entire call; rows are never freed
        // while a shared reference to the table exists.
        let row_ptrs: Vec<*const Row>;
        let n_table;
        let n_candidates;
        if let Some(table) = self.tables.get(name) {
            n_table = table.len();
            row_ptrs = table.iter_matching_ptrs(&constraints);
            n_candidates = row_ptrs.len();
            vlog!(self, "  [v1] match_lookup_envs {}(...): iterating {} table row(s) (from {} total)",
                name, n_candidates, n_table);
            for row_ptr in &row_ptrs {
                let row = unsafe { &**row_ptr };
                if let Some(ext) = try_unify_args(args, row, env) {
                    if self.verify_funcall_args(args, row, &ext) {
                        result.push(ext);
                    }
                }
            }
            return result;
        }

        if let Some(let_table) = self.let_tables.get(name) {
            n_table = let_table.len();
            row_ptrs = let_table.iter_matching_ptrs(&constraints);
            n_candidates = row_ptrs.len();
            vlog!(self, "  [v1] match_lookup_envs {}(...): iterating {} let-table row(s) (from {} total)",
                name, n_candidates, n_table);
            for row_ptr in &row_ptrs {
                let row = unsafe { &**row_ptr };
                if let Some(ext) = try_unify_args(args, row, env) {
                    if self.verify_funcall_args(args, row, &ext) {
                        result.push(ext);
                    }
                }
            }
            return result;
        }

        if self.event_names.contains(name) {
            let n_candidates = events.iter().filter(|ev| ev.name == *name).count();
            if events.len() > 0 {
                vlog!(self, "  [v1] match_lookup_envs {}(...): iterating {} matching event(s) out of {} total",
                    name, n_candidates, events.len());
            }
            for ev in events {
                if ev.name == *name && ev.args.len() == args.len() {
                    if let Some(ext) = try_unify_args(args, &ev.args, env) {
                        if self.verify_funcall_args(args, &ev.args, &ext) {
                            result.push(ext);
                        }
                    }
                }
            }
            return result;
        }

        result
    }

    // ─── Filter evaluation ───────────────────────────────────────────────────

    fn eval_filter(&self, filter: &FilterExpr, env: &Env, events: &[EventInstance]) -> bool {
        self.eval_filter_bool(filter, env, events)
    }

    /// Check existence of a TableLookup without allocating Vec<Env> or cloning rows.
    fn lookup_filter_exists(&self, name: &str, args: &[TermExpr], env: &Env, events: &[EventInstance]) -> bool {
        let constraints: Vec<(usize, Value)> = args.iter().enumerate()
            .filter_map(|(i, arg)| self.try_eval_term(arg, env).map(|v| (i, v)))
            .collect();

        if let Some(table) = self.tables.get(name) {
            return table.exists_eq_by_pos(&constraints);
        }
        if let Some(let_table) = self.let_tables.get(name) {
            return let_table.exists_eq_by_pos(&constraints);
        }
        if self.event_names.contains(name) {
            return events.iter().any(|ev| {
                ev.name == *name
                    && ev.args.len() == args.len()
                    && constraints.iter().all(|(i, v)| ev.args.get(*i) == Some(v))
            });
        }
        false
    }

    /// Boolean evaluation of a filter with short-circuiting.
    /// Avoids Vec<Env> allocation for all cases that don't bind new variables.
    fn eval_filter_bool(&self, filter: &FilterExpr, env: &Env, events: &[EventInstance]) -> bool {
        match filter {
            FilterExpr::BoolLit(b) => *b,
            FilterExpr::Or(l, r) => {
                self.eval_filter_bool(l, env, events)
                    || self.eval_filter_bool(r, env, events)
            }
            FilterExpr::Not(f) => !self.eval_filter_bool(f, env, events),
            FilterExpr::Compare { lhs, op, rhs } => {
                let l_opt = self.try_eval_term(lhs, env);
                let r_opt = self.try_eval_term(rhs, env);
                match (l_opt, r_opt) {
                    (Some(l), Some(r)) => match op {
                        CmpOp::Eq  => l == r,
                        CmpOp::Neq => l != r,
                        CmpOp::Lt  => l < r,
                        CmpOp::Le  => l <= r,
                        CmpOp::Gt  => l > r,
                        CmpOp::Ge  => l >= r,
                    },
                    _ => false,
                }
            }
            FilterExpr::TableLookup { name, args } => {
                if let Some(let_def) = self.let_defs.get(name) {
                    if let_def.is_filter {
                        return !self.eval_filter_let_call_envs(let_def, args, env, events).is_empty();
                    }
                }
                self.lookup_filter_exists(name, args, env, events)
            }
            FilterExpr::And(l, r) => {
                // The left side may bind variables the right side reads, so its
                // environments must be enumerated.  Stop at the first combination
                // that satisfies the right side and re-verifies the left.
                for e in self.eval_filter_envs(l, env, events) {
                    for e2 in self.eval_filter_envs(r, &e, events) {
                        if self.eval_filter_bool(l, &e2, events) {
                            return true;
                        }
                    }
                }
                false
            }
        }
    }

    /// Evaluate a filter, returning all extended environments where it holds.
    /// For atoms without free variables this returns vec![env.clone()] if true, vec![] if false.
    /// For atoms with free variables, returns one env per satisfying binding.
    fn eval_filter_envs(&self, filter: &FilterExpr, env: &Env, events: &[EventInstance]) -> Vec<Env> {
        match filter {
            FilterExpr::TableLookup { name, args } => {
                if let Some(let_def) = self.let_defs.get(name) {
                    if let_def.is_filter {
                        return self.eval_filter_let_call_envs(let_def, args, env, events);
                    }
                }

                // Use match_lookup_envs so that variables not yet bound in `env`
                // are handled via full-table enumeration + unification, rather
                // than causing an immediate failure.  This is essential for
                // filter-let bodies such as
                //   let x(a) [filter] := e(b) if c(b, a)
                // where `b` is a free variable that must be enumerated from `e`.
                self.match_lookup_envs(filter, env, events)
            }

            // For non-lookup filters, handle binding semantics
            FilterExpr::BoolLit(b) => {
                if *b { vec![env.clone()] } else { vec![] }
            }

            FilterExpr::And(l, r) => {
                // Evaluate left-to-right, collecting extended envs (existential bindings).
                // FunCall terms in l are treated as wildcards during initial matching.
                let l_envs = self.eval_filter_envs(l, env, events);
                let mut result = Vec::new();
                for e in &l_envs {
                    result.extend(self.eval_filter_envs(r, e, events));
                }
                // Re-verify: now that r may have bound additional variables,
                // re-check l to validate any FunCall terms that were wildcarded
                // during the initial left-to-right evaluation.
                result.retain(|env| self.eval_filter(l, env, events));
                result
            }

            FilterExpr::Or(l, r) => {
                let mut result = self.eval_filter_envs(l, env, events);
                result.extend(self.eval_filter_envs(r, env, events));
                result
            }

            FilterExpr::Not(f) => {
                // De Morgan: ¬(A ∨ B) → (¬A ∧ ¬B).  Inline without cloning
                // FilterExpr nodes — Not never introduces new bindings, so we only
                // need bool truth values for each branch.
                if let FilterExpr::Or(l, r) = f.as_ref() {
                    if !self.eval_filter_bool(l, env, events)
                        && !self.eval_filter_bool(r, env, events)
                    {
                        return vec![env.clone()];
                    }
                    return vec![];
                }
                // Double-negation: ¬¬A → A (preserves bindings introduced by A).
                if let FilterExpr::Not(inner_f) = f.as_ref() {
                    return self.eval_filter_envs(inner_f, env, events);
                }
                // Standard Not: use bool path to avoid Vec<Env> allocation.
                if self.eval_filter_bool(f, env, events) { vec![] } else { vec![env.clone()] }
            }

            FilterExpr::Compare { lhs, op, rhs } => {
                let l_opt = self.try_eval_term(lhs, env);
                let r_opt = self.try_eval_term(rhs, env);
                match (l_opt, r_opt) {
                    (Some(l), Some(r)) => {
                        let ok = match op {
                            CmpOp::Eq => l == r,
                            CmpOp::Neq => l != r,
                            CmpOp::Lt => l < r,
                            CmpOp::Le => l <= r,
                            CmpOp::Gt => l > r,
                            CmpOp::Ge => l >= r,
                        };
                        if ok { vec![env.clone()] } else { vec![] }
                    }
                    // Equality with one unbound variable: bind it
                    (None, Some(r)) if *op == CmpOp::Eq => {
                        if let TermExpr::Var(name) = lhs {
                            let mut ext = env.clone();
                            ext.insert(name.as_str(), r);
                            vec![ext]
                        } else {
                            vec![]
                        }
                    }
                    (Some(l), None) if *op == CmpOp::Eq => {
                        if let TermExpr::Var(name) = rhs {
                            let mut ext = env.clone();
                            ext.insert(name.as_str(), l);
                            vec![ext]
                        } else {
                            vec![]
                        }
                    }
                    _ => vec![] // cannot evaluate — treat as false
                }
            }
        }
    }

    fn is_filter_let(&self, name: &str) -> bool {
        self.let_defs
            .get(name)
            .map(|d| d.is_filter)
            .unwrap_or(false)
    }

    /// True if `name` resolves to a backing table for guard/lookup matching: a
    /// declared table, a non-filter let, or an aggregation / table-op let.  All
    /// of these own a row table (`tables` or `let_tables`); filter lets do not.
    fn is_table_backed(&self, name: &str) -> bool {
        self.tables.contains_key(name) || self.let_tables.contains_key(name)
    }

    /// Evaluate a `filter let` call from concrete argument values only.
    /// This path never performs table-backed lookup or existential row search.
    fn eval_filter_let_call_envs(
        &self,
        let_def: &LetDef,
        args: &[TermExpr],
        env: &Env,
        events: &[EventInstance],
    ) -> Vec<Env> {
        if args.len() != let_def.params.len() {
            return vec![];
        }

        // Arguments must be available from the current environment.
        let mut arg_vals = Vec::with_capacity(args.len());
        for arg in args {
            if let Some(v) = self.try_eval_term(arg, env) {
                arg_vals.push(v);
            } else {
                return vec![];
            }
        }

        // Merge parameter bindings into a local environment.
        let mut local_env = env.clone();
        for ((param_name, _), value) in let_def.params.iter().zip(arg_vals.iter()) {
            if let Some(existing) = local_env.get(param_name) {
                if existing != value {
                    return vec![];
                }
            } else {
                local_env.insert(param_name.as_str(), value.clone());
            }
        }

        // A filter let may carry guard patterns when the compiler was able to pull
        // event/table guards from the body (best-effort trigger).  In that case
        // we first match the patterns against the events to enumerate free-variable
        // bindings, then verify the filter for each resulting environment.
        // If there are no patterns, we just evaluate the filter directly.
        if let_def.clause.patterns.is_empty() {
            if self.eval_filter(&let_def.clause.filter, &local_env, events) {
                vec![env.clone()]
            } else {
                vec![]
            }
        } else {
            let matched_envs =
                self.match_guard_conj_against_events(&let_def.clause.patterns[0], events);
            let mut result = Vec::new();
            for matched in &matched_envs {
                // Merge the param bindings into the pattern-matched env
                let mut combined = matched.clone();
                let mut ok = true;
                for ((param_name, _), value) in let_def.params.iter().zip(arg_vals.iter()) {
                    if let Some(existing) = combined.get(param_name) {
                        if existing != value { ok = false; break; }
                    } else {
                        combined.insert(param_name.as_str(), value.clone());
                    }
                }
                if ok && self.eval_filter(&let_def.clause.filter, &combined, events) {
                    result.push(env.clone());
                }
            }
            // Deduplicate (the caller env is always the same object, but be safe)
            result.dedup();
            result
        }
    }

    fn try_eval_term(&self, term: &TermExpr, env: &Env) -> Option<Value> {
        match term {
            TermExpr::Var(name) => env.get(name).cloned(),
            TermExpr::Lit(v) => Some(v.clone()),
            TermExpr::FunCall { name, args } => {
                let arg_vals: Vec<Value> = args.iter()
                    .filter_map(|a| self.try_eval_term(a, env))
                    .collect();
                if arg_vals.len() != args.len() {
                    return None;
                }
                // Native dispatch: avoids Python GIL round-trip for stdlib functions.
                if let Some(result) = dispatch_builtin(name, &arg_vals) {
                    return Some(result);
                }
                // Fall back to Python for user-defined functions.
                if let Some((param_names, py_func)) = self.py_functions.get(name) {
                    Python::with_gil(|py| {
                        let kwargs = PyDict::new_bound(py);
                        for (pname, val) in param_names.iter().zip(arg_vals.iter()) {
                            match val {
                                Value::Int(i)         => kwargs.set_item(pname, *i).unwrap(),
                                Value::Float(OrderedFloat(f)) => kwargs.set_item(pname, *f).unwrap(),
                                Value::Str(s)         => kwargs.set_item(pname, &**s).unwrap(),
                                Value::Bool(b)        => kwargs.set_item(pname, *b).unwrap(),
                            }
                        }
                        let result = py_func.call_bound(py, (), Some(&kwargs))
                            .unwrap_or_else(|e| panic!("Python error in '{}': {}", name, e));
                        if let Ok(i) = result.extract::<i64>(py) {
                            Some(Value::Int(i))
                        } else if let Ok(f) = result.extract::<f64>(py) {
                            Some(Value::Float(OrderedFloat(f)))
                        } else if let Ok(b) = result.extract::<bool>(py) {
                            Some(Value::Bool(b))
                        } else if let Ok(s) = result.extract::<String>(py) {
                            Some(Value::Str(s.into()))
                        } else {
                            panic!("Python function '{}' returned unsupported type", name);
                        }
                    })
                } else {
                    panic!("Unknown function '{}' (not a built-in and not defined as a Python fun)", name);
                }
            }
        }
    }

}

/// Try to unify term arguments against concrete values, extending an env.
/// Returns Some(extended_env) on success, None on mismatch.
fn try_unify_args(args: &[TermExpr], vals: &[Value], env: &Env) -> Option<Env> {
    if args.len() != vals.len() {
        return None;
    }
    let mut new_env = env.clone_with_room(args.len());
    for (arg, val) in args.iter().zip(vals.iter()) {
        if !try_unify_term(arg, val, &mut new_env) {
            return None;
        }
    }
    Some(new_env)
}

/// Unify a single term against a value. Variables get bound; literals must match.
fn try_unify_term(term: &TermExpr, val: &Value, env: &mut Env) -> bool {
    match term {
        TermExpr::Var(name) => {
            if let Some(existing) = env.get(name) {
                existing == val
            } else {
                env.insert(name.as_str(), val.clone());
                true
            }
        }
        TermExpr::Lit(lit) => lit == val,
        TermExpr::FunCall { .. } => {
            // Treat FunCall terms as wildcards during initial unification.
            // They are verified in a second pass once all variables are bound.
            true
        }
    }
}
