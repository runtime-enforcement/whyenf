/// The enforcement engine: evaluates programs against logs.

use std::collections::{BTreeSet, HashMap};
use std::time::Instant;
use serde::{Serialize, Deserialize};
use pyo3::prelude::*;
use pyo3::types::PyDict;
use crate::ast::*;
use crate::table::{Table, Row};

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

// ─── Runtime environment ─────────────────────────────────────────────────────

/// Binding environment: variable name → Value
type Env = HashMap<String, Value>;

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
    let_full: BTreeSet<String>,
    /// Set of event names declared as events (for disambiguation)
    event_names: BTreeSet<String>,
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
    /// The timestamp for which we last emitted proactive output
    /// (to avoid duplicates when multiple TPs share the same ts).
    last_proactive_ts: Option<u64>,
    /// Whether to print rule labels on enforcement actions
    label_mode: bool,
    /// Whether to output enforcement actions in JSON format
    json_mode: bool,
    /// Whether to print verbose debug info
    verbose_mode: bool,
    /// Verbose detail level: 0 = off, 1 = basic (same as verbose_mode), 2 = full detail
    verbose_level: u8,
    /// Current time (verbose mode)
    current_time: std::time::SystemTime
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
}

impl Engine {
    pub fn new(program: Program, label_mode: bool, json_mode: bool, verbose_mode: bool, verbose_level: u8) -> Self {
        let event_names: BTreeSet<String> = program
            .event_decls
            .iter()
            .map(|d| d.name.clone())
            .collect();

        let mut tables = HashMap::new();
        
        for td in &program.tables {
            let cols: Vec<String> = td.columns.iter().map(|(n, _)| n.clone()).collect();
            tables.insert(td.name.clone(), Table::new(td.name.clone(), cols));
        }

        let mut let_tables = HashMap::new();    

        for ld in &program.let_defs {
            let cols: Vec<String> = ld.params.iter().map(|(n, _)| n.clone()).collect();
            let_tables.insert(ld.name.clone(), Table::new(ld.name.clone(), cols));
        }

        // Collect let definitions
        let let_defs: HashMap<String, LetDef> = program
            .let_defs
            .iter()
            .map(|d| (d.name.clone(), d.clone()))
            .collect();

        // Compile Python functions
        let py_functions = Python::with_gil(|py| {
            let mut fns = HashMap::new();
            for fd in &program.fun_decls {
                let params_str = fd.param_names.join(", ");
                // Wrap the user's Python code into a proper function definition
                // Indent each line of the body by 4 spaces
                let indented_body: String = fd.body.lines()
                    .map(|line| format!("    {}", line))
                    .collect::<Vec<_>>()
                    .join("\n");
                // Escape function names that are Python keywords (e.g. "match")
                let py_fn_name = match fd.name.as_str() {
                    "match" | "class" | "def" | "return" | "import" | "from"
                    | "if" | "else" | "elif" | "for" | "while" | "with" | "as"
                    | "try" | "except" | "finally" | "raise" | "pass" | "break"
                    | "continue" | "and" | "or" | "not" | "is" | "in" | "lambda"
                    | "global" | "nonlocal" | "del" | "yield" | "assert" | "True"
                    | "False" | "None" | "async" | "await" | "type" | "case"
                        => format!("_ef_{}", fd.name),
                    _ => fd.name.clone(),
                };
                let py_src = format!(
                    "def {}({}):\n{}\n",
                    py_fn_name, params_str, indented_body
                );
                // Execute the def statement to define the function in a module dict
                let module = PyModule::from_code_bound(
                    py,
                    &py_src,
                    &format!("{}.py", fd.name),
                    &fd.name,
                ).unwrap_or_else(|e| {
                    panic!("Python compilation error in function '{}': {}", fd.name, e);
                });
                let func = module.getattr(py_fn_name.as_str())
                    .unwrap_or_else(|e| {
                        panic!("Cannot find Python function '{}': {}", fd.name, e);
                    });
                fns.insert(fd.name.clone(), (fd.param_names.clone(), func.into_any().unbind()));
            }
            fns
        });

        Engine {
            program,
            tables,
            let_tables,
            let_full: BTreeSet::new(),
            event_names,
            let_defs,
            py_functions,
            obligations: HashMap::new(),
            next_tp_obligations: Vec::new(),
            current_ts: None,
            last_proactive_ts: None,
            label_mode,
            json_mode,
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

    /// Process a log supplied as an iterator, printing enforcer output for each time-point.
    pub fn run<'a>(&mut self, log: impl Iterator<Item = &'a TimePoint>) {
        for tp in log {
            self.process_timepoint(tp);
        }
        self.finish();
    }

    /// Process a single time-point (streaming API).
    pub fn process_one(&mut self, tp: &TimePoint) {
        self.process_timepoint(tp);
    }

    /// Flush all remaining delayed obligations (call after the last time-point).
    pub fn finish(&mut self) {
        // Emit proactive output for the last timestamp seen
        if let Some(ts) = self.current_ts {
            self.emit_proactive(ts);
        }
        // Flush any obligations at future timestamps
        if let Some(max_ts) = self.obligations.keys().max().cloned() {
            let start = self.current_ts.map_or(0, |t| t + 1);
            if start <= max_ts {
                self.flush_obligations_range(start, max_ts + 1);
            }
        }
    }

    // ─── State persistence ───────────────────────────────────────────────────

    /// Save mutable engine state to a JSON file (atomic: write tmp then rename).
    pub fn save_state(&self, path: &str) {
        let state = EngineState {
            tables: self.tables.clone(),
            let_tables: self.let_tables.clone(),
            let_full: self.let_full.clone(),
            obligations: self.obligations.clone(),
            next_tp_obligations: self.next_tp_obligations.clone(),
            current_ts: self.current_ts,
            last_proactive_ts: self.last_proactive_ts,
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
        self.let_full = state.let_full;
        self.obligations = state.obligations;
        self.next_tp_obligations = state.next_tp_obligations;
        self.current_ts = state.current_ts;
        self.last_proactive_ts = state.last_proactive_ts;
        eprintln!("[enfflash] State loaded from {}", path);
    }

    fn process_timepoint(&mut self, tp: &TimePoint) {
        let new_ts = tp.timestamp;

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

        // 1. Update non-lagged tables and let-defs in original formula order
        vlog!(self, "── Phase 1: update non-lagged tables and let-defs ──");
        let phase1_start = Instant::now();
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
        let mut working_labels: std::collections::HashMap<(String, Vec<Value>), Vec<String>> =
            std::collections::HashMap::new();
        // Track which (event_name, args) pairs we've already produced to detect
        // new additions.  Pre-populate with the timepoint's own events so that
        // we never cause an event that already exists.
        let mut caused_set: BTreeSet<(String, Vec<Value>)> = BTreeSet::new();
        for ev in &tp.events {
            caused_set.insert((ev.name.clone(), ev.args.clone()));
        }
        let mut suppressed_set: BTreeSet<(String, Vec<Value>)> = BTreeSet::new();

        // Drain next-tp obligations (from Next operator) — they fire reactively
        // when the next real time-point arrives.
        let pending_next: Vec<Obligation> = std::mem::take(&mut self.next_tp_obligations);
        for ob in pending_next {
            let valid = match &ob.validate {
                Some(f) => self.eval_filter(f, &ob.env, &[]),
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

        const MAX_ITERATIONS: usize = 100;
        for _iteration in 0..MAX_ITERATIONS {
            let iter_start = Instant::now();
            // Re-evaluate tables and let-defs against the (growing) working event set
            // so that they see events caused in previous iterations.
            self.update_tables_and_lets(&working_events, false);
            vlog!(self, "── Phase 2: fixpoint iteration {} ({} events in working set) ──",
                  _iteration, working_events.len());
            let mut new_suppress: Vec<(EventInstance, Vec<String>)> = Vec::new();
            let mut new_cause: Vec<(EventInstance, Vec<String>)> = Vec::new();

            for rule_idx in 0..self.program.rules.len() {
                let rule = self.program.rules[rule_idx].clone();
                let bindings = self.match_clause_against_events(&rule.trigger, &working_events);

                if self.verbose_level >= 2 && !bindings.is_empty() {
                    let action_sym = match rule.action { RuleAction::Cause => "+", RuleAction::Suppress => "-", RuleAction::Observe => "?" };
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
                    let action_sym = match rule.action { RuleAction::Cause => "+", RuleAction::Suppress => "-", RuleAction::Observe => "?" };
                    vlog!(self, "  rule #{} {}{} matched → {}",
                            rule_idx, action_sym, rule.event, ev);

                    // Combine rule's own label with inherited labels
                    let combined_labels: Vec<String> = if self.label_mode {
                        let mut all = Vec::new();
                        for l in rule_label.iter().chain(inherited_labels.iter()) {
                            if !all.contains(l) {
                                all.push(l.clone());
                            }
                        }
                        all
                    } else {
                        vec![]
                    };

                    if let Some(_tp_off) = rule.tp_offset {
                        // Next-tp obligation: fires at the next real time-point
                        vlog!(self, "    → next-tp obligation: {} {}", action_sym, ev);
                        self.next_tp_obligations.push(Obligation {
                            event: ev,
                            action: rule.action,
                            deadline: 0, // not used for next-tp
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

        let phase2_elapsed = phase2_start.elapsed();

        self.print_enforcer_output(&all_suppress, &all_cause, false);

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
        self.update_tables_and_lets(&tp.events, true);
        let phase3_elapsed = phase3_start.elapsed();

        if self.verbose_mode {
            let total = phase1_elapsed + phase2_elapsed + phase2b_elapsed + phase3_elapsed;
            eprintln!("── Timing @{}: total {:.1?} │ P1(tables+lets) {:.1?} │ P2(fixpoint) {:.1?} │ P2b(obligations) {:.1?} │ P3(lagged) {:.1?}",
                new_ts, total, phase1_elapsed, phase2_elapsed, phase2b_elapsed, phase3_elapsed);
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
        let mut seen_cause: BTreeSet<(String, Vec<Value>)> = BTreeSet::new();
        let mut seen_suppress: BTreeSet<(String, Vec<Value>)> = BTreeSet::new();
        for ob in self.obligations.remove(&ts).unwrap_or_default() {
            let valid = match &ob.validate {
                Some(f) => self.eval_filter(f, &ob.env, &[]),
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
        self.print_enforcer_output(&proactive_suppress, &proactive_cause, true);
        self.current_ts = saved_ts;
    }

    /// Discharge obligations for timestamps in [from_ts, up_to_ts).
    fn flush_obligations_range(&mut self, from_ts: u64, up_to_ts: u64) {
        vlog!(self, "── Flushing obligations in [{}, {}) ──", from_ts, up_to_ts);
        for ts in from_ts..up_to_ts {
            self.emit_proactive(ts);
        }
    }


    fn print_enforcer_output(
        &self,
        suppress: &[(EventInstance, Vec<String>)],
        cause: &[(EventInstance, Vec<String>)],
        proactive: bool,
    ) {
        // Filter out synthetic Cau_/Sup_ events — they are internal to the
        // enforcement typing and should not be reported as enforcement actions.
        let suppress: Vec<_> = suppress.iter()
            .filter(|(ev, _)| !ev.name.starts_with("Cau_") && !ev.name.starts_with("Sup_"))
            .collect();
        let cause: Vec<_> = cause.iter()
            .filter(|(ev, _)| !ev.name.starts_with("Cau_") && !ev.name.starts_with("Sup_"))
            .collect();
        if self.json_mode {
            self.print_enforcer_output_json(&suppress, &cause, proactive);
        } else {
            self.print_enforcer_output_textual(&suppress, &cause, proactive);
        }
    }

    /// JSON output matching the OCaml `Order.print_json` format.
    fn print_enforcer_output_json(
        &self,
        suppress: &[&(EventInstance, Vec<String>)],
        cause: &[&(EventInstance, Vec<String>)],
        proactive: bool,
    ) {
        let ts = self.current_ts.unwrap();
        let cause_json = format!("[ {} ]",
            cause.iter().map(|(e, _)| e.to_json()).collect::<Vec<_>>().join(", "));
        let suppress_json = format!("[ {} ]",
            suppress.iter().map(|(e, _)| e.to_json()).collect::<Vec<_>>().join(", "));

        if proactive {
            if !cause.is_empty() {
                println!("{{ \"ts\": {}, \"cause\": {}, \"proactive\": true }}", ts, cause_json);
            } else {
                println!("{{ \"ts\": {}, \"proactive\": true }}", ts);
            }
        } else {
            let has_cause = !cause.is_empty();
            let has_suppress = !suppress.is_empty();
            if has_cause && has_suppress {
                println!("{{ \"ts\": {}, \"cause\": {}, \"suppress\": {} }}", ts, cause_json, suppress_json);
            } else if has_cause {
                println!("{{ \"ts\": {}, \"cause\": {} }}", ts, cause_json);
            } else if has_suppress {
                println!("{{ \"ts\": {}, \"suppress\": {} }}", ts, suppress_json);
            } else {
                println!("{{ \"ts\": {} }}", ts);
            }
        }
    }

    /// Textual output (original format).
    fn print_enforcer_output_textual(
        &self,
        suppress: &[&(EventInstance, Vec<String>)],
        cause: &[&(EventInstance, Vec<String>)],
        proactive: bool,
    ) {
        if proactive {
            if !cause.is_empty() {
                if self.label_mode {
                    for (ev, labels) in cause {
                        let formatted = labels.iter().map(|l| format!("\"{}\"", l)).collect::<Vec<_>>().join(", ");
                        println!("[Enforcer:Label] Cause {}: {}", ev, formatted);
                    }
                }
                println!(
                    "[Enforcer] @{} proactively commands:\nCause:\n{}\nOK.",
                    self.current_ts.unwrap(),    
                    cause.iter().map(|(e, _)| e.to_string()).collect::<Vec<_>>().join(", ")
                );
            } else {
                println!("[Enforcer] @{} nothing to do proactively.", self.current_ts.unwrap());
            }
        } else {
            if self.label_mode {
                for (ev, labels) in suppress {
                    let formatted = labels.iter().map(|l| format!("\"{}\"", l)).collect::<Vec<_>>().join(", ");
                    println!("[Enforcer:Label] Suppress {}: {}", ev, formatted);
                }
                for (ev, labels) in cause {
                    let formatted = labels.iter().map(|l| format!("\"{}\"", l)).collect::<Vec<_>>().join(", ");
                    println!("[Enforcer:Label] Cause {}: {}", ev, formatted);
                }
            } 
            if !suppress.is_empty() || !cause.is_empty() {
                println!("[Enforcer] @{} reactively commands:", self.current_ts.unwrap());
                if !suppress.is_empty() {
                    let items: Vec<String> = suppress.iter().map(|(e, _)| e.to_string()).collect();
                    println!("Suppress:\n{}", items.join(", "));
                }
                if !cause.is_empty() {
                    let items: Vec<String> = cause.iter().map(|(e, _)| e.to_string()).collect();
                    println!("Cause:\n{}", items.join(", "));
                }
                println!("OK.");
            }
            else {
                println!("[Enforcer] @{} OK.", self.current_ts.unwrap());
            }
        }
    }

    // ─── Unified table + let-def updates (in original formula order) ────────

    fn update_tables_and_lets(&mut self, events: &[EventInstance], lagged: bool) {
        let items: Vec<ProgramItem> = self.program.items.clone();
        for item in &items {
            match item {
                ProgramItem::Table(td) => {
                    if td.lagged != lagged {
                        continue;
                    }
                    // Process remove clause FIRST, then add.
                    // If both match the same row, add wins (matches Since semantics).
                    if let Some(ref rm_clause) = td.remove_clause {
                        let rm_envs = if rm_clause.patterns.is_empty() || rm_clause.patterns.iter().all(|d| d.is_empty()) {
                            if let Some(table) = self.tables.get(&td.name) {
                                let mut envs = Vec::new();
                                for row in table.iter() {
                                    let mut env = Env::new();
                                    for ((col_name, _), val) in td.columns.iter().zip(row.iter()) {
                                        env.insert(col_name.clone(), val.clone());
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
                ProgramItem::Let(ld) => {
                    if lagged { continue; }
                    // Clear previous rows — let-defs are re-evaluated from scratch
                    if let Some(let_table) = self.let_tables.get_mut(&ld.name) {
                        let_table.clear();
                    }
                    self.let_full.remove(&ld.name);
                    // Process clause
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
                        if let Some(let_table) = self.let_tables.get_mut(&ld.name) {
                            let is_new = let_table.add(row.clone());
                            if is_new {
                                vlog!(self, "  let table {} += [{}]", ld.name,
                                      row.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "));
                            }
                        }
                    }
                }
                ProgramItem::Rule(_) => {} // rules handled separately
            }
        }

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

    // ─── Pattern matching ────────────────────────────────────────────────────

    /// Match a conjunction of guard patterns (events, let-defs, eq-consts) against events.
    /// Returns all valid binding environments.
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
                            ext.insert(var_name.clone(), val.clone());
                            new_envs.push(ext);
                        }
                    }
                }
                GuardPattern::Event(pat) => {
                    for env in &envs {
                        // Check if this pattern name is a let-def or a table (Since/Once)
                        if self.let_defs.contains_key(&pat.name) || self.tables.contains_key(&pat.name) {
                            let args_as_terms: Vec<TermExpr> = pat.args.iter().map(|a| match a {
                                PatternArg::Var(name) => TermExpr::Var(name.clone()),
                                PatternArg::Literal(v) => TermExpr::Lit(v.clone()),
                                PatternArg::Wildcard => TermExpr::Lit(Value::Bool(false)),
                            }).collect();
                            let lookup = FilterExpr::TableLookup {
                                name: pat.name.clone(),
                                args: args_as_terms,
                            };
                            new_envs.extend(self.eval_filter_envs(&lookup, env, events));
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
        }
        envs
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
        let mut new_env = env.clone();
        for (arg, val) in pat.args.iter().zip(event.args.iter()) {
            match arg {
                PatternArg::Var(name) => {
                    if let Some(existing) = new_env.get(name) {
                        if existing != val {
                            return None; // Conflict
                        }
                    } else {
                        new_env.insert(name.clone(), val.clone());
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

    // ─── Filter evaluation ───────────────────────────────────────────────────

    fn eval_filter(&self, filter: &FilterExpr, env: &Env, events: &[EventInstance]) -> bool {
        !self.eval_filter_envs(filter, env, events).is_empty()
    }

    /// Evaluate a filter, returning all extended environments where it holds.
    /// For atoms without free variables this returns vec![env.clone()] if true, vec![] if false.
    /// For atoms with free variables, returns one env per satisfying binding.
    fn eval_filter_envs(&self, filter: &FilterExpr, env: &Env, events: &[EventInstance]) -> Vec<Env> {
        match filter {
            FilterExpr::TableLookup { name, args } => {
                let free_vars = collect_free_vars_in_terms(args, env);

                if free_vars.is_empty() {
                    // No free vars — evaluate directly
                    let vals: Vec<Value> = args.iter().map(|a| self.eval_term(a, env)).collect();

                    if let Some(table) = self.tables.get(name) {
                        let found = table.contains(&vals);
                        vlog2!(self, "    [v2] TableLookup {}({}) in table → {}",
                            name, vals.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "),
                            found);
                        if found {
                            return vec![env.clone()];
                        }
                        return vec![];
                    }

                    if let Some(let_table) = self.let_tables.get(name) {
                        // Check if this let-def has universal (wildcard) rows
                        let universal = self.let_full.contains(name);
                        let found = universal || let_table.contains(&vals);
                        vlog2!(self, "    [v2] LetDef {}({}) → {}{}",
                            name, vals.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "),
                            found, if universal { " [universal]" } else { "" });
                        if found {
                            return vec![env.clone()];
                        }
                        return vec![];
                    }

                    if self.event_names.contains(name) {
                        let found = events.iter().any(|ev| ev.name == *name && ev.args == vals);
                        vlog2!(self, "    [v2] EventLookup {}({}) in {} events → {}",
                            name, vals.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "),
                            events.len(), found);
                        if found {
                            return vec![env.clone()];
                        }
                        return vec![];
                    }

                    vec![]
                } else {
                    // Free variables: existential — enumerate matches
                    let mut result = Vec::new();

                    if let Some(table) = self.tables.get(name) {
                        for row in table.iter() {
                            if let Some(ext) = try_unify_args(args, row, env) {
                                if self.verify_funcall_args(args, row, &ext) {
                                    result.push(ext);
                                }
                            }
                        }
                        return result;
                    }

                    if let Some(let_table) = self.let_tables.get(name) {
                        for row in let_table.iter() {
                            if let Some(ext) = try_unify_args(args, row, env) {
                                if self.verify_funcall_args(args, row, &ext) {
                                    result.push(ext);
                                }
                            }
                        }
                        return result;
                    }

                    if self.event_names.contains(name) {
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
                // Apply De Morgan simplification: ¬(A ∨ B) → (¬A ∧ ¬B)
                // This is critical for correct evaluation when Or branches have
                // free variables — the plain Not(Or(...)) evaluation loses variable
                // bindings across Or branches.
                if let FilterExpr::Or(l, r) = f.as_ref() {
                    let neg_l = FilterExpr::Not(Box::new(l.as_ref().clone()));
                    let neg_r = FilterExpr::Not(Box::new(r.as_ref().clone()));
                    let conj = FilterExpr::And(Box::new(neg_l), Box::new(neg_r));
                    return self.eval_filter_envs(&conj, env, events);
                }
                // Double-negation elimination: ¬¬A → A
                // This preserves variable bindings that would be lost through
                // the standard Not evaluation.
                if let FilterExpr::Not(inner_f) = f.as_ref() {
                    return self.eval_filter_envs(inner_f, env, events);
                }
                // Standard Not: if the inner has any satisfying env, return empty.
                let inner = self.eval_filter_envs(f, env, events);
                if inner.is_empty() {
                    vec![env.clone()]
                } else {
                    vec![]
                }
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
                            ext.insert(name.clone(), r);
                            vec![ext]
                        } else {
                            vec![]
                        }
                    }
                    (Some(l), None) if *op == CmpOp::Eq => {
                        if let TermExpr::Var(name) = rhs {
                            let mut ext = env.clone();
                            ext.insert(name.clone(), l);
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

    fn eval_term(&self, term: &TermExpr, env: &Env) -> Value {
        match self.try_eval_term(term, env) {
            Some(value) => value,
            None => panic! ("Some variable from {:?} is not defined in {:?}", term, env)
        }
    }

    fn try_eval_term(&self, term: &TermExpr, env: &Env) -> Option<Value> {
        match term {
            TermExpr::Var(name) => env
                .get(name)
                .cloned(),
            TermExpr::Lit(v) => Some (v.clone()),
            TermExpr::FunCall { name, args } => {
                // Evaluate arguments
                let arg_vals: Vec<Value> = args.iter().filter_map(|a| self.try_eval_term(a, env)).collect();

                if arg_vals.len() != args.len() {
                    return None
                }

                // Look up the Python function
                if let Some((param_names, py_func)) = self.py_functions.get(name) {
                    Python::with_gil(|py| {
                        let kwargs = PyDict::new_bound(py);
                        for (pname, val) in param_names.iter().zip(arg_vals.iter()) {
                            match val {
                                Value::Int(i) => kwargs.set_item(pname, *i).unwrap(),
                                Value::Float(OrderedFloat(f)) => kwargs.set_item(pname, *f).unwrap(),
                                Value::Str(s) => kwargs.set_item(pname, s.as_str()).unwrap(),
                                Value::Bool(b) => kwargs.set_item(pname, *b).unwrap(),
                            }
                        }
                        let result = py_func.call_bound(py, (), Some(&kwargs))
                            .unwrap_or_else(|e| panic!("Python error in '{}': {}", name, e));
                        // Convert back to Value
                        if let Ok(i) = result.extract::<i64>(py) {
                            Some (Value::Int(i))
                        } else if let Ok(f) = result.extract::<f64>(py) {
                            Some (Value::Float(OrderedFloat(f)))
                        } else if let Ok(b) = result.extract::<bool>(py) {
                            Some (Value::Bool(b))
                        } else if let Ok(s) = result.extract::<String>(py) {
                            Some (Value::Str(s))
                        } else {
                            panic!("Python function '{}' returned unsupported type", name);
                        }
                    })
                } else {
                    panic!("Unknown function: {}", name);
                }
            }
        }
    }

}

/// Try to evaluate a term if all its variables are bound. Returns None if any var is unbound.
fn try_eval_term_partial(term: &TermExpr, env: &Env) -> Option<Value> {
    match term {
        TermExpr::Var(name) => env.get(name).cloned(),
        TermExpr::Lit(v) => Some(v.clone()),
        TermExpr::FunCall { .. } => None, // can't evaluate partially
    }
}

/// Collect variable names used in term arguments that are NOT bound in `env`.
fn collect_free_vars_in_terms(args: &[TermExpr], env: &Env) -> Vec<String> {
    let mut free = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for arg in args {
        collect_free_in_term(arg, env, &mut free, &mut seen);
    }
    free
}

fn collect_free_in_term(
    term: &TermExpr,
    env: &Env,
    free: &mut Vec<String>,
    seen: &mut std::collections::HashSet<String>,
) {
    match term {
        TermExpr::Var(name) => {
            if !env.contains_key(name) && seen.insert(name.clone()) {
                free.push(name.clone());
            }
        }
        TermExpr::Lit(_) => {}
        TermExpr::FunCall { args, .. } => {
            for a in args {
                collect_free_in_term(a, env, free, seen);
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
    let mut new_env = env.clone();
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
                env.insert(name.clone(), val.clone());
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
