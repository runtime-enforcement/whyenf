/// The enforcement engine: evaluates programs against logs.

use std::collections::{BTreeSet, HashMap};
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

// ─── Runtime environment ─────────────────────────────────────────────────────

/// Binding environment: variable name → Value
type Env = HashMap<String, Value>;

/// Pending obligation from a delayed rule.
#[derive(Debug, Clone)]
struct Obligation {
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
    /// Whether to print rule labels on enforcement actions
    label_mode: bool,
    /// Whether to print verbose debug info
    verbose_mode: bool,
    /// Current time (verbose mode)
    current_time: std::time::SystemTime
}

impl Engine {
    pub fn new(program: Program, label_mode: bool, verbose_mode: bool) -> Self {
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
            event_names,
            let_defs,
            py_functions,
            obligations: HashMap::new(),
            next_tp_obligations: Vec::new(),
            current_ts: None,
            label_mode,
            verbose_mode,
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
        if let Some(max_ts) = self.obligations.keys().max().cloned() {
            self.flush_obligations(max_ts + 1);
        }
    }

    fn process_timepoint(&mut self, tp: &TimePoint) {
        let new_ts = tp.timestamp;

        vlog!(self, "\n╔══════════════════════════════════════════════════════════");
        vlog!(self, "║ Timepoint @{} — {} event(s)", new_ts, tp.events.len());
        for ev in &tp.events {
            vlog!(self, "║   {}", ev);
        }
        vlog!(self, "╚══════════════════════════════════════════════════════════");

        // If timestamp advanced, check obligations whose deadline is now past
        if self.current_ts == None {
            self.current_ts = Some(new_ts);
        }

        if new_ts > self.current_ts.unwrap() {
            // Flush intermediate timestamps in [current_ts, new_ts) — proactive gap-fill
            self.flush_obligations(new_ts);
        }
        self.current_ts = Some(new_ts);

        // 1. Update non-lagged  tables
        vlog!(self, "── Phase 1: update non-lagged tables ──");
        self.update_tables(&tp.events, false);

        // 2. Evaluate rules → produce suppress / cause lists
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
            vlog!(self, "── Phase 2: fixpoint iteration {} ({} events in working set) ──",
                  _iteration, working_events.len());
            let mut new_suppress: Vec<(EventInstance, Vec<String>)> = Vec::new();
            let mut new_cause: Vec<(EventInstance, Vec<String>)> = Vec::new();

            for rule_idx in 0..self.program.rules.len() {
                let rule = self.program.rules[rule_idx].clone();
                let bindings = self.match_clause_against_events(&rule.trigger, &working_events);

                let rule_label: Vec<String> = if self.label_mode {
                    rule.label.iter().cloned().collect()
                } else {
                    vec![]
                };

                for env in &bindings {
                    // Collect inherited labels from matched trigger pattern events
                    let inherited_labels: Vec<String> = if self.label_mode {
                        let mut inh = Vec::new();
                        for pat in &rule.trigger.patterns {
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
                        inh
                    } else {
                        vec![]
                    };

                    if let Some(let_def) = self.let_defs.get(&rule.event).cloned() {
                        // ── Let-bound predicate rule ─────────────────────────
                        let action_sym = match rule.action { RuleAction::Cause => "+", RuleAction::Suppress => "-", RuleAction::Observe => "?" };
                        vlog!(self, "  rule #{} {}{} (let-bound) matched with {} binding(s)",
                              rule_idx, action_sym, rule.event, 1);
                        let mut def_env = env.clone();
                        for ((pn, _), rp) in let_def.params.iter().zip(rule.params.iter()) {
                            if let Some(val) = self.try_eval_term(rp, env) {
                                def_env.insert(pn.clone(), val.clone());
                            }
                        }
                        let labels: Vec<String> = if self.label_mode {
                            let mut all = Vec::new();
                            for l in rule_label.iter().chain(let_def.label.iter()).chain(inherited_labels.iter()) {
                                if !all.contains(l) {
                                    all.push(l.clone());
                                }
                            }
                            all
                        } else {
                            vec![]
                        };
                        let body = let_def.body.clone();

                        match rule.action {
                            RuleAction::Cause => {
                                let events = self.collect_cause_events(&body, &def_env)
                                    .unwrap_or_else(|| panic!(
                                        "Rule '+{}': let body must be a pure conjunction of event patterns (no comparisons/negations)",
                                        rule.event
                                    ));
                                if let Some(_tp_off) = rule.tp_offset {
                                    for ev in events {
                                        self.next_tp_obligations.push(Obligation {
                                            event: ev,
                                            action: RuleAction::Cause,
                                            deadline: 0,
                                            validate: rule.validate.clone(),
                                            env: env.clone(),
                                            rule_idx,
                                            labels: labels.clone(),
                                        });
                                    }
                                } else if let Some(delay) = rule.delay {
                                    for ev in events {
                                        self.obligations
                                            .entry(self.current_ts.unwrap() + delay)
                                            .or_default()
                                            .push(Obligation {
                                                event: ev,
                                                action: RuleAction::Cause,
                                                deadline: self.current_ts.unwrap() + delay,
                                                validate: rule.validate.clone(),
                                                env: env.clone(),
                                                rule_idx,
                                                labels: labels.clone(),
                                            });
                                    }
                                } else {
                                    for ev in events {
                                        let key = (ev.name.clone(), ev.args.clone());
                                        if !caused_set.contains(&key) {
                                            caused_set.insert(key);
                                            new_cause.push((ev, labels.clone()));
                                        }
                                    }
                                }
                            }
                            RuleAction::Suppress => {
                                if let Some(ev) = self.find_leftmost_event(&body, &def_env) {
                                    if let Some(_tp_off) = rule.tp_offset {
                                        self.next_tp_obligations.push(Obligation {
                                            event: ev,
                                            action: RuleAction::Suppress,
                                            deadline: 0,
                                            validate: rule.validate.clone(),
                                            env: env.clone(),
                                            rule_idx,
                                            labels: labels.clone(),
                                        });
                                    } else if let Some(delay) = rule.delay {
                                        self.obligations
                                            .entry(self.current_ts.unwrap() + delay)
                                            .or_default()
                                            .push(Obligation {
                                                event: ev,
                                                action: RuleAction::Suppress,
                                                deadline: self.current_ts.unwrap() + delay,
                                                validate: rule.validate.clone(),
                                                env: env.clone(),
                                                rule_idx,
                                                labels: labels.clone(),
                                            });
                                    } else {
                                        let key = (ev.name.clone(), ev.args.clone());
                                        if !suppressed_set.contains(&key) {
                                            suppressed_set.insert(key);
                                            new_suppress.push((ev, labels.clone()));
                                        }
                                    }
                                }
                            }
                            RuleAction::Observe => {}
                        }
                    } else {
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
                                        new_suppress.push((ev, combined_labels));
                                    }
                                }
                                RuleAction::Cause => {
                                    let key = (ev.name.clone(), ev.args.clone());
                                    if !caused_set.contains(&key) {
                                        caused_set.insert(key);
                                        new_cause.push((ev, combined_labels));
                                    }
                                }
                                RuleAction::Observe => {}
                            }
                        }
                    }
                }
            }

            // Check if we reached the fixpoint (no new events)
            if new_cause.is_empty() && new_suppress.is_empty() {
                vlog!(self, "  → fixpoint reached after {} iteration(s)", _iteration + 1);
                break;
            }

            // Add newly caused events to the working set so subsequent iterations
            // can match them in triggers / filters.
            for (ev, labels) in &new_cause {
                vlog!(self, "  → new cause: {}", ev);
                caused_set.insert((ev.name.clone(), ev.args.clone()));
                if !labels.is_empty() {
                    working_labels.insert((ev.name.clone(), ev.args.clone()), labels.clone());
                }
                working_events.push(ev.clone());
            }
            for (ev, labels) in &new_suppress {
                vlog!(self, "  → new suppress: {}", ev);
                suppressed_set.insert((ev.name.clone(), ev.args.clone()));
                if !labels.is_empty() {
                    working_labels.insert((ev.name.clone(), ev.args.clone()), labels.clone());
                }
                // Suppressed events are also added to the working set so that
                // subsequent rules can observe the suppression.
                working_events.push(ev.clone());
            }

            all_suppress.extend(new_suppress);
            all_cause.extend(new_cause);
        }

        self.print_enforcer_output(&all_suppress, &all_cause, false);

        // 2b. Discharge obligations at this timestamp (proactive, AFTER reactive)
        {
            let mut proactive_cause: Vec<(EventInstance, Vec<String>)> = Vec::new();
            let mut proactive_suppress: Vec<(EventInstance, Vec<String>)> = Vec::new();
            let mut seen_cause: BTreeSet<(String, Vec<Value>)> = BTreeSet::new();
            let mut seen_suppress: BTreeSet<(String, Vec<Value>)> = BTreeSet::new();
            for ob in self.obligations.remove(&new_ts).unwrap_or_default() {
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
        }
        // Advance current_ts past this timepoint so flush_obligations
        // for the next timepoint starts at new_ts+1, not new_ts again.
        self.current_ts = Some(new_ts + 1);

        // 3. Update lagged tables
        vlog!(self, "── Phase 3: update lagged tables ──");
        self.update_tables(&tp.events, true);

        if self.verbose_mode {
            self.print_stats();
        }
    }

    /// Discharge obligations whose deadline < `up_to_ts`.
    /// Only prints proactive output for timestamps that actually have obligations.
    fn flush_obligations(&mut self, up_to_ts: u64) {
        vlog!(self, "── Flushing obligations with deadline < {} ──", up_to_ts);

        let start = self.current_ts.unwrap();
        for ts in start..up_to_ts {
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
        }
        self.current_ts = Some(up_to_ts);
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
        if proactive {
            if !cause.is_empty() {
                if self.label_mode {
                    for (ev, labels) in &cause {
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
                for (ev, labels) in &suppress {
                    let formatted = labels.iter().map(|l| format!("\"{}\"", l)).collect::<Vec<_>>().join(", ");
                    println!("[Enforcer:Label] Suppress {}: {}", ev, formatted);
                }
                for (ev, labels) in &cause {
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

    // ─── Table updates ───────────────────────────────────────────────────────

    fn update_tables(&mut self, events: &[EventInstance], lagged: bool) {
        let table_defs: Vec<TableDef> = self.program.tables.clone();
        for td in &table_defs {
            if td.lagged != lagged {
                continue; // skip if this table is not meant to be updated at this time-point
            }
            // Process remove clause FIRST, then add.
            // If both match the same row, add wins (matches Since semantics).
            if let Some(ref rm_clause) = td.remove_clause {
                let rm_envs = if rm_clause.patterns.is_empty() {
                    // Filter-only remove clause (no event patterns):
                    // evaluate filter against each existing row.
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
                    // Pattern-based remove: match patterns against events
                    self.match_patterns_against_events(&rm_clause.patterns, events)
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

    // ─── Pattern matching ────────────────────────────────────────────────────

    /// Match event patterns only (no filter) against a set of events.
    /// Returns all valid binding environments.
    fn match_patterns_against_events(
        &self,
        patterns: &[EventPattern],
        events: &[EventInstance],
    ) -> Vec<Env> {
        let mut envs = vec![Env::new()];
        for pat in patterns {
            let mut new_envs = Vec::new();
            for env in &envs {
                for event in events {
                    if event.name == pat.name && event.args.len() == pat.args.len() {
                        if let Some(extended) = self.try_match_pattern(pat, event, env) {
                            new_envs.push(extended);
                        }
                    }
                }
            }
            envs = new_envs;
        }
        envs
    }

    /// Match a clause (conjunction of event patterns + filter) against a set of events.
    /// Returns all valid binding environments, extended by any bindings from the filter.
    fn match_clause_against_events(
        &self,
        clause: &Clause,
        events: &[EventInstance],
    ) -> Vec<Env> {
        let envs = self.match_patterns_against_events(&clause.patterns, events);
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
                        if table.contains(&vals) {
                            return vec![env.clone()];
                        }
                        return vec![];
                    }

                    if let Some(def) = self.let_defs.get(name) {
                        let mut def_env = env.clone();
                        for ((pn, _), val) in def.params.iter().zip(vals.iter()) {
                            def_env.insert(pn.clone(), val.clone());
                        }
                        let body = def.body.clone();
                        if self.eval_filter(&body, &def_env, events) {
                            return vec![env.clone()];
                        }
                        return vec![];
                    }

                    if self.event_names.contains(name) {
                        if events.iter().any(|ev| ev.name == *name && ev.args == vals) {
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
                                result.push(ext);
                            }
                        }
                        return result;
                    }

                    if self.event_names.contains(name) {
                        for ev in events {
                            if ev.name == *name && ev.args.len() == args.len() {
                                if let Some(ext) = try_unify_args(args, &ev.args, env) {
                                    result.push(ext);
                                }
                            }
                        }
                        return result;
                    }

                    // Let definitions with free args: bind what we can, evaluate body,
                    // and propagate internal parameter bindings back to caller variables.
                    if let Some(def) = self.let_defs.get(name) {
                        let mut def_env = env.clone();
                        for ((pn, _), arg) in def.params.iter().zip(args.iter()) {
                            if let Some(val) = try_eval_term_partial(arg, env) {
                                def_env.insert(pn.clone(), val);
                            }
                        }
                        let body = def.body.clone();
                        // Use eval_filter_envs to get all satisfying environments
                        // (which may bind internal params via equality/lookups)
                        let body_envs = self.eval_filter_envs(&body, &def_env, events);
                        for body_env in &body_envs {
                            // Map internal param bindings back to caller arg variables
                            let mut ext_env = env.clone();
                            let mut consistent = true;
                            for ((pn, _), arg) in def.params.iter().zip(args.iter()) {
                                if let TermExpr::Var(caller_var) = arg {
                                    if let Some(val) = body_env.get(pn) {
                                        if let Some(existing) = ext_env.get(caller_var) {
                                            if existing != val {
                                                consistent = false;
                                                break;
                                            }
                                        } else {
                                            ext_env.insert(caller_var.clone(), val.clone());
                                        }
                                    }
                                }
                            }
                            if consistent {
                                result.push(ext_env);
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
                // Evaluate left side, collecting extended envs (existential bindings)
                let envs = self.eval_filter_envs(l, env, events);
                // For each env that satisfied the left, check the right
                let mut result = Vec::new();
                for e in &envs {
                    result.extend(self.eval_filter_envs(r, e, events));
                }
                result
            }

            FilterExpr::Or(l, r) => {
                let mut result = self.eval_filter_envs(l, env, events);
                if result.is_empty() {
                    result = self.eval_filter_envs(r, env, events);
                }
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

    // ─── Existential quantification helpers ──────────────────────────────────

    // ─── Let-bound predicate expansion ───────────────────────────────────────

    /// Collect all event instances to cause from a let body.
    /// The body must be a conjunction of event-name lookups (and `BoolLit(true)` leaves).
    /// Returns `None` if the body contains any non-event conditions (comparisons, negations, table
    /// lookups, let-def calls) — callers should treat this as a runtime error.
    fn collect_cause_events(&self, filter: &FilterExpr, env: &Env) -> Option<Vec<EventInstance>> {
        match filter {
            FilterExpr::BoolLit(true) => Some(vec![]),
            FilterExpr::BoolLit(false) => Some(vec![]),
            FilterExpr::And(l, r) => {
                let mut left = self.collect_cause_events(l, env)?;
                let right = self.collect_cause_events(r, env)?;
                left.extend(right);
                Some(left)
            }
            FilterExpr::TableLookup { name, args } if self.event_names.contains(name) => {
                let vals: Vec<Value> = args.iter().map(|a| self.eval_term(a, env)).collect();
                Some(vec![EventInstance { name: name.clone(), args: vals }])
            }
            FilterExpr::TableLookup { name, args } if self.let_defs.contains_key(name) => {
                let def = self.let_defs[name].clone();
                let vals: Vec<Value> = args.iter().map(|a| self.eval_term(a, env)).collect();
                let mut def_env = env.clone();
                for ((pn, _), val) in def.params.iter().zip(vals.iter()) {
                    def_env.insert(pn.clone(), val.clone());
                }
                self.collect_cause_events(&def.body.clone(), &def_env)
            }
            _ => None, // table lookup, comparison, negation — not allowed
        }
    }

    /// Find the leftmost event reference in a let body (for suppression).
    /// Traverses the And-tree depth-first, left-to-right.
    fn find_leftmost_event(&self, filter: &FilterExpr, env: &Env) -> Option<EventInstance> {
        match filter {
            FilterExpr::And(l, r) => self
                .find_leftmost_event(l, env)
                .or_else(|| self.find_leftmost_event(r, env)),
            FilterExpr::TableLookup { name, args } if self.event_names.contains(name) => {
                let vals: Vec<Value> = args.iter().map(|a| self.eval_term(a, env)).collect();
                Some(EventInstance { name: name.clone(), args: vals })
            }
            FilterExpr::TableLookup { name, args } if self.let_defs.contains_key(name) => {
                let def = self.let_defs[name].clone();
                let vals: Vec<Value> = args.iter().map(|a| self.eval_term(a, env)).collect();
                let mut def_env = env.clone();
                for ((pn, _), val) in def.params.iter().zip(vals.iter()) {
                    def_env.insert(pn.clone(), val.clone());
                }
                self.find_leftmost_event(&def.body.clone(), &def_env)
            }
            _ => None,
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
            // Can't unify a function call against a value during existential search
            // Would need to evaluate — skip for now
            false
        }
    }
}
