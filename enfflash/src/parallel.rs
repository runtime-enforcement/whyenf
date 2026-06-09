/// Parallel enforcement orchestrator — Rayon-based.
///
/// Each split group gets its own [`Engine`] instance stored in a plain
/// `Vec<Worker>`.  Per time-point, all workers run `process_one` in parallel
/// via `rayon::par_iter_mut` — no channels, no OS-thread handshake, just a
/// Rayon work-stealing call over in-memory data.
///
/// State persistence works the same as the sequential engine: per-group files
/// `{BASE}_group{N}` are loaded at startup (if they exist) and saved after
/// `finish()` / SIGINT.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::io::{self, BufRead, BufReader};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use rayon::prelude::*;

use crate::ast::{EventInstance, Program, TimePoint, Value};
use crate::engine::{Engine, EnfOutput};
use crate::preprocess;
use crate::program_parser;
use crate::typecheck;

// ─── Manifest ────────────────────────────────────────────────────────────────

/// One data-split hashing axis for a group: an event named in [fields] is
/// accepted only if `hash(args[fields[name]]) % modulo == bucket`.  Events not
/// listed wildcard on this axis (accepted regardless).
#[derive(Debug, Clone)]
struct DataRoute {
    modulo: u64,
    bucket: u64,
    fields: HashMap<String, usize>,
}

#[derive(Debug)]
struct GroupSpec {
    program_path:     String,
    trigger_events:   HashSet<String>,
    data_routes:      Vec<DataRoute>,
    /// Events carrying a tainted (un-partitionable) field — always accepted.
    broadcast_events: HashSet<String>,
}

fn load_manifest(path: &str) -> Vec<GroupSpec> {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("Cannot read manifest '{}': {}", path, e));
    let v: serde_json::Value = serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("Manifest parse error in '{}': {}", path, e));
    v["groups"].as_array()
        .unwrap_or_else(|| panic!("Manifest '{}' has no 'groups' array", path))
        .iter()
        .map(|g| GroupSpec {
            program_path: g["program"].as_str()
                .unwrap_or_else(|| panic!("group missing 'program'"))
                .to_string(),
            trigger_events: g["trigger_events"].as_array()
                .unwrap_or_else(|| panic!("group missing 'trigger_events'"))
                .iter()
                .map(|e| e.as_str().expect("trigger_events must be strings").to_string())
                .collect(),
            data_routes: g["data_routes"].as_array().map(|arr| arr.iter().map(|r| {
                DataRoute {
                    modulo: r["modulo"].as_u64().expect("data_route modulo must be int"),
                    bucket: r["bucket"].as_u64().expect("data_route bucket must be int"),
                    fields: r["fields"].as_object().expect("data_route fields must be object")
                        .iter()
                        .map(|(k, v)| (k.clone(), v.as_u64().expect("field index must be int") as usize))
                        .collect(),
                }
            }).collect()).unwrap_or_default(),
            broadcast_events: g["broadcast_events"].as_array().map(|arr| arr.iter()
                .map(|e| e.as_str().expect("broadcast_events must be strings").to_string())
                .collect()).unwrap_or_default(),
        })
        .collect()
}

/// Deterministic hash of a field value into a bucket index.  Uses the standard
/// `DefaultHasher` (fixed-key SipHash), so the same value always maps to the
/// same bucket across events and runs.
fn hash_value(v: &Value) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    v.hash(&mut h);
    h.finish()
}

fn load_program(path: &str) -> Program {
    let src = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("Cannot read program '{}': {}", path, e));
    let (preprocessed, py_bodies) = preprocess::preprocess_fun_bodies(&src);
    let mut program = program_parser::ProgramParser::new()
        .parse(&preprocessed)
        .unwrap_or_else(|e| panic!("Program parse error in '{}': {}", path, e));
    preprocess::restore_fun_bodies(&mut program, &py_bodies);
    let check = typecheck::check_program(&program);
    if !check.is_empty() {
        for e in &check.errors { eprintln!("[typecheck] ERROR in '{}': {}", path, e); }
        std::process::exit(1);
    }
    program
}

fn worker_state_path(base: &str, idx: usize) -> String {
    format!("{}_group{}", base, idx)
}

// ─── Worker ───────────────────────────────────────────────────────────────────

struct Worker {
    engine:           Engine,
    triggers:         HashSet<String>,
    data_routes:      Vec<DataRoute>,
    broadcast_events: HashSet<String>,
    save_path:        Option<String>,
}

/// Should this worker receive event [ev]?  Combines the event-split filter
/// (trigger vocabulary) with the data-split filter (hash routing).
fn event_accepted(w: &Worker, ev: &EventInstance) -> bool {
    // Always keep `tick`: it is how the engine recognises a tick time-point
    // (Engine::is_tick_timepoint) and skips reactive processing.  Dropping it
    // would make the worker emit a spurious reactive output.
    if ev.name == "tick" { return true; }
    // Event-split filter: only events this group's clauses trigger on.
    if !w.triggers.contains(&ev.name) { return false; }
    // Data-split: tainted-field events broadcast to every shard.
    if w.broadcast_events.contains(&ev.name) { return true; }
    // Each axis the event participates in must match this shard's bucket;
    // axes the event does not expose are wildcards.
    for route in &w.data_routes {
        if let Some(&idx) = route.fields.get(&ev.name) {
            if idx < ev.args.len()
               && hash_value(&ev.args[idx]) % route.modulo != route.bucket {
                return false;
            }
        }
    }
    true
}

fn filter_timepoint(tp: &TimePoint, w: &Worker) -> TimePoint {
    TimePoint {
        timestamp: tp.timestamp,
        events: tp.events.iter()
            .filter(|ev| event_accepted(w, ev))
            .cloned()
            .collect(),
    }
}

// ─── Output joining ───────────────────────────────────────────────────────────

#[derive(Default)]
struct Pending {
    cause:           Vec<EventInstance>,
    suppress:        Vec<EventInstance>,
    dur_nanos:       Option<u64>,
    latency_micros:  u64,
}

fn merge_into(map: &mut BTreeMap<(u64, bool), Pending>, out: EnfOutput) {
    let entry = map.entry((out.ts, out.proactive)).or_default();
    for (ev, _) in out.cause {
        if !entry.cause.iter().any(|e: &EventInstance| *e == ev) {
            entry.cause.push(ev);
        }
    }
    for (ev, _) in out.suppress {
        if !entry.suppress.iter().any(|e: &EventInstance| *e == ev) {
            entry.suppress.push(ev);
        }
    }
    if let Some(d) = out.dur_nanos {
        entry.dur_nanos = Some(entry.dur_nanos.unwrap_or(0).max(d));
    }
    entry.latency_micros = entry.latency_micros.max(out.latency_micros);
}

fn emit_pending(ts: u64, proactive: bool, p: Pending, json_mode: bool) {
    let out = EnfOutput {
        ts,
        proactive,
        cause:    p.cause.into_iter().map(|e| (e, vec![])).collect(),
        suppress: p.suppress.into_iter().map(|e| (e, vec![])).collect(),
        dur_nanos:      p.dur_nanos,
        latency_micros: p.latency_micros,
    };
    out.print(json_mode, false);
}

// ─── Main entry point ─────────────────────────────────────────────────────────

pub fn run(manifest_path: &str, log_path: Option<&str>, json_mode: bool, state_base: Option<&str>) {
    let specs = load_manifest(manifest_path);
    eprintln!("[parallel] {} group(s) from '{}'", specs.len(), manifest_path);

    let mut workers: Vec<Worker> = specs.into_iter().enumerate().map(|(idx, spec)| {
        eprintln!("[parallel] Loading '{}' (triggers: {:?})", spec.program_path, spec.trigger_events);
        let program   = load_program(&spec.program_path);
        let save_path = state_base.map(|b| worker_state_path(b, idx));
        let load_path = state_base.map(|b| worker_state_path(b, idx));
        let mut engine = Engine::new(program, false, false, false, false, 0);
        if let Some(ref path) = load_path {
            engine.load_state(path);
        }
        Worker { engine, triggers: spec.trigger_events,
                 data_routes: spec.data_routes,
                 broadcast_events: spec.broadcast_events, save_path }
    }).collect();

    let mut pending: BTreeMap<(u64, bool), Pending> = BTreeMap::new();
    let mut last_ts: Option<u64> = None;

    // ── SIGINT ────────────────────────────────────────────────────────────────
    let interrupted = Arc::new(AtomicBool::new(false));
    {
        let flag = Arc::clone(&interrupted);
        ctrlc::set_handler(move || {
            eprintln!("\n[parallel] Interrupted (SIGINT)");
            flag.store(true, Ordering::SeqCst);
        }).expect("Error setting Ctrl-C handler");
    }

    // ── Stream log ────────────────────────────────────────────────────────────
    let reader: Box<dyn BufRead> = match log_path {
        Some(p) => Box::new(BufReader::new(
            std::fs::File::open(p)
                .unwrap_or_else(|e| panic!("Cannot open log '{}': {}", p, e))
        )),
        None => Box::new(BufReader::new(io::stdin())),
    };

    let tp_parser = crate::log_parser::SingleTimePointParser::new();
    let mut buf   = String::new();

    for line in reader.lines() {
        if interrupted.load(Ordering::SeqCst) { break; }
        let line = line.unwrap_or_else(|e| panic!("Read error: {}", e));
        buf.push_str(&line);
        buf.push('\n');
        if !line.trim_end().ends_with(';') { continue; }

        let tp = tp_parser.parse(&buf)
            .unwrap_or_else(|e| panic!("Log parse error: {}", e));
        buf.clear();

        let current_ts = tp.timestamp;

        // Parallel: all workers call process_one concurrently via Rayon.
        // Each worker filters the timepoint to its trigger vocabulary and its
        // data-split bucket.
        let per_worker: Vec<Vec<EnfOutput>> = workers.par_iter_mut()
            .map(|w| {
                let filtered = filter_timepoint(&tp, w);
                w.engine.process_one(&filtered)
            })
            .collect();

        for outputs in per_worker {
            for out in outputs { merge_into(&mut pending, out); }
        }

        // Emit proactive output for every timestamp strictly below the current
        // one.  Proactive obligations for ts T are produced while processing the
        // first time-point whose timestamp exceeds T (e.g. the tick that advances
        // the clock), and all workers advance in lockstep, so every (ts < current)
        // entry in `pending` is now complete and can be flushed.
        if let Some(prev) = last_ts {
            if prev < current_ts {
                let done: Vec<_> = pending.range(..(current_ts, false)).map(|(&k, _)| k).collect();
                for key in done {
                    let p = pending.remove(&key).unwrap();
                    emit_pending(key.0, key.1, p, json_mode);
                }
            }
        }

        // Emit the *reactive* output for the current time-point immediately —
        // exactly as the single engine does (main.rs prints each process_one
        // result right away).  Holding it back until the next time-point arrives
        // added a full inter-tick delay (≈1 s in live mode) to every enforced
        // request, which is the sole reason parallel mode appeared far slower
        // than sequential mode.  Proactive output for `current_ts` is not produced
        // yet (it is emitted when the clock next advances), so only
        // `(current_ts, false)` entries can be present here.
        if let Some(p) = pending.remove(&(current_ts, false)) {
            emit_pending(current_ts, false, p, json_mode);
        }
        last_ts = Some(current_ts);
    }

    // ── Finish ────────────────────────────────────────────────────────────────
    let final_per_worker: Vec<Vec<EnfOutput>> = workers.par_iter_mut()
        .map(|w| {
            let out = w.engine.finish();
            if let Some(ref path) = w.save_path {
                w.engine.save_state(path);
            }
            out
        })
        .collect();

    for outputs in final_per_worker {
        for out in outputs { merge_into(&mut pending, out); }
    }

    for ((ts, proactive), p) in pending {
        emit_pending(ts, proactive, p, json_mode);
    }
}
