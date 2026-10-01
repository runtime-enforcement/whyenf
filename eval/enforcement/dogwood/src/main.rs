//! `dogwood-enforce`: replay an MFOTL-style log through Dogwood's reference
//! authorizer, for the tool-only benchmarks of `eval/enforcement`.
//!
//! Usage: `dogwood-enforce -sig SIG -formula POLICY.dw [-log LOG] [-verbose]`
//!
//! * The signature `SIG` is the benchmark's MFOTL signature.  Every predicate
//!   becomes a Dogwood action `L::Action::"p"` whose `context.input` record has
//!   the predicate's arguments (`string` → `String`, `int` → `Long`, `float` →
//!   `Long` in hundredths, since Dogwood's `sum` and comparisons are on `Long`).
//! * The policy's header lists the predicates to *decide*:
//!   `// decide: p, q`.  Their events are Dogwood `request` events (decision
//!   points); a denied one counts as suppressed and is followed by a
//!   `denied { rid }` history event, so that policies can exclude suppressed
//!   events from the history (`!formerly … ::denied{ rid: r }`).  Every other
//!   event is a history-only `state` event.  Each request carries a unique
//!   `rid`.
//! * A time-point `@ts e1 e2 …;` is a set of events: duplicates are dropped,
//!   the `state` events are recorded first, then the decided events are
//!   authorized one by one, all at timestamp `ts` (seconds).  `state` events of
//!   predicates the policy never mentions cannot affect a decision and are not
//!   recorded.
//! * Two optional header directives adapt the time-point semantics:
//!   - `// time-scale: N` multiplies timestamps by N (the policy's windows are
//!     then in units of 1/N s).  Dogwood windows must be positive, so with
//!     one time point per second, `within 1s` under `time-scale: 10` means
//!     "in the current time point".
//!   - `// order: p, q.f=v, …` processes the events of a time point in this
//!     order (events matching an earlier pattern first; unmatched ones last,
//!     in log order), state events still before decisions.  MFOTL events of a
//!     time point are simultaneous, but Dogwood sees them one by one: e.g. a
//!     witness decided in the same time point must be decided first.
//! * Measurement markers `> c <` are echoed as `> c ev tp cau sup ins ms <`,
//!   like Enfflash (eval/enforcement/replayer.py).

use std::collections::{BTreeSet, HashMap};
use std::fs;
use std::io::{self, BufRead, Write};
use std::time::{SystemTime, UNIX_EPOCH};

use dogwood_language::{
    Authorizer, Decision, Event, InMemoryTemporalEngine, LoweredPolicySet, PolicySchema,
    ServiceSchema, Validator, Value,
};

const NS: &str = "L";
const SCOPE: &str = "L::App::\"app\"";

const EVENT_SCHEMA: &str = r#"
max_window = 36500d

decision event <A>::request {
    ...inputs(A),
    rid: String,
}

event <A>::state {
    ...inputs(A),
}

event <A>::denied {
    rid: String,
}
"#;

#[derive(Clone, Copy, PartialEq)]
enum Ty {
    Str,
    Int,
    Float,
}

struct Pred {
    args: Vec<(String, Ty)>,
}

// ── Signature ────────────────────────────────────────────────────────────

/// Parse `name(a:t, …)[+-]` declarations; function declarations are skipped.
fn parse_sig(src: &str) -> Vec<(String, Pred)> {
    let src: String = src
        .lines()
        .filter(|l| {
            let t = l.trim_start();
            !(t.starts_with("fun ") || t.starts_with("sfun ") || t.starts_with("afun ")
                || t.starts_with('#') || t.starts_with("//"))
        })
        .collect::<Vec<_>>()
        .join("\n");
    let mut out = Vec::new();
    let b = src.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i].is_ascii_alphabetic() || b[i] == b'_' {
            let s = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            let name = &src[s..i];
            let mut j = i;
            while j < b.len() && b[j].is_ascii_whitespace() {
                j += 1;
            }
            if j < b.len() && b[j] == b'(' {
                let close = src[j..].find(')').map(|k| j + k).expect("unclosed declaration");
                let body = &src[j + 1..close];
                let args = body
                    .split(',')
                    .map(|a| a.trim())
                    .filter(|a| !a.is_empty())
                    .map(|a| {
                        let (n, t) = a.split_once(':').unwrap_or(("", a));
                        let ty = match t.trim() {
                            "int" => Ty::Int,
                            "float" => Ty::Float,
                            _ => Ty::Str,
                        };
                        (n.trim().to_string(), ty)
                    })
                    .collect();
                out.push((name.to_string(), Pred { args }));
                i = close + 1;
            }
        } else {
            i += 1;
        }
    }
    out
}

/// The Dogwood action schema of a signature.
fn cedar_schema(sig: &[(String, Pred)]) -> String {
    let mut s = format!("namespace {NS} {{\n  entity App;\n");
    for (name, p) in sig {
        let rec = p
            .args
            .iter()
            .enumerate()
            .map(|(k, (n, t))| {
                let n = if n.is_empty() { format!("x{k}") } else { n.clone() };
                let t = if *t == Ty::Str { "String" } else { "Long" };
                format!("{n}: {t}")
            })
            .collect::<Vec<_>>()
            .join(", ");
        s += &format!(
            "  action \"{name}\" appliesTo {{ principal: [App], resource: [App], context: {{ input: {{ {rec} }} }} }};\n"
        );
    }
    s + "}\n"
}

// ── Log ──────────────────────────────────────────────────────────────────

/// Parse one time-point `@ts e(a, …) …;` into its timestamp and events.
fn parse_tp(line: &str) -> Option<(i64, Vec<(String, Vec<String>)>)> {
    let line = line.trim();
    let rest = line.strip_prefix('@')?;
    let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
    let ts: i64 = rest[..end].parse().ok()?;
    let b: Vec<char> = rest[end..].chars().collect();
    let mut evs = Vec::new();
    let mut i = 0;
    while i < b.len() {
        if b[i].is_alphabetic() || b[i] == '_' {
            let s = i;
            while i < b.len() && (b[i].is_alphanumeric() || b[i] == '_') {
                i += 1;
            }
            let name: String = b[s..i].iter().collect();
            while i < b.len() && b[i].is_whitespace() {
                i += 1;
            }
            if i >= b.len() || b[i] != '(' {
                continue;
            }
            i += 1;
            let mut args = Vec::new();
            let mut cur = String::new();
            let mut quoted = false;
            while i < b.len() {
                let c = b[i];
                if c == '"' {
                    // A quoted string, with backslash escapes; whitespace
                    // before the opening quote is not part of the argument.
                    quoted = true;
                    cur.clear();
                    i += 1;
                    while i < b.len() && b[i] != '"' {
                        if b[i] == '\\' && i + 1 < b.len() {
                            i += 1;
                        }
                        cur.push(b[i]);
                        i += 1;
                    }
                } else if c == ',' || c == ')' {
                    let a = if quoted { cur.clone() } else { cur.trim().to_string() };
                    if !(a.is_empty() && !quoted && c == ')' && args.is_empty()) {
                        args.push(a);
                    }
                    cur.clear();
                    quoted = false;
                    if c == ')' {
                        i += 1;
                        break;
                    }
                } else if !quoted {
                    cur.push(c);
                }
                i += 1;
            }
            evs.push((name, args));
        } else {
            i += 1;
        }
    }
    Some((ts, evs))
}

fn value(ty: Ty, a: &str) -> Option<Value> {
    Some(match ty {
        Ty::Str => Value::String(a.to_string()),
        Ty::Int => Value::Int(a.trim().parse().ok()?),
        Ty::Float => Value::Int((a.trim().parse::<f64>().ok()? * 100.0).round() as i64),
    })
}

// ── Main ─────────────────────────────────────────────────────────────────

#[derive(Default)]
struct Stats {
    ev: u64,
    tp: u64,
    sup: u64,
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let opt = |flag: &str| args.iter().position(|a| a == flag).map(|k| args[k + 1].clone());
    let sig_path = opt("-sig").expect("-sig SIG required");
    let formula_path = opt("-formula").expect("-formula POLICY.dw required");
    let verbose = args.iter().any(|a| a == "-verbose");

    let sig = parse_sig(&fs::read_to_string(&sig_path).expect("cannot read signature"));
    let policy = fs::read_to_string(&formula_path).expect("cannot read policy");
    let decide: BTreeSet<String> = policy
        .lines()
        .filter_map(|l| l.trim().strip_prefix("// decide:"))
        .flat_map(|l| l.split(',').map(|p| p.trim().to_string()))
        .filter(|p| !p.is_empty())
        .collect();
    let mentioned = |p: &str| policy.contains(&format!("Action::\"{p}\""));
    let directive = |key: &str| {
        policy.lines().find_map(|l| l.trim().strip_prefix(key).map(|v| v.trim().to_string()))
    };
    let time_scale: i64 = directive("// time-scale:").map_or(1, |v| v.parse().expect("time-scale: integer"));
    // `// order:` patterns: (predicate, optional (field, value)).
    let order: Vec<(String, Option<(String, String)>)> = directive("// order:")
        .map(|v| {
            v.split(',')
                .map(|p| p.trim())
                .filter(|p| !p.is_empty())
                .map(|p| match p.split_once('.') {
                    Some((pred, fv)) => {
                        let (f, v) = fv.split_once('=').expect("order: pred.field=value");
                        (pred.to_string(), Some((f.to_string(), v.to_string())))
                    }
                    None => (p.to_string(), None),
                })
                .collect()
        })
        .unwrap_or_default();
    let rank = |name: &str, fields: &[(String, Value)]| {
        order
            .iter()
            .position(|(pred, fv)| {
                pred == name
                    && fv.as_ref().is_none_or(|(f, v)| {
                        fields.iter().any(|(n, x)| n == f && *x == Value::String(v.clone()))
                    })
            })
            .unwrap_or(order.len())
    };

    let service = ServiceSchema::builder()
        .event_schema_str(EVENT_SCHEMA)
        .build()
        .unwrap_or_else(|e| panic!("event schema: {e}"));
    let schema_src = cedar_schema(&sig);
    if args.iter().any(|a| a == "-print-schema") {
        println!("{schema_src}");
        return;
    }
    let schema = PolicySchema::from_cedarschema_str(&schema_src).unwrap_or_else(|e| panic!("action schema: {e}"));
    let lowered = LoweredPolicySet::from_str(&policy, &service, &schema).unwrap_or_else(|e| {
        eprintln!("[dogwood] policy error: {e:?}");
        std::process::exit(1)
    });
    let check = Validator::new().validate(&lowered);
    if !check.validation_passed() {
        eprintln!("[dogwood] validation failed: {check:?}");
        std::process::exit(1);
    }
    if args.iter().any(|a| a == "-check") {
        eprintln!("[dogwood] OK (decide: {decide:?})");
        return;
    }
    let mut auth = Authorizer::builder(lowered)
        .temporal_engine(InMemoryTemporalEngine::new().slice_leaves())
        .build()
        .unwrap_or_else(|e| panic!("authorizer: {e}"));

    let preds: HashMap<&str, &Pred> = sig.iter().map(|(n, p)| (n.as_str(), p)).collect();
    let input: Box<dyn BufRead> = match opt("-log") {
        Some(p) => Box::new(io::BufReader::new(fs::File::open(p).expect("cannot open log"))),
        None => Box::new(io::BufReader::new(io::stdin())),
    };
    let mut out = io::stdout().lock();
    let mut stats = Stats::default();
    let mut rid: u64 = 0;
    let mut last_ts = i64::MIN;

    for line in input.lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };
        let t = line.trim();
        if t.starts_with('>') && t.ends_with('<') {
            let inner = t[1..t.len() - 1].trim();
            let ms = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_millis()).unwrap_or(0);
            if writeln!(out, "> {inner} {} {} 0 {} 0 {ms} <", stats.ev, stats.tp, stats.sup)
                .and_then(|_| out.flush())
                .is_err()
            {
                return;
            }
            stats = Stats::default();
            continue;
        }
        let Some((ts, evs)) = parse_tp(t) else { continue };
        let ts = (ts * time_scale).max(last_ts);
        last_ts = ts;
        stats.tp += 1;

        // Set semantics; state events before decisions.
        let mut seen = BTreeSet::new();
        let mut states = Vec::new();
        let mut requests = Vec::new();
        for (name, a) in evs {
            if name == "tick" && a.is_empty() {
                continue;
            }
            stats.ev += 1;
            let Some(p) = preds.get(name.as_str()) else { continue };
            if p.args.len() != a.len() || !seen.insert((name.clone(), a.clone())) {
                continue;
            }
            let Some(vals) = p.args.iter().zip(&a).map(|((_, ty), s)| value(*ty, s)).collect::<Option<Vec<_>>>() else {
                continue;
            };
            let fields: Vec<(String, Value)> = p
                .args
                .iter()
                .enumerate()
                .map(|(k, (n, _))| if n.is_empty() { format!("x{k}") } else { n.clone() })
                .zip(vals)
                .collect();
            if decide.contains(&name) {
                requests.push((name, fields));
            } else if mentioned(&name) {
                states.push((name, fields));
            }
        }
        // Stable sorts: unmatched events keep their log order.
        states.sort_by_key(|(n, f)| rank(n, f));
        requests.sort_by_key(|(n, f)| rank(n, f));
        for (name, fields) in states {
            let mut b = Event::builder(&format!("{NS}::Action::{name}"), "state").timestamp(ts);
            for (n, v) in fields {
                b = b.field("input", &n, v);
            }
            auth.is_authorized(&b.build());
        }
        for (name, fields) in requests {
            rid += 1;
            let r = Value::String(rid.to_string());
            let mut b = Event::builder(&format!("{NS}::Action::{name}"), "request")
                .timestamp(ts)
                .principal(SCOPE)
                .resource(SCOPE)
                .logged_field("rid", r.clone());
            for (n, v) in fields {
                b = b.field("input", &n, v.clone()).request_context("input", &n, v);
            }
            let resp = auth.is_authorized(&b.build());
            let allowed = matches!(&resp, Some(r) if r.decision() == Decision::Allow);
            if !allowed {
                stats.sup += 1;
                if verbose {
                    let errs: Vec<String> = resp.iter().flat_map(|r| r.diagnostics().errors().map(|e| e.to_string())).collect();
                    eprintln!("[dogwood] @{ts} suppress {name} (rid {rid}) {errs:?}");
                }
                let d = Event::builder(&format!("{NS}::Action::{name}"), "denied")
                    .timestamp(ts)
                    .logged_field("rid", r);
                auth.is_authorized(&d.build());
            }
        }
    }
}
