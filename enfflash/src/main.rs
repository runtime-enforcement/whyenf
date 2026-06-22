mod ast;
mod monotonicity;
mod table;
mod engine;
mod sections;
mod preprocess;
mod typecheck;

use clap::Parser as ClapParser;
use std::fs;
use std::io::{self, BufRead};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

// LALRPOP-generated parsers
#[allow(clippy::all, unused, dead_code)]
mod log_parser;
#[allow(clippy::all, unused, dead_code)]
mod program_parser;

#[derive(ClapParser, Debug)]
#[command(name = "enfflash", about = "Blazingly fast runtime enforcement engine")]
struct Cli {
    /// Path to the enfflash program file
    #[arg(short, long)]
    program: String,

    /// Path to the log file (reads from stdin if omitted)
    #[arg(short, long)]
    log: Option<String>,

    /// Print the labels of rules involved in each enforcement action
    #[arg(long)]
    label: bool,

    /// Output enforcement actions in JSON format
    #[arg(long)]
    json: bool,

    /// Emit {"sync":true} after each reactive timepoint (used by parallel orchestrator)
    #[arg(long)]
    sync: bool,

    /// Print debug info about the engine's internal state (0=off, 1=basic, 2=full detail)
    #[arg(long, default_value_t = 0)]
    verbose: u8,

    /// Path to a state file for saving/restoring engine state across runs
    #[arg(long)]
    state: Option<String>,

    /// Ignore wave/section structure; run all rules as one global fixpoint per timepoint
    #[arg(long)]
    flat: bool,

    /// Print the program's estimated per-time-point complexity (from the .ef
    /// `// complexity` annotation emitted by the compiler) and exit.
    #[arg(long)]
    complexity: bool,
}

/// Per-marker statistics for the `> ... <` latency protocol (see eval replayer).
#[derive(Default)]
struct Stats {
    ev_done: u64,
    tp_done: u64,
    ev_cau:  u64,
    ev_sup:  u64,
    tp_ins:  u64,
}

fn main() {
    // Restore the default SIGPIPE behaviour. Rust ignores SIGPIPE by default,
    // which turns a closed stdout (e.g. the eval replayer killing us at the end
    // of a run) into an EPIPE write error that `println!` escalates to a panic.
    // With SIG_DFL the process is simply terminated quietly, as expected of a
    // streaming CLI tool.
    unsafe { libc::signal(libc::SIGPIPE, libc::SIG_DFL); }

    let cli = Cli::parse();

    // Read program source & preprocess Python function bodies
    let prog_src = fs::read_to_string(&cli.program)
        .unwrap_or_else(|e| panic!("Cannot read program file '{}': {}", cli.program, e));

    // `--complexity`: surface the per-time-point complexity the compiler wrote
    // into the .ef as a `// complexity …` comment, then exit.
    if cli.complexity {
        // The annotation reads `// complexity (…): <expr>`; print just <expr>.
        let annotation = prog_src.lines().find_map(|l| {
            let l = l.trim_start();
            if l.starts_with("// complexity") {
                l.split_once(": ").map(|(_, expr)| expr.trim().to_string())
            } else {
                None
            }
        });
        match annotation {
            Some(c) => println!("{}", c),
            None => eprintln!(
                "[enfflash] no complexity annotation in '{}' \
                 (recompile with a recent enfguard)", cli.program),
        }
        return;
    }

    let (preprocessed, py_bodies) = preprocess::preprocess_fun_bodies(&prog_src);

    let mut program = program_parser::ProgramParser::new()
        .parse(&preprocessed)
        .unwrap_or_else(|e| panic!("Program parse error: {}", e));

    // Restore actual Python bodies
    preprocess::restore_fun_bodies(&mut program, &py_bodies);

    if cli.verbose > 0 {
        eprintln!(
            "[enfflash] Loaded program: {} event decls, {} fun decls, {} let defs, {} tables, {} rules",
            program.event_decls.len(),
            program.fun_decls.len(),
            program.let_defs.len(),
            program.tables.len(),
            program.rules.len(),
        );
    }

    // Type check
    let check = typecheck::check_program(&program);
    if !check.is_empty() {
        for e in &check.errors {
            eprintln!("[typecheck] ERROR: {}", e);
        }
        std::process::exit(1);
    }

    // Stream the log: read until ';', parse one time-point at a time.
    let reader: Box<dyn BufRead> = match &cli.log {
        Some(path) => Box::new(io::BufReader::new(
            fs::File::open(path)
                .unwrap_or_else(|e| panic!("Cannot open log file '{}': {}", path, e))
        )),
        None => Box::new(io::BufReader::new(io::stdin())),
    };

    let mut engine = engine::Engine::new(program, cli.label, cli.json, cli.sync, cli.verbose > 0, cli.verbose, cli.flat);
    if cli.verbose > 0 {
        engine.print_program_summary();
    }

    // Load saved state if --state is given and file exists
    if let Some(ref state_path) = cli.state {
        engine.load_state(state_path);
    }

    // Set up SIGINT (Ctrl-C) handler for graceful state save
    let interrupted = Arc::new(AtomicBool::new(false));
    {
        let interrupted = Arc::clone(&interrupted);
        ctrlc::set_handler(move || {
            eprintln!("\n[enfflash] Interrupted (SIGINT)");
            interrupted.store(true, Ordering::SeqCst);
        }).expect("Error setting Ctrl-C handler");
    }

    let tp_parser = log_parser::SingleTimePointParser::new();
    let mut buf = String::new();
    // Accumulator for the `> ... <` measurement/latency protocol used by the
    // eval replayer (see eval/enforcement/replayer.py).  Stats accumulate over
    // the time-points processed since the previous marker, then reset.
    let mut stats = Stats::default();
    for line in reader.lines() {
        if interrupted.load(Ordering::SeqCst) {
            break;
        }
        let line = line.unwrap_or_else(|e| panic!("Read error: {}", e));
        let trimmed = line.trim();
        // Measurement marker: `> <comment> <`.  Echo back the comment followed
        // by the accumulated stats and a wall-clock timestamp (ms), then reset.
        if buf.trim().is_empty() && trimmed.starts_with('>') && trimmed.ends_with('<') {
            let inner = trimmed[1..trimmed.len() - 1].trim();
            let now_ms = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_millis())
                .unwrap_or(0);
            println!(
                "> {} {} {} {} {} {} {} <",
                inner, stats.ev_done, stats.tp_done, stats.ev_cau,
                stats.ev_sup, stats.tp_ins, now_ms
            );
            let _ = io::Write::flush(&mut io::stdout());
            stats = Stats::default();
            continue;
        }
        buf.push_str(&line);
        buf.push('\n');
        if line.trim_end().ends_with(';') {
            let tp = tp_parser.parse(&buf)
                .unwrap_or_else(|e| panic!("Log parse error: {}", e));
            stats.tp_done += 1;
            stats.ev_done += tp.events.iter()
                .filter(|e| !(e.name == "tick" && e.args.is_empty()))
                .count() as u64;
            let outputs = engine.process_one(&tp);
            for o in &outputs {
                stats.ev_cau += o.cause.len() as u64;
                stats.ev_sup += o.suppress.len() as u64;
                if o.proactive && !o.cause.is_empty() {
                    stats.tp_ins += 1;
                }
            }
            engine.print_outputs(&outputs);
            buf.clear();
        }
    }
    // Flush any remaining delayed obligations
    let outputs = engine.finish();
    engine.print_outputs(&outputs);

    // Save state on exit (normal or interrupted)
    if let Some(ref state_path) = cli.state {
        engine.save_state(state_path);
    }
}
