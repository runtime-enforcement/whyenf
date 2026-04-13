mod ast;
mod monotonicity;
mod table;
mod engine;
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

    /// Print debug info about the engine's internal state (0=off, 1=basic, 2=full detail)
    #[arg(long, default_value_t = 0)]
    verbose: u8,

    /// Path to a state file for saving/restoring engine state across runs
    #[arg(long)]
    state: Option<String>,
}

fn main() {
    let cli = Cli::parse();

    // Read program source & preprocess Python function bodies
    let prog_src = fs::read_to_string(&cli.program)
        .unwrap_or_else(|e| panic!("Cannot read program file '{}': {}", cli.program, e));
    let (preprocessed, py_bodies) = preprocess::preprocess_fun_bodies(&prog_src);

    let mut program = program_parser::ProgramParser::new()
        .parse(&preprocessed)
        .unwrap_or_else(|e| panic!("Program parse error: {}", e));

    // Restore actual Python bodies
    preprocess::restore_fun_bodies(&mut program, &py_bodies);

    eprintln!(
        "[enfflash] Loaded program: {} event decls, {} fun decls, {} let defs, {} tables, {} rules",
        program.event_decls.len(),
        program.fun_decls.len(),
        program.let_defs.len(),
        program.tables.len(),
        program.rules.len(),
    );

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

    let mut engine = engine::Engine::new(program, cli.label, cli.json, cli.verbose > 0, cli.verbose);
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
    for line in reader.lines() {
        if interrupted.load(Ordering::SeqCst) {
            break;
        }
        let line = line.unwrap_or_else(|e| panic!("Read error: {}", e));
        buf.push_str(&line);
        buf.push('\n');
        if line.trim_end().ends_with(';') {
            let tp = tp_parser.parse(&buf)
                .unwrap_or_else(|e| panic!("Log parse error: {}", e));
            engine.process_one(&tp);
            buf.clear();
        }
    }
    // Flush any remaining delayed obligations
    engine.finish();

    // Save state on exit (normal or interrupted)
    if let Some(ref state_path) = cli.state {
        engine.save_state(state_path);
    }
}
