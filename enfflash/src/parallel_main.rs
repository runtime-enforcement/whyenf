mod ast;
mod monotonicity;
mod table;
mod engine;
mod preprocess;
mod typecheck;
mod parallel;

#[allow(clippy::all, unused, dead_code)]
mod log_parser;
#[allow(clippy::all, unused, dead_code)]
mod program_parser;

use clap::Parser as ClapParser;

#[derive(ClapParser, Debug)]
#[command(
    name = "enfflash-parallel",
    about = "Parallel enforcement — one in-process engine thread per split group"
)]
struct Cli {
    /// Path to the split manifest JSON (produced by Compiler.split_and_compile)
    #[arg(short, long)]
    manifest: String,

    /// Path to the log file (reads from stdin if omitted)
    #[arg(short, long)]
    log: Option<String>,

    /// Output enforcement actions in JSON format
    #[arg(long)]
    json: bool,

    /// Base path for per-group state files (group N saved as BASE_groupN).
    /// Loads on startup if files exist; saves on exit (normal or SIGINT).
    #[arg(long)]
    state: Option<String>,
}

fn main() {
    let cli = Cli::parse();
    parallel::run(&cli.manifest, cli.log.as_deref(), cli.json, cli.state.as_deref());
}
