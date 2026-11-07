//! Runs the recorded benchmarks and compares them with the baseline
//! (docs/testing.md, "Benchmarks").

use std::path::PathBuf;
use std::process::ExitCode;

use clap::Parser;
use stitchwort_bench::baseline::{self, Baseline};
use stitchwort_bench::{Record, programs, run};

#[derive(Parser)]
#[command(
    name = "stitchwort-bench",
    about = "Run the benchmarks and compare them with the recorded baseline"
)]
struct Cli {
    /// Run only benchmarks whose names contain one of these
    filters: Vec<String>,
    /// Runs of each benchmark (the `examples` sweep is run once); the time
    /// recorded is their median
    #[arg(long, default_value_t = 5)]
    runs: usize,
    /// Only the deterministic counts, from one run of each benchmark: no times
    #[arg(long)]
    no_time: bool,
    /// Record this run as the new baseline (for the benchmarks run)
    #[arg(long)]
    update: bool,
    /// The baseline file
    #[arg(long, default_value_os_t = baseline::default_path())]
    baseline: PathBuf,
    /// Write each benchmark part's counts (one example file, say) from the
    /// first run to this file, one line per part: for comparing two builds
    #[arg(long)]
    parts: Option<PathBuf>,
    /// Threads the `examples` benchmark spreads its examples over. The counts
    /// depend a little on it (a thread's buffers grow as it goes), so only
    /// compare runs with the same number
    #[arg(long, default_value_t = 8)]
    jobs: usize,
    /// List the benchmarks
    #[arg(long)]
    list: bool,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    programs::JOBS.store(cli.jobs, std::sync::atomic::Ordering::Relaxed);
    let selected: Vec<_> = programs::ALL
        .iter()
        .filter(|b| cli.filters.is_empty() || cli.filters.iter().any(|f| b.name.contains(f)))
        .collect();
    if cli.list {
        for b in &selected {
            println!("{:22} {}", b.name, b.about);
        }
        return ExitCode::SUCCESS;
    }
    if selected.is_empty() {
        eprintln!("error: no benchmark matches {:?}", cli.filters);
        return ExitCode::FAILURE;
    }
    // Times from an unoptimised build mean nothing next to a release one.
    let timed = !cli.no_time && !cfg!(debug_assertions);
    if !cli.no_time && !timed {
        eprintln!("warning: not timing: this is a debug build (use `cargo run --release`)");
    }
    let runs = if timed { cli.runs } else { 1 };
    let mut old = match Baseline::read(&cli.baseline) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };

    let mut records: Vec<(&str, Record)> = Vec::new();
    let mut failures = Vec::new();
    let mut part_lines = String::new();
    for b in &selected {
        eprint!("{} ...", b.name);
        // The sweep takes a minute even spread over threads, its counts are
        // checked for repeating by `tests/repeat.rs`, and its time is far
        // above the noise: one run of it, not five.
        let runs = if b.name == "examples" { 1 } else { runs };
        match run(b, runs, timed) {
            Ok(outcome) => {
                eprintln!(" done");
                if let Some(variation) = &outcome.variation {
                    failures.push(format!(
                        "{}: the counts differed between runs, so they aren't a reliable signal:\n{variation}",
                        b.name
                    ));
                }
                for (part, c) in &outcome.parts {
                    part_lines += &format!(
                        "{} {part} steps={} visits={} allocations={} peak_bytes={}\n",
                        b.name, c.steps, c.visits, c.allocations, c.peak_bytes
                    );
                }
                records.push((b.name, outcome.record));
            }
            Err(e) => {
                eprintln!(" failed");
                failures.push(format!("{} didn't run:\n{e}", b.name));
            }
        }
    }

    if let Some(path) = &cli.parts
        && let Err(e) = std::fs::write(path, part_lines)
    {
        eprintln!("error: can't write {}: {e}", path.display());
    }
    let results: Vec<(&str, &Record)> = records.iter().map(|(n, r)| (*n, r)).collect();
    let comparison = baseline::compare(&old, &results, !cli.filters.is_empty());
    println!(
        "Compared with {} ({}{} run(s) each)\n",
        cli.baseline.display(),
        if timed { "" } else { "counts only, " },
        runs
    );
    print!("{comparison}");
    for failure in &failures {
        println!("FAILED: {failure}");
    }

    if cli.update {
        if !failures.is_empty() {
            eprintln!("error: not updating the baseline, since some benchmarks failed");
            return ExitCode::FAILURE;
        }
        for (name, mut record) in records {
            // Without a new time, keep the old one rather than none.
            if record.time_ms.is_none() {
                record.time_ms = old.get(name).and_then(|r| r.time_ms);
            }
            old.set(name, record);
        }
        if let Err(e) = std::fs::write(&cli.baseline, old.to_toml()) {
            eprintln!("error: can't write {}: {e}", cli.baseline.display());
            return ExitCode::FAILURE;
        }
        println!("\nUpdated {}.", cli.baseline.display());
        return ExitCode::SUCCESS;
    }
    if comparison.failed() || !failures.is_empty() {
        println!(
            "\nIf a regression is expected (the change is worth its cost), \
             record a new baseline with --update and say why in the commit."
        );
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

// test-alloc: the library's global allocator, stitchwort_bench::alloc::Counting, wraps mimalloc.
