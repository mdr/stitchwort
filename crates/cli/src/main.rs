use std::collections::BTreeSet;
use std::io::{IsTerminal, Read};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use rustyline::error::ReadlineError;
use stitchwort_cli::driver::{Cache, Outcome, Session, TestResult};
use stitchwort_cli::project::{
    DiskFiles, Target, analyse, find_project, namespace_of, project_sources, run_unknown_namespace,
};
use stitchwort_cli::render::render;
use stitchwort_cli::run::Main;
use stitchwort_elab::project::FileModeContext;
use stitchwort_fmt::Error as FmtError;
use stitchwort_syntax::{Diagnostic, Severity, SourceMap, parse_namespace_line};

#[derive(Parser)]
#[command(name = "stitchwort", version, about = "The Stitchwort language")]
struct Cli {
    #[command(subcommand)]
    command: Command,
    /// Read the standard library from this directory (laid out as
    /// `crates/elab/src/std`) instead of the copy built in, so edits to it
    /// take effect without a rebuild. The environment variable
    /// `STITCHWORT_STD_DIR` does the same; this wins
    #[arg(long, global = true, value_name = "DIR")]
    std_dir: Option<PathBuf>,
}

/// A session for the compiler thread.
fn new_session(navigation: bool) -> Session {
    if navigation {
        Session::navigable_for_stack(STACK)
    } else {
        Session::for_stack(STACK)
    }
}

#[derive(Subcommand)]
enum DevCommand {
    /// Which machine instructions a program's reachable code uses, and
    /// whether it fits native compilation's N1 subset
    /// (docs/proposals/native-compilation.md, Appendix: N1 coverage census)
    OpcodeCensus {
        /// A file, or the full name of a function in the project
        target: String,
        /// Also list every reachable body with its instructions
        #[arg(long)]
        functions: bool,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// Stage N0 of docs/proposals/native-compilation.md: JIT-compile the
    /// Cranelift spike, check it and print its measurements. Needs a build
    /// with the `native` feature (`cargo build --release -p stitchwort-cli
    /// --features native`)
    NativeSpike {
        /// How many calls of `sum(20)` to time for the per-call cost
        #[arg(long, default_value_t = 1_000_000)]
        rounds: u64,
        /// Where compiled code goes: `system` (cranelift-jit's own memory)
        /// or, on macOS on Apple Silicon, `map-jit` (the default there)
        #[arg(long)]
        memory: Option<String>,
    },
}

#[derive(Subcommand)]
enum Command {
    /// Type-check source files, or namespaces of the project (all of them
    /// if none are named)
    Check {
        /// Files (a name ending in `.sw`, or with a `/`), or namespaces of
        /// the project; not both
        targets: Vec<String>,
        /// The project folder (the one with `stitchwort.yaml`), if not the
        /// folder you're in or the nearest one above it
        #[arg(long)]
        project: Option<PathBuf>,
        /// Also write the code navigation index (JSON; see
        /// docs/proposals/code-navigation.md) to this file, or to standard
        /// output for `-`. One file or any number of namespaces
        #[arg(long, value_name = "FILE")]
        index: Option<String>,
        #[command(flatten)]
        counterexamples: CounterexampleArgs,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// Print an embedded standard library file (`List/Toolkit.sw`;
    /// `core/Int.sw` is a file of the core), as the index's `std` markers name them
    StdSource { path: String },
    /// Run tests, reusing cached results where nothing they depend on has
    /// changed: a file's, or a namespace's (with every namespace under it,
    /// and those they use), or the whole project's. A target that matches
    /// no tests is a warning and a failure
    Test {
        /// A file, or a namespace of the project
        target: Option<String>,
        #[command(flatten)]
        cache: CacheArgs,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
        /// Run the tests on the reference evaluator (the type checker's own,
        /// which is much slower) instead of the fast runtime
        #[arg(long)]
        reference: bool,
    },
    /// Type-check a file, then run its `main`; or run a function of the
    /// project by its full name (`Day05.main`). Reads standard input and
    /// writes standard output
    Run {
        /// A file, or the full name of a function in the project
        target: String,
        /// Compile the program to JavaScript and run it with Node.js (`node`
        /// on the PATH), which is much faster
        #[arg(long)]
        js: bool,
        /// Run on the reference evaluator (the type checker's own, which is
        /// much slower and recurses less deeply) instead of the fast runtime
        #[arg(long, conflicts_with = "js")]
        reference: bool,
        /// Run the functions `main` calls as native code, where they and
        /// everything they reach compile (stage N1; experimental). Needs a
        /// build with the `native` feature
        #[arg(long, conflicts_with_all = ["js", "reference"])]
        native: bool,
        /// With --native, say on standard error what ran natively, and why
        /// anything didn't
        #[arg(long, requires = "native")]
        verbose: bool,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
        /// Write the fast runtime's allocation trace (`alloc`, `reuse`,
        /// `inc`, `dec`, `free` of constructor cells, identities numbered
        /// by first appearance) to FILE. Only in a build with the
        /// `alloc-trace` feature; for comparing native code with the
        /// machine
        #[arg(long, hide = true, value_name = "FILE", conflicts_with_all = ["js", "reference"])]
        alloc_trace: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// List the axioms a definition or theorem depends on, directly or
    /// through what it uses, one per line, sorted (today only `Quot.sound`).
    /// An empty report means no axiom is used; it does not mean the term
    /// computes to data in the kernel (a proof built from `Quot.ind` can
    /// still be stuck)
    Axioms {
        /// A file, or the full name of a definition in the project
        /// (`Main.total`)
        target: String,
        /// The definition's name in the file, when the target is a file
        name: Option<String>,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// Developer tools for measuring the implementation (not a stable interface)
    #[command(hide = true, subcommand)]
    Dev(DevCommand),
    /// Format source files in place: indentation, spacing, blank lines and brackets, in the house style. Prints the files it changed
    Fmt {
        /// Files (`.sw`) or folders to format; `-` reads standard input and
        /// writes standard output. None: the project's sources
        files: Vec<PathBuf>,
        /// Write nothing; list the files that would change, and exit with
        /// status 1 if any would
        #[arg(long)]
        check: bool,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
    },
    /// Evaluate an expression in the context of a file
    Eval {
        file: PathBuf,
        expr: String,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// Start an interactive session, optionally with a file loaded
    Repl { file: Option<PathBuf> },
    /// Run the language server, speaking LSP on standard input and output
    /// (docs/proposals/language-server.md)
    Lsp,
    /// Extract a file's exports, or a namespace's, to JavaScript
    Build {
        /// A file, or a namespace of the project
        target: String,
        /// Generate an ES module and TypeScript declarations
        #[arg(long, required = true)]
        js: bool,
        /// Output directory
        #[arg(short, long, default_value = ".")]
        out: PathBuf,
        /// Also write a source map (`NAME.js.map`) from the generated
        /// module to the `.sw` source, one entry per definition, and refer
        /// to it from the module
        #[arg(long)]
        source_map: bool,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
}

/// `check --counterexamples` (docs/proposals/counterexample-search.md
/// §7.3, D1159).
#[derive(clap::Args)]
struct CounterexampleArgs {
    /// Also search every theorem's statement for a counterexample, its
    /// proof checked or not, and print each one found, then how many
    /// theorems were found false, had none found (evidence, not a proof),
    /// gave up, or were out of scope. A counterexample to a theorem that
    /// checked means something is wrong: an axiom, the compiler, or the
    /// search
    #[arg(long)]
    counterexamples: bool,
    /// With --counterexamples, print a line for every theorem searched,
    /// not only those found false
    #[arg(long, requires = "counterexamples")]
    verbose: bool,
    /// With --counterexamples, the time each theorem's search may take, as
    /// `500ms` or `2s` (default 500ms)
    #[arg(
        long,
        value_name = "TIME",
        value_parser = parse_millis,
        requires = "counterexamples"
    )]
    counterexample_budget: Option<u64>,
}

/// Milliseconds from `500ms`, `2s` or `1.5s`.
fn parse_millis(text: &str) -> Result<u64, String> {
    let bad = || format!("`{text}` isn't a time: write it as `500ms` or `2s`");
    let (number, scale) = if let Some(ms) = text.strip_suffix("ms") {
        (ms, 1.0)
    } else if let Some(s) = text.strip_suffix('s') {
        (s, 1000.0)
    } else {
        return Err(bad());
    };
    let value: f64 = number.trim().parse().map_err(|_| bad())?;
    if !value.is_finite() || value <= 0.0 {
        return Err(bad());
    }
    Ok((value * scale).round().max(1.0) as u64)
}

/// The caches: checked library files and project namespaces
/// (docs/proposals/check-cache.md) and,
/// for `test`, test results.
#[derive(clap::Args)]
struct CacheArgs {
    /// Don't read or write the caches: check everything (and for `test`,
    /// run every test)
    #[arg(long)]
    no_cache: bool,
    /// Where to keep the caches (default: `.stitchwort/cache` in the
    /// project folder, or in this folder for a file)
    #[arg(long)]
    cache_dir: Option<PathBuf>,
}

/// The compiler runs on a thread with this much stack, so that deep programs
/// have room before they run into their resource limits.
const STACK: usize = 64 * 1024 * 1024;

/// Checking builds and frees terms and values by the million; with the
/// system allocator (on macOS at least) allocating and freeing was about a
/// quarter of a `check`. mimalloc makes `check` of the AoC project retire
/// about 28% fewer instructions (docs/proposals/proof-check-speed.md).
#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// Rust ignores `SIGPIPE`, so `println!` into a closed pipe
/// (`stitchwort std-source … | head`) panics. That is the reader leaving, not
/// a fault: exit quietly, with the status a shell shows for a process ended by
/// `SIGPIPE`.
fn exit_quietly_on_broken_pipe() {
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let message = (info.payload().downcast_ref::<String>().map(String::as_str))
            .or_else(|| info.payload().downcast_ref::<&str>().copied())
            .unwrap_or("");
        if message.starts_with("failed printing to std") && message.contains("Broken pipe") {
            std::process::exit(141);
        }
        previous(info);
    }));
}

fn main() -> ExitCode {
    exit_quietly_on_broken_pipe();
    let cli = Cli::parse();
    if let Some(dir) = &cli.std_dir
        && let Err(e) = stitchwort_elab::use_std_dir(dir)
    {
        eprintln!("error: {e}");
        return ExitCode::FAILURE;
    }
    // A program run natively may switch the terminal to keys mode: the
    // signals that would end it are caught first, before any thread starts,
    // so that the terminal is put back (docs/proposals/terminal-io.md §5).
    #[cfg(unix)]
    if matches!(cli.command, Command::Run { js: false, .. }) {
        stitchwort_host::terminal::catch_signals();
    }
    // Under Node the terminal is Node's to put back: wait for it.
    #[cfg(unix)]
    if matches!(cli.command, Command::Run { js: true, .. }) {
        stitchwort_cli::node_wait::wait_for_node();
    }
    // `run --native` runs native code on this thread, whose stack is then
    // the safety margin behind the frame limit (native-compilation.md §4.3).
    let stack = match &cli.command {
        Command::Run { native: true, .. } => stitchwort_host::NATIVE_STACK,
        _ => STACK,
    };
    stitchwort_host::with_stack(stack, move || {
        stitchwort_elab::timings::start();
        let code = run(cli);
        stitchwort_elab::timings::report();
        code
    })
}

fn run(cli: Cli) -> ExitCode {
    match cli.command {
        Command::Check {
            targets,
            project,
            index,
            counterexamples,
            cache,
        } => check(
            &targets,
            project.as_deref(),
            index.as_deref(),
            &counterexamples,
            &cache,
        ),
        Command::StdSource { path } => match stitchwort_cli::nav::std_source(&path, STACK) {
            Some(text) => {
                print!("{text}");
                ExitCode::SUCCESS
            }
            None => {
                eprintln!("error: there's no standard library file `{path}`");
                ExitCode::FAILURE
            }
        },
        Command::Test {
            target,
            cache,
            project,
            reference,
        } => test(target.as_deref(), &cache, project.as_deref(), reference),
        Command::Run {
            target,
            js,
            reference,
            native,
            verbose,
            project,
            alloc_trace,
            cache,
        } => run_target(
            &target,
            js,
            reference,
            native.then_some(verbose),
            alloc_trace.as_deref(),
            project.as_deref(),
            &cache,
        ),
        Command::Axioms {
            target,
            name,
            project,
            cache,
        } => axioms(&target, name.as_deref(), project.as_deref(), &cache),
        Command::Dev(DevCommand::OpcodeCensus {
            target,
            functions,
            project,
            cache,
        }) => opcode_census(&target, functions, project.as_deref(), &cache),
        Command::Fmt {
            files,
            check,
            project,
        } => fmt_command(&files, check, project.as_deref()),
        Command::Eval { file, expr, cache } => eval(&file, &expr, &cache),
        Command::Repl { file } => repl(file.as_deref()),
        Command::Lsp => {
            match stitchwort_cli::lsp::run_stdio(stitchwort_cli::lsp::Options::new(STACK)) {
                Ok(()) => ExitCode::SUCCESS,
                Err(e) => {
                    eprintln!("error: {e}");
                    ExitCode::FAILURE
                }
            }
        }
        Command::Build {
            target,
            out,
            source_map,
            project,
            cache,
            ..
        } => build(&target, &out, source_map, project.as_deref(), &cache),
        Command::Dev(DevCommand::NativeSpike { rounds, memory }) => {
            native_spike(rounds, memory.as_deref())
        }
    }
}

#[cfg(feature = "native")]
fn native_spike(rounds: u64, memory: Option<&str>) -> ExitCode {
    let memory = match memory.map(str::parse).transpose() {
        Ok(memory) => memory.unwrap_or_default(),
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };
    match stitchwort_native::checks::report(memory, rounds) {
        Ok(report) => {
            print!("{report}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(not(feature = "native"))]
fn native_spike(_rounds: u64, _memory: Option<&str>) -> ExitCode {
    eprintln!(
        "error: this `stitchwort` was built without native code; build it with `--features native`"
    );
    ExitCode::FAILURE
}

/// A target is a file if it ends in `.sw` or has a `/`; otherwise it's a
/// name in the project.
fn is_file_target(target: &str) -> bool {
    target.ends_with(".sw") || target.contains('/')
}

fn exit(ok: bool) -> ExitCode {
    if ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

// ---- Goals -------------------------------------------------------------

/// How many open goals (`?`) are among `reported`.
fn goals_open(reported: &[Diagnostic]) -> usize {
    reported
        .iter()
        .filter(|d| d.severity == Severity::Goal)
        .count()
}

/// "2 goals open", after the goals themselves, if there are any
/// (docs/proposals/lsp-goal-holes.md, D636): a declaration with one isn't
/// finished, and nor is anything that uses it, so none of them is checked.
fn report_goals(goals: usize) {
    if goals > 0 {
        let s = if goals == 1 { "" } else { "s" };
        eprintln!(
            "{goals} goal{s} open: the declarations with them, and what uses them, aren't \
             finished, so they aren't checked"
        );
    }
}

// ---- Projects ----------------------------------------------------------

struct Project {
    dir: PathBuf,
    /// The project folder's name, for messages.
    name: String,
    files: DiskFiles,
}

/// The project folder's name: its last component, as the filesystem has it.
fn project_name(dir: &Path) -> String {
    dir.canonicalize()
        .ok()
        .as_deref()
        .and_then(Path::file_name)
        .or_else(|| dir.file_name())
        .map_or("project".to_string(), |n| n.to_string_lossy().to_string())
}

/// The project for a command: the `--project` folder, or the nearest one
/// at or above the current folder. `command` is what the note suggests for
/// a single file (`check a single file`, `stitchwort check hello.sw`).
fn locate_project(flag: Option<&Path>, what: &str, example: &str) -> Option<Project> {
    let dir = match flag {
        Some(dir) => {
            if !dir.join("stitchwort.yaml").is_file() {
                eprintln!("error: there's no stitchwort.yaml in {}", dir.display());
                return None;
            }
            dir.to_path_buf()
        }
        None => {
            let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
            let Some(dir) = find_project(&cwd) else {
                eprintln!(
                    "error: there's no stitchwort.yaml in {} or any folder above it",
                    cwd.display()
                );
                eprintln!(
                    "  note: to {what} a single file, pass its path, as in `stitchwort {example}`"
                );
                return None;
            };
            dir
        }
    };
    Some(Project {
        name: project_name(&dir),
        files: DiskFiles { root: dir.clone() },
        dir,
    })
}

/// Loads the namespaces `target` needs; reports what's wrong, or the
/// warnings.
fn load_project(session: &mut Session, project: &Project, target: &Target) -> bool {
    load_project_into(session, project, target, &mut Vec::new())
}

/// [`load_project`], also keeping what it reported in `reported`.
fn load_project_into(
    session: &mut Session,
    project: &Project,
    target: &Target,
    reported: &mut Vec<Diagnostic>,
) -> bool {
    load_project_counting(session, project, target, reported).is_some()
}

/// [`load_project_into`], giving the number of namespaces checked.
fn load_project_counting(
    session: &mut Session,
    project: &Project,
    target: &Target,
    reported: &mut Vec<Diagnostic>,
) -> Option<usize> {
    match session.load_project(&project.files, &project.name, target) {
        Ok(loaded) => {
            reported.extend(std::mem::take(&mut session.warnings));
            report(&session.sources, reported);
            Some(loaded.checked.len())
        }
        Err(diagnostics) => {
            report(&session.sources, &diagnostics);
            reported.extend(diagnostics);
            None
        }
    }
}

// ---- Files -------------------------------------------------------------

/// If `path` is in a project, what `E-FILE-MODE` needs to say why the file
/// can't use it: the project's namespaces, found by reading only its
/// configuration and the namespace line of each file (anything that can't
/// be read is ignored). `verb` is "run", "checked", "tested" or "built".
fn file_mode_context(path: &Path, text: &str, verb: &'static str) -> Option<FileModeContext> {
    let absolute = std::path::absolute(path).ok()?;
    let dir = find_project(absolute.parent()?)?;
    let name = project_name(&dir);
    let mut sources = SourceMap::new();
    let found = project_sources(&DiskFiles { root: dir }, &name, &mut sources).ok()?;
    let mut namespaces = BTreeSet::new();
    for (file, text) in &found {
        let id = sources.add(file.clone(), text.clone());
        if let Ok(Some(line)) = parse_namespace_line(id, text) {
            namespaces.insert(line.path.text);
        }
    }
    if namespaces.is_empty() {
        return None;
    }
    let id = sources.add("<file>", text);
    let own = parse_namespace_line(id, text).ok().flatten();
    let note = match (&own, verb) {
        (Some(n), "run") => format!(
            "to use the project, run a function by name: `stitchwort run {}.main`",
            n.path.text
        ),
        (Some(n), "checked") => format!(
            "to use the project, check the namespace: `stitchwort check {}`",
            n.path.text
        ),
        (Some(n), "tested") => format!(
            "to use the project, test the namespace: `stitchwort test {}`",
            n.path.text
        ),
        (Some(n), _) => format!(
            "to use the project, build the namespace: `stitchwort build --js {}`",
            n.path.text
        ),
        (None, _) => "to use the project, start the file with `namespace Name` and use the name, as in `stitchwort run Name.main`".to_string(),
    };
    Some(FileModeContext {
        file: path.display().to_string(),
        own: own.as_ref().map(|n| n.path.text.clone()),
        verb,
        project: name,
        namespaces,
        note,
    })
}

fn load(session: &mut Session, path: &Path) -> bool {
    load_file(session, path, None)
}

/// Loads a file on its own. With a `verb`, a file inside a project that
/// uses the project is told why it can't.
fn load_file(session: &mut Session, path: &Path, verb: Option<&'static str>) -> bool {
    load_file_into(session, path, verb, &mut Vec::new())
}

/// [`load_file`], also keeping what it reported in `reported`.
fn load_file_into(
    session: &mut Session,
    path: &Path,
    verb: Option<&'static str>,
    reported: &mut Vec<Diagnostic>,
) -> bool {
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(err) => {
            eprintln!("error: can't read {}: {err}", path.display());
            return false;
        }
    };
    let context = verb.and_then(|verb| file_mode_context(path, &text, verb));
    let folder = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
        session.include_in_folder(
            std::rc::Rc::new(DiskFiles {
                root: folder.to_path_buf(),
            }),
            name,
        );
    }
    match session.load_file(&path.display().to_string(), &text, context) {
        Ok(_) => {
            reported.extend(std::mem::take(&mut session.warnings));
            report(&session.sources, reported);
            true
        }
        Err(diagnostics) => {
            report(&session.sources, &diagnostics);
            reported.extend(diagnostics);
            false
        }
    }
}

/// Writes the navigation index of `session` to `index` (`-` is standard
/// output).
fn write_index(
    session: &Session,
    ok: bool,
    index: &str,
    root: &str,
    diagnostics: &[Diagnostic],
) -> bool {
    let json = stitchwort_cli::nav::index_json(session, !ok, None, root, diagnostics);
    if index == "-" {
        println!("{json}");
        return true;
    }
    match std::fs::write(index, json) {
        Ok(()) => true,
        Err(err) => {
            eprintln!("error: can't write {index}: {err}");
            false
        }
    }
}

fn check(
    targets: &[String],
    project: Option<&Path>,
    index: Option<&str>,
    counterexamples: &CounterexampleArgs,
    cache: &CacheArgs,
) -> ExitCode {
    let files = targets.iter().filter(|t| is_file_target(t)).count();
    if files > 0 && files < targets.len() {
        eprintln!("error: give either files or names in the project, not both");
        return ExitCode::FAILURE;
    }
    if files > 1 && index.is_some() {
        eprintln!("error: --index takes one file, or namespaces of the project");
        return ExitCode::FAILURE;
    }
    if files > 0 {
        let mut ok = true;
        for path in targets {
            // Each file gets its own session.
            let mut session = new_session(index.is_some());
            use_cache(&mut session, cache, Path::new("."));
            let mut reported = Vec::new();
            let loaded = load_file_into(
                &mut session,
                Path::new(path),
                Some("checked"),
                &mut reported,
            );
            let goals = goals_open(&reported);
            report_goals(goals);
            ok &= loaded && goals == 0;
            if loaded && goals == 0 {
                eprintln!("checked {path}");
            }
            if let Some(index) = index {
                ok = write_index(&session, loaded, index, "", &reported) && ok;
            }
            if counterexamples.counterexamples {
                ok = search_counterexamples(&mut session, counterexamples, &|_| true) && ok;
            }
            discard(session);
        }
        return exit(ok);
    }
    let Some(project) = locate_project(project, "check", "check hello.sw") else {
        return ExitCode::FAILURE;
    };
    let target = if targets.is_empty() {
        Target::Everything
    } else {
        Target::Namespaces(targets.to_vec())
    };
    let mut session = new_session(index.is_some());
    use_cache(&mut session, cache, &project.dir);
    let mut reported = Vec::new();
    let checked = load_project_counting(&mut session, &project, &target, &mut reported);
    let goals = goals_open(&reported);
    report_goals(goals);
    let mut ok = checked.is_some() && goals == 0;
    if let (true, Some(count)) = (ok, checked) {
        let plural = if count == 1 { "" } else { "s" };
        eprintln!("checked {count} namespace{plural} of {}", project.name);
    }
    if let Some(index) = index {
        let root = format!("{}/", project.name);
        ok = write_index(&session, ok, index, &root, &reported) && ok;
    }
    if counterexamples.counterexamples {
        // The theorems of the namespaces named, and those under them.
        let keep = |path: &str| {
            targets.is_empty()
                || targets.iter().any(|t| {
                    path.strip_prefix(t.as_str())
                        .is_some_and(|rest| rest.starts_with('.'))
                })
        };
        ok = search_counterexamples(&mut session, counterexamples, &keep) && ok;
    }
    discard(session);
    exit(ok)
}

/// `check --counterexamples` (D1159, docs/proposals/counterexample-search.md
/// §7.3, §9.3): searches the statement of every theorem `keep` keeps, and
/// prints each counterexample (with `--verbose`, a line for every theorem)
/// and a summary. `false` if a counterexample was found.
fn search_counterexamples(
    session: &mut Session,
    args: &CounterexampleArgs,
    keep: &dyn Fn(&str) -> bool,
) -> bool {
    use stitchwort_cli::counterexample::Verdict;
    use stitchwort_elab::counterexample::{Budget, ON_REQUEST};
    let budget = Budget {
        millis: args.counterexample_budget.unwrap_or(ON_REQUEST.millis),
        ..ON_REQUEST
    };
    let searches = session.search_theorems(budget, keep);
    let verdicts: Vec<_> = searches.iter().map(|s| s.verdict()).collect();
    let shown = |verdict: Verdict| args.verbose || verdict == Verdict::False;
    let width = searches
        .iter()
        .zip(&verdicts)
        .filter(|(_, (v, _))| shown(*v))
        .map(|(s, _)| s.name.len())
        .max()
        .unwrap_or(0);
    let mut counts = [0usize; 5];
    for (search, (verdict, line)) in searches.iter().zip(verdicts) {
        counts[verdict as usize] += 1;
        if !shown(verdict) {
            continue;
        }
        let mark = match verdict {
            Verdict::False => "✗",
            Verdict::NoneFound => "~",
            _ => "-",
        };
        println!("  {mark} {:width$}  {line}", search.name);
        // On a theorem that checked, a counterexample means something is
        // wrong (§7.3): say what.
        if search.checked
            && let Some(note) = &search.note
        {
            println!(
                "      this theorem checked, so an axiom it uses, the compiler or the search is \
                 wrong; please report it:"
            );
            for line in note.lines() {
                println!("      {line}");
            }
        }
    }
    let total = searches.len();
    let [false_, none, gave_up, inconclusive, not_applicable] = counts;
    eprintln!(
        "searched {total} theorem{} for counterexamples: {false_} false, {none} with none found, \
         {gave_up} gave up, {inconclusive} inconclusive, {not_applicable} not applicable",
        if total == 1 { "" } else { "s" }
    );
    false_ == 0
}

/// Ends with a session that's no longer needed without freeing it: the
/// process is about to exit, which frees everything at once, and taking a
/// checked project's terms and values apart one by one took about 2% of a
/// `check` (docs/proposals/proof-check-speed.md). Nothing in a session
/// needs dropping to be written out (the caches are written as they go).
fn discard(session: Session) {
    std::mem::forget(session);
}

/// The cache directory to use, if any: `--cache-dir` as given, or
/// `.stitchwort/cache` in `base`, making `.stitchwort/` (with a
/// `.gitignore` that ignores it all) if there isn't one yet.
fn cache_dir(cache: &CacheArgs, base: &Path) -> Option<PathBuf> {
    if cache.no_cache {
        return None;
    }
    if let Some(dir) = &cache.cache_dir {
        return Some(dir.clone());
    }
    let stitchwort = base.join(".stitchwort");
    if !stitchwort.exists() && std::fs::create_dir_all(&stitchwort).is_ok() {
        let _ = std::fs::write(stitchwort.join(".gitignore"), "*\n");
    }
    Some(stitchwort.join("cache"))
}

/// Loads library files and project namespaces through the check cache,
/// unless `--no-cache`.
fn use_cache(session: &mut Session, cache: &CacheArgs, base: &Path) {
    if let Some(dir) = cache_dir(cache, base) {
        session.use_check_cache(&dir);
    }
}

/// The test results' cache.
fn test_cache(cache: &CacheArgs, base: &Path) -> Cache {
    cache_dir(cache, base).map_or_else(Cache::disabled, Cache::at)
}

fn test(
    target: Option<&str>,
    cache: &CacheArgs,
    project: Option<&Path>,
    reference: bool,
) -> ExitCode {
    let mut session = new_session(false);
    let run_tests = |session: &Session, cache: &Cache| {
        if reference {
            session.run_tests(cache)
        } else {
            session.run_tests_fast(cache)
        }
    };
    match target {
        Some(file) if is_file_target(file) => {
            use_cache(&mut session, cache, Path::new("."));
            let mut reported = Vec::new();
            if !load_file_into(&mut session, Path::new(file), Some("tested"), &mut reported) {
                return ExitCode::FAILURE;
            }
            let cache = test_cache(cache, Path::new("."));
            let code = print_tests(&run_tests(&session, &cache), false);
            discard(session);
            // The tests of unfinished declarations aren't checked, so they
            // didn't run.
            let goals = goals_open(&reported);
            report_goals(goals);
            if goals > 0 { ExitCode::FAILURE } else { code }
        }
        _ => {
            let Some(project) = locate_project(project, "test", "test hello.sw") else {
                return ExitCode::FAILURE;
            };
            let target_name = target;
            let target = match target {
                Some(name) => Target::Subtrees(vec![name.to_string()]),
                None => Target::Everything,
            };
            use_cache(&mut session, cache, &project.dir);
            let mut reported = Vec::new();
            if !load_project_into(&mut session, &project, &target, &mut reported) {
                return ExitCode::FAILURE;
            }
            let cache = test_cache(cache, &project.dir);
            let results = run_tests(&session, &cache);
            let code = print_tests(&results, true);
            discard(session);
            // A target that matched no tests (a typo, a namespace without
            // any) must never look like a pass.
            let none = match target_name {
                Some(name) if results.is_empty() => {
                    eprintln!("warning: no tests matched '{name}'");
                    true
                }
                _ => false,
            };
            let goals = goals_open(&reported);
            report_goals(goals);
            if goals > 0 || none {
                ExitCode::FAILURE
            } else {
                code
            }
        }
    }
}

/// Prints the results, with each namespace's name above its tests if
/// `grouped`.
fn print_tests(results: &[TestResult], grouped: bool) -> ExitCode {
    let width = results.iter().map(|r| r.name.len()).max().unwrap_or(0);
    let mut namespace: Option<&str> = None;
    for result in results {
        if grouped && namespace != Some(result.namespace.as_str()) {
            namespace = Some(result.namespace.as_str());
            println!("{}", result.namespace);
        }
        let (mark, why) = match result.outcome {
            Outcome::Passed => ("✓", String::new()),
            Outcome::Failed => (
                "✗",
                match result.detail.as_ref().and_then(|d| d.comparison.as_ref()) {
                    Some(c) => format!("  (`{}` is False)", c.op),
                    None => "  (evaluated to False)".to_string(),
                },
            ),
            Outcome::OutOfResources(e) => ("!", format!("  (no result: {e})")),
        };
        let how = if result.cached { "cached" } else { "ran" };
        println!("  {mark} {:width$}  {how}{why}", result.name);
        if let Some(detail) = &result.detail {
            if let Some(c) = &detail.comparison {
                println!("      left:  {}", c.left);
                println!("      right: {}", c.right);
                if let Some(difference) = &c.difference {
                    println!("      {}", difference.replace('\n', "\n      "));
                }
            }
            if let Some(p) = &detail.part {
                println!("      in: {}  ({}:{}:{})", p.text, p.file, p.line, p.column);
            }
        }
    }
    let count = |f: fn(&Outcome) -> bool| results.iter().filter(|r| f(&r.outcome)).count();
    let passed = count(|o| *o == Outcome::Passed);
    let failed = count(|o| *o == Outcome::Failed);
    let unfinished = count(|o| matches!(o, Outcome::OutOfResources(_)));
    let cached = results.iter().filter(|r| r.cached).count();
    let unfinished_note = if unfinished > 0 {
        format!(", {unfinished} ran out of resources")
    } else {
        String::new()
    };
    println!(
        "{} test(s): {passed} passed, {failed} failed{unfinished_note} ({cached} from the cache)",
        results.len(),
    );
    exit(passed == results.len())
}

/// Loads `target` (a file, or the full name of a function in the project)
/// and finds its `main`: where `run` and the dev commands start.
fn load_main(
    target: &str,
    project: Option<&Path>,
    cache: &CacheArgs,
) -> Result<(Session, Main), ExitCode> {
    let mut session = new_session(false);
    let main = if is_file_target(target) {
        use_cache(&mut session, cache, Path::new("."));
        let mut reported = Vec::new();
        if !load_file_into(&mut session, Path::new(target), Some("run"), &mut reported) {
            return Err(ExitCode::FAILURE);
        }
        // What's finished can run; `main` can't if it isn't (`Session::main`).
        report_goals(goals_open(&reported));
        session.main()
    } else {
        let Some(project) = locate_project(project, "run", "run hello.sw") else {
            return Err(ExitCode::FAILURE);
        };
        use_cache(&mut session, cache, &project.dir);
        session.include_from(std::rc::Rc::new(DiskFiles {
            root: project.dir.clone(),
        }));
        let sources = match project_sources(&project.files, &project.name, &mut session.sources) {
            Ok(sources) => sources,
            Err(diagnostics) => {
                report(&session.sources, &diagnostics);
                return Err(ExitCode::FAILURE);
            }
        };
        let analysis = analyse(&mut session, &project.name, sources);
        if !analysis.diagnostics.is_empty() {
            report(&session.sources, &analysis.diagnostics);
            return Err(ExitCode::FAILURE);
        }
        let Some(namespace) = namespace_of(&analysis, target).map(str::to_string) else {
            let d = run_unknown_namespace(&project.name, target, &analysis);
            report(&session.sources, &[d]);
            return Err(ExitCode::FAILURE);
        };
        match session.load_analysis(
            &project.name,
            analysis,
            &Target::Namespaces(vec![namespace]),
        ) {
            Ok(_) => {
                let reported = std::mem::take(&mut session.warnings);
                report(&session.sources, &reported);
                report_goals(goals_open(&reported));
            }
            Err(diagnostics) => {
                report(&session.sources, &diagnostics);
                return Err(ExitCode::FAILURE);
            }
        }
        session.main_named(target, &project.name)
    };
    let main = match main {
        Ok(main) => main,
        Err(diagnostic) => {
            report(&session.sources, &[diagnostic]);
            return Err(ExitCode::FAILURE);
        }
    };
    Ok((session, main))
}

/// `run`: a file's `main`, or a function of the project by its full name.
fn run_target(
    target: &str,
    js: bool,
    reference: bool,
    native: Option<bool>,
    alloc_trace: Option<&Path>,
    project: Option<&Path>,
    cache: &CacheArgs,
) -> ExitCode {
    #[cfg(not(feature = "alloc-trace"))]
    if alloc_trace.is_some() {
        eprintln!(
            "error: this build has no allocation trace (build with `--features alloc-trace`)"
        );
        return ExitCode::FAILURE;
    }
    #[cfg(not(feature = "native"))]
    if native.is_some() {
        eprintln!(
            "error: this `stitchwort` was built without native code; build it with `--features native`"
        );
        return ExitCode::FAILURE;
    }
    let runner = match native {
        Some(verbose) => Runner::Native {
            verbose,
            trace: alloc_trace.is_some(),
        },
        None if reference => Runner::Reference,
        None => Runner::Machine,
    };
    let (mut session, main) = match load_main(target, project, cache) {
        Ok(loaded) => loaded,
        Err(code) => return code,
    };
    if js {
        run_main_js(&mut session, main)
    } else {
        #[cfg(feature = "alloc-trace")]
        if let Some(path) = alloc_trace {
            // Native code's layout probe makes values: kept out of the trace.
            if native.is_some() {
                let _ = stitchwort_rt::native_abi::probe_layout();
            }
            stitchwort_rt::alloc_trace::start();
            let code = run_main(&mut session, &main, runner);
            let trace = stitchwort_rt::alloc_trace::finish();
            if let Err(err) = std::fs::write(path, trace.render()) {
                eprintln!("error: can't write {}: {err}", path.display());
                return ExitCode::FAILURE;
            }
            return code;
        }
        let _ = alloc_trace;
        run_main(&mut session, &main, runner)
    }
}

/// `dev opcode-census`: lowers and compiles `target`'s `main` as `run` does
/// and reports which instructions its reachable code uses and whether that
/// code fits the N1 subset of native compilation.
fn opcode_census(
    target: &str,
    functions: bool,
    project: Option<&Path>,
    cache: &CacheArgs,
) -> ExitCode {
    let (session, main) = match load_main(target, project, cache) {
        Ok(loaded) => loaded,
        Err(code) => return code,
    };
    let program = match session.lower_fast(&main) {
        Ok(program) => program,
        Err(err) => {
            eprintln!("error: can't lower `{target}`: {err:?}");
            return ExitCode::FAILURE;
        }
    };
    let image = stitchwort_rt::code::compile(&program);
    let census = stitchwort_rt::census::census_image(&program, &image);
    print!("{}", render_census(target, &census, functions));
    let fitting = stitchwort_rt::census::fitting_islands(&image, &census);
    println!(
        "bodies whose own island fits: {} of {} reachable",
        fitting.len(),
        census.bodies.len()
    );
    for (name, size) in fitting.iter().take(5) {
        println!("  {name}: island of {size}");
    }
    println!("adding to N1, greedily (family: bodies whose island fits, then; entry fits):");
    for (family, n, entry_fits) in stitchwort_rt::census::greedy_additions(&image, &census) {
        println!(
            "  +{family}: {n}{}",
            if entry_fits { " entry-fits" } else { "" }
        );
    }
    let callees = stitchwort_rt::census::callee_censuses(&program, &image);
    let fitting = callees.iter().filter(|c| c.fits_n1()).count();
    let verdict = if fitting == callees.len() {
        "FITS"
    } else {
        "BLOCKED"
    };
    println!(
        "callee islands: {verdict} {target} fit={fitting} of={}",
        callees.len()
    );
    for callee in &callees {
        let name = &callee.bodies[0].name;
        let status = if callee.fits_n1() { "fits" } else { "BLOCKED" };
        let blockers: Vec<String> = callee
            .blockers()
            .into_iter()
            .map(|(key, (n, bodies))| format!("{key}={n}/{bodies}"))
            .collect();
        println!(
            "  [{status}] {name}: reachable={} {}",
            callee.bodies.len(),
            blockers.join(" ")
        );
    }
    ExitCode::SUCCESS
}

/// The census as text. The first line is machine-readable:
/// `island: FITS|BLOCKED`, then the counts.
fn render_census(target: &str, census: &stitchwort_rt::census::Census, functions: bool) -> String {
    use std::fmt::Write as _;
    let mut out = String::new();
    let blockers = census.blockers();
    let verdict = if census.fits_n1() { "FITS" } else { "BLOCKED" };
    let blocked_bodies = census
        .bodies
        .iter()
        .filter(|b| !b.blockers.is_empty())
        .count();
    let _ = writeln!(
        out,
        "island: {verdict} {target} reachable_bodies={} blocked_bodies={blocked_bodies} image_bodies={}",
        census.bodies.len(),
        census.image_bodies
    );
    if let Some(only) = census.sole_blocker() {
        let _ = writeln!(
            out,
            "sole blocker (adding it alone makes the island fit): {only}"
        );
    }
    let mut ranked: Vec<_> = blockers.iter().collect();
    ranked.sort_by_key(|(key, (n, bodies))| {
        (
            std::cmp::Reverse(*bodies),
            std::cmp::Reverse(*n),
            (*key).clone(),
        )
    });
    if !ranked.is_empty() {
        let _ = writeln!(out, "blockers (instruction: occurrences, bodies):");
        for (key, (n, bodies)) in ranked {
            let _ = writeln!(out, "  {key}: {n}, {bodies}");
        }
    }
    let mut families: Vec<_> = census.family_blockers().into_iter().collect();
    families.sort_by_key(|(key, (n, bodies))| {
        (
            std::cmp::Reverse(*bodies),
            std::cmp::Reverse(*n),
            key.clone(),
        )
    });
    if !families.is_empty() {
        let _ = writeln!(out, "blocker families (family: occurrences, bodies):");
        for (key, (n, bodies)) in families {
            let _ = writeln!(out, "  {key}: {n}, {bodies}");
        }
    }
    let _ = writeln!(out, "instructions reached (kind: occurrences, bodies):");
    let mut totals: Vec<_> = census.instr_totals().into_iter().collect();
    totals.sort_by_key(|(name, (n, _))| (std::cmp::Reverse(*n), *name));
    for (name, (n, bodies)) in totals {
        let _ = writeln!(out, "  {name}: {n}, {bodies}");
    }
    if functions {
        let _ = writeln!(out, "bodies:");
        for body in &census.bodies {
            let status = if body.blockers.is_empty() {
                "ok"
            } else {
                "BLOCKED"
            };
            let used: Vec<String> = body
                .instrs
                .iter()
                .map(|(k, n)| format!("{k}={n}"))
                .collect();
            let _ = writeln!(out, "  [{status}] {}: {}", body.name, used.join(" "));
            for (key, n) in &body.blockers {
                let _ = writeln!(out, "      blocked by {key} x{n}");
            }
        }
    }
    out
}

/// `axioms`: loads the file or project, finds the definition and prints
/// the axioms it depends on (`stitchwort_driver::axioms`).
fn axioms(target: &str, name: Option<&str>, project: Option<&Path>, cache: &CacheArgs) -> ExitCode {
    let mut session = new_session(false);
    let key = if is_file_target(target) {
        let Some(name) = name else {
            eprintln!("error: name the definition to report on: `stitchwort axioms {target} NAME`");
            return ExitCode::FAILURE;
        };
        use_cache(&mut session, cache, Path::new("."));
        if !load_file(&mut session, Path::new(target), None) {
            return ExitCode::FAILURE;
        }
        name
    } else {
        if name.is_some() {
            eprintln!("error: a name in the project takes no second argument");
            return ExitCode::FAILURE;
        }
        let Some(project) = locate_project(project, "report on", "axioms hello.sw NAME") else {
            return ExitCode::FAILURE;
        };
        use_cache(&mut session, cache, &project.dir);
        if !load_project(&mut session, &project, &Target::Everything) {
            return ExitCode::FAILURE;
        }
        target
    };
    session.elab.leave_namespace();
    let Some(id) = session.elab.lookup_def(key) else {
        eprintln!("error: there's no definition `{key}`");
        return ExitCode::FAILURE;
    };
    if session.elab.is_unfinished(id) {
        eprintln!(
            "error: `{key}` isn't finished: it, or something it uses, has an open goal (`?`), so \
             it isn't checked"
        );
        return ExitCode::FAILURE;
    }
    let found = stitchwort_driver::axioms::axioms(&session.elab.globals, id);
    for axiom in found {
        println!("{axiom}");
    }
    discard(session);
    ExitCode::SUCCESS
}

/// `fmt`: formats files or folders in place (`-` is standard input and
/// output), or with no files the project's sources.
fn fmt_command(files: &[PathBuf], check: bool, project: Option<&Path>) -> ExitCode {
    let mut paths = Vec::new();
    let mut stdin = false;
    if files.is_empty() {
        let Some(project) = locate_project(project, "format", "fmt hello.sw") else {
            return ExitCode::FAILURE;
        };
        let mut sources = SourceMap::new();
        match project_sources(&project.files, &project.name, &mut sources) {
            Ok(found) => {
                paths.extend(found.into_iter().map(|(path, _)| project.dir.join(path)));
            }
            Err(diagnostics) => {
                report(&sources, &diagnostics);
                return ExitCode::from(2);
            }
        }
    } else {
        for file in files {
            if file == Path::new("-") {
                stdin = true;
            } else if file.is_dir() {
                paths.extend(sw_files_in(file));
            } else {
                paths.push(file.clone());
            }
        }
    }

    let mut failure = false;
    let mut would_change = false;
    if stdin {
        let mut text = String::new();
        if let Err(err) = std::io::stdin().read_to_string(&mut text) {
            eprintln!("error: can't read standard input: {err}");
            return ExitCode::from(2);
        }
        let mut sources = SourceMap::new();
        let id = sources.add("-", text.clone());
        match stitchwort_fmt::format_in(id, &text) {
            Ok(formatted) => {
                // Always the whole text, changed or not: an editor replaces
                // its buffer with what this prints.
                let formatted = formatted.text;
                would_change |= formatted != text;
                if !check {
                    print!("{formatted}");
                }
            }
            Err(FmtError::Refused(diagnostics)) => {
                report(&sources, &diagnostics);
                failure = true;
            }
            Err(FmtError::Internal(message)) => {
                eprintln!("error: formatter bug in -: {message} (file left unchanged)");
                failure = true;
            }
        }
    }

    for path in &paths {
        failure |= !format_file(path, check, &mut would_change);
    }

    if failure {
        ExitCode::from(2)
    } else if check && would_change {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Every `.sw` file under `dir`, recursively, sorted by path.
fn sw_files_in(dir: &Path) -> Vec<PathBuf> {
    fn walk(dir: &Path, found: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(&path, found);
            } else if path.extension().is_some_and(|extension| extension == "sw") {
                found.push(path);
            }
        }
    }
    let mut found = Vec::new();
    walk(dir, &mut found);
    found.sort();
    found
}

/// Formats `path` in place, unless `check`; prints it if it changed. Returns
/// whether the file was formatted (or, with `check`, would be).
fn format_file(path: &Path, check: bool, would_change: &mut bool) -> bool {
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(err) => {
            eprintln!("error: can't read {}: {err}", path.display());
            return false;
        }
    };
    let mut sources = SourceMap::new();
    let id = sources.add(path.display().to_string(), text.clone());
    match stitchwort_fmt::format_in(id, &text) {
        Ok(formatted) => {
            let formatted = formatted.text;
            if formatted == text {
                return true;
            }
            *would_change = true;
            if !check && let Err(err) = std::fs::write(path, &formatted) {
                eprintln!("error: can't write {}: {err}", path.display());
                return false;
            }
            println!("{}", path.display());
            true
        }
        Err(FmtError::Refused(diagnostics)) => {
            report(&sources, &diagnostics);
            false
        }
        Err(FmtError::Internal(message)) => {
            eprintln!(
                "error: formatter bug in {}: {message} (file left unchanged)",
                path.display()
            );
            false
        }
    }
}

/// Which runner `run` uses for `main`.
#[derive(Clone, Copy)]
enum Runner {
    /// The machine of `stitchwort-rt`.
    Machine,
    /// The reference evaluator.
    Reference,
    /// The machine, with the functions `main` calls as native code where
    /// they compile; `verbose` says what happened on standard error, and
    /// `trace` counts references through the runtime for the allocation
    /// trace.
    #[cfg_attr(not(feature = "native"), allow(dead_code))]
    Native { verbose: bool, trace: bool },
}

fn run_main(session: &mut Session, main: &Main, runner: Runner) -> ExitCode {
    let mut input = std::io::stdin().lock();
    let mut output = std::io::BufWriter::new(std::io::stdout().lock());
    #[cfg(unix)]
    let (mut terminal, restore) = (
        stitchwort_host::terminal::UnixTerminal,
        stitchwort_host::terminal::Restore,
    );
    #[cfg(not(unix))]
    let (mut terminal, restore) = (stitchwort_cli::run::NoTerminal, ());
    let result = match runner {
        Runner::Reference => session.run_main_on(main, &mut input, &mut output, &mut terminal),
        Runner::Machine => session.run_main_fast_on(main, &mut input, &mut output, &mut terminal),
        Runner::Native { verbose, trace } => run_main_native(
            session,
            main,
            verbose,
            trace,
            &mut input,
            &mut output,
            &mut terminal,
        ),
    };
    // Out of keys mode before an error is shown, so it's on the normal
    // screen.
    drop(restore);
    match result {
        Ok(()) => ExitCode::SUCCESS,
        // `main` failed and nothing handled it (D1048): not a runtime error.
        Err(stitchwort_cli::run::RunError::Failed(msg)) => {
            eprintln!("error: {msg}");
            ExitCode::FAILURE
        }
        Err(err) => {
            report(&session.sources, &[err.diagnostic(main)]);
            ExitCode::from(2)
        }
    }
}

/// `run --native`: `main` on the machine, with the functions it calls
/// running as native code where their islands compile (stage N1 of
/// docs/proposals/native-compilation.md).
#[cfg(feature = "native")]
fn run_main_native(
    session: &Session,
    main: &Main,
    verbose: bool,
    trace: bool,
    input: &mut impl std::io::BufRead,
    output: &mut impl std::io::Write,
    terminal: &mut dyn stitchwort_cli::run::Terminal,
) -> Result<(), stitchwort_cli::run::RunError> {
    use std::cell::RefCell;
    use std::rc::Rc;
    let program = session.lower_fast(main)?;
    let notes = Rc::new(RefCell::new(Vec::new()));
    let options = stitchwort_native::n1::Options {
        trace_refcounts: trace,
        stack_size: Some(stitchwort_host::NATIVE_STACK),
    };
    let mut factory = stitchwort_native::n1::factory(options, notes.clone());
    let result = stitchwort_rt::run_main_native(
        &program,
        stitchwort_rt::Limits::from_core(session.elab.limits),
        &mut factory,
        input,
        output,
        terminal,
    );
    if verbose {
        for note in notes.borrow().iter() {
            eprintln!("{note}");
        }
    }
    result
}

#[cfg(not(feature = "native"))]
fn run_main_native(
    _session: &Session,
    _main: &Main,
    _verbose: bool,
    _trace: bool,
    _input: &mut impl std::io::BufRead,
    _output: &mut impl std::io::Write,
    _terminal: &mut dyn stitchwort_cli::run::Terminal,
) -> Result<(), stitchwort_cli::run::RunError> {
    unreachable!("`run --native` is refused without the `native` feature")
}

/// `run --js`: writes `main` and a runner as JavaScript to a temporary
/// directory and runs it with Node, which inherits standard input, output
/// and error.
fn run_main_js(session: &mut Session, main: Main) -> ExitCode {
    use stitchwort_js::run::{EXIT_FAIL, EXIT_IO, EXIT_RESOURCE};
    let program = match session.extract_program(&main) {
        Ok(program) => program,
        Err(diagnostic) => {
            report(&session.sources, &[diagnostic]);
            return ExitCode::FAILURE;
        }
    };
    let dir = TempDir::new();
    let launcher = dir.path.join("run.mjs");
    let error_file = dir.path.join("error.txt");
    let written = std::fs::create_dir_all(&dir.path)
        .and_then(|()| std::fs::write(dir.path.join("program.mjs"), &program.module))
        .and_then(|()| std::fs::write(&launcher, &program.launcher));
    if let Err(err) = written {
        eprintln!("error: can't write the JavaScript program: {err}");
        return ExitCode::FAILURE;
    }
    let status = match std::process::Command::new("node")
        .arg(&launcher)
        .arg(&error_file)
        .spawn()
        .and_then(|mut node| {
            #[cfg(unix)]
            stitchwort_cli::node_wait::set_node(node.id());
            node.wait()
        }) {
        Ok(status) => status,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            eprintln!(
                "error: `run --js` needs Node.js, but there's no `node` on the PATH (it's in the nix dev shell)"
            );
            return ExitCode::FAILURE;
        }
        Err(err) => {
            eprintln!("error: can't start `node`: {err}");
            return ExitCode::FAILURE;
        }
    };
    let message = || {
        std::fs::read_to_string(&error_file)
            .unwrap_or_default()
            .trim()
            .to_string()
    };
    match status.code() {
        Some(0) => ExitCode::SUCCESS,
        Some(EXIT_RESOURCE) => {
            let diagnostic = Diagnostic::error(
                "E-RESOURCE",
                format!("ran out of resources: {} (in Node.js)", message()),
            )
            .with_label(main.span, "while running this program")
            .with_note(
                "this isn't a type error or a failed test: there's no answer within the limits",
            );
            report(&session.sources, &[diagnostic]);
            ExitCode::from(2)
        }
        Some(EXIT_FAIL) => {
            let msg = std::fs::read_to_string(&error_file).unwrap_or_default();
            eprintln!("error: {msg}");
            ExitCode::FAILURE
        }
        Some(EXIT_IO) => {
            report(&session.sources, &[Diagnostic::error("E-IO", message())]);
            ExitCode::from(2)
        }
        // Node has reported what went wrong.
        Some(_) => ExitCode::from(2),
        // Ended by a signal (Ctrl-C, after putting the terminal back): the
        // status a shell expects, as for a native run.
        #[cfg(unix)]
        None if std::os::unix::process::ExitStatusExt::signal(&status).is_some() => {
            ExitCode::from(128u8.wrapping_add(
                std::os::unix::process::ExitStatusExt::signal(&status).unwrap_or(0) as u8,
            ))
        }
        None => {
            eprintln!("error: `node` was stopped by a signal ({status})");
            ExitCode::from(2)
        }
    }
}

/// A fresh temporary directory, removed when dropped, or the directory
/// `STITCHWORT_RUN_JS_DIR` names, kept.
struct TempDir {
    path: PathBuf,
    keep: bool,
}

impl TempDir {
    fn new() -> TempDir {
        // For looking at the generated program: it's written there, and kept.
        if let Some(dir) = std::env::var_os("STITCHWORT_RUN_JS_DIR") {
            return TempDir {
                path: dir.into(),
                keep: true,
            };
        }
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.subsec_nanos());
        TempDir {
            path: std::env::temp_dir()
                .join(format!("stitchwort-run-js-{}-{nanos}", std::process::id())),
            keep: false,
        }
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        if !self.keep {
            let _ = std::fs::remove_dir_all(&self.path);
        }
    }
}

fn eval(path: &Path, expr: &str, cache: &CacheArgs) -> ExitCode {
    let mut session = new_session(false);
    use_cache(&mut session, cache, Path::new("."));
    if !load(&mut session, path) {
        return ExitCode::FAILURE;
    }
    match evaluate(&mut session, expr, false) {
        Ok(output) => {
            println!("{output}");
            ExitCode::SUCCESS
        }
        Err(diagnostic) => {
            report(&session.sources, &[diagnostic]);
            ExitCode::FAILURE
        }
    }
}

/// Evaluates `expr`, or with `type_only`, shows its type.
fn evaluate(session: &mut Session, expr: &str, type_only: bool) -> Result<String, Diagnostic> {
    let expr = session.parse_expression("<input>", expr)?;
    if type_only {
        let (_, ty) = session.elab.infer_expr(&expr)?;
        return Ok(session.elab.show(&ty));
    }
    let (value, ty) = session.elab.eval_expr(&expr)?;
    Ok(format!("{value}: {ty}"))
}

fn repl(path: Option<&Path>) -> ExitCode {
    let mut session = new_session(false);
    if let Some(path) = path
        && !load(&mut session, path)
    {
        return ExitCode::FAILURE;
    }
    let mut editor = match rustyline::DefaultEditor::new() {
        Ok(editor) => editor,
        Err(err) => {
            eprintln!("error: can't start the REPL: {err}");
            return ExitCode::FAILURE;
        }
    };
    println!(
        "Stitchwort {}. Enter an expression to evaluate it, `import Std (List)` to use a namespace's names, `:t expr` for its type, `:q` to quit.",
        env!("CARGO_PKG_VERSION")
    );

    loop {
        let line = match editor.readline("sw> ") {
            Ok(line) => line,
            Err(ReadlineError::Interrupted | ReadlineError::Eof) => return ExitCode::SUCCESS,
            Err(err) => {
                eprintln!("error: {err}");
                return ExitCode::FAILURE;
            }
        };
        let input = line.trim();
        if input.is_empty() {
            continue;
        }
        let _ = editor.add_history_entry(input);
        if input == "import" || input.starts_with("import ") {
            // Imports accumulate over the session, as a file's do.
            let diagnostics = session.add_imports("<input>", input);
            if !diagnostics.is_empty() {
                report(&session.sources, &diagnostics);
            }
            continue;
        }
        let result = match input {
            ":q" | ":quit" => return ExitCode::SUCCESS,
            _ => match input.strip_prefix(":t ") {
                Some(expr) => evaluate(&mut session, expr, true),
                None => evaluate(&mut session, input, false),
            },
        };
        match result {
            Ok(output) => println!("{output}"),
            Err(diagnostic) => report(&session.sources, &[diagnostic]),
        }
    }
}

fn build(
    target: &str,
    out: &Path,
    source_map: bool,
    project: Option<&Path>,
    cache: &CacheArgs,
) -> ExitCode {
    if !is_file_target(target) {
        return build_namespace(target, out, source_map, project, cache);
    }
    let path = Path::new(target);
    let mut session = new_session(false);
    use_cache(&mut session, cache, Path::new("."));
    let mut reported = Vec::new();
    if !load_file_into(&mut session, path, Some("built"), &mut reported) {
        return ExitCode::FAILURE;
    }
    if refuse_goals(&reported) {
        return ExitCode::FAILURE;
    }
    let output = match session.extract() {
        Ok(output) => output,
        Err(diagnostic) => {
            report(&session.sources, &[diagnostic]);
            return ExitCode::FAILURE;
        }
    };
    let stem = path
        .file_stem()
        .map_or("out".into(), |s| s.to_string_lossy());
    let map = source_map.then_some(MapSources {
        sources: &session.sources,
        project: None,
    });
    write_output(out, &stem, output, map)
}

/// `build --js NAMESPACE`: the exports of one namespace of the project, in
/// `{NAMESPACE}.js` and `{NAMESPACE}.d.ts`.
fn build_namespace(
    namespace: &str,
    out: &Path,
    source_map: bool,
    project: Option<&Path>,
    cache: &CacheArgs,
) -> ExitCode {
    let Some(project) = locate_project(project, "build", "build --js hello.sw") else {
        return ExitCode::FAILURE;
    };
    let mut session = new_session(false);
    use_cache(&mut session, cache, &project.dir);
    let mut reported = Vec::new();
    if !load_project_into(
        &mut session,
        &project,
        &Target::Namespaces(vec![namespace.to_string()]),
        &mut reported,
    ) {
        return ExitCode::FAILURE;
    }
    if refuse_goals(&reported) {
        return ExitCode::FAILURE;
    }
    match session.extract_namespace(namespace) {
        Ok(output) => {
            let map = source_map.then_some(MapSources {
                sources: &session.sources,
                project: Some((&project.name, &project.dir)),
            });
            write_output(out, namespace, output, map)
        }
        Err(diagnostic) => {
            report(&session.sources, &[diagnostic]);
            ExitCode::FAILURE
        }
    }
}

/// `build` doesn't write JavaScript while goals are open: only checked code
/// is built (D636). Says so if there are any.
fn refuse_goals(reported: &[Diagnostic]) -> bool {
    let goals = goals_open(reported);
    if goals > 0 {
        let s = if goals == 1 { "" } else { "s" };
        eprintln!(
            "error: nothing was built: {goals} goal{s} open; fill in every `?` first, so that \
             everything built is checked"
        );
    }
    goals > 0
}

/// What a source map needs to name the `.sw` files: the sources, and for a
/// project build, the project's name and folder (its files are displayed as
/// `name/path`).
struct MapSources<'a> {
    sources: &'a SourceMap,
    project: Option<(&'a str, &'a Path)>,
}

/// Writes `{stem}.js` and `{stem}.d.ts` in `out`, and with `map`,
/// `{stem}.js.map` too, which the module refers to.
fn write_output(
    out: &Path,
    stem: &str,
    mut output: stitchwort_js::Output,
    map: Option<MapSources>,
) -> ExitCode {
    let js = out.join(format!("{stem}.js"));
    let dts = out.join(format!("{stem}.d.ts"));
    let map_file = out.join(format!("{stem}.js.map"));
    if let Some(map) = &map {
        let json = stitchwort_js::sourcemap::to_json(
            &format!("{stem}.js"),
            &output.mappings,
            map.sources,
            &|file| source_path(out, map.project, &file.name),
        );
        let written = std::fs::create_dir_all(out).and_then(|()| std::fs::write(&map_file, json));
        if let Err(err) = written {
            eprintln!("error: can't write output: {err}");
            return ExitCode::FAILURE;
        }
        output
            .js
            .push_str(&format!("//# sourceMappingURL={stem}.js.map\n"));
    }
    let written = std::fs::create_dir_all(out)
        .and_then(|()| std::fs::write(&js, output.js))
        .and_then(|()| std::fs::write(&dts, output.dts));
    match written {
        Ok(()) => {
            if map.is_some() {
                println!(
                    "wrote {}, {} and {}",
                    js.display(),
                    dts.display(),
                    map_file.display()
                );
            } else {
                println!("wrote {} and {}", js.display(), dts.display());
            }
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("error: can't write output: {err}");
            ExitCode::FAILURE
        }
    }
}

/// How a source map refers to the file the compiler calls `name`, and
/// whether the map holds its text: a file on disk by its path from `out`
/// (the text is there to read), and anything else (the embedded library) as
/// `stitchwort:{name}`, with its text.
fn source_path(out: &Path, project: Option<(&str, &Path)>, name: &str) -> (String, bool) {
    let on_disk = match project {
        Some((project, dir)) => name
            .strip_prefix(project)
            .and_then(|rest| rest.strip_prefix('/'))
            .map(|rest| dir.join(rest)),
        None => Some(PathBuf::from(name)),
    };
    let relative = on_disk
        .filter(|path| path.is_file())
        .and_then(|path| {
            Some((
                std::path::absolute(path).ok()?,
                std::path::absolute(out).ok()?,
            ))
        })
        .map(|(path, out)| relative_path(&out, &path));
    match relative {
        Some(path) => (path, false),
        None => (format!("stitchwort:{name}"), true),
    }
}

/// `path` from the folder `from`, written with `/`s. Both are absolute.
fn relative_path(from: &Path, path: &Path) -> String {
    let from: Vec<_> = from.components().collect();
    let path: Vec<_> = path.components().collect();
    let common = from.iter().zip(&path).take_while(|(a, b)| a == b).count();
    let mut parts: Vec<String> = vec!["..".into(); from.len() - common];
    parts.extend(
        path[common..]
            .iter()
            .map(|c| c.as_os_str().to_string_lossy().into_owned()),
    );
    parts.join("/")
}

fn report(sources: &SourceMap, diagnostics: &[Diagnostic]) {
    let color = std::io::stderr().is_terminal();
    for diagnostic in diagnostics {
        eprint!("{}", render(sources, diagnostic, color));
    }
}
