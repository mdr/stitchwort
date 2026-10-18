use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use rustyline::error::ReadlineError;
use stitchwort_cli::driver::{Cache, Outcome, Session};
use stitchwort_cli::render::render;
use stitchwort_syntax::{Diagnostic, SourceMap, Syntax};

#[derive(Parser)]
#[command(name = "stitchwort", version, about = "The Stitchwort language")]
struct Cli {
    #[command(subcommand)]
    command: Command,
    /// The declaration syntax the files are written in: `old` (signature
    /// lines and equations) or `new` (`def` headers). Also set by the
    /// `STITCHWORT_SYNTAX` environment variable
    #[arg(long, global = true, value_parser = ["old", "new"])]
    syntax: Option<String>,
}

/// The syntax chosen for this run, by `--syntax` or `STITCHWORT_SYNTAX`.
static SYNTAX: std::sync::OnceLock<Syntax> = std::sync::OnceLock::new();

/// A session for the compiler thread, reading the chosen syntax.
fn new_session() -> Session {
    let mut session = Session::for_stack(STACK);
    session.syntax = SYNTAX.get().copied().unwrap_or_default();
    session
}

#[derive(Subcommand)]
enum Command {
    /// Type-check source files
    Check {
        #[arg(required = true)]
        files: Vec<PathBuf>,
    },
    /// Run a file's tests, reusing cached results where nothing they depend on
    /// has changed
    Test {
        file: PathBuf,
        /// Run every test, ignoring (and not writing) cached results
        #[arg(long)]
        no_cache: bool,
        /// Where to keep cached results
        #[arg(long, default_value = ".stitchwort/cache")]
        cache_dir: PathBuf,
    },
    /// Type-check a file, then run its `main`, reading standard input and
    /// writing standard output
    Run { file: PathBuf },
    /// Evaluate an expression in the context of a file
    Eval { file: PathBuf, expr: String },
    /// Start an interactive session, optionally with a file loaded
    Repl { file: Option<PathBuf> },
    /// Extract a file's exports to JavaScript
    Build {
        file: PathBuf,
        /// Generate an ES module and TypeScript declarations
        #[arg(long, required = true)]
        js: bool,
        /// Output directory
        #[arg(short, long, default_value = ".")]
        out: PathBuf,
    },
}

/// The compiler runs on a thread with this much stack, so that deep programs
/// have room before they run into their resource limits.
const STACK: usize = 64 * 1024 * 1024;

fn main() -> ExitCode {
    let cli = Cli::parse();
    let name = cli
        .syntax
        .clone()
        .or_else(|| std::env::var("STITCHWORT_SYNTAX").ok());
    let syntax = match name.as_deref().map(Syntax::from_name) {
        None => Syntax::default(),
        Some(Some(syntax)) => syntax,
        Some(None) => {
            eprintln!("error: STITCHWORT_SYNTAX must be `old` or `new`");
            return ExitCode::FAILURE;
        }
    };
    SYNTAX.set(syntax).expect("set once");
    stitchwort_cli::driver::with_stack(STACK, move || run(cli))
}

fn run(cli: Cli) -> ExitCode {
    match cli.command {
        Command::Check { files } => check(&files),
        Command::Test {
            file,
            no_cache,
            cache_dir,
        } => test(
            &file,
            if no_cache {
                Cache::disabled()
            } else {
                Cache::at(cache_dir)
            },
        ),
        Command::Run { file } => run_main(&file),
        Command::Eval { file, expr } => eval(&file, &expr),
        Command::Repl { file } => repl(file.as_deref()),
        Command::Build { file, out, .. } => build(&file, &out),
    }
}

fn load(session: &mut Session, path: &Path) -> bool {
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(err) => {
            eprintln!("error: can't read {}: {err}", path.display());
            return false;
        }
    };
    match session.load(&path.display().to_string(), &text) {
        Ok(_) => {
            report(&session.sources, &std::mem::take(&mut session.warnings));
            true
        }
        Err(diagnostics) => {
            report(&session.sources, &diagnostics);
            false
        }
    }
}

fn check(paths: &[PathBuf]) -> ExitCode {
    let mut ok = true;
    for path in paths {
        // Files can't refer to each other yet, so each gets its own session.
        ok &= load(&mut new_session(), path);
    }
    if ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn test(path: &Path, cache: Cache) -> ExitCode {
    let mut session = new_session();
    if !load(&mut session, path) {
        return ExitCode::FAILURE;
    }
    let results = session.run_tests(&cache);
    let width = results.iter().map(|r| r.name.len()).max().unwrap_or(0);
    for result in &results {
        let (mark, why) = match result.outcome {
            Outcome::Passed => ("✓", String::new()),
            Outcome::Failed => ("✗", "  (evaluated to False)".to_string()),
            Outcome::OutOfResources(e) => ("!", format!("  (no result: {e})")),
        };
        let how = if result.cached { "cached" } else { "ran" };
        println!("  {mark} {:width$}  {how}{why}", result.name);
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
    if passed == results.len() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn run_main(path: &Path) -> ExitCode {
    let mut session = new_session();
    if !load(&mut session, path) {
        return ExitCode::FAILURE;
    }
    let main = match session.main() {
        Ok(main) => main,
        Err(diagnostic) => {
            report(&session.sources, &[diagnostic]);
            return ExitCode::FAILURE;
        }
    };
    let mut input = std::io::stdin().lock();
    let mut output = std::io::BufWriter::new(std::io::stdout().lock());
    match session.run_main(&main, &mut input, &mut output) {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            report(&session.sources, &[err.diagnostic(&main)]);
            ExitCode::FAILURE
        }
    }
}

fn eval(path: &Path, expr: &str) -> ExitCode {
    let mut session = new_session();
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
    Ok(format!("{value} : {ty}"))
}

fn repl(path: Option<&Path>) -> ExitCode {
    let mut session = new_session();
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
        "Stitchwort {}. Enter an expression to evaluate it, `:t expr` for its type, `:q` to quit.",
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

fn build(path: &Path, out: &Path) -> ExitCode {
    let mut session = new_session();
    if !load(&mut session, path) {
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
    let js = out.join(format!("{stem}.js"));
    let dts = out.join(format!("{stem}.d.ts"));
    let written = std::fs::create_dir_all(out)
        .and_then(|()| std::fs::write(&js, output.js))
        .and_then(|()| std::fs::write(&dts, output.dts));
    match written {
        Ok(()) => {
            println!("wrote {} and {}", js.display(), dts.display());
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("error: can't write output: {err}");
            ExitCode::FAILURE
        }
    }
}

fn report(sources: &SourceMap, diagnostics: &[Diagnostic]) {
    let color = std::io::stderr().is_terminal();
    for diagnostic in diagnostics {
        eprint!("{}", render(sources, diagnostic, color));
    }
}
