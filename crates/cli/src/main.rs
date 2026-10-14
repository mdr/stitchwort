use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use rustyline::error::ReadlineError;
use stitchwort_cli::driver::Session;
use stitchwort_cli::render::render;
use stitchwort_syntax::{Diagnostic, SourceMap, parse_expression};

#[derive(Parser)]
#[command(name = "stitchwort", version, about = "The Stitchwort language")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Type-check source files
    Check {
        #[arg(required = true)]
        files: Vec<PathBuf>,
    },
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

fn main() -> ExitCode {
    match Cli::parse().command {
        Command::Check { files } => check(&files),
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
        Ok(_) => true,
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
        ok &= load(&mut Session::new(), path);
    }
    if ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn eval(path: &Path, expr: &str) -> ExitCode {
    let mut session = Session::new();
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
    let file = session.sources.add("<input>", expr);
    let expr = parse_expression(file, expr)?;
    let (term, ty) = session.elab.infer_expr(&expr)?;
    let ty = session.elab.show(&ty);
    if type_only {
        return Ok(ty);
    }
    let value = session.elab.eval(&term);
    Ok(format!("{} : {ty}", session.elab.show(&value)))
}

fn repl(path: Option<&Path>) -> ExitCode {
    let mut session = Session::new();
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
    let mut session = Session::new();
    if !load(&mut session, path) {
        return ExitCode::FAILURE;
    }
    let output = match stitchwort_js::generate(&session.elab.globals) {
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
