use std::collections::BTreeSet;
use std::io::IsTerminal;
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
use stitchwort_syntax::{Diagnostic, SourceMap, parse_namespace_line};

#[derive(Parser)]
#[command(name = "stitchwort", version, about = "The Stitchwort language")]
struct Cli {
    #[command(subcommand)]
    command: Command,
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
    },
    /// Print an embedded standard library file (`List/Toolkit.sw`;
    /// `core.sw` is the core), as the index's `std` markers name them
    StdSource { path: String },
    /// Run tests, reusing cached results where nothing they depend on has
    /// changed: a file's, or a namespace's (and those of the namespaces it
    /// uses), or the whole project's
    Test {
        /// A file, or a namespace of the project
        target: Option<String>,
        /// Run every test, ignoring (and not writing) cached results
        #[arg(long)]
        no_cache: bool,
        /// Where to keep cached results (default: `.stitchwort/cache` in the
        /// project folder, or in this folder for a file)
        #[arg(long)]
        cache_dir: Option<PathBuf>,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
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
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
    },
    /// Evaluate an expression in the context of a file
    Eval { file: PathBuf, expr: String },
    /// Start an interactive session, optionally with a file loaded
    Repl { file: Option<PathBuf> },
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
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
    },
}

/// The compiler runs on a thread with this much stack, so that deep programs
/// have room before they run into their resource limits.
const STACK: usize = 64 * 1024 * 1024;

fn main() -> ExitCode {
    let cli = Cli::parse();
    stitchwort_cli::driver::with_stack(STACK, move || run(cli))
}

fn run(cli: Cli) -> ExitCode {
    match cli.command {
        Command::Check {
            targets,
            project,
            index,
        } => check(&targets, project.as_deref(), index.as_deref()),
        Command::StdSource { path } => match stitchwort_cli::nav::std_source(&path, STACK) {
            Some(text) => {
                print!("{text}");
                ExitCode::SUCCESS
            }
            None => {
                eprintln!("error: there's no embedded library file `{path}`");
                ExitCode::FAILURE
            }
        },
        Command::Test {
            target,
            no_cache,
            cache_dir,
            project,
        } => test(target.as_deref(), no_cache, cache_dir, project.as_deref()),
        Command::Run {
            target,
            js,
            project,
        } => run_target(&target, js, project.as_deref()),
        Command::Eval { file, expr } => eval(&file, &expr),
        Command::Repl { file } => repl(file.as_deref()),
        Command::Build {
            target,
            out,
            project,
            ..
        } => build(&target, &out, project.as_deref()),
    }
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
    match session.load_project(&project.files, &project.name, target) {
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

fn check(targets: &[String], project: Option<&Path>, index: Option<&str>) -> ExitCode {
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
            let mut reported = Vec::new();
            let loaded = load_file_into(
                &mut session,
                Path::new(path),
                Some("checked"),
                &mut reported,
            );
            ok &= loaded;
            if let Some(index) = index {
                ok = write_index(&session, loaded, index, "", &reported) && ok;
            }
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
    let mut reported = Vec::new();
    let mut ok = load_project_into(&mut session, &project, &target, &mut reported);
    if let Some(index) = index {
        let root = format!("{}/", project.name);
        ok = write_index(&session, ok, index, &root, &reported) && ok;
    }
    exit(ok)
}

/// The cache to use: `--cache-dir` as given, or `.stitchwort/cache` in
/// `base`, making `.stitchwort/` (with a `.gitignore` that ignores it all)
/// if there isn't one yet.
fn cache(no_cache: bool, cache_dir: Option<PathBuf>, base: &Path) -> Cache {
    if no_cache {
        return Cache::disabled();
    }
    if let Some(dir) = cache_dir {
        return Cache::at(dir);
    }
    let stitchwort = base.join(".stitchwort");
    if !stitchwort.exists() && std::fs::create_dir_all(&stitchwort).is_ok() {
        let _ = std::fs::write(stitchwort.join(".gitignore"), "*\n");
    }
    Cache::at(stitchwort.join("cache"))
}

fn test(
    target: Option<&str>,
    no_cache: bool,
    cache_dir: Option<PathBuf>,
    project: Option<&Path>,
) -> ExitCode {
    let mut session = new_session(false);
    match target {
        Some(file) if is_file_target(file) => {
            if !load_file(&mut session, Path::new(file), Some("tested")) {
                return ExitCode::FAILURE;
            }
            let cache = cache(no_cache, cache_dir, Path::new("."));
            print_tests(&session.run_tests(&cache), false)
        }
        _ => {
            let Some(project) = locate_project(project, "test", "test hello.sw") else {
                return ExitCode::FAILURE;
            };
            let target = match target {
                Some(name) => Target::Namespaces(vec![name.to_string()]),
                None => Target::Everything,
            };
            if !load_project(&mut session, &project, &target) {
                return ExitCode::FAILURE;
            }
            let cache = cache(no_cache, cache_dir, &project.dir);
            print_tests(&session.run_tests(&cache), true)
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
    exit(passed == results.len())
}

/// `run`: a file's `main`, or a function of the project by its full name.
fn run_target(target: &str, js: bool, project: Option<&Path>) -> ExitCode {
    let mut session = new_session(false);
    let main = if is_file_target(target) {
        if !load_file(&mut session, Path::new(target), Some("run")) {
            return ExitCode::FAILURE;
        }
        session.main()
    } else {
        let Some(project) = locate_project(project, "run", "run hello.sw") else {
            return ExitCode::FAILURE;
        };
        session.include_from(std::rc::Rc::new(DiskFiles {
            root: project.dir.clone(),
        }));
        let sources = match project_sources(&project.files, &project.name, &mut session.sources) {
            Ok(sources) => sources,
            Err(diagnostics) => {
                report(&session.sources, &diagnostics);
                return ExitCode::FAILURE;
            }
        };
        let analysis = analyse(&mut session, &project.name, sources);
        if !analysis.diagnostics.is_empty() {
            report(&session.sources, &analysis.diagnostics);
            return ExitCode::FAILURE;
        }
        let Some(namespace) = namespace_of(&analysis, target).map(str::to_string) else {
            let d = run_unknown_namespace(&project.name, target, &analysis);
            report(&session.sources, &[d]);
            return ExitCode::FAILURE;
        };
        match session.load_analysis(
            &project.name,
            analysis,
            &Target::Namespaces(vec![namespace]),
        ) {
            Ok(_) => report(&session.sources, &std::mem::take(&mut session.warnings)),
            Err(diagnostics) => {
                report(&session.sources, &diagnostics);
                return ExitCode::FAILURE;
            }
        }
        session.main_named(target, &project.name)
    };
    let main = match main {
        Ok(main) => main,
        Err(diagnostic) => {
            report(&session.sources, &[diagnostic]);
            return ExitCode::FAILURE;
        }
    };
    if js {
        run_main_js(&mut session, main)
    } else {
        run_main(&mut session, &main)
    }
}

fn run_main(session: &mut Session, main: &Main) -> ExitCode {
    let mut input = std::io::stdin().lock();
    let mut output = std::io::BufWriter::new(std::io::stdout().lock());
    match session.run_main(main, &mut input, &mut output) {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            report(&session.sources, &[err.diagnostic(main)]);
            ExitCode::from(2)
        }
    }
}

/// `run --js`: writes `main` and a runner as JavaScript to a temporary
/// directory and runs it with Node, which inherits standard input, output
/// and error.
fn run_main_js(session: &mut Session, main: Main) -> ExitCode {
    use stitchwort_js::run::{EXIT_IO, EXIT_RESOURCE};
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
        .status()
    {
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
        Some(EXIT_IO) => {
            report(&session.sources, &[Diagnostic::error("E-IO", message())]);
            ExitCode::from(2)
        }
        // Node has reported what went wrong.
        Some(_) => ExitCode::from(2),
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

fn eval(path: &Path, expr: &str) -> ExitCode {
    let mut session = new_session(false);
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

fn build(target: &str, out: &Path, project: Option<&Path>) -> ExitCode {
    if !is_file_target(target) {
        return build_namespace(target, out, project);
    }
    let path = Path::new(target);
    let mut session = new_session(false);
    if !load_file(&mut session, path, Some("built")) {
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
    write_output(out, &stem, output)
}

/// `build --js NAMESPACE`: the exports of one namespace of the project, in
/// `{NAMESPACE}.js` and `{NAMESPACE}.d.ts`.
fn build_namespace(namespace: &str, out: &Path, project: Option<&Path>) -> ExitCode {
    let Some(project) = locate_project(project, "build", "build --js hello.sw") else {
        return ExitCode::FAILURE;
    };
    let mut session = new_session(false);
    if !load_project(
        &mut session,
        &project,
        &Target::Namespaces(vec![namespace.to_string()]),
    ) {
        return ExitCode::FAILURE;
    }
    match session.extract_namespace(namespace) {
        Ok(output) => write_output(out, namespace, output),
        Err(diagnostic) => {
            report(&session.sources, &[diagnostic]);
            ExitCode::FAILURE
        }
    }
}

/// Writes `{stem}.js` and `{stem}.d.ts` in `out`.
fn write_output(out: &Path, stem: &str, output: stitchwort_js::Output) -> ExitCode {
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
