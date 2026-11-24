use std::collections::BTreeSet;
use std::io::{IsTerminal, Read};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use rustyline::error::ReadlineError;
use stitchwort_cli::driver::{Cache, Outcome, Session, TestResult};
use stitchwort_cli::project::{
    DiskFiles, Load, Target, TheoremCount, analyse, find_project, namespace_of, project_sources,
    run_unknown_namespace, unknown_namespace,
};
use stitchwort_cli::render::{ColorChoice, render};
use stitchwort_cli::run::Main;
use stitchwort_elab::project::FileModeContext;
use stitchwort_fmt::Error as FmtError;
use stitchwort_syntax::{Diagnostic, Severity, SourceMap, parse_namespace_line};

mod breaks_cmd;
mod build;
mod doc_cmd;
mod oracle_cmd;
mod oracle_sites;
mod rename_cmd;
mod sweep_cmd;
mod trial_cmd;

#[derive(Parser)]
#[command(name = "stitchwort", version, about = "The Stitchwort language")]
struct Cli {
    #[command(subcommand)]
    command: Command,
    /// Read the standard library from this directory (laid out as
    /// `crates/elab/src/std`) instead of the copy built in, so edits to it
    /// take effect without a rebuild. The environment variable
    /// `STITCHWORT_STD_DIR` does the same; this wins. A library file is
    /// checked only when a program needs it: `check --std` checks named ones
    #[arg(long, global = true, value_name = "DIR")]
    std_dir: Option<PathBuf>,
    /// Show each goal in full. Without it, a line of a goal (a hypothesis,
    /// or the target) longer than 400 characters is cut in the middle,
    /// saying how much is left out; `check --index` always has the whole
    /// goal
    #[arg(long, global = true)]
    full_goals: bool,
    /// When to colour error messages: `auto` (the default) colours them
    /// when stderr is a terminal and the environment variable `NO_COLOR`
    /// isn't set to anything; `always` and `never` decide it whatever the
    /// output is or `NO_COLOR` says. The text is the same either way:
    /// colour only adds to it
    #[arg(long, global = true, value_enum, default_value_t = ColorArg::Auto, value_name = "WHEN")]
    color: ColorArg,
    /// The colour theme, for terminals with a dark or a light background:
    /// `dark` (Catppuccin Mocha) or `light` (Latte). `auto` (the default)
    /// uses the environment variable `STITCHWORT_THEME` (`dark` or `light`)
    /// if set, else asks the terminal for its background colour (when
    /// stdin and stdout are terminals), else reads `COLORFGBG`, else is
    /// dark. 24-bit colours are used when `COLORTERM` is `truecolor` or
    /// `24bit`, else the nearest of 256
    #[arg(long, global = true, value_enum, default_value_t = ThemeArg::Auto, value_name = "THEME")]
    theme: ThemeArg,
}

/// `--theme`'s values.
#[derive(Clone, Copy, clap::ValueEnum)]
enum ThemeArg {
    Auto,
    Dark,
    Light,
}

/// `--color`'s values.
#[derive(Clone, Copy, clap::ValueEnum)]
enum ColorArg {
    Auto,
    Always,
    Never,
}

/// How `--color` was given; see [`report`].
static COLOR: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

/// Whether diagnostics on stderr are coloured: `--color`, then `NO_COLOR`
/// (<https://no-color.org>: any non-empty value), then whether stderr is
/// a terminal.
fn color_on_stderr() -> bool {
    let choice = match COLOR.load(std::sync::atomic::Ordering::Relaxed) {
        1 => ColorChoice::Always,
        2 => ColorChoice::Never,
        _ => ColorChoice::Auto,
    };
    let no_color = std::env::var("NO_COLOR").ok();
    let on = choice.enabled(std::io::stderr().is_terminal(), no_color.as_deref());
    if on {
        stitchwort_cli::theme::init();
    }
    on
}

/// Whether goals are shown in full (`--full-goals`).
static FULL_GOALS: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// A session for the compiler thread.
fn new_session(navigation: bool) -> Session {
    if navigation {
        Session::navigable_for_stack(STACK)
    } else {
        Session::for_stack(STACK)
    }
}

#[derive(Subcommand)]
enum SweepCommand {
    /// Move theorems' `∀` variables, and the premises their proofs name,
    /// before the colon; a proof by arms becomes `:= match x with`
    /// (docs/proposals/theorem-binders.md §5). Each rewrite is checked to
    /// keep its statement's hash; one that doesn't is refused and listed.
    /// Exit status: 0 done, 1 not clean (nothing written), 2 refused
    TheoremBinders {
        /// Files (`.sw`) or folders to sweep
        paths: Vec<PathBuf>,
        /// The files are the standard library's: check an edited copy
        /// against the library as it is
        #[arg(long)]
        std: bool,
        /// The paths are single files, each checked on its own: no project
        /// is needed
        #[arg(long, conflicts_with_all = ["std", "project"])]
        files: bool,
        /// With --std: the library's source folder (default:
        /// `crates/elab/src/std` here or above)
        #[arg(long, value_name = "DIR", requires = "std")]
        std_root: Option<PathBuf>,
        /// Check, but write nothing
        #[arg(long)]
        dry_run: bool,
        /// Only list what would be rewritten and skipped: no check, nothing
        /// written
        #[arg(long)]
        plan: bool,
        /// Print the result as JSON (version 1)
        #[arg(long)]
        json: bool,
        /// Leave this theorem as it is (a full name, or as written; may be
        /// repeated): listed as refused
        #[arg(long, value_name = "NAME")]
        keep: Vec<String>,
        /// Check with the "proofs only" promise instead of "same
        /// statement": a definition whose proofs changed (a theorem it
        /// embeds was re-proved) is accepted if its hash with proofs left
        /// out held
        #[arg(long)]
        proofs_only: bool,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
}

#[derive(Subcommand)]
enum OracleCommand {
    /// Delete each `.read` in turn and check the file: it must then fail
    /// (the `.read` was needed) or keep every statement and definition
    /// (redundant); anything else changed meaning silently (SW-3105 §4.6).
    /// Exit status: 0 nothing changed meaning, 1 something did, 2 refused
    Readings(OracleArgs),
    /// Replace each call of a build helper (`Bool.falseOfNotTrue x p`,
    /// `(r ..).backward p`, ...) by its proof and check the file: still
    /// failing (needed), or meaning kept (removable: the sweep's work list),
    /// or a statement changed (bad). Exit status as for `readings`
    Builds(OracleArgs),
}

#[derive(clap::Args)]
struct OracleArgs {
    /// Files (`.sw`) or folders to try
    paths: Vec<PathBuf>,
    /// The files are the standard library's: check an edited copy against
    /// the library as it is (one full library load per site)
    #[arg(long)]
    std: bool,
    /// The paths are single files, each checked on its own: no project is
    /// needed
    #[arg(long, conflicts_with_all = ["std", "project"])]
    files: bool,
    /// The library's source folder (default: `crates/elab/src/std` here or
    /// above): the `@[reading]` theorems whose `.backward` the `builds`
    /// half looks for are listed from it, and with --std it is what is
    /// edited
    #[arg(long, value_name = "DIR")]
    std_root: Option<PathBuf>,
    /// Try at most this many sites, in file and line order
    #[arg(long, value_name = "N")]
    limit: Option<usize>,
    /// Print the result as JSON (version 1)
    #[arg(long)]
    json: bool,
    /// The project folder, if not the folder you're in or the nearest one
    /// above it
    #[arg(long)]
    project: Option<PathBuf>,
    #[command(flatten)]
    cache: CacheArgs,
}

#[derive(Subcommand)]
enum DevCommand {
    /// Build the lossless syntax tree of every `.sw` file under the paths
    /// and check that each reads back as the file, byte for byte. Prints
    /// the files that don't, and totals: declarations, ones that didn't
    /// parse, nodes, ones whose marks don't nest and internal errors. Exit
    /// status 1 if any file fails, a declaration doesn't parse or its marks
    /// don't nest, or it is an internal error, or (with --spans) a span is
    /// no node
    Tree {
        /// Files or folders
        paths: Vec<PathBuf>,
        /// Print each file's tree
        #[arg(long)]
        print: bool,
        /// Also time parsing every file this many times, and print the best
        /// time of each: as `check` parses (the lossless tree, then the
        /// compiler's tree lowered from it), and the lossless tree alone,
        /// so the difference is the lowering
        #[arg(long, value_name = "ROUNDS")]
        time: Option<u32>,
        /// With --time, time only parsing as `check` does, and skip the
        /// round trip: for counting the instructions of that alone
        #[arg(long, requires = "time")]
        parse_only: bool,
        /// Also check that every span in the compiler's tree is a node of
        /// the lossless tree or a single token, and print each that isn't
        #[arg(long)]
        spans: bool,
        /// Parse each file as one expression, as a search query is, and
        /// print its tree (`Expression` and the expression), or on standard
        /// error `error: MESSAGE` and exit 1 if it doesn't parse (the
        /// self-hosted formatter's stage 2a gate, SW-3819)
        #[arg(long, conflicts_with_all = ["time", "spans"])]
        expression: bool,
    },
    /// The one-line-break oracle of syntax error recovery
    /// (docs/proposals/syntax-error-recovery.md §6): break each line of
    /// every file under the paths that checks, one at a time (its last
    /// token dropped; a stray `)` before its middle token), check the
    /// broken file, and count the errors other than the syntax error, which
    /// are false ones, by the recovery point the parser used. Lists the
    /// worst breaks. In a project by default; `--files` checks each file on
    /// its own, `--std` library files. Prints progress on stderr after each
    /// file
    Breaks {
        /// Files or folders
        paths: Vec<PathBuf>,
        /// The paths are standard library files or folders, each break
        /// checked in a copy of the library by `check --std`
        #[arg(long, conflicts_with_all = ["files", "project"])]
        std: bool,
        /// The paths are files each checked on its own, as `check FILE` does
        #[arg(long, conflicts_with = "project")]
        files: bool,
        /// With --std, the library's source (default: the nearest
        /// `crates/elab/src/std` above this folder)
        #[arg(long, requires = "std")]
        std_root: Option<PathBuf>,
        /// Try at most this many breaks
        #[arg(long)]
        limit: Option<usize>,
        /// How many of the worst breaks to list
        #[arg(long, default_value_t = 20)]
        worst: usize,
        /// Print the results as one JSON object
        #[arg(long)]
        json: bool,
        /// Append one JSON object per finished file to PATH as soon as that
        /// file is done, flushed, so a killed run keeps every finished
        /// file's results
        #[arg(long, value_name = "PATH")]
        jsonl: Option<PathBuf>,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// Print every `.sw` file's tokens with their trivia after the
    /// formatter's rule N, one line a token (the dump the self-hosted
    /// formatter's lexer is compared with, `task fmt:twin`). A file that
    /// doesn't lex prints `error: MESSAGE` on standard error; exit status 1
    Tokens {
        /// Files or folders
        paths: Vec<PathBuf>,
    },
    /// Print the layout document the formatter's rules build for each
    /// declaration of every `.sw` file, with the text the engine prints for it
    /// (the dump the self-hosted formatter's engine is compared with,
    /// `task fmt:twin`): per declaration a line `decl N`, a line `size N`, a line `text
    /// ESCAPED`, then the document one node a line in pre-order. A file the
    /// formatter refuses prints `error: MESSAGE` on standard error; exit
    /// status 1
    Doc {
        /// Files or folders
        paths: Vec<PathBuf>,
    },
    /// Print the lossless tree of every `.sw` file after each of the
    /// formatter's four tidy passes (`== P1 ==`, the tree, `== P2 ==`, ...),
    /// for the self-hosted formatter's comparison (`task fmt:twin`). A file
    /// that doesn't lex prints `error: MESSAGE` on standard error; exit
    /// status 1
    Passes {
        /// Files or folders
        paths: Vec<PathBuf>,
    },
    /// The formatter's report over a tree of files: format every `.sw` file
    /// under the paths, without writing anything, and check each result: the
    /// same tokens up to the tidy passes' rewrites, the same comments on the
    /// same tokens, the same syntax tree, and the same text when formatted
    /// again. Prints each file that fails a check, then totals: declarations,
    /// parameter groups merged, and code lines over 120 before and after.
    /// Exit status 1 if any file fails a check or isn't idempotent
    FmtTree {
        /// Files or folders
        paths: Vec<PathBuf>,
        /// Print each formatted file
        #[arg(long)]
        print: bool,
    },
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
        /// The targets are standard library files or folders, not a
        /// project's: `Nat/Arith.sw`, `Nat`, or `Std.Nat.Arith`. Each is
        /// checked in full, theorem bodies included, with the files it
        /// needs, from the library `--std-dir` names (or the usual one);
        /// unchanged files come from the check cache. A library file is
        /// only checked when something needs it, so `check FILE` of a
        /// program that doesn't use an edited library file doesn't see it
        #[arg(
            long,
            requires = "targets",
            conflicts_with_all = ["project", "index", "only", "counterexamples"]
        )]
        std: bool,
        /// With --std: also print the warnings the core and the library
        /// files give (programs never see them), and a count by code and
        /// file. Checks every file in full, without the check cache, since
        /// a file the cache answers for has no warnings to give
        #[arg(long, requires = "std")]
        warnings: bool,
        /// The project folder (the one with `stitchwort.yaml`), if not the
        /// folder you're in or the nearest one above it
        #[arg(long)]
        project: Option<PathBuf>,
        /// Also write the code navigation index (JSON; see
        /// docs/proposals/code-navigation.md) to this file, or to standard
        /// output for `-`. One file or any number of namespaces
        #[arg(long, value_name = "FILE")]
        index: Option<String>,
        /// Check only this theorem (its full name; repeat the option, or
        /// separate names with commas, for several), and the theorems it
        /// needs, in the namespaces named, or in its own namespace if none
        /// is. The other theorems of those namespaces are not checked, and
        /// the output says how many were. Everything that isn't a theorem
        /// is checked as usual. Doesn't apply with `--std`
        #[arg(
            long,
            value_name = "THEOREM",
            value_delimiter = ',',
            conflicts_with_all = ["index", "counterexamples"]
        )]
        only: Vec<String>,
        /// Replace each `rewrite repeatedly` in the files checked by the
        /// `rewrite` steps it made (`rewrite r1, r2 then t`), writing the
        /// files back. Checks without the check cache, which skips what it
        /// answers for. A call that rewrites differently in the cases it is
        /// checked in (under `cases then`) is left as it is, and listed
        #[arg(long, conflicts_with_all = ["index", "counterexamples"])]
        expand_repeatedly: bool,
        /// Replace each walk (`byWalking [lemmas] then t`) in the files
        /// checked by the chain of lemmas it stands for, writing the files
        /// back, and print which lemma each walk used at each call. A walk
        /// that stops is written as far as it got, with `?` where it
        /// stopped. Checks without the check cache
        #[arg(long, conflicts_with_all = ["index", "counterexamples"])]
        expand_walk: bool,
        /// Replace each `byFacts` in the files checked by the term it found
        /// (`imp h.left`), writing the files back. A `byFacts` that left a
        /// part to `then t`, or used an equation's field, is left as it is.
        /// Checks without the check cache
        #[arg(long, conflicts_with_all = ["index", "counterexamples", "expand_walk", "expand_repeatedly"])]
        expand_facts: bool,
        /// With --expand-walk or --expand-facts: print each file's expanded
        /// text on standard output instead of writing it back, leaving the
        /// file unchanged. A walk's trace lines then go to standard error,
        /// so standard output is just the file text
        #[arg(long)]
        stdout: bool,
        #[command(flatten)]
        counterexamples: CounterexampleArgs,
        #[command(flatten)]
        cache: CacheArgs,
        /// Also use check-cache entries carried over from another build of
        /// Stitchwort: ones it wrote from the same source, when its kernel
        /// side (`crates/core` and what that is built with) is this
        /// build's. This kernel accepted their terms, but this build's
        /// elaborator hasn't confirmed they are what the source now means:
        /// a new error, warning or reading of a statement can be hidden
        /// until a check without this option. The output says how many were
        /// carried over (docs/proposals/check-cache-across-updates.md). Also
        /// on with STITCHWORT_CARRY_OVER=1 when standard error is a terminal
        #[arg(long, conflicts_with_all = ["std", "expand_repeatedly", "expand_walk", "expand_facts", "no_cache"])]
        carry_over: bool,
        /// Check every check-cache entry used again with the kernel, rather
        /// than trusting it: its terms go through the kernel's checks, and
        /// only elaboration is skipped. No namespace is left out unloaded.
        /// An entry the kernel refuses is elaborated instead. The output
        /// says how many were checked again, and how many refused. With
        /// --carry-over, the entries carried over are checked too (those
        /// from a build with another kernel side always are)
        #[arg(long, conflicts_with_all = ["std", "expand_repeatedly", "expand_walk", "expand_facts", "no_cache"])]
        recheck: bool,
        /// After the check, print stderr tables of where the time went: each
        /// namespace (a cached one is marked, not timed), then each
        /// declaration checked with its elaboration, kernel and total time,
        /// slowest first. `--timings=N` lists the N slowest declarations,
        /// `--timings=all` every one; 20 without a value
        #[arg(
            long,
            value_name = "all|N",
            num_args = 0..=1,
            require_equals = true,
            default_missing_value = "20",
            value_parser = parse_timings
        )]
        timings: Option<usize>,
        /// Check a project with N workers side by side: they fill the check
        /// cache, then the check runs as with one job over what they wrote,
        /// so its messages and result are the same. With --no-cache their
        /// entries are kept in memory for the run. One job, whatever this
        /// says, with --recheck, --carry-over, --only, --no-project-cache,
        /// the --expand options or a file. Also STITCHWORT_JOBS; 1 if
        /// neither is given
        #[arg(short = 'j', long, value_name = "N", value_parser = parse_jobs)]
        jobs: Option<usize>,
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
        /// Run the tests as native code, compiled together; a test that
        /// can't run natively runs on the fast runtime, with the same
        /// outcome. Needs a build with the `native` feature
        #[arg(long, conflicts_with = "reference")]
        native: bool,
        /// With --native, say on standard error what ran natively, and why
        /// anything didn't
        #[arg(long, requires = "native")]
        verbose: bool,
        /// Run every test afresh and compare each result with the cached
        /// one, failing on any that differs; the cache is not written. A
        /// check that the cache's key covers everything a result depends on
        #[arg(long, conflicts_with = "no_cache")]
        verify_cache: bool,
        /// Run only the test with this name (as written between the quotes
        /// in `test "name" := …`)
        #[arg(long, value_name = "NAME")]
        only: Option<String>,
        /// Print the results as one JSON object on standard output, for
        /// editors: `{"ok", "tests": [{"namespace", "name", "outcome"
        /// ("passed", "failed" or "unfinished"), "cached", "file", "line",
        /// "column", "message", "failure"?}]}`
        #[arg(long)]
        json: bool,
        /// The target is a standard library file or folder, not a
        /// project's: `Nat/Arith.sw`, `Nat` or `Std.Nat.Arith`. Runs the
        /// `test`s declared in those files only (not those of the files
        /// they need), on the reference evaluator, after checking them in
        /// full without the check cache, so it takes seconds to a minute.
        /// From the library `--std-dir` names (or the usual one). Takes
        /// `--only` and `--json`
        #[arg(
            long,
            requires = "target",
            conflicts_with_all = ["project", "reference", "native", "verify_cache"]
        )]
        std: bool,
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
        /// After the run, print on standard error where its time went: for
        /// each definition, its calls, and its self and total time, sampled
        /// every millisecond. An interrupted run (Ctrl-C, `timeout`) prints
        /// the profile so far. Only on the fast runtime
        #[arg(long, conflicts_with_all = ["js", "reference", "native", "alloc_trace"])]
        profile: bool,
        /// With --profile, how many definitions to show, most self time
        /// first (0 for all)
        #[arg(long, value_name = "N", default_value_t = 25, requires = "profile")]
        profile_top: usize,
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
        /// The program's arguments, after `--`, which `IO.args` gives:
        /// `stitchwort run Main.main -- 11 7`
        #[arg(last = true, value_name = "ARGS")]
        args: Vec<String>,
    },
    /// List the axioms definitions or theorems depend on, directly or
    /// through what they use, one per line, sorted (today only `Quot.sound`).
    /// A definition that uses none is reported as such; that does not mean
    /// the term computes to data in the kernel (a proof built from
    /// `Quot.ind` can still be stuck). With several names, each is reported
    /// under its own heading
    Axioms {
        /// A file, or the full name of a definition in the project
        /// (`Main.total`)
        target: String,
        /// The definitions' names in the file, when the target is a file;
        /// more full names, when it is a definition in the project
        names: Vec<String>,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// Check that theorems can be trusted, as a proof lane does before it
    /// reports (SW-912): each fails if it depends on an axiom beyond the
    /// allowed ones or is unfinished (it, or something it uses, has a `?`),
    /// and warns if no input the counterexample search made satisfied its
    /// hypotheses (it may be vacuous). Exits with status 1 if any theorem
    /// fails, or with --strict if any warns
    Audit {
        /// Files, or namespaces or full theorem names of the project (all
        /// of its theorems if none are named); `Std` or `Std.List` for the
        /// standard library's. After one file, names of theorems in it
        targets: Vec<String>,
        /// Print JSON (one object: `ok`, `allowed_axioms`, `theorems`,
        /// `summary`) instead of text
        #[arg(long)]
        json: bool,
        /// Fail on warnings too
        #[arg(long)]
        strict: bool,
        /// The axioms allowed, comma-separated (`--allowed-axioms ''` for
        /// none), instead of the project's `audit: allowed-axioms:` or the
        /// default, `Quot.sound`
        #[arg(long, value_name = "LIST")]
        allowed_axioms: Option<String>,
        /// Don't search for counterexamples (no vacuity warnings)
        #[arg(long)]
        no_search: bool,
        /// The time each theorem's search may take, as `500ms` or `2s`
        /// (default 2s, a backstop: up to 1500 inputs end a search first)
        #[arg(long, value_name = "TIME", value_parser = parse_millis)]
        counterexample_budget: Option<u64>,
        /// Print a line for every theorem, not only those with findings
        #[arg(long)]
        verbose: bool,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// Search the library's and the project's theorems, definitions and
    /// constructors by the shape of their type (docs/syntax.md, "Lemma
    /// search"). Exits with status 0 with results, 1 with none, 2 if the
    /// query doesn't elaborate
    Search {
        /// Comma-separated parts: a pattern (`_` any term, `?x` a named
        /// hole, a leading `⊢` for conclusions only), names the type must
        /// mention (`List.length`), and `"text"` the name must contain.
        /// Not with --at
        query: Option<String>,
        /// A file to search with the library, instead of the project
        file: Option<PathBuf>,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it (with neither a file nor a project, the library
        /// alone)
        #[arg(long)]
        project: Option<PathBuf>,
        /// Match the pattern against either side of conclusions stated as
        /// `=` or `Iff` (rewrite rules), conditional ones included
        #[arg(long)]
        rewrite: bool,
        /// Print JSON (version 1)
        #[arg(long)]
        json: bool,
        /// How many results to show
        #[arg(long, default_value_t = 10)]
        limit: usize,
        /// Also the library's hidden helpers (`%` in the name) and
        /// `…Example` theorems
        #[arg(long)]
        all: bool,
        /// Theorems only (with --definitions or --constructors: those too)
        #[arg(long)]
        theorems: bool,
        /// Definitions (functions and values) only, or with the others named
        #[arg(long)]
        definitions: bool,
        /// Constructors only, or with the others named
        #[arg(long)]
        constructors: bool,
        /// Only declarations in this namespace, written in full
        /// (`Std.List`, `Aoc.Year2021.Day16`), or one inside it; repeat for
        /// more than one. With --at, the induction hypothesis and the
        /// goal's hypotheses are offered too
        #[arg(long = "in", value_name = "NAMESPACE")]
        within: Vec<String>,
        /// Append a line of JSON describing this search (the query, what it
        /// elaborated to, the results with their ranks, the time) to this
        /// file; also from the environment variable STITCHWORT_SEARCH_LOG
        #[arg(long, value_name = "FILE")]
        log: Option<PathBuf>,
        /// What closes the goal `?` at FILE:LINE[:COL] (or with --goal N, the
        /// file's N-th goal): lemmas applied to it, kernel-checked, and
        /// rewrites (docs/syntax.md, "What closes this ?")
        #[arg(long, value_name = "FILE:LINE[:COL]")]
        at: Option<String>,
        /// With --at FILE: the file's N-th goal, in source order
        #[arg(long, value_name = "N")]
        goal: Option<usize>,
        /// With --at: answer with the simplest closer alone if one closes
        /// the goal (`byComputing`, a hypothesis, `byDecision`, `arithmetic`, `algebra`,
        /// `cases`, in that order), as the editor's "Search for a proof"
        /// does, instead of searching
        #[arg(long)]
        simplest_first: bool,
        /// With --at: how many matching declarations to try
        #[arg(long, value_name = "N", default_value_t = 50)]
        candidates: usize,
        /// With --at: how long checking may take, as `10s` or `500ms`
        #[arg(long, value_name = "TIME", default_value = "10s")]
        time: String,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// Without `--at`, every open goal (`?`) of the project and what relies
    /// on it or can't be checked until it is filled (docs/syntax.md, "Goals").
    /// With `--at`, the goal at a point of a proof, and the names in scope
    /// there: `⊢ goal` in a proof, `expected T` in program code
    /// (docs/syntax.md, "The goal at a point"). Exits with status 0 with an
    /// answer, 2 with none there or for a bad argument, 1 if the file
    /// doesn't parse
    Goal {
        /// Namespaces of the project: list only the open goals in them and
        /// under them, checking just these and what they use (as `check
        /// NAMESPACE…` does), not the whole project
        #[arg(conflicts_with_all = ["at", "summary"])]
        targets: Vec<String>,
        /// FILE:LINE[:COL], 1-based; without COL, the line's first
        /// character that isn't a blank
        #[arg(long, value_name = "FILE:LINE[:COL]")]
        at: Option<String>,
        /// Count the open goals per namespace, in the project's order, with
        /// the total, instead of listing them: for a book's chapters
        #[arg(long)]
        summary: bool,
        /// The answer as a JSON object (docs/syntax.md, "The goal at a
        /// point")
        #[arg(long)]
        json: bool,
        /// The project folder, if not the nearest one above the file
        #[arg(long)]
        project: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// Which declarations of the project refer to each NAME (a full name,
    /// or a short one that only one declaration has), read off the checked
    /// terms, not the text, so two namespaces that define the same short
    /// name are told apart. Listed by namespace, with FILE:LINE. With
    /// `--unused NAMESPACE…`, the definitions in those namespaces nothing
    /// else in the project refers to (tests and `…Example` theorems left
    /// out). With `--unused --dead`, the definitions no root reaches instead:
    /// the roots are tests, `…Example` theorems, declarations outside the
    /// namespaces, and each `--root NAME`. Exits with status 0 with an
    /// answer, 2 when a name is unknown or ambiguous (the candidates are
    /// listed), 1 if the project doesn't load (docs/syntax.md, "Who uses a
    /// declaration")
    Uses {
        /// Declarations to look up; with `--unused`, namespaces to list in
        #[arg(value_name = "NAME", required = true)]
        names: Vec<String>,
        /// List unused definitions of the namespaces instead
        #[arg(long)]
        unused: bool,
        /// With `--unused`, list the definitions no root reaches instead
        #[arg(long, requires = "unused")]
        dead: bool,
        /// With `--dead`, an extra root to reach from; may be repeated
        #[arg(long, value_name = "NAME", requires = "dead")]
        root: Vec<String>,
        /// The answer as a JSON object: version 1; `declarations`, each
        /// with `name` and `users` (`declaration`, `namespace`, `file`,
        /// `line`); with `--unused`, `unused` (`dead` with `--dead`)
        #[arg(long)]
        json: bool,
        /// The project folder, if not the nearest one above the current one
        #[arg(long)]
        project: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// What a declaration does: its header, doc, examples (tests and
    /// `…Example` theorems named after it) and theorems about it, or a
    /// namespace's docs and what it declares (docs/syntax.md, "Doc
    /// comments"). Exits with status 0 when the name is found, 1 when it
    /// isn't, 2 when it is more than one. With `--coverage`, how much of
    /// each namespace is documented instead (exit 0; 2 for an error)
    #[command(group(clap::ArgGroup::new("what").required(true).multiple(true).args(["name", "coverage"])))]
    Doc {
        /// A full name (`Std.List.filterMap`), a library name without `Std.`
        /// (`List.filterMap`), or a name of the project (as `import N (..)`
        /// sees it), or a namespace. With `--coverage`, the namespaces
        name: Option<String>,
        /// A file to read with the library, instead of the project. With
        /// `--coverage`, a namespace
        file: Option<PathBuf>,
        /// With `--coverage`, more namespaces
        #[arg(hide = true)]
        more: Vec<String>,
        /// Report how much is documented, from parsing alone: per namespace
        /// (none: the library, or the project's), the definitions, types,
        /// interfaces and abilities with a doc and with an example, the
        /// theorems with a doc (apart), the undocumented names (the library's; a
        /// project's with `--list`) and the
        /// `…Example` theorems that attach to nothing. Only `--|` docs count:
        /// a plain `--` comment is no doc
        #[arg(long)]
        coverage: bool,
        /// With `--coverage` on a project, also list the declarations without
        /// a doc. The library's report always lists them: documenting it all
        /// is the aim there, not in a project's code
        #[arg(long, requires = "coverage")]
        list: bool,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it (with neither a file nor a project, the library
        /// alone). For a library name it adds the project's theorems
        #[arg(long)]
        project: Option<PathBuf>,
        /// Print JSON (version 1)
        #[arg(long)]
        json: bool,
        /// How many theorems about it to show; `0` for none, which also
        /// skips checking (no elaborated type)
        #[arg(long, default_value_t = 8, value_name = "N")]
        theorems: usize,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// Rename a local, hypothesis, function or theorem everywhere in the
    /// project (docs/proposals/refactoring.md). The renamed project is
    /// checked first, and compared with the project now: its diagnostics,
    /// and the meaning (content hash) of every declaration. Written only if
    /// that finds no problem, or with `--anyway`. Exit status: 0 renamed
    /// cleanly, 1 problems and nothing written, 2 refused or not understood
    /// (nothing written; `--anyway` doesn't override that), 3 written with
    /// problems left to fix
    Rename {
        /// A declaration's full name (`Shop.step`), or a position in a
        /// project file, `src/shop.sw:12:5` (line and column from 1): a
        /// declaration's name, a use of it, or a local's binder or use
        target: String,
        /// The new name: one lowercase identifier, not a keyword
        new_name: String,
        /// Write the edits even if the check finds problems, and list them
        /// as what is left to fix by hand
        #[arg(long)]
        anyway: bool,
        /// Write nothing: list the edits, and the problems
        #[arg(long)]
        dry_run: bool,
        /// Print the result as JSON (version 1)
        #[arg(long)]
        json: bool,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// Developer tool for sweeps: try edits on the checked project, or an
    /// edited copy of the standard library, and list the new diagnostics and
    /// the declarations whose content hash moved. Writes nothing unless
    /// `--apply`. Exit status: 0 nothing found, 1 problems, 2 refused
    #[command(hide = true)]
    TrialEdits {
        /// JSON: a list of edits (or an object with an `edits` list, as
        /// `rename --dry-run --json` prints). An edit is `{file, line,
        /// column, endLine, endColumn, newText}` (from 1), or `{file, text}`
        /// to replace a whole file
        edits: Option<PathBuf>,
        /// Accept a theorem's changed proof if its statement (type hash)
        /// held; definitions must keep their hash. Default: every
        /// declaration keeps its hash
        #[arg(long)]
        same_statement: bool,
        /// Accept any declaration whose hash with its proofs left out held:
        /// only proofs changed, a theorem's or those a definition embeds
        /// (its statement still says the same, and it computes the same)
        #[arg(long, conflicts_with = "same_statement")]
        proofs_only: bool,
        /// Write the edited files if nothing was found
        #[arg(long)]
        apply: bool,
        /// With `--apply`, write them even if problems were found
        #[arg(long, requires = "apply")]
        anyway: bool,
        /// Print the result as JSON (version 1)
        #[arg(long)]
        json: bool,
        /// With the global `--std-dir EDITED`: compare the whole library as
        /// `EDITED` has it with the library as it was, from this directory
        /// (default: what the environment picks without `--std-dir`)
        #[arg(long, value_name = "DIR")]
        std_before: Option<PathBuf>,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
    /// Developer tool: print the content hashes of declarations (their
    /// names, or all of them): the hash, the hash of the statement alone,
    /// the kind and the full name
    #[command(hide = true)]
    Hash {
        /// Full names; a name includes what is declared under it
        names: Vec<String>,
        /// Hash the standard library instead of the project
        #[arg(long)]
        std: bool,
        /// Print JSON (version 1)
        #[arg(long)]
        json: bool,
        /// With --json, list the declarations each definition mentions
        #[arg(long, requires = "json")]
        uses: bool,
        /// With --std --json, also list the library's warnings and where
        /// they are
        #[arg(long, requires_all = ["std", "json"])]
        warnings: bool,
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
    /// Developer tools that rewrite many declarations, writing only what
    /// the trial check accepts
    #[command(hide = true, subcommand)]
    Sweep(SweepCommand),
    /// The deletion oracle: try deleting each `.read`, or replacing each
    /// build helper by its proof, and check what the edit does
    #[command(hide = true, subcommand)]
    Oracle(OracleCommand),
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
    /// Build a standalone executable that runs a file's `main`, a project
    /// folder's (its one namespace with a `main`), or a function of the
    /// project by its full name (`Rogue.main`), and needs neither
    /// `stitchwort` nor the source. It links with the system's C compiler
    /// (`$CC`, or `cc`). With --js, extract a file's exports, or a
    /// namespace's, to JavaScript instead
    Build {
        /// A file, a project folder, or the full name of a function in the
        /// project; with --js, a file or a namespace of the project
        target: String,
        /// Generate an ES module and TypeScript declarations
        #[arg(long)]
        js: bool,
        /// The executable to write (default: the file's, folder's or
        /// namespace's name, in this folder); with --js, the output
        /// directory (default: this folder)
        #[arg(short, long)]
        out: Option<PathBuf>,
        /// With --js, also write a source map (`NAME.js.map`) from the
        /// generated module to the `.sw` source, one entry per definition,
        /// and refer to it from the module
        #[arg(long, requires = "js")]
        source_map: bool,
        /// Compile `main` and every function it reaches to native code in
        /// the executable, as `run --native` does, or fail if any can't be:
        /// the executable has no machine to fall back to. Needs a build
        /// with the `native` feature
        #[arg(long, conflicts_with = "js")]
        native: bool,
        /// With --native, say on standard error what was compiled
        #[arg(long, requires = "native")]
        verbose: bool,
        /// With --native, each compiled body counts its own entries, which
        /// a runtime built with the `call-counts` feature reports when
        /// `STITCHWORT_CALL_COUNTS` is set (`task profile:native`). With
        /// the usual runtime it does nothing but slow the program
        #[arg(long, requires = "native")]
        count_bodies: bool,
        /// With --native, also write OUT.pcmap.json: for each compiled
        /// body, which bytecode instruction, and which part of it (checks,
        /// reference counts, calls, its own work), each stretch of its
        /// machine code is for, for `task profile:native --by-instruction`.
        /// The code is the same as without it
        #[arg(long, requires = "native")]
        pc_map: bool,
        /// The project folder, if not the folder you're in or the nearest
        /// one above it
        #[arg(long)]
        project: Option<PathBuf>,
        #[command(flatten)]
        cache: CacheArgs,
    },
}

impl Command {
    /// Whether running it reads the standard library. `fmt` doesn't; `lsp`
    /// reads it after `initialize`, so that it can say why to the editor.
    fn needs_std(&self) -> bool {
        !matches!(self, Command::Fmt { .. } | Command::Lsp)
    }
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
    /// Check the project's own namespaces afresh, neither reading nor
    /// writing their cache entries, while the standard library still comes
    /// from the cache: for timing or profiling the target without paying
    /// for the library
    #[arg(long, conflicts_with = "no_cache")]
    no_project_cache: bool,
    /// Where to keep the caches (default: `.stitchwort/cache` in the
    /// project folder, or in this folder for a file)
    #[arg(long)]
    cache_dir: Option<PathBuf>,
}

/// The compiler runs on a thread with this much stack, so that deep programs
/// have room before they run into their resource limits.
const STACK: usize = 64 * 1024 * 1024;

/// How much of [`STACK`] `dev tree` lets the parser and the lowering use,
/// as `check` does (`Limits::for_stack`): the rest is room for what runs
/// below the point the limit is measured from.
const TREE_STACK: usize = STACK - STACK / 4;

/// Checking builds and frees terms and values by the million; with the
/// system allocator (on macOS at least) allocating and freeing was about a
/// quarter of a `check`. mimalloc makes `check` of the AoC project retire
/// about 28% fewer instructions (docs/proposals/proof-check-speed.md).
#[global_allocator]
static ALLOCATOR: stitchwort_alloc::Allocator = stitchwort_alloc::Allocator;

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

/// `--timings`' value: a count of declarations, or `all`.
fn parse_timings(value: &str) -> Result<usize, String> {
    if value == "all" {
        return Ok(usize::MAX);
    }
    match value.parse::<usize>() {
        Ok(n) if n > 0 => Ok(n),
        _ => Err(format!(
            "expected `all` or a positive number, not `{value}`"
        )),
    }
}

/// `--jobs`' value: a positive number of workers.
fn parse_jobs(value: &str) -> Result<usize, String> {
    match value.parse::<usize>() {
        Ok(n) if n > 0 => Ok(n),
        _ => Err(format!("expected a positive number, not `{value}`")),
    }
}

/// Whether `check --jobs N --no-cache` runs N workers, passing their results
/// to each other as entries in memory (D3731), or one job. The one switch
/// for it.
const PARALLEL_NO_CACHE: bool = true;

/// How many workers `check` uses: `--jobs`, else `STITCHWORT_JOBS`, else 1.
fn jobs_asked(jobs: Option<usize>) -> usize {
    jobs.or_else(|| {
        std::env::var("STITCHWORT_JOBS")
            .ok()
            .and_then(|v| parse_jobs(v.trim()).ok())
    })
    .unwrap_or(1)
}

fn main() -> ExitCode {
    exit_quietly_on_broken_pipe();
    let cli = Cli::parse();
    FULL_GOALS.store(cli.full_goals, std::sync::atomic::Ordering::Relaxed);
    COLOR.store(cli.color as u8, std::sync::atomic::Ordering::Relaxed);
    stitchwort_cli::theme::THEME_FLAG.store(cli.theme as u8, std::sync::atomic::Ordering::Relaxed);
    if let Some(dir) = &cli.std_dir
        && let Err(e) = stitchwort_elab::use_std_dir(dir)
    {
        eprintln!("error: {e}");
        return ExitCode::from(2);
    }
    // The standard library is setup, not program input: find it before any
    // work starts, so a missing or unreadable copy is one error, not a panic
    // from deep inside a check. `fmt` doesn't need it, and `lsp` reads it
    // once it is speaking to the editor, to report it there (see `serve`).
    if cli.command.needs_std()
        && let Err(e) = stitchwort_elab::load_std_text()
    {
        eprintln!("error: {e}");
        return ExitCode::from(2);
    }
    // A check may be ended from outside (`timeout`, Ctrl-C): say so and
    // exit with the status for "did not finish", rather than nothing at all
    // (SW-4032). Before any other thread starts, as `catch_signals` is.
    #[cfg(unix)]
    if matches!(&cli.command, Command::Check { .. }) {
        catch_check_signals();
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
    // `run --native` and `test --native` run native code on this thread,
    // whose stack must hold whatever the run sizes for its frames: up to
    // the cap (docs/proposals/native-only.md §3). Checking still uses only
    // `STACK` of it (`new_session`).
    let stack = match &cli.command {
        Command::Run { native: true, .. } | Command::Test { native: true, .. } => {
            stitchwort_host::NATIVE_STACK
        }
        _ => STACK,
    };
    if let Command::Check {
        timings: Some(shown),
        ..
    } = &cli.command
    {
        stitchwort_elab::timings::request(*shown);
    }
    let ran = stitchwort_host::try_with_stack(stack, move || {
        stitchwort_elab::timings::start();
        stitchwort_elab::progress::report_to(|note| eprintln!("note: {note}"));
        let code = run(cli);
        stitchwort_elab::timings::report();
        stitchwort_syntax::stack::probe::report_deepest();
        code
    });
    ran.unwrap_or_else(|e| {
        eprintln!("error: can't reserve a stack of {stack} bytes to run on: {e}");
        ExitCode::from(2)
    })
}

/// Runs `cli`'s command, each by a function of its own. Those that would be
/// inlined here are `#[inline(never)]`: inlined, every command's locals
/// shared one frame of 21 KiB, under whichever command ran (SW-3180).
fn run(cli: Cli) -> ExitCode {
    let std_dir_given = cli.std_dir.is_some();
    match cli.command {
        Command::Check {
            targets,
            std: true,
            warnings,
            cache,
            ..
        } => check_std(&targets, warnings, &cache),
        Command::Check {
            targets,
            std: false,
            project,
            warnings: _,
            index,
            only,
            expand_repeatedly,
            expand_walk,
            expand_facts,
            stdout,
            counterexamples,
            cache,
            carry_over,
            recheck,
            timings: _,
            jobs,
        } => check(
            &targets,
            project.as_deref(),
            index.as_deref(),
            &only,
            (expand_repeatedly, expand_walk, expand_facts, stdout),
            &counterexamples,
            &cache,
            (carry_over || carry_over_from_environment(), recheck),
            jobs_asked(jobs),
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
            only,
            json,
            std: true,
            ..
        } => test_std(
            target.as_deref().unwrap_or_default(),
            &TestOutput {
                only: only.as_deref(),
                json,
            },
        ),
        Command::Test {
            target,
            cache,
            project,
            reference,
            native,
            verbose,
            verify_cache,
            only,
            json,
            std: false,
        } => test(
            target.as_deref(),
            &cache,
            project.as_deref(),
            reference,
            native.then_some(verbose),
            verify_cache,
            &TestOutput {
                only: only.as_deref(),
                json,
            },
        ),
        Command::Run {
            target,
            js,
            reference,
            native,
            verbose,
            profile,
            profile_top,
            project,
            alloc_trace,
            cache,
            args,
        } => {
            stitchwort_rt::host::set_args(args);
            run_target(
                &target,
                js,
                reference,
                native.then_some(verbose),
                profile.then_some(profile_top),
                alloc_trace.as_deref(),
                project.as_deref(),
                &cache,
            )
        }
        Command::Axioms {
            target,
            names,
            project,
            cache,
        } => axioms(&target, &names, project.as_deref(), &cache),
        Command::Goal {
            targets,
            at,
            summary,
            json,
            project,
            cache,
        } => match (at, summary) {
            (Some(_), true) => {
                eprintln!("error: --summary counts each namespace's goals: it takes no --at");
                ExitCode::from(2)
            }
            (Some(at), false) => goal_at(&at, project.as_deref(), json, &cache),
            (None, true) => goal_summary(project.as_deref(), json, &cache),
            (None, false) => goal_list(&targets, project.as_deref(), json, &cache),
        },
        Command::Uses {
            names,
            unused,
            dead,
            root,
            json,
            project,
            cache,
        } => uses(
            &names,
            unused,
            dead,
            &root,
            json,
            project.as_deref(),
            &cache,
        ),
        Command::Search {
            query,
            file,
            project,
            rewrite,
            json,
            limit,
            all,
            theorems,
            definitions,
            constructors,
            within,
            log,
            at,
            goal,
            simplest_first,
            candidates,
            time,
            cache,
        } => {
            let log = log.or_else(|| std::env::var_os("STITCHWORT_SEARCH_LOG").map(PathBuf::from));
            if let Some(at) = at {
                if query.is_some() || file.is_some() {
                    eprintln!(
                        "error: --at takes no query or file: it searches for what closes the goal there"
                    );
                    return ExitCode::from(2);
                }
                let Some(time) = parse_duration(&time) else {
                    eprintln!("error: --time takes a time such as `10s` or `500ms`, not `{time}`");
                    return ExitCode::from(2);
                };
                let options = stitchwort_driver::search_at::AtOptions {
                    limit,
                    max_candidates: candidates,
                    time,
                    all,
                    exclude: Vec::new(),
                    within,
                    stop_after_closing: None,
                    simplest_first,
                };
                return search_at(
                    &at,
                    goal,
                    project.as_deref(),
                    &options,
                    json,
                    log.as_deref(),
                    &cache,
                );
            }
            let Some(query) = query else {
                eprintln!("error: give a query, or --at FILE:LINE for what closes the goal there");
                return ExitCode::from(2);
            };
            let narrowed = theorems || definitions || constructors;
            let options = stitchwort_driver::search::Options {
                rewrite,
                kinds: stitchwort_driver::search::Kinds {
                    theorems: theorems || !narrowed,
                    definitions: definitions || !narrowed,
                    constructors: constructors || !narrowed,
                },
                all,
                limit,
                within,
            };
            search(
                &query,
                file.as_deref(),
                project.as_deref(),
                &options,
                json,
                log.as_deref(),
                &cache,
            )
        }
        Command::Doc {
            name,
            file,
            more,
            coverage,
            list,
            project,
            json,
            theorems,
            cache,
        } => {
            let names: Vec<String> = (name.iter().cloned())
                .chain(file.iter().map(|f| f.display().to_string()))
                .chain(more)
                .collect();
            doc_cmd::doc(&doc_cmd::Args {
                name: name.as_deref().unwrap_or_default(),
                file: if coverage { None } else { file.as_deref() },
                coverage: coverage.then_some(&names[..]),
                project: project.as_deref(),
                json,
                list,
                theorems,
                cache: &cache,
            })
        }
        Command::Rename {
            target,
            new_name,
            anyway,
            dry_run,
            json,
            project,
            cache,
        } => rename_cmd::rename(&rename_cmd::Args {
            target: &target,
            new_name: &new_name,
            anyway,
            dry_run,
            json,
            project: project.as_deref(),
            cache: &cache,
        }),
        Command::TrialEdits {
            edits,
            same_statement,
            proofs_only,
            apply,
            anyway,
            json,
            std_before,
            project,
            cache,
        } => trial_cmd::trial_edits(&trial_cmd::TrialArgs {
            edits: edits.as_deref(),
            same_statement,
            proofs_only,
            apply,
            anyway,
            json,
            std_before: std_before.as_deref(),
            std_mode: std_dir_given,
            project: project.as_deref(),
            cache: &cache,
        }),
        Command::Sweep(SweepCommand::TheoremBinders {
            paths,
            std,
            files,
            std_root,
            dry_run,
            plan,
            json,
            keep,
            proofs_only,
            project,
            cache,
        }) => sweep_cmd::theorem_binders(&sweep_cmd::Args {
            paths: &paths,
            std,
            files,
            std_root: std_root.as_deref(),
            dry_run,
            plan,
            json,
            keep: &keep,
            proofs_only,
            project: project.as_deref(),
            cache: &cache,
        }),
        Command::Oracle(which) => {
            let (half, a) = match which {
                OracleCommand::Readings(a) => (oracle_sites::Half::Readings, a),
                OracleCommand::Builds(a) => (oracle_sites::Half::Builds, a),
            };
            oracle_cmd::run(&oracle_cmd::Args {
                half,
                paths: &a.paths,
                std: a.std,
                files: a.files,
                std_root: a.std_root.as_deref(),
                limit: a.limit,
                json: a.json,
                project: a.project.as_deref(),
                cache: &a.cache,
            })
        }
        Command::Hash {
            names,
            std,
            json,
            uses,
            warnings,
            project,
            cache,
        } => trial_cmd::hash(&trial_cmd::HashArgs {
            names: &names,
            std,
            json,
            uses,
            warnings,
            project: project.as_deref(),
            cache: &cache,
        }),
        Command::Audit {
            targets,
            json,
            strict,
            allowed_axioms,
            no_search,
            counterexample_budget,
            verbose,
            project,
            cache,
        } => audit(
            &targets,
            &AuditArgs {
                json,
                strict,
                allowed_axioms,
                no_search,
                counterexample_budget,
                verbose,
            },
            project.as_deref(),
            &cache,
        ),
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
            js: true,
            out,
            source_map,
            project,
            cache,
            ..
        } => build(
            &target,
            out.as_deref().unwrap_or(Path::new(".")),
            source_map,
            project.as_deref(),
            &cache,
        ),
        Command::Build {
            target,
            js: false,
            out,
            native,
            verbose,
            count_bodies,
            pc_map,
            project,
            cache,
            ..
        } => build::build_executable(
            &target,
            out.as_deref(),
            project.as_deref(),
            native.then_some(verbose),
            build::Profiling {
                count_bodies,
                pc_map,
            },
            &cache,
        ),
        Command::Dev(DevCommand::Tree {
            paths,
            expression: true,
            ..
        }) => expression_tree_command(&paths),
        Command::Dev(DevCommand::Tree {
            paths,
            print,
            time,
            parse_only,
            spans,
            ..
        }) => tree_command(&paths, print, time, parse_only, spans),
        Command::Dev(DevCommand::Breaks {
            paths,
            std,
            files,
            std_root,
            limit,
            worst,
            json,
            jsonl,
            project,
            cache,
        }) => breaks_cmd::run(&breaks_cmd::Args {
            paths: &paths,
            std,
            files,
            std_root: std_root.as_deref(),
            limit,
            worst,
            json,
            jsonl: jsonl.as_deref(),
            project: project.as_deref(),
            cache: &cache,
        }),
        Command::Dev(DevCommand::FmtTree { paths, print }) => fmt_tree_command(&paths, print),
        Command::Dev(DevCommand::Tokens { paths }) => tokens_command(&paths),
        Command::Dev(DevCommand::Passes { paths }) => passes_command(&paths),
        Command::Dev(DevCommand::Doc { paths }) => doc_command(&paths),
        Command::Dev(DevCommand::NativeSpike { rounds, memory }) => {
            native_spike(rounds, memory.as_deref())
        }
    }
}

#[cfg(feature = "native")]
#[inline(never)]
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
#[inline(never)]
fn native_spike(_rounds: u64, _memory: Option<&str>) -> ExitCode {
    eprintln!("error: this `stitchwort` was built without native code; build it with `task build`");
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

/// The exit status of a `check` that stopped before it finished: out of a
/// resource, or ended by a signal (SW-4032).
const STOPPED_EARLY: u8 = 3;

/// The first diagnostic saying a resource limit stopped the check before it
/// finished: evaluation steps, time, depth, or size. Other errors, including
/// an internal budget that gave up (`cases`, `rewrite repeatedly`, an
/// instance search), are ordinary failures of a check that finished.
fn stopped_early(diagnostics: &[Diagnostic]) -> Option<&Diagnostic> {
    diagnostics
        .iter()
        .find(|d| d.severity == Severity::Error && d.code == "E-RESOURCE")
}

/// Says in one line that `check` stopped before finishing, and why; `at` is
/// the declaration being checked, if known.
fn report_stopped_early(why: &str, at: Option<&str>) {
    match at {
        Some(at) => eprintln!("check stopped early: {why}, while checking {at}"),
        None => eprintln!("check stopped early: {why}"),
    }
}

/// [`report_stopped_early`] for a resource error: its message is why, and
/// its notes name the declaration (SW-843).
fn report_stopped_early_diagnostic(diagnostic: &Diagnostic) {
    let at = diagnostic
        .notes
        .iter()
        .find_map(|note| note.strip_prefix("it happened while checking "));
    report_stopped_early(&diagnostic.message, at);
}

/// For `check` only: catch the signal an outer `timeout` sends (and Ctrl-C,
/// `SIGHUP`, `SIGQUIT`), say on standard error that the check stopped
/// early, and exit 3 instead of ending with no report (SW-4032).
#[cfg(unix)]
fn catch_check_signals() {
    use nix::sys::signal::{SigSet, Signal};
    let mut set = SigSet::empty();
    for signal in [
        Signal::SIGINT,
        Signal::SIGTERM,
        Signal::SIGHUP,
        Signal::SIGQUIT,
    ] {
        set.add(signal);
    }
    if set.thread_block().is_err() {
        return;
    }
    let started = std::thread::Builder::new()
        .name("check-signals".into())
        .spawn(move || {
            let Ok(signal) = set.wait() else { return };
            report_stopped_early(
                &format!("stopped by {}", signal.as_str()),
                stitchwort_elab::progress::current().as_deref(),
            );
            std::process::exit(i32::from(STOPPED_EARLY));
        });
    if started.is_err() {
        // Without the thread nothing would see the signals: unblock them.
        let _ = set.thread_unblock();
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

/// `project`'s `stitchwort.yaml`, or `None` after reporting why it can't be
/// read.
fn read_project_config(project: &Project) -> Option<stitchwort_cli::project::Config> {
    let text = std::fs::read_to_string(project.dir.join("stitchwort.yaml")).unwrap_or_default();
    let mut sources = SourceMap::new();
    let id = sources.add("stitchwort.yaml", text.clone());
    match stitchwort_cli::project::parse_config(id, "stitchwort.yaml", &text) {
        Ok(config) => Some(config),
        Err(d) => {
            report(&sources, &[d]);
            None
        }
    }
}

/// "N goals open, allowed by `check: open-goals: warn`": the start of the
/// line `check` and the REPL print for a project that allows open goals.
fn open_goals_allowed(goals: usize) -> String {
    let s = if goals == 1 { "" } else { "s" };
    format!("{goals} goal{s} open, allowed by `check: open-goals: warn`")
}

/// The error lines of the summary (docs/proposals/tests-with-errors.md
/// §4.3): which declarations have an error, and which can't be checked
/// until one is fixed. Nothing for a project without errors.
fn report_errors(session: &Session) {
    let errors = session.errors();
    if !errors.has.is_empty() {
        let names: Vec<String> = (errors.has.iter().take(3))
            .map(|e| format!("`{}`", e.declaration))
            .collect();
        let shown = match (names.as_slice(), errors.has.len()) {
            ([one], _) => one.clone(),
            ([a, b], 2) => format!("{a} and {b}"),
            ([a, b, c], 3) => format!("{a}, {b} and {c}"),
            (names, n) => format!("{} and {} more", names.join(", "), n - names.len()),
        };
        let s = if errors.has.len() == 1 { "" } else { "s" };
        eprintln!("{} error{s}: in {shown}", errors.has.len());
    }
    let waiting = &errors.waiting;
    if !waiting.is_empty() {
        let s = if waiting.len() == 1 { "" } else { "s" };
        eprintln!(
            "{} declaration{s} can't be checked until an error is fixed:",
            waiting.len()
        );
        let width = waiting.iter().map(|w| w.name.len()).max().unwrap_or(0);
        const SHOWN: usize = 20;
        for w in waiting.iter().take(SHOWN) {
            eprintln!("  {:width$}  needs {}", w.name, w.needs.describe());
        }
        if waiting.len() > SHOWN {
            eprintln!("  and {} more", waiting.len() - SHOWN);
        }
    }
}

/// The goal count line, then what relies on the goals and what can't be
/// checked until they are filled (docs/proposals/using-unfinished-proofs.md
/// §5.1), after the goals themselves. `warn` is `check: open-goals: warn`,
/// which reports the goals as warnings that don't fail the check. Before
/// them, the error lines, and what relies on a declaration with an error
/// that stands in for its statement (docs/proposals/tests-with-errors.md
/// §4.3, D3527).
fn report_goals(session: &Session, reported: &[Diagnostic]) {
    use stitchwort_driver::reliance::{Dependent, GoalPlace, describe_goals, is_goal};
    report_errors(session);
    let goals = reported.iter().filter(|d| is_goal(d)).count();
    let stand_ins = (session.elab.assumptions().iter()).any(|a| session.elab.is_error_stand_in(*a));
    if goals == 0 && !stand_ins {
        return;
    }
    let reliance = session.reliance(reported);
    // Each dependent with only the gaps of one kind, if it has any.
    let of_kind = |list: &[Dependent], error: bool| -> Vec<Dependent> {
        (list.iter())
            .filter_map(|d| {
                let gaps: Vec<GoalPlace> = (d.goals.iter())
                    .filter(|g| g.is_error() == error)
                    .cloned()
                    .collect();
                (!gaps.is_empty()).then(|| Dependent {
                    name: d.name.clone(),
                    goals: gaps,
                })
            })
            .collect()
    };
    let rely = |n: usize| {
        if n == 1 {
            ("", "relies")
        } else {
            ("s", "rely")
        }
    };
    let list_blocked = |blocked: &[Dependent], needs: &dyn Fn(&[GoalPlace]) -> String| {
        let width = blocked.iter().map(|b| b.name.len()).max().unwrap_or(0);
        const SHOWN: usize = 20;
        for b in blocked.iter().take(SHOWN) {
            eprintln!("  {:width$}  needs {}", b.name, needs(&b.goals));
        }
        if blocked.len() > SHOWN {
            eprintln!(
                "  and {} more (`stitchwort goal` lists them)",
                blocked.len() - SHOWN
            );
        }
    };
    // What waits for an error is listed with the errors, above.
    let relying = of_kind(&reliance.relying, true).len();
    if relying > 0 {
        let (s, rely) = rely(relying);
        eprintln!(
            "{relying} declaration{s} {rely} on a declaration with an error, checked assuming \
             its statement"
        );
    }
    if goals > 0 {
        let allowed = reported
            .iter()
            .any(|d| d.severity == Severity::Warning && d.code == "GOAL");
        let s = if goals == 1 { "" } else { "s" };
        if allowed {
            eprintln!(
                "{}; `stitchwort audit` fails what relies on {}",
                open_goals_allowed(goals),
                if goals == 1 { "it" } else { "them" }
            );
        } else {
            eprintln!("{goals} goal{s} open");
        }
        let relying = of_kind(&reliance.relying, false).len();
        if relying > 0 {
            let (s, rely) = rely(relying);
            eprintln!(
                "{relying} declaration{s} {rely} on open goals, checked assuming they hold \
                 (`stitchwort goal` lists them)"
            );
        }
        let blocked = of_kind(&reliance.blocked, false);
        if !blocked.is_empty() {
            let s = if blocked.len() == 1 { "" } else { "s" };
            eprintln!(
                "{} declaration{s} can't be checked until a goal is filled (not checked at all):",
                blocked.len()
            );
            list_blocked(&blocked, &|gaps| describe_goals(gaps, true));
        }
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
    load_project_counting(
        session,
        project,
        target,
        Load::Everything,
        stitchwort_cli::project::OpenGoals::Fail,
        reported,
    )
    .is_some()
}

/// [`load_project_into`], giving the number of namespaces checked.
fn load_project_counting(
    session: &mut Session,
    project: &Project,
    target: &Target,
    load: Load,
    open_goals: stitchwort_cli::project::OpenGoals,
    reported: &mut Vec<Diagnostic>,
) -> Option<(usize, Option<TheoremCount>)> {
    match session.load_project_for(&project.files, &project.name, target, load) {
        Ok(loaded) => {
            reported.extend(std::mem::take(&mut session.warnings));
            if open_goals == stitchwort_cli::project::OpenGoals::Warn {
                for d in reported.iter_mut().filter(|d| d.severity == Severity::Goal) {
                    d.severity = Severity::Warning;
                }
            }
            report(&session.sources, reported);
            Some((loaded.checked.len(), loaded.theorems))
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

/// `check --std`: the library files and folders `targets` name, with what
/// they need, checked in full.
#[inline(never)]
fn check_std(targets: &[String], warnings: bool, cache: &CacheArgs) -> ExitCode {
    let mut session = new_session(false);
    if !warnings {
        use_cache(&mut session, cache, Path::new("."));
    }
    match session.elab.check_library_targets(targets) {
        Ok(files) => {
            let plural = if files.len() == 1 { "" } else { "s" };
            eprintln!("checked {} standard library file{plural}", files.len());
            if warnings {
                report_library_warnings(&session, &files);
            }
            discard(session);
            ExitCode::SUCCESS
        }
        Err(diagnostics) => {
            report(&session.sources, &diagnostics);
            let stopped = if let Some(diagnostic) = stopped_early(&diagnostics) {
                report_stopped_early_diagnostic(diagnostic);
                true
            } else {
                false
            };
            discard(session);
            if stopped {
                ExitCode::from(STOPPED_EARLY)
            } else {
                ExitCode::FAILURE
            }
        }
    }
}

/// `check --std --warnings`: each warning the library gave, then a count
/// by code and file. `named` are the library paths (`Nat/Arith.sw`) the
/// check named; the core is always included.
fn report_library_warnings(session: &Session, named: &[String]) {
    let styled = |name: &str| {
        name == "<prelude>"
            || name
                .strip_prefix("std/")
                .is_some_and(|path| named.iter().any(|n| n == path))
    };
    let mut all = session.library_warning_report(&styled);
    // The files the named ones need were elaborated too; theirs are for
    // their own check.
    all.retain(|d| {
        d.primary_span()
            .is_none_or(|s| styled(&session.sources.get(s.file).name))
    });
    all.sort_by_key(|d| {
        d.primary_span().map_or((String::new(), 0), |s| {
            (session.sources.get(s.file).name.clone(), s.start)
        })
    });
    report(&session.sources, &all);
    let mut counts: std::collections::BTreeMap<(String, String), usize> = Default::default();
    for d in &all {
        let file = d.primary_span().map_or_else(
            || "?".to_string(),
            |s| session.sources.get(s.file).name.clone(),
        );
        *counts.entry((d.code.to_string(), file)).or_default() += 1;
    }
    println!("code\tfile\tcount");
    for ((code, file), n) in &counts {
        println!("{code}\t{file}\t{n}");
    }
    eprintln!("{} library warning(s)", all.len());
}

#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn check(
    targets: &[String],
    project: Option<&Path>,
    index: Option<&str>,
    only: &[String],
    (expand, expand_walk, expand_facts, to_stdout): (bool, bool, bool, bool),
    counterexamples: &CounterexampleArgs,
    cache: &CacheArgs,
    (carry_over, recheck): (bool, bool),
    jobs: usize,
) -> ExitCode {
    if to_stdout && !expand_walk && !expand_facts {
        eprintln!("error: --stdout is only for --expand-walk and --expand-facts");
        return ExitCode::FAILURE;
    }
    let files = targets.iter().filter(|t| is_file_target(t)).count();
    if files > 0 && !only.is_empty() {
        eprintln!("error: --only names theorems of a project's namespaces, not of a file");
        return ExitCode::FAILURE;
    }
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
        let mut stopped = false;
        for path in targets {
            // Each file gets its own session.
            let mut session = new_session(index.is_some());
            if expand {
                session.elab.record_expansions();
            } else if !expand_walk && !expand_facts {
                use_cache(&mut session, cache, Path::new("."));
                session.elab.set_carry_over(carry_over);
                session.elab.set_recheck(recheck);
            }
            let mut reported = Vec::new();
            let loaded = load_file_into(
                &mut session,
                Path::new(path),
                Some("checked"),
                &mut reported,
            );
            let goals = goals_open(&reported);
            report_goals(&session, &reported);
            if let Some(diagnostic) = stopped_early(&reported) {
                report_stopped_early_diagnostic(diagnostic);
                stopped = true;
            }
            ok &= loaded && goals == 0;
            if loaded && goals == 0 {
                eprintln!("checked {path}");
            }
            report_carried_over(&session, recheck);
            if let Some(index) = index {
                ok = write_index(&session, loaded, index, "", &reported) && ok;
            }
            if counterexamples.counterexamples {
                ok = search_counterexamples(&mut session, counterexamples, &|_| true) && ok;
            }
            if expand && loaded {
                ok = write_expansions(&session, Path::new(".")) && ok;
            }
            if expand_walk {
                ok = write_walk_expansions(&session, Path::new("."), to_stdout) && ok;
            }
            if expand_facts {
                ok = write_facts_expansions(&session, Path::new("."), to_stdout) && ok;
            }
            discard(session);
        }
        return if stopped {
            ExitCode::from(STOPPED_EARLY)
        } else {
            exit(ok)
        };
    }
    let Some(project) = locate_project(project, "check", "check hello.sw") else {
        return ExitCode::FAILURE;
    };
    let target = if !only.is_empty() {
        Target::Theorems {
            namespaces: targets.to_vec(),
            only: only.to_vec(),
        }
    } else if targets.is_empty() {
        Target::Everything
    } else {
        Target::Namespaces(targets.to_vec())
    };
    let Some(config) = read_project_config(&project) else {
        return ExitCode::FAILURE;
    };
    let mut session = new_session(index.is_some());
    if expand {
        session.elab.record_expansions();
    } else if !expand_walk && !expand_facts {
        use_cache(&mut session, cache, &project.dir);
        session.elab.set_carry_over(carry_over);
        session.elab.set_recheck(recheck);
    }
    let mut filled = None;
    if jobs > 1 {
        // Quietly one job, so a default of more can't break these.
        let one = [
            (recheck, "--recheck re-checks every entry it loads"),
            (
                carry_over,
                "entries carried over make those after them inexact",
            ),
            (!only.is_empty(), "--only checks part of a namespace"),
            (
                cache.no_project_cache,
                "--no-project-cache writes no namespace entries",
            ),
            (
                expand || expand_walk || expand_facts,
                "the --expand options check without the cache",
            ),
            (cache.no_cache && !PARALLEL_NO_CACHE, "--no-cache"),
        ];
        match one.iter().find(|(why, _)| *why) {
            Some((_, why)) => stitchwort_elab::timings::jobs(1, Some(format!("one job: {why}"))),
            None => {
                let navigation = index.is_some();
                let fill =
                    fill_in_parallel(&mut session, &project, &target, jobs, navigation, cache);
                filled = Some(fill);
            }
        }
    }
    let mut reported = Vec::new();
    // Only the diagnostics are wanted, unless the loaded namespaces are
    // indexed or searched.
    let load = if index.is_none() && !counterexamples.counterexamples {
        Load::Diagnostics
    } else {
        Load::Everything
    };
    let load = filled.map_or(load, |fill| fill.load_after(load));
    // For measuring a load without proofs (parallel-checking.md §10.6,
    // `measure_load.sh`) before a plain check does it itself: what it
    // reports over a namespace with an error may differ in a note's text.
    if load == Load::Diagnostics
        && std::env::var_os("STITCHWORT_LOAD_PROOFS").is_some_and(|v| v == "0")
    {
        session.elab.set_load_without_proofs(true);
    }
    let checked = load_project_counting(
        &mut session,
        &project,
        &target,
        load,
        config.open_goals,
        &mut reported,
    );
    let goals = goals_open(&reported);
    report_goals(&session, &reported);
    let stopped = if let Some(diagnostic) = stopped_early(&reported) {
        report_stopped_early_diagnostic(diagnostic);
        true
    } else {
        false
    };
    let mut ok = checked.is_some() && goals == 0;
    if let (true, Some((count, theorems))) = (ok, checked) {
        let plural = if count == 1 { "" } else { "s" };
        match theorems {
            Some(t) if t.checked < t.total => eprintln!(
                "checked {} of {} theorems of the namespaces named: the other {} were NOT \
                 checked ({count} namespace{plural} of {} loaded)",
                t.checked,
                t.total,
                t.total - t.checked,
                project.name
            ),
            Some(t) => eprintln!(
                "checked {} of {} theorems of the namespaces named: all of them were needed \
                 ({count} namespace{plural} of {} loaded)",
                t.checked, t.total, project.name
            ),
            None => eprintln!("checked {count} namespace{plural} of {}", project.name),
        }
    }
    report_carried_over(&session, recheck);
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
    if expand && ok {
        ok = write_expansions(&session, &project.dir) && ok;
    }
    if expand_walk {
        ok = write_walk_expansions(&session, &project.dir, to_stdout) && ok;
    }
    if expand_facts {
        ok = write_facts_expansions(&session, &project.dir, to_stdout) && ok;
    }
    discard(session);
    if stopped {
        ExitCode::from(STOPPED_EARLY)
    } else {
        exit(ok)
    }
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
    // Without --verbose: the counterexamples, and the theorems that checked
    // though no input made their hypotheses true, which may be vacuous (T2
    // of docs/research/agentic-proving.md).
    let shown = |search: &stitchwort_cli::counterexample::TheoremSearch, verdict: Verdict| {
        args.verbose
            || verdict == Verdict::False
            || (verdict == Verdict::NeverHeld && search.checked && !search.refutes)
    };
    let width = searches
        .iter()
        .zip(&verdicts)
        .filter(|(s, (v, _))| shown(s, *v))
        .map(|(s, _)| s.name.len())
        .max()
        .unwrap_or(0);
    let mut counts = [0usize; 6];
    // Of those with none found, how many on weak evidence (SW-903).
    let mut weak = 0;
    for (search, (verdict, line)) in searches.iter().zip(verdicts) {
        counts[verdict as usize] += 1;
        if verdict == Verdict::NoneFound && search.weak_evidence().is_some() {
            weak += 1;
        }
        if !shown(search, verdict) {
            continue;
        }
        let mark = match verdict {
            Verdict::False => "✗",
            Verdict::NoneFound => "~",
            Verdict::NeverHeld if search.checked && !search.refutes => "!",
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
    let [false_, none, never, gave_up, inconclusive, not_applicable] = counts;
    // Those whose hypotheses never held gave up too: said apart (T2).
    let gave_up = gave_up + never;
    let never = if never > 0 {
        format!(" ({never} with the hypotheses true in no case)")
    } else {
        String::new()
    };
    let weak = if weak > 0 {
        format!(" ({weak} on weak evidence)")
    } else {
        String::new()
    };
    eprintln!(
        "searched {total} theorem{} for counterexamples: {false_} false, {none} with none \
         found{weak}, {gave_up} gave up{never}, {inconclusive} inconclusive, {not_applicable} not \
         applicable",
        if total == 1 { "" } else { "s" }
    );
    false_ == 0
}

/// Ends with a session that's no longer needed without freeing it: the
/// process is about to exit, which frees everything at once, and taking a
/// checked project's terms and values apart one by one took about 2% of a
/// `check` (docs/proposals/proof-check-speed.md). Nothing in a session
/// needs dropping to be written out (the caches are written as they go).
/// `check --expand-repeatedly`: writes back each file with a `rewrite
/// repeatedly` checked, each call replaced by its `rewrite` steps
/// ([`stitchwort_elab::expansion_text`]); a file's name is read from `base`
/// if it isn't found as it is. Whether every call was expanded.
fn write_expansions(session: &Session, base: &Path) -> bool {
    let expansions = session.elab.take_expansions();
    let mut ok = true;
    for (file, source) in session.sources.iter() {
        if !expansions.iter().any(|e| e.call.file == file) {
            continue;
        }
        let (text, done, refused) = stitchwort_elab::expand_file(&source.text, file, &expansions);
        for (offset, why) in refused {
            let line = source.text[..offset].matches('\n').count() + 1;
            eprintln!("{}:{line}: not expanded: {why}", source.name);
            ok = false;
        }
        // A project's files are named from the folder above it.
        let name = Path::new(&source.name);
        let path = [
            Some(name.to_path_buf()),
            Some(base.join(name)),
            base.parent().map(|p| p.join(name)),
        ]
        .into_iter()
        .flatten()
        .find(|p| p.exists())
        .unwrap_or_else(|| name.to_path_buf());
        if let Err(e) = std::fs::write(&path, text) {
            eprintln!("error: can't write {}: {e}", path.display());
            return false;
        }
        let plural = if done == 1 { "" } else { "s" };
        eprintln!("expanded {done} call{plural} in {}", path.display());
    }
    ok
}

/// `check --expand-walk`: writes back each file with a walk checked, each
/// replaced by the chain it stands for
/// ([`stitchwort_elab::expand_walk_file`]), and prints each walk's trace.
/// With `to_stdout`, prints the expanded text on standard output instead of
/// writing it, and puts the trace on standard error. A file's name is read
/// from `base` if it isn't found as it is.
fn write_walk_expansions(session: &Session, base: &Path, to_stdout: bool) -> bool {
    let expansions = session.elab.take_walk_expansions();
    for (file, source) in session.sources.iter() {
        let mine: Vec<_> = expansions.iter().filter(|e| e.span.file == file).collect();
        if mine.is_empty() {
            continue;
        }
        for e in &mine {
            let line = source.text[..e.span.range().start].matches('\n').count() + 1;
            let header = format!("{}:{line}: walk", source.name);
            if to_stdout {
                eprintln!("{header}");
            } else {
                println!("{header}");
            }
            for step in &e.trace {
                let step = stitchwort_elab::walk_trace_line(&source.text, step);
                if to_stdout {
                    eprintln!("  {step}");
                } else {
                    println!("  {step}");
                }
            }
        }
        let (text, done) = stitchwort_elab::expand_walk_file(&source.text, file, &expansions);
        let plural = if done == 1 { "" } else { "s" };
        if to_stdout {
            print!("{text}");
            eprintln!("expanded {done} walk{plural} in {}", source.name);
            continue;
        }
        let name = Path::new(&source.name);
        let path = [
            Some(name.to_path_buf()),
            Some(base.join(name)),
            base.parent().map(|p| p.join(name)),
        ]
        .into_iter()
        .flatten()
        .find(|p| p.exists())
        .unwrap_or_else(|| name.to_path_buf());
        if let Err(e) = std::fs::write(&path, text) {
            eprintln!("error: can't write {}: {e}", path.display());
            return false;
        }
        eprintln!("expanded {done} walk{plural} in {}", path.display());
    }
    true
}

/// `check --expand-facts`: writes back each file with a `byFacts` checked,
/// each replaced by the term it found ([`stitchwort_elab::expand_walk_file`],
/// which writes the pieces). With `to_stdout`, prints the expanded text on
/// standard output instead, leaving the file unchanged.
fn write_facts_expansions(session: &Session, base: &Path, to_stdout: bool) -> bool {
    let (expansions, kept) = session.elab.take_facts_expansions();
    for (file, source) in session.sources.iter() {
        for (span, why) in kept.iter().filter(|(s, _)| s.file == file) {
            let line = source.text[..span.start as usize].matches('\n').count() + 1;
            eprintln!("{}:{line}: not expanded: {why}", source.name);
        }
        let listed = to_stdout && kept.iter().any(|(s, _)| s.file == file);
        if !listed && !expansions.iter().any(|e| e.span.file == file) {
            continue;
        }
        let (text, done) = stitchwort_elab::expand_walk_file(&source.text, file, &expansions);
        let plural = if done == 1 { "" } else { "s" };
        if to_stdout {
            print!("{text}");
            eprintln!("expanded {done} byFacts call{plural} in {}", source.name);
            continue;
        }
        let name = Path::new(&source.name);
        let path = [
            Some(name.to_path_buf()),
            Some(base.join(name)),
            base.parent().map(|p| p.join(name)),
        ]
        .into_iter()
        .flatten()
        .find(|p| p.exists())
        .unwrap_or_else(|| name.to_path_buf());
        if let Err(e) = std::fs::write(&path, text) {
            eprintln!("error: can't write {}: {e}", path.display());
            return false;
        }
        eprintln!("expanded {done} byFacts call{plural} in {}", path.display());
    }
    true
}

/// After `check --carry-over`: how many units came from entries carried over
/// from another build, which this build's elaborator didn't check
/// (docs/proposals/check-cache-across-updates.md §8: the label is the whole
/// defence against taking such a check for a full one). Then, after a
/// carry-over across a kernel change or `check --recheck`, how many entries
/// this kernel checked again, and refused (with `recheck`, always a line).
fn report_carried_over(session: &Session, recheck: bool) {
    let stats = session.elab.check_cache_stats();
    if let Some(units) = stats.carried_over_units() {
        eprintln!(
            "carried over from another build: {units}; this kernel accepted them, but this \
             build didn't elaborate them (a check without --carry-over does)"
        );
    }
    match stats.rechecked_units() {
        Some(units) => eprintln!("checked again by this kernel, without elaborating: {units}"),
        // So that `--recheck` with nothing to check (no cache, an empty
        // one) doesn't look like an audit that passed.
        None if recheck => eprintln!("checked again by this kernel: nothing"),
        None => {}
    }
}

/// `check --jobs N` (docs/proposals/parallel-checking.md §9): fills the
/// check cache `session` uses with `jobs` workers, before `session` checks
/// `target` as usual. With `--no-cache`, if the workers ran, `session` is
/// given the run's store in memory, which they filled.
fn fill_in_parallel(
    session: &mut Session,
    project: &Project,
    target: &Target,
    jobs: usize,
    navigation: bool,
    cache: &CacheArgs,
) -> stitchwort_driver::parallel::Fill {
    use stitchwort_driver::check_cache::{CheckCache, MemoryStore};
    use stitchwort_elab::cache::Store;
    let memory = cache.no_cache.then(MemoryStore::default);
    let dir = cache_dir(cache, &project.dir);
    let make_store = || -> std::rc::Rc<dyn Store> {
        match (&memory, &dir) {
            (Some(memory), _) => std::rc::Rc::new(memory.clone()),
            (None, Some(dir)) => std::rc::Rc::new(CheckCache::at(dir)),
            (None, None) => unreachable!("a cache directory unless --no-cache"),
        }
    };
    let seed = std::env::var("STITCHWORT_JOBS_SEED")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok());
    let make_session = move |_: usize| new_session(navigation);
    let fill = stitchwort_driver::parallel::fill(
        &project.files,
        &project.name,
        target,
        &stitchwort_driver::parallel::Jobs {
            count: jobs,
            stack: STACK,
            make_session: &make_session,
            make_store: &make_store,
            seed,
        },
    );
    let note = if fill.ran {
        format!(
            "{} workers: {} namespaces had entries, {} filled, {} left to the check after; \
             {} dependencies elaborated again, {} entries refused, {} late misses, \
             {} waits for a library file given up",
            fill.workers,
            fill.found,
            fill.filled,
            fill.left,
            fill.twice,
            fill.stats.refused,
            fill.stats.late_misses,
            fill.claims_gave_up
        )
    } else {
        "one job: fewer than two namespaces to check".to_string()
    };
    stitchwort_elab::timings::jobs(fill.workers.max(1), Some(note));
    // Only after a fill is there anything in it for the check to find;
    // otherwise it would encode entries for nothing.
    if let (true, Some(memory)) = (fill.ran, &memory) {
        session
            .elab
            .set_check_cache(std::rc::Rc::new(memory.clone()));
    }
    fill
}

/// Whether `STITCHWORT_CARRY_OVER=1` turns carrying over on: only when
/// standard error is a terminal, where the label is seen. A variable
/// exported in a shell or a task would otherwise reach the verifier, the
/// tiers and the rolling check, which must stay exact, with nothing in
/// their commands to show it; scripts and agents pass `--carry-over`.
fn carry_over_from_environment() -> bool {
    use std::io::IsTerminal;
    std::env::var("STITCHWORT_CARRY_OVER").is_ok_and(|v| v == "1")
        && std::io::stderr().is_terminal()
}

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
        if cache.no_project_cache {
            session.use_library_check_cache(&dir);
        } else {
            session.use_check_cache(&dir);
        }
    }
}

/// The test results' cache.
fn test_cache(cache: &CacheArgs, base: &Path) -> Cache {
    cache_dir(cache, base).map_or_else(Cache::disabled, Cache::at)
}

/// Reports what `--verify-cache` found; whether there was no disagreement.
fn verified(cache: &Cache) -> bool {
    let Some(v) = cache.verification() else {
        return true;
    };
    for d in &v.disagreements {
        let show = |o: Outcome| match o {
            Outcome::Passed => "passed",
            Outcome::Failed => "failed",
            Outcome::OutOfResources(_) => "unfinished",
        };
        eprintln!(
            "error: cache disagrees with a fresh run: {}.{} (hash {}): cached {}, fresh {}",
            d.namespace,
            d.name,
            d.hash.hex(),
            show(d.cached),
            show(d.fresh)
        );
    }
    println!(
        "verified the cache: {} compared, {} had no cached result, {} disagree",
        v.compared,
        v.missing,
        v.disagreements.len()
    );
    // A cache that knows nothing about this build (a fresh binary's first
    // run) verifies nothing, and saying so is not a pass.
    if v.compared == 0 && v.missing > 0 {
        let tests = if v.missing == 1 { "test" } else { "tests" };
        eprintln!(
            "error: the cache was empty for this binary: {} {tests} had no cached result, so \
             there was nothing to compare; run `stitchwort test` first (or `task \
             test:verify-cache`, which fills the cache)",
            v.missing
        );
        return false;
    }
    v.disagreements.is_empty()
}

/// What `test` runs and how it prints: `--only` and `--json`.
struct TestOutput<'a> {
    only: Option<&'a str>,
    json: bool,
}

impl TestOutput<'_> {
    /// Prints the results, as text or as JSON. `asked_for_some`: the run
    /// named what to test (`--only`, a namespace), so no results is a failure.
    fn print(
        &self,
        session: &Session,
        results: &[TestResult],
        grouped: bool,
        asked_for_some: bool,
        errors: usize,
    ) -> ExitCode {
        if self.json {
            print_tests_json(session, results, asked_for_some, errors)
        } else {
            print_tests(results, grouped)
        }
    }
}

#[inline(never)]
fn test(
    target: Option<&str>,
    cache: &CacheArgs,
    project: Option<&Path>,
    reference: bool,
    native: Option<bool>,
    verify_cache: bool,
    output: &TestOutput,
) -> ExitCode {
    #[cfg(not(feature = "native"))]
    if native.is_some() {
        eprintln!(
            "error: this `stitchwort` was built without native code; build it with `task build`"
        );
        return ExitCode::FAILURE;
    }
    let mut session = new_session(false);
    let test_cache = |cache: &CacheArgs, base: &Path| {
        let cache = test_cache(cache, base);
        if verify_cache {
            cache.verifying()
        } else {
            cache
        }
    };
    // Whatever checks runs, also when a declaration has errors: a test that
    // uses one fails, saying so (D3523).
    let run_tests = |session: &Session, cache: &Cache, file: Option<&str>| {
        let in_file = |span: stitchwort_syntax::Span| {
            file.is_none_or(|name| session.sources.get(span.file).name.as_str() == name)
        };
        let keep = |test: &stitchwort_elab::TestDecl| {
            output.only.is_none_or(|n| n == test.name) && in_file(test.span)
        };
        let results = if reference {
            session.run_tests_where(cache, keep)
        } else {
            #[cfg(feature = "native")]
            let results = match native {
                Some(verbose) => {
                    let native = NativeTestCompiler { verbose };
                    session.run_tests_native_where(cache, keep, &native)
                }
                None => session.run_tests_fast_where(cache, keep),
            };
            #[cfg(not(feature = "native"))]
            let results = session.run_tests_fast_where(cache, keep);
            results
        };
        session.with_broken_tests_where(results, |test| {
            output.only.is_none_or(|n| n == test.name) && in_file(test.span)
        })
    };
    // A file target that is a source file of a project is tested in the
    // project (SW-3390); a file on its own stays file mode.
    let mut project_file = None;
    if let Some(file) = target.filter(|t| is_file_target(t)) {
        match project_of_file(Path::new(file), project) {
            Ok(Some((dir, relative, namespace))) => {
                project_file = Some((
                    Project {
                        name: project_name(&dir),
                        files: DiskFiles { root: dir.clone() },
                        dir,
                    },
                    relative,
                    namespace,
                ));
            }
            Ok(None) => {}
            Err(message) => {
                eprintln!("error: {message}");
                return ExitCode::FAILURE;
            }
        }
    }
    match target {
        Some(file) if project_file.is_none() && is_file_target(file) => {
            use_cache(&mut session, cache, Path::new("."));
            let mut reported = Vec::new();
            let loaded =
                load_file_into(&mut session, Path::new(file), Some("tested"), &mut reported);
            if !loaded && !something_checked(&session) {
                return ExitCode::FAILURE;
            }
            let cache = test_cache(cache, Path::new("."));
            let results = run_tests(&session, &cache, None);
            let errors = session.errors().has.len().max(usize::from(!loaded));
            let code = output.print(&session, &results, false, output.only.is_some(), errors);
            let code = if verified(&cache) {
                code
            } else {
                ExitCode::FAILURE
            };
            // The tests of unfinished declarations aren't checked, so they
            // didn't run.
            let goals = goals_open(&reported);
            report_goals(&session, &reported);
            discard(session);
            let none = output.only.is_some_and(|name| {
                let none = results.is_empty();
                if none {
                    eprintln!("warning: no test is called '{name}'");
                }
                none
            });
            if goals > 0 || none || !loaded {
                ExitCode::FAILURE
            } else {
                code
            }
        }
        _ => {
            let (project, target, target_name, file) = match project_file {
                Some((project, relative, namespace)) => {
                    let target = match namespace {
                        Some(namespace) => Target::Namespaces(vec![namespace]),
                        None => Target::Everything,
                    };
                    let display = format!("{}/{}", project.name, relative);
                    (project, target, None, Some(display))
                }
                None => {
                    let Some(project) = locate_project(project, "test", "test hello.sw") else {
                        return ExitCode::FAILURE;
                    };
                    let target_name = target.map(str::to_string);
                    let target = match target {
                        Some(name) => Target::Subtrees(vec![name.to_string()]),
                        None => Target::Everything,
                    };
                    (project, target, target_name, None)
                }
            };
            let Some(config) = read_project_config(&project) else {
                return ExitCode::FAILURE;
            };
            use_cache(&mut session, cache, &project.dir);
            let mut reported = Vec::new();
            let loaded = load_project_counting(
                &mut session,
                &project,
                &target,
                Load::Everything,
                config.open_goals,
                &mut reported,
            )
            .is_some();
            if !loaded && !something_checked(&session) {
                return ExitCode::FAILURE;
            }
            let cache = test_cache(cache, &project.dir);
            let results = run_tests(&session, &cache, file.as_deref());
            let errors = session.errors().has.len().max(usize::from(!loaded));
            let code = output.print(
                &session,
                &results,
                true,
                output.only.is_some() || target_name.is_some(),
                errors,
            );
            let code = if verified(&cache) {
                code
            } else {
                ExitCode::FAILURE
            };
            let goals = goals_open(&reported);
            report_goals(&session, &reported);
            discard(session);
            // A target that matched no tests (a typo, a namespace without
            // any) must never look like a pass.
            let none = match (target_name.as_deref(), output.only) {
                (_, Some(name)) if results.is_empty() => {
                    eprintln!("warning: no test is called '{name}'");
                    true
                }
                (Some(name), _) if results.is_empty() => {
                    eprintln!("warning: no tests matched '{name}'");
                    true
                }
                _ => false,
            };
            if goals > 0 || none || !loaded {
                ExitCode::FAILURE
            } else {
                code
            }
        }
    }
}

/// `test --std`: the tests declared in the library files `target` names,
/// not those of the files they need. The library is checked in full
/// without the check cache (it skips a file's tests), which the tests of
/// library files need.
#[inline(never)]
fn test_std(target: &str, output: &TestOutput) -> ExitCode {
    let mut session = new_session(false);
    session.elab.options.library_tests = true;
    let files = match session.elab.check_library_targets(&[target.to_string()]) {
        Ok(files) => files,
        Err(diagnostics) => {
            report(&session.sources, &diagnostics);
            discard(session);
            return ExitCode::FAILURE;
        }
    };
    let named: BTreeSet<String> = files.iter().map(|f| format!("std/{f}")).collect();
    let keep = |test: &stitchwort_elab::TestDecl| {
        output.only.is_none_or(|n| n == test.name)
            && named.contains(session.sources.get(test.span.file).name.as_str())
    };
    let results = session.run_library_tests_where(&Cache::disabled(), keep);
    let code = output.print(&session, &results, true, true, 0);
    discard(session);
    if results.is_empty() {
        match output.only {
            Some(name) => eprintln!("warning: no test is called '{name}'"),
            None => eprintln!("warning: no tests in '{target}'"),
        }
        return ExitCode::FAILURE;
    }
    code
}

/// Whether a load that failed still checked some tests, which then run
/// (D3523): the errors are reported, and the run still fails.
fn something_checked(session: &Session) -> bool {
    !session.elab.tests().is_empty() || !session.elab.broken_tests().is_empty()
}

/// `test --native`'s compiler (`stitchwort_driver::test_run::NativeTests`):
/// the tests' program compiled as `run --native` compiles `main`'s, with
/// each test a way in.
#[cfg(feature = "native")]
struct NativeTestCompiler {
    verbose: bool,
}

#[cfg(feature = "native")]
impl stitchwort_driver::test_run::NativeTests for NativeTestCompiler {
    fn compile(
        &self,
        program: &stitchwort_rt::Program,
        roots: &[u32],
        limits: stitchwort_rt::Limits,
    ) -> Result<stitchwort_driver::test_run::NativeTestCode, Vec<String>> {
        let image = stitchwort_rt::code::compile(program);
        let islands = stitchwort_native::n1::compile_roots(
            program,
            image,
            roots,
            stitchwort_native::n1::Options::default(),
        )?;
        let limits = limits.for_native(islands.max_frame);
        let stack = stitchwort_native::n1::stack_for(
            limits.frames as u64,
            islands.max_frame,
            &islands.widest,
        )?;
        // The thread's stack is the cap (`main`), so whatever this sizes fits.
        debug_assert!(stack <= stitchwort_host::NATIVE_STACK);
        let summary = format!(
            "native: compiled {} test(s), {} bodies (frames of at most {} bytes, in {:.1} ms)",
            roots.len(),
            islands.bodies,
            islands.max_frame,
            islands.compile_time.as_secs_f64() * 1000.0
        );
        Ok(stitchwort_driver::test_run::NativeTestCode {
            code: Box::new(islands),
            stack,
            limits,
            summary,
        })
    }

    fn note(&self, line: &str) {
        if self.verbose {
            eprintln!("{line}");
        }
    }
}

/// Prints the results as `test --json` describes: one JSON object, with
/// where each test is declared and, for a failure, the message an editor
/// shows and the sides it compares.
fn print_tests_json(
    session: &Session,
    results: &[TestResult],
    asked_for_some: bool,
    errors: usize,
) -> ExitCode {
    let tests: Vec<serde_json::Value> = results
        .iter()
        .map(|r| {
            let (outcome, message) = match r.outcome {
                Outcome::Passed => ("passed", None),
                Outcome::Failed => {
                    let message = match (&r.unfinished, r.detail.as_ref()) {
                        (Some(why), _) => why.clone(),
                        (None, Some(d)) => match d.comparison.as_ref() {
                            Some(c) => format!("`{}` is False", c.op),
                            None => "evaluated to False".to_string(),
                        },
                        (None, None) => "evaluated to False".to_string(),
                    };
                    ("failed", Some(message))
                }
                Outcome::OutOfResources(e) => ("unfinished", Some(format!("no result: {e}"))),
            };
            let at = session.test_location(&r.namespace, &r.name);
            let mut test = serde_json::json!({
                "namespace": r.namespace,
                "name": r.name,
                "outcome": outcome,
                "cached": r.cached,
                "file": at.as_ref().map(|a| a.file.clone()),
                "line": at.as_ref().map(|a| a.line),
                "column": at.as_ref().map(|a| a.column),
                "message": message,
                "assuming": r.assuming,
            });
            if let Some(detail) = &r.detail {
                let part = detail.part.as_ref().map(|p| {
                    serde_json::json!({
                        "text": p.text, "file": p.file, "line": p.line, "column": p.column,
                    })
                });
                let comparison = detail.comparison.as_ref().map(|c| {
                    serde_json::json!({
                        "op": c.op,
                        "left": c.left_lines.as_ref().unwrap_or(&c.left),
                        "right": c.right_lines.as_ref().unwrap_or(&c.right),
                        "difference": c.difference,
                    })
                });
                test["failure"] = serde_json::json!({"part": part, "comparison": comparison});
            }
            test
        })
        .collect();
    let ok = results.iter().all(|r| r.outcome == Outcome::Passed)
        && !(asked_for_some && results.is_empty())
        && errors == 0;
    println!(
        "{}",
        serde_json::json!({"ok": ok, "errors": errors, "tests": tests})
    );
    exit(ok)
}

/// `  (assuming `a`, `b`)`, the gaps a passing test relies on (SW-2939,
/// D3525): open goals by name, a declaration with an error as "`x`, which
/// has an error (place)"; the first three, then "and N more". Empty for
/// none.
fn assuming_note(gaps: &[stitchwort_driver::reliance::GoalPlace]) -> String {
    if gaps.is_empty() {
        return String::new();
    }
    let mut parts: Vec<String> = (gaps.iter().take(3))
        .map(|g| match g.is_error() {
            true => g.describe(false),
            false => format!("`{}`", g.short()),
        })
        .collect();
    if gaps.len() > 3 {
        parts.push(format!("and {} more", gaps.len() - 3));
    }
    format!("  (assuming {})", parts.join(", "))
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
        let (mark, how, why) = match result.outcome {
            Outcome::Passed => (
                "✓",
                if result.cached { "cached" } else { "ran" },
                assuming_note(&result.assuming),
            ),
            Outcome::Failed => (
                "✗",
                // A test with `unfinished` never ran: its code reaches an
                // open goal, or uses a declaration with an error.
                if result.unfinished.is_some() {
                    "not run"
                } else if result.cached {
                    "cached"
                } else {
                    "ran"
                },
                match (&result.unfinished, result.detail.as_ref()) {
                    (Some(why), _) => format!("  ({why})"),
                    (None, Some(d)) => {
                        let shown = match d.comparison.as_ref() {
                            Some(c) => format!("  (`{}` is False)", c.op),
                            None => "  (evaluated to False)".to_string(),
                        };
                        shown + &assuming_note(&result.assuming)
                    }
                    (None, None) => {
                        "  (evaluated to False)".to_string() + &assuming_note(&result.assuming)
                    }
                },
            ),
            Outcome::OutOfResources(e) => (
                "!",
                if result.cached { "cached" } else { "ran" },
                format!("  (no result: {e})") + &assuming_note(&result.assuming),
            ),
        };
        println!("  {mark} {:width$}  {how}{why}", result.name);
        if let Some(detail) = &result.detail {
            if let Some(c) = &detail.comparison {
                // A text of several lines is shown as its lines, under the label.
                let side = |label: &str, shown: &str, lines: &Option<String>| match lines {
                    Some(lines) => println!("      {label} {}", lines.replace('\n', "\n        ")),
                    None => println!("      {label} {shown}"),
                };
                side("left: ", &c.left, &c.left_lines);
                side("right:", &c.right, &c.right_lines);
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
        "{} test(s): {passed} passed, {failed} failed{unfinished_note} \
         ({cached} from the cache)",
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
) -> Result<(Session, Main, usize), ExitCode> {
    let mut session = new_session(false);
    let goals;
    let main = if is_file_target(target) {
        use_cache(&mut session, cache, Path::new("."));
        let mut reported = Vec::new();
        if !load_file_into(&mut session, Path::new(target), Some("run"), &mut reported) {
            return Err(ExitCode::FAILURE);
        }
        // What's finished can run; `main` can't if it isn't (`Session::main`).
        goals = goals_open(&reported);
        report_goals(&session, &reported);
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
                goals = goals_open(&reported);
                report_goals(&session, &reported);
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
    Ok((session, main, goals))
}

/// `run`: a file's `main`, or a function of the project by its full name.
#[allow(clippy::too_many_arguments)] // one per `run` option
#[inline(never)]
fn run_target(
    target: &str,
    js: bool,
    reference: bool,
    native: Option<bool>,
    profile: Option<usize>,
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
            "error: this `stitchwort` was built without native code; build it with `task build`"
        );
        return ExitCode::FAILURE;
    }
    let runner = match native {
        Some(verbose) => Runner::Native {
            verbose,
            trace: alloc_trace.is_some(),
        },
        None if reference => Runner::Reference,
        None if profile.is_some() => Runner::Profile {
            top: profile.unwrap_or_default(),
        },
        None => Runner::Machine,
    };
    let (mut session, main, _) = match load_main(target, project, cache) {
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
    let (session, main, _) = match load_main(target, project, cache) {
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
    let is_std = |name: &str| name.starts_with("Std.");
    println!(
        "  of which the standard library's: {} of {} reachable",
        fitting.iter().filter(|(name, _)| is_std(name)).count(),
        census.bodies.iter().filter(|b| is_std(&b.name)).count()
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

/// `axioms`: loads the file or project, finds the definitions and prints
/// the axioms each depends on (`stitchwort_driver::axioms`). One name is
/// reported plainly; several, each under its own heading.
#[inline(never)]
fn axioms(target: &str, names: &[String], project: Option<&Path>, cache: &CacheArgs) -> ExitCode {
    let mut session = new_session(false);
    let keys: Vec<&str> = if is_file_target(target) {
        if names.is_empty() {
            eprintln!(
                "error: name the definitions to report on: `stitchwort axioms {target} NAME...`"
            );
            return ExitCode::FAILURE;
        }
        use_cache(&mut session, cache, Path::new("."));
        if !load_file(&mut session, Path::new(target), None) {
            return ExitCode::FAILURE;
        }
        names.iter().map(String::as_str).collect()
    } else {
        let Some(project) = locate_project(project, "report on", "axioms hello.sw NAME") else {
            return ExitCode::FAILURE;
        };
        use_cache(&mut session, cache, &project.dir);
        if !load_project(&mut session, &project, &Target::Everything) {
            return ExitCode::FAILURE;
        }
        std::iter::once(target)
            .chain(names.iter().map(String::as_str))
            .collect()
    };
    session.elab.leave_namespace();
    let mut ids = Vec::new();
    for key in &keys {
        if let Some(owner) = session.elab.proof_private_to(key) {
            eprintln!(
                "error: `{key}` is defined inside the proof of `{owner}` and can be used only \
                 there (E-PROOF-PRIVATE)"
            );
            return ExitCode::FAILURE;
        }
        let Some(id) = session.elab.lookup_def(key) else {
            eprintln!("error: there's no definition `{key}`");
            return ExitCode::FAILURE;
        };
        // Checked assuming open goals hold is reported below; what wasn't
        // checked has no terms to walk.
        if session.elab.is_unfinished(id)
            && (!session.elab.relies_on_goal(id)
                || session.elab.ev().def(id).state() != stitchwort_core::globals::State::Final)
        {
            let waits = session.elab.blocked_on(id).into_iter().collect();
            let goals = session.goal_places(&waits);
            if goals.is_empty() {
                eprintln!(
                    "error: `{key}` isn't finished: it, or something it uses, has an open goal \
                     (`?`), so it isn't checked"
                );
            } else {
                eprintln!(
                    "error: `{key}` can't be checked until {}",
                    stitchwort_driver::reliance::until(&goals)
                );
            }
            return ExitCode::FAILURE;
        }
        ids.push(id);
    }
    let several = keys.len() > 1;
    for (key, id) in keys.iter().zip(ids) {
        let found = stitchwort_driver::axioms::axioms(&session.elab.ev(), id);
        let indent = if several { "  " } else { "" };
        if several {
            println!("{key}:");
        }
        let goals = session.elab.goals_relied_on(id);
        if found.is_empty() && goals.is_empty() {
            println!("{indent}no axioms are used");
        }
        for axiom in found {
            println!("{indent}{axiom}");
        }
        for goal in goals {
            let place = session.goal_place(goal);
            let what = if place.is_error() {
                "has an error, assumed"
            } else {
                "open goal in"
            };
            let what = match place.is_error() {
                true => format!("`{}` {what}", place.declaration),
                false => format!("{what} `{}`", place.declaration),
            };
            println!(
                "{indent}{what} ({}): {}",
                place.place(),
                session.goal_type_text(goal)
            );
        }
    }
    discard(session);
    ExitCode::SUCCESS
}

fn parse_duration(text: &str) -> Option<std::time::Duration> {
    parse_millis(text)
        .ok()
        .map(std::time::Duration::from_millis)
}

/// `search --at FILE:LINE[:COL]` (SW-915 stage 2): checks the file, finds
/// the goal, and prints what closes it.
fn search_at(
    at: &str,
    index: Option<usize>,
    project: Option<&Path>,
    options: &stitchwort_driver::search_at::AtOptions,
    json: bool,
    log: Option<&Path>,
    cache: &CacheArgs,
) -> ExitCode {
    use stitchwort_driver::search::Scope;
    use stitchwort_driver::search_at::{GoalAt, goals_in, pick};
    let started = std::time::Instant::now();
    let fail = |code: &str, message: String| {
        if json {
            println!(
                "{}",
                serde_json::json!({"version": 1, "error": {"code": code, "message": message}})
            );
        }
        eprintln!("error: {message}");
        ExitCode::from(2)
    };
    // FILE, FILE:LINE or FILE:LINE:COL.
    let mut path = at;
    let mut numbers = Vec::new();
    for _ in 0..2 {
        match path.rsplit_once(':') {
            Some((head, tail)) if tail.parse::<usize>().is_ok() => {
                numbers.push(tail.parse::<usize>().expect("just parsed"));
                path = head;
            }
            _ => break,
        }
    }
    numbers.reverse();
    let which = match numbers[..] {
        [line, col] => Some(GoalAt::Line(line, Some(col))),
        [line] => Some(GoalAt::Line(line, None)),
        _ => None,
    };
    let which = match (which, index) {
        (Some(_), Some(_)) => {
            return fail("E-SEARCH-AT", "give a line or --goal N, not both".into());
        }
        (Some(w), None) => w,
        (None, Some(n)) => GoalAt::Index(n),
        (None, None) => GoalAt::Index(1),
    };
    let path = Path::new(path);
    // A file of a project (found from the file's folder, or --project) is
    // searched in the project: its namespace, imports and declarations.
    match project_of_file(path, project) {
        Ok(Some((dir, relative, _))) => {
            let mut session = new_session(false);
            let cache_dir = cache_dir(cache, &dir);
            let files = DiskFiles { root: dir.clone() };
            let goal = stitchwort_driver::search_at::ProjectGoal {
                project: &project_name(&dir),
                files: &files,
                path: &relative,
                cache: cache_dir.as_deref(),
                at: which,
            };
            let result = session.search_at_project(&goal, options);
            return finish_search_at(session, result, json, log, at, started);
        }
        Ok(None) => {}
        Err(message) => return fail("E-SEARCH-AT", message),
    }
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(err) => {
            return fail(
                "E-SEARCH-AT",
                format!("can't read {}: {err}", path.display()),
            );
        }
    };
    let mut session = new_session(false);
    use_cache(&mut session, cache, Path::new("."));
    let context = file_mode_context(path, &text, "searched");
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
    let name = path.display().to_string();
    let diagnostics = match session.load_file(&name, &text, context) {
        Ok(_) => std::mem::take(&mut session.warnings),
        Err(diagnostics) => {
            let errors: Vec<_> = (diagnostics.iter())
                .filter(|d| d.severity == stitchwort_syntax::Severity::Error)
                .cloned()
                .collect();
            if !errors.is_empty() && !json {
                report(&session.sources, &errors);
                eprintln!("warning: the file doesn't check: its goals are searched as they stand");
            }
            let mut all = diagnostics;
            all.extend(std::mem::take(&mut session.warnings));
            all
        }
    };
    let Some(file) = (session.sources.iter())
        .filter(|(_, f)| f.name == name)
        .map(|(id, _)| id)
        .last()
    else {
        return fail("E-SEARCH-AT", format!("{name} didn't load"));
    };
    let goals = goals_in(&session.sources, file, &diagnostics);
    let found = match pick(&goals, which) {
        Ok(found) => found.clone(),
        Err(message) => return fail("E-SEARCH-AT", format!("{name}: {message}")),
    };
    if let Err(diagnostics) = session.elab.load_all_libraries() {
        report(&session.sources, &diagnostics);
        return ExitCode::from(2);
    }
    // The proofs are checked in a session with only the file loaded, as it
    // is when one is pasted in (the search's has the whole library).
    let mut checking = new_session(false);
    use_cache(&mut checking, cache, Path::new("."));
    if let Some(file_name) = path.file_name().and_then(|n| n.to_str()) {
        checking.include_in_folder(
            std::rc::Rc::new(DiskFiles {
                root: folder.to_path_buf(),
            }),
            file_name,
        );
    }
    let _ = checking.load_file(&name, &text, file_mode_context(path, &text, "searched"));
    std::mem::take(&mut checking.warnings);
    let result = session.search_at(&found, &name, options, &Scope::File, Some(&mut checking));
    discard(checking);
    finish_search_at(session, result, json, log, at, started)
}

/// Splits `FILE`, `FILE:LINE` or `FILE:LINE:COL` into the file and the
/// numbers after it, in order.
fn split_at_argument(at: &str) -> (&str, Vec<usize>) {
    let mut path = at;
    let mut numbers = Vec::new();
    for _ in 0..2 {
        match path.rsplit_once(':') {
            Some((head, tail)) if tail.parse::<usize>().is_ok() => {
                numbers.push(tail.parse::<usize>().expect("just parsed"));
                path = head;
            }
            _ => break,
        }
    }
    numbers.reverse();
    (path, numbers)
}

/// `goal --at FILE:LINE[:COL]`: the goal and the names in scope at a point,
/// found by checking the file with a probe there
/// ([`stitchwort_driver::Session::context_at_text`], and
/// `context_at_project` for a file of a project).
fn goal_at(at: &str, project: Option<&Path>, json: bool, cache: &CacheArgs) -> ExitCode {
    let fail = |code: &str, message: String, status: u8| {
        if json {
            println!(
                "{}",
                serde_json::json!({"version": 1, "error": {"code": code, "message": message}})
            );
        }
        eprintln!("error: {message}");
        ExitCode::from(status)
    };
    let (path, numbers) = split_at_argument(at);
    let (line, column) = match numbers[..] {
        [line] => (line, None),
        [line, column] => (line, Some(column)),
        _ => {
            return fail(
                "E-GOAL-AT",
                "--at takes FILE:LINE or FILE:LINE:COL".into(),
                2,
            );
        }
    };
    if line == 0 || column == Some(0) {
        return fail("E-GOAL-AT", "lines and columns count from 1".into(), 2);
    }
    let path = Path::new(path);
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(err) => {
            return fail(
                "E-GOAL-AT",
                format!("can't read {}: {err}", path.display()),
                2,
            );
        }
    };
    let Some(line_text) = text.split('\n').nth(line - 1) else {
        return fail(
            "E-GOAL-AT",
            format!("{} has no line {line}", path.display()),
            2,
        );
    };
    let line_text = line_text.strip_suffix('\r').unwrap_or(line_text);
    // The column as the answer reports it (1-based, in characters), and the
    // protocol's (0-based, in UTF-16 units) for the probe.
    let column = match column {
        Some(column) => column,
        None => match line_text.chars().position(|c| !c.is_whitespace()) {
            Some(i) => i + 1,
            None => return no_goal(path, line, 1, json),
        },
    };
    let character: u32 = (line_text.chars().take(column - 1))
        .map(|c| c.len_utf16() as u32)
        .sum();
    // A file that doesn't parse has no answer to give; say why.
    let mut sources = SourceMap::new();
    let id = sources.add(path.display().to_string(), text.clone());
    if let Err(diagnostics) = stitchwort_syntax::parse_module(id, &text) {
        report(&sources, &diagnostics);
        if json {
            println!(
                "{}",
                serde_json::json!({"version": 1, "error": {
                    "code": "E-GOAL-AT-PARSE",
                    "message": format!("{} doesn't parse", path.display()),
                }})
            );
        }
        return ExitCode::from(1);
    }
    let name = path.display().to_string();
    let mut session = new_session(false);
    let found = match project_of_file(path, project) {
        Ok(Some((dir, relative, _))) => {
            let cache_dir = cache_dir(cache, &dir);
            let files = DiskFiles { root: dir.clone() };
            session.context_at_project(
                &project_name(&dir),
                &files,
                &relative,
                cache_dir.as_deref(),
                (line - 1) as u32,
                character,
            )
        }
        Ok(None) => {
            use_cache(&mut session, cache, Path::new("."));
            let folder = path
                .parent()
                .filter(|p| !p.as_os_str().is_empty())
                .unwrap_or(Path::new("."));
            if let Some(file) = path.file_name().and_then(|n| n.to_str()) {
                session.include_in_folder(
                    std::rc::Rc::new(DiskFiles {
                        root: folder.to_path_buf(),
                    }),
                    file,
                );
            }
            session.context_at_text(&name, &text, (line - 1) as u32, character)
        }
        Err(message) => return fail("E-GOAL-AT", message, 2),
    };
    let Some(context) = found else {
        return no_goal(path, line, column, json);
    };
    if json {
        println!(
            "{}",
            serde_json::to_string(&goal_json(&name, line, column, &context))
                .expect("an answer serialises")
        );
    } else {
        println!("{name}:{line}:{column}");
        print!("{}", context.render_text());
    }
    ExitCode::SUCCESS
}

/// `goal` without `--at`: every open goal of the project, and the
/// declarations that rely on it or wait for it
/// (docs/proposals/using-unfinished-proofs.md §5.2). With `--json`:
/// version 1; `goals`, each with `declaration`, `file`, `line`, `column`,
/// `goal` (what must be shown), `reliedOnBy`, `blocking` and
/// `equationLemmas` (unfinished lemmas made for a definition with a `?`).
fn goal_list(
    targets: &[String],
    project: Option<&Path>,
    json: bool,
    cache: &CacheArgs,
) -> ExitCode {
    let target = if targets.is_empty() {
        Target::Everything
    } else {
        Target::Namespaces(targets.to_vec())
    };
    let Some((session, mut reliance, _)) =
        load_project_goals(project, &target, Load::Diagnostics, cache)
    else {
        return ExitCode::FAILURE;
    };
    if !targets.is_empty() {
        reliance.goals.retain(|g| {
            targets.iter().any(|t| {
                (g.place.declaration.strip_prefix(t.as_str())).is_some_and(|r| r.starts_with('.'))
            })
        });
    }
    if json {
        let goals: Vec<_> = reliance
            .goals
            .iter()
            .map(|g| {
                serde_json::json!({
                    "declaration": g.place.declaration,
                    "file": g.place.file,
                    "line": g.place.line,
                    "column": g.place.column,
                    "goal": g.target,
                    "goalComputed": g.computed,
                    "reliedOnBy": g.relied_on_by,
                    "blocking": g.blocking,
                    "equationLemmas": g.equations,
                })
            })
            .collect();
        println!(
            "{}",
            serde_json::json!({"version": 2, "open": goals.len(), "goals": goals})
        );
        discard(session);
        return ExitCode::SUCCESS;
    }
    let n = reliance.goals.len();
    if n == 0 {
        println!("no goals open");
    } else {
        println!("{n} goal{} open", if n == 1 { "" } else { "s" });
    }
    for g in &reliance.goals {
        println!(
            "\n`{}`  {}\n  ⊢ {}",
            g.place.declaration,
            g.place.place(),
            g.target.replace('\n', "\n    ")
        );
        if let Some(computed) = &g.computed {
            println!(
                "    computes to {}",
                stitchwort_syntax::cut_computed(computed)
            );
        }
        let list = |names: &[String]| {
            const SHOWN: usize = 8;
            let mut text = names
                .iter()
                .take(SHOWN)
                .cloned()
                .collect::<Vec<_>>()
                .join(", ");
            if names.len() > SHOWN {
                text.push_str(&format!(
                    " and {} more (--json lists them)",
                    names.len() - SHOWN
                ));
            }
            text
        };
        if !g.relied_on_by.is_empty() {
            println!("  relied on by: {}", list(&g.relied_on_by));
        }
        if !g.blocking.is_empty() {
            println!(
                "  can't be checked until it is filled: {}",
                list(&g.blocking)
            );
        }
        if !g.equations.is_empty() {
            println!(
                "  its equation lemmas ({}) are unfinished too",
                g.equations
                    .iter()
                    .map(|e| format!("`{e}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
    }
    discard(session);
    ExitCode::SUCCESS
}

/// `uses`: the declarations of the project that refer to each name, or
/// with `unused`, the definitions of the namespaces nothing refers to
/// (`dead`: the definitions no root reaches).
fn uses(
    names: &[String],
    unused: bool,
    dead: bool,
    roots: &[String],
    json: bool,
    project: Option<&Path>,
    cache: &CacheArgs,
) -> ExitCode {
    // Every namespace must be loaded, not just reported from its cache entry:
    // `defs_named` and `users_of` read the declarations and checked terms of
    // the loaded namespaces (SW-4335).
    let Some((session, _, order)) =
        load_project_goals(project, &Target::Everything, Load::Everything, cache)
    else {
        return ExitCode::FAILURE;
    };
    let by_namespace = |users: &[stitchwort_driver::uses::User]| {
        let mut last = None;
        for u in users {
            if last != Some(&u.namespace) {
                let ns = if u.namespace.is_empty() {
                    "(top level)"
                } else {
                    &u.namespace
                };
                println!("  {ns}");
                last = Some(&u.namespace);
            }
            println!("    {}  {}:{}", u.declaration, u.file, u.line);
        }
    };
    if unused {
        let users = if dead {
            let mut root_ids = Vec::new();
            for name in roots {
                match one_named(&session, &order, name) {
                    Ok(id) => root_ids.push(id),
                    Err(code) => return code,
                }
            }
            session.dead_in(&order, names, &root_ids)
        } else {
            session.unused_in(&order, names)
        };
        if json {
            if dead {
                println!("{}", serde_json::json!({"version": 1, "dead": users}));
            } else {
                println!("{}", serde_json::json!({"version": 1, "unused": users}));
            }
        } else if users.is_empty() {
            println!(
                "nothing {} in {}",
                if dead { "dead" } else { "unused" },
                names.join(", ")
            );
        } else {
            println!("{} {}:", users.len(), if dead { "dead" } else { "unused" });
            by_namespace(&users);
        }
        discard(session);
        return ExitCode::SUCCESS;
    }
    let mut answers = Vec::new();
    for name in names {
        let id = match one_named(&session, &order, name) {
            Ok(id) => id,
            Err(code) => return code,
        };
        let path = session.elab.ev().def(id).path().to_string();
        answers.push((path, session.users_of(&order, id)));
    }
    if json {
        let declarations: Vec<_> = answers
            .iter()
            .map(|(name, users)| serde_json::json!({"name": name, "users": users}))
            .collect();
        println!(
            "{}",
            serde_json::json!({"version": 1, "declarations": declarations})
        );
    } else {
        for (name, users) in &answers {
            if users.is_empty() {
                println!("`{name}` is used by nothing in the project");
            } else {
                println!("`{name}` is used by {}:", users.len());
                by_namespace(users);
            }
        }
    }
    discard(session);
    ExitCode::SUCCESS
}

/// The one declaration `name` means in `namespaces`, or exit 2 (reported)
/// when the project has none or more than one.
fn one_named(
    session: &Session,
    namespaces: &[String],
    name: &str,
) -> Result<stitchwort_core::DefId, ExitCode> {
    let found = session.defs_named(namespaces, name);
    match found.as_slice() {
        [] => {
            eprintln!("error: there's no declaration `{name}` in the project");
            Err(ExitCode::from(2))
        }
        [id] => Ok(*id),
        _ => {
            let paths: Vec<String> = found
                .iter()
                .map(|id| session.elab.ev().def(*id).path().to_string())
                .collect();
            eprintln!(
                "error: `{name}` is ambiguous: {}; name one in full",
                paths
                    .iter()
                    .map(|p| format!("`{p}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            Err(ExitCode::from(2))
        }
    }
}

/// The project's open goals and its namespaces in canonical order, for
/// `goal`'s listings and `uses`. `load` says whether every namespace must be
/// loaded or a plain check's cache may answer for one. `None` (reported) if
/// the project can't be loaded.
fn load_project_goals(
    project: Option<&Path>,
    target: &Target,
    load: Load,
    cache: &CacheArgs,
) -> Option<(Session, stitchwort_driver::reliance::Reliance, Vec<String>)> {
    let project = locate_project(project, "list goals of", "goal --at hello.sw:3")?;
    let mut session = new_session(false);
    use_cache(&mut session, cache, &project.dir);
    let loaded = session.load_project_for(&project.files, &project.name, target, load);
    let order = match loaded {
        Ok(loaded) => loaded.checked,
        Err(diagnostics) => {
            report(&session.sources, &diagnostics);
            return None;
        }
    };
    let reported = std::mem::take(&mut session.warnings);
    let reliance = session.reliance(&reported);
    Some((session, reliance, order))
}

/// `goal --summary`: how many open goals each namespace has, in the
/// project's order, and the total, so a reader working through a book sees
/// their progress chapter by chapter. With `--json`: `namespaces` (`name`,
/// `open`) and `open`.
fn goal_summary(project: Option<&Path>, json: bool, cache: &CacheArgs) -> ExitCode {
    let Some((session, reliance, order)) =
        load_project_goals(project, &Target::Everything, Load::Diagnostics, cache)
    else {
        return ExitCode::FAILURE;
    };
    let mut counts: Vec<(&str, usize)> = order.iter().map(|ns| (ns.as_str(), 0)).collect();
    for goal in &reliance.goals {
        // A goal is in the longest namespace that prefixes its declaration:
        // both `A` and `A.B` may be namespaces.
        let owner = order
            .iter()
            .filter(|ns| {
                goal.place
                    .declaration
                    .strip_prefix(ns.as_str())
                    .is_some_and(|rest| rest.is_empty() || rest.starts_with('.'))
            })
            .max_by_key(|ns| ns.len());
        if let Some(owner) = owner
            && let Some((_, open)) = counts.iter_mut().find(|(name, _)| *name == owner)
        {
            *open += 1;
        }
    }
    let total = reliance.goals.len();
    if json {
        let each: Vec<_> = counts
            .iter()
            .map(|(name, open)| serde_json::json!({"name": name, "open": open}))
            .collect();
        println!("{}", serde_json::json!({"namespaces": each, "open": total}));
        discard(session);
        return ExitCode::SUCCESS;
    }
    for (name, open) in &counts {
        if *open == 0 {
            println!("{name}: done");
        } else {
            println!("{name}: {open} open");
        }
    }
    let plural = |n: usize, word: &str| format!("{n} {word}{}", if n == 1 { "" } else { "s" });
    println!(
        "{} open in {} of {}",
        plural(total, "goal"),
        counts.iter().filter(|(_, open)| *open > 0).count(),
        plural(counts.len(), "namespace"),
    );
    discard(session);
    ExitCode::SUCCESS
}

/// `goal --at --json`'s answer: version 2; `at` (`file`, `line`, `column`,
/// 1-based); `declaration`; `context`: `kind` (`proof` or `program`),
/// `target` (the goal, or the expected type), `checked` (whether `target`
/// is what the expression was checked against rather than a type found for
/// it), `hasType` (the type found, when it isn't `target`), `range` (the
/// expression: 1-based `line`, `column`, `endLine`, `endColumn`; columns in
/// UTF-16 units), `locals` (`name`, `type`, `value?`) and `step` (on a step
/// of a proof, else null: `form`, `description`, `range`, `index` and `of`
/// from 1, `before`, `after`, `kind`, `adds`, `rule`, `target`). Every
/// goal (`target`, `before`, `after`) is as written, and its
/// `…Computed` twin (`targetComputed`, `beforeComputed`, `afterComputed`)
/// is what it computes to, or null when it prints the same (D3522).
fn goal_json(
    file: &str,
    line: usize,
    column: usize,
    context: &stitchwort_driver::at::Context,
) -> serde_json::Value {
    let range = |[l1, c1, l2, c2]: [u32; 4]| serde_json::json!({"line": l1 + 1, "column": c1 + 1, "endLine": l2 + 1, "endColumn": c2 + 1});
    let kind = |proof: bool| if proof { "proof" } else { "program" };
    let step = context.step.as_ref().map(|s| {
        serde_json::json!({
            "form": s.form,
            "description": s.description,
            "range": range(s.range),
            "index": s.index,
            "of": s.of,
            "kind": kind(s.proof),
            "before": s.before,
            "beforeComputed": s.before_computed,
            "after": s.after,
            "afterComputed": s.after_computed,
            "adds": s.adds,
            "rule": s.rule,
            "target": s.target,
        })
    });
    serde_json::json!({
        "version": 2,
        "at": {"file": file, "line": line, "column": column},
        "declaration": context.declaration,
        "context": {
            "kind": kind(context.proof),
            "target": context.ty,
            "targetComputed": context.ty_computed,
            "checked": context.checked,
            "hasType": context.found,
            "range": range(context.range),
            "locals": context.locals,
            "step": step,
        },
    })
}

/// Nothing was checked at the point (a comment, a signature, between
/// declarations): status 2, with `"context": null` in JSON.
fn no_goal(path: &Path, line: usize, column: usize, json: bool) -> ExitCode {
    let name = path.display();
    if json {
        println!(
            "{}",
            serde_json::json!({
                "version": 1,
                "at": {"file": name.to_string(), "line": line, "column": column},
                "context": null,
            })
        );
    }
    eprintln!("no goal at {name}:{line}:{column}: nothing was checked there");
    ExitCode::from(2)
}

/// The project that file `path` is a source file of: `--project`'s, or the
/// one found from the file's folder up; its folder, the file's path in it,
/// and its namespace line if it has one. `None` for a file on its own (no
/// project, or not one of its source files when found by looking).
fn project_of_file(
    path: &Path,
    flag: Option<&Path>,
) -> Result<Option<(PathBuf, String, Option<String>)>, String> {
    let absolute = std::fs::canonicalize(path)
        .map_err(|err| format!("can't read {}: {err}", path.display()))?;
    let dir = match flag {
        Some(dir) => Some(
            std::fs::canonicalize(dir)
                .map_err(|err| format!("can't read the project {}: {err}", dir.display()))?,
        ),
        None => absolute.parent().and_then(find_project),
    };
    let Some(dir) = dir else {
        return Ok(None);
    };
    let not_source = |why: &str| {
        if flag.is_some() {
            Err(format!(
                "{} isn't a source file of the project {}: {why}",
                path.display(),
                dir.display()
            ))
        } else {
            Ok(None)
        }
    };
    let Ok(relative) = absolute.strip_prefix(&dir) else {
        return not_source("it isn't in its folder");
    };
    let relative: Vec<String> = (relative.components())
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect();
    let relative = relative.join("/");
    let mut sources = stitchwort_syntax::SourceMap::new();
    let files = DiskFiles { root: dir.clone() };
    match project_sources(&files, &project_name(&dir), &mut sources) {
        Ok(found) => {
            let Some((_, text)) = found.iter().find(|(p, _)| *p == relative) else {
                return not_source("it isn't under its source folders");
            };
            let mut scratch = SourceMap::new();
            let id = scratch.add(relative.clone(), text.as_str());
            let namespace = parse_namespace_line(id, text)
                .ok()
                .flatten()
                .map(|line| line.path.text);
            Ok(Some((dir, relative, namespace)))
        }
        Err(errors) if flag.is_some() => Err(errors
            .first()
            .map_or("the project can't be read".into(), |d| d.message.clone())),
        Err(_) => Ok(None),
    }
}

/// Prints what `search --at` found (or why it couldn't), logs it, and
/// gives the exit status.
fn finish_search_at(
    session: Session,
    result: Result<stitchwort_driver::search_at::AtReport, stitchwort_syntax::Diagnostic>,
    json: bool,
    log: Option<&Path>,
    at: &str,
    started: std::time::Instant,
) -> ExitCode {
    use stitchwort_driver::search_at::render_text;
    if let Some(log) = log {
        let entry = match &result {
            Ok(report) => stitchwort_cli::search_log::at_entry(at, report, started),
            Err(d) => stitchwort_cli::search_log::error_entry(
                &stitchwort_cli::search_log::private_at(at),
                d,
                started,
            ),
        };
        stitchwort_cli::search_log::append(log, &entry);
    }
    let code = match result {
        Ok(report) => {
            if json {
                println!(
                    "{}",
                    serde_json::to_string(&report).expect("a report serialises")
                );
            } else {
                print!("{}", render_text(&report));
            }
            if report.total.closing > 0 || !report.tactics.is_empty() {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
        Err(d) => {
            if json {
                println!(
                    "{}",
                    serde_json::json!({"version": 1, "error": {"code": d.code, "message": d.message}})
                );
            }
            report(&session.sources, &[d]);
            ExitCode::from(2)
        }
    };
    discard(session);
    code
}

/// For `search` of a file or project that doesn't check (SW-935): one
/// line saying so, with the first error, instead of every error again on
/// every search; `check` shows them all.
fn unchecked_summary(
    sources: &stitchwort_syntax::SourceMap,
    diagnostics: &[stitchwort_syntax::Diagnostic],
    what: &str,
) {
    use stitchwort_syntax::Severity;
    let errors: Vec<_> = (diagnostics.iter())
        .filter(|d| d.severity == Severity::Error)
        .collect();
    let goals = (diagnostics.iter())
        .filter(|d| d.severity == Severity::Goal)
        .count();
    let plural = |n: usize, one: &str, many: &str| {
        if n == 1 {
            format!("1 {one}")
        } else {
            format!("{n} {many}")
        }
    };
    let Some(first) = errors.first() else {
        if goals > 0 {
            eprintln!(
                "note: {what} has {} open: the declarations with them aren't searched",
                plural(goals, "goal", "goals")
            );
        }
        return;
    };
    let place = first
        .primary_span()
        .map(|span| {
            let (file, line) = stitchwort_driver::render::location(sources, span);
            format!(" at {file}:{line}")
        })
        .unwrap_or_default();
    eprintln!(
        "warning: {what} doesn't check ({}; the first{place}: [{}] {}): only what checked is searched; `stitchwort check` shows the errors",
        plural(errors.len(), "error", "errors"),
        first.code,
        first.message
    );
}

/// `search` (SW-915): loads the file, or the project (or neither), and the
/// whole library, searches it and prints the report.
fn search(
    query: &str,
    file: Option<&Path>,
    project: Option<&Path>,
    options: &stitchwort_driver::search::Options,
    json: bool,
    log: Option<&Path>,
    cache: &CacheArgs,
) -> ExitCode {
    use stitchwort_driver::search::{Scope, render_text};
    let started = std::time::Instant::now();
    let mut session = new_session(false);
    let scope = match file {
        Some(path) => {
            use_cache(&mut session, cache, Path::new("."));
            let text = match std::fs::read_to_string(path) {
                Ok(text) => text,
                Err(err) => {
                    eprintln!("error: can't read {}: {err}", path.display());
                    return ExitCode::from(2);
                }
            };
            let context = file_mode_context(path, &text, "searched");
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
            // A file that doesn't check (a proof being written) is
            // reported, and its declarations that did are still searched.
            // Its namespace and imports stay, so a pattern names things as
            // the file does.
            if let Err(diagnostics) = session.load_file(&path.display().to_string(), &text, context)
            {
                unchecked_summary(&session.sources, &diagnostics, "the file");
            }
            std::mem::take(&mut session.warnings);
            Scope::File
        }
        None => {
            let found = match project {
                Some(_) => locate_project(project, "search", "search 'PATTERN' hello.sw"),
                None => {
                    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
                    stitchwort_driver::project::find_project(&cwd)
                        .and_then(|dir| locate_project(Some(&dir), "search", ""))
                }
            };
            match found {
                Some(project) => {
                    use_cache(&mut session, cache, &project.dir);
                    session.include_from(std::rc::Rc::new(DiskFiles {
                        root: project.dir.clone(),
                    }));
                    let sources = match project_sources(
                        &project.files,
                        &project.name,
                        &mut session.sources,
                    ) {
                        Ok(sources) => sources,
                        Err(diagnostics) => {
                            report(&session.sources, &diagnostics);
                            return ExitCode::from(2);
                        }
                    };
                    let analysis = analyse(&mut session, &project.name, sources);
                    if !analysis.diagnostics.is_empty() {
                        report(&session.sources, &analysis.diagnostics);
                        return ExitCode::from(2);
                    }
                    let names = analysis
                        .namespaces
                        .iter()
                        .map(|ns| ns.name.clone())
                        .collect();
                    // A namespace that doesn't check is reported, and its
                    // declarations that did are still searched.
                    match session.load_analysis(&project.name, analysis, &Target::Everything) {
                        Ok(_) => {
                            std::mem::take(&mut session.warnings);
                        }
                        Err(diagnostics) => {
                            unchecked_summary(&session.sources, &diagnostics, "the project");
                        }
                    }
                    session.elab.leave_namespace();
                    Scope::Project(names)
                }
                None if project.is_some() => return ExitCode::from(2),
                None => {
                    use_cache(&mut session, cache, Path::new("."));
                    Scope::Project(Vec::new())
                }
            }
        }
    };
    if let Err(diagnostics) = session.elab.load_all_libraries() {
        report(&session.sources, &diagnostics);
        return ExitCode::from(2);
    }
    let found = session.search(query, options, &scope);
    if let Some(log) = log {
        let scope_json = match (file, &scope) {
            (Some(path), _) => serde_json::json!({
                "file": stitchwort_cli::search_log::private_path(&path.display().to_string())
            }),
            (None, Scope::Project(ns)) => serde_json::json!({"namespaces": ns}),
            (None, Scope::File | Scope::ProjectFile { .. }) => serde_json::Value::Null,
        };
        let entry = match &found {
            Ok(report) => stitchwort_cli::search_log::entry(report, options, scope_json, started),
            Err(d) => stitchwort_cli::search_log::error_entry(query, d, started),
        };
        stitchwort_cli::search_log::append(log, &entry);
    }
    let code = match found {
        Ok(found) => {
            if json {
                println!(
                    "{}",
                    serde_json::to_string(&found).expect("a search report serialises")
                );
            } else {
                print!("{}", render_text(&found));
            }
            if found.total > 0 {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
        Err(d) => {
            if json {
                println!(
                    "{}",
                    serde_json::json!({"version": 1, "error": {"code": d.code, "message": d.message}})
                );
            }
            report(&session.sources, &[d]);
            ExitCode::from(2)
        }
    };
    discard(session);
    code
}

/// `audit`'s options.
struct AuditArgs {
    json: bool,
    strict: bool,
    allowed_axioms: Option<String>,
    no_search: bool,
    counterexample_budget: Option<u64>,
    verbose: bool,
}

/// Whether `target` names the standard library or a namespace of it.
fn is_std_target(target: &str) -> bool {
    target == "Std" || target.starts_with("Std.")
}

/// Whether the full name `path` is `root` or under it.
fn is_under(path: &str, root: &str) -> bool {
    path == root || path.strip_prefix(root).is_some_and(|r| r.starts_with('.'))
}

/// `audit` (SW-912, D2040): loads the files or the project's namespaces,
/// audits the theorems the targets select (`stitchwort_driver::audit`) and
/// prints the findings, as text or JSON.
#[inline(never)]
fn audit(
    targets: &[String],
    args: &AuditArgs,
    project: Option<&Path>,
    cache: &CacheArgs,
) -> ExitCode {
    use stitchwort_driver::audit;
    // The allowlist from the flag, else the project's, else the default.
    let mut allowed: Option<Vec<String>> = args.allowed_axioms.as_ref().map(|list| {
        (list.split(','))
            .map(str::trim)
            .filter(|a| !a.is_empty())
            .map(str::to_string)
            .collect()
    });
    if let Some(list) = &allowed
        && let Some(unknown) = audit::unknown_axioms(list).first()
    {
        eprintln!(
            "error: `{unknown}` isn't an axiom: the axioms are {}",
            audit::AXIOMS.join(", ")
        );
        return ExitCode::from(2);
    }
    let search = (!args.no_search).then(|| {
        use stitchwort_elab::counterexample::{Budget, ON_AUDIT};
        Budget {
            millis: args.counterexample_budget.unwrap_or(ON_AUDIT.millis),
            ..ON_AUDIT
        }
    });
    let files: Vec<&String> = targets.iter().filter(|t| is_file_target(t)).collect();
    if !files.is_empty() {
        let names: Vec<String> = (targets.iter())
            .filter(|t| !is_file_target(t))
            .cloned()
            .collect();
        if files.len() > 1 && !names.is_empty() {
            eprintln!("error: name theorems after one file: `stitchwort audit FILE NAME...`");
            return ExitCode::from(2);
        }
        if !is_file_target(&targets[0]) {
            eprintln!("error: give the file first: `stitchwort audit FILE NAME...`");
            return ExitCode::from(2);
        }
        let options = audit::Options {
            allowed: allowed_or_default(allowed),
            search,
        };
        let mut audits = Vec::new();
        let mut errors = 0;
        // Each file gets its own session, as for `check`.
        for file in files {
            let mut session = new_session(false);
            use_cache(&mut session, cache, Path::new("."));
            // A file with errors is still audited, theorem by theorem.
            let loaded = load_file(&mut session, Path::new(file.as_str()), Some("checked"));
            if !loaded && session.elab.failed_decls().is_empty() {
                return ExitCode::FAILURE;
            }
            // A failure with no declaration of its own to blame (a failed
            // import) is still an error.
            errors += session.errors().has.len().max(usize::from(!loaded));
            session.elab.leave_namespace();
            match audit_loaded(&mut session, &[], &names, true, &options) {
                Ok(found) => audits.extend(found),
                Err(code) => return code,
            }
            discard(session);
        }
        return print_audit(&audits, &options.allowed, errors, args);
    }
    let mut session = new_session(false);
    // Which theorems: those under the `roots`, and those `named`.
    let mut roots: Vec<String> = Vec::new();
    let mut named: Vec<String> = Vec::new();
    let mut loaded = true;
    if !targets.is_empty() && targets.iter().all(|t| is_std_target(t)) {
        // The standard library is loaded with every session.
        roots = targets.to_vec();
    } else {
        let Some(project) = locate_project(project, "audit", "audit hello.sw") else {
            return ExitCode::FAILURE;
        };
        if allowed.is_none() {
            let config = project.dir.join("stitchwort.yaml");
            let text = std::fs::read_to_string(&config).unwrap_or_default();
            let mut sources = SourceMap::new();
            let id = sources.add("stitchwort.yaml", text.clone());
            match stitchwort_cli::project::parse_config(id, "stitchwort.yaml", &text) {
                Ok(config) => allowed = config.allowed_axioms,
                Err(d) => {
                    report(&sources, &[d]);
                    return ExitCode::FAILURE;
                }
            }
        }
        use_cache(&mut session, cache, &project.dir);
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
        // Each target is a namespace or a prefix of some (their theorems,
        // and those of the namespaces under them), or a theorem's full name
        // (its namespace is loaded).
        let mut namespaces = Vec::new();
        for target in targets {
            if is_std_target(target) {
                roots.push(target.clone());
            } else if (analysis.namespaces.iter()).any(|n| is_under(&n.name, target)) {
                namespaces.push(target.clone());
                roots.push(target.clone());
            } else if let Some(namespace) = namespace_of(&analysis, target) {
                namespaces.push(namespace.to_string());
                named.push(target.clone());
            } else {
                let known: BTreeSet<String> = (analysis.namespaces.iter())
                    .map(|n| n.name.clone())
                    .collect();
                let d = unknown_namespace(&project.name, target, &known);
                report(&session.sources, &[d]);
                return ExitCode::FAILURE;
            }
        }
        let load = if targets.is_empty() {
            Target::Everything
        } else {
            Target::Subtrees(namespaces)
        };
        match session.load_analysis(&project.name, analysis, &load) {
            Ok(_) => {
                let reported = std::mem::take(&mut session.warnings);
                report(&session.sources, &reported);
            }
            Err(diagnostics) => {
                loaded = false;
                report(&session.sources, &diagnostics);
                // Errors in declarations leave the rest checked, and
                // audited; anything else (a bad project) leaves nothing.
                if session.elab.failed_decls().is_empty() {
                    return ExitCode::FAILURE;
                }
            }
        }
        session.elab.leave_namespace();
    }
    // The library's files load as programs need them: for its theorems,
    // every one.
    if roots.iter().any(|r| is_std_target(r))
        && let Err(diagnostics) = session.elab.load_all_libraries()
    {
        report(&session.sources, &diagnostics);
        return ExitCode::FAILURE;
    }
    let options = audit::Options {
        allowed: allowed_or_default(allowed),
        search,
    };
    let audits = match audit_loaded(&mut session, &roots, &named, false, &options) {
        Ok(audits) => audits,
        Err(code) => return code,
    };
    let errors = session.errors().has.len().max(usize::from(!loaded));
    discard(session);
    print_audit(&audits, &options.allowed, errors, args)
}

/// The allowlist given, or the default.
fn allowed_or_default(allowed: Option<Vec<String>>) -> BTreeSet<String> {
    use stitchwort_driver::audit::DEFAULT_ALLOWED;
    allowed
        .unwrap_or_else(|| DEFAULT_ALLOWED.iter().map(|a| a.to_string()).collect())
        .into_iter()
        .collect()
}

/// Audits the theorems of a loaded session: those under `roots` and those
/// `named` (each must be found), or with neither, every one outside the
/// library. In a file, a name is as written in it (`foo`, not `Main.foo`).
fn audit_loaded(
    session: &mut Session,
    roots: &[String],
    named: &[String],
    file: bool,
    options: &stitchwort_driver::audit::Options,
) -> Result<Vec<stitchwort_driver::audit::TheoremAudit>, ExitCode> {
    let matches =
        |path: &str, name: &str| path == name || (file && path.ends_with(&format!(".{name}")));
    let everything = roots.is_empty() && named.is_empty();
    let keep = |path: &str| {
        if everything {
            return !path.starts_with("Std.");
        }
        roots.iter().any(|r| is_under(path, r)) || named.iter().any(|n| matches(path, n))
    };
    let selected = stitchwort_driver::audit::theorems(&session.elab.ev(), &keep);
    for name in named {
        if !selected.iter().any(|(_, p)| matches(p, name)) {
            eprintln!("error: there's no theorem `{name}`");
            return Err(ExitCode::FAILURE);
        }
    }
    // In a file, theorems are shown by the names written in it.
    let selected: Vec<_> = if file {
        let g = &session.elab.ev();
        (selected.into_iter())
            .map(|(id, _)| (id, g.def(id).name().to_string()))
            .collect()
    } else {
        selected
    };
    let mut audits = session.audit(&selected, options);
    // Theorems with errors have no definition to audit; they get a verdict
    // too, unless they were audited (a failed definition that exists).
    for failed in session.audit_failed(&keep) {
        if !audits.iter().any(|a| a.name == failed.name) {
            audits.push(failed);
        }
    }
    // A lane audits every namespace it touched, and some (an AoC day's
    // program namespace, say) have no theorems: say so and carry on, so the
    // namespaces that do have theorems are still audited. A namespace the
    // project doesn't have is an error before this (`E-NAMESPACE-UNKNOWN`).
    for root in roots {
        if !audits.iter().any(|a| is_under(&a.name, root)) {
            eprintln!("note: no theorems in `{root}`");
        }
    }
    Ok(audits)
}

/// Prints `audit`'s findings, as text or JSON, and gives its exit status.
fn print_audit(
    audits: &[stitchwort_driver::audit::TheoremAudit],
    allowed: &BTreeSet<String>,
    errors: usize,
    args: &AuditArgs,
) -> ExitCode {
    use stitchwort_driver::audit;
    // The counts cover every audited declaration, generated ones included;
    // only the number before the colon is the theorems written in source.
    let failed = audits
        .iter()
        .filter(|a| a.worst() == Some(audit::Severity::Fail))
        .count();
    let warned = audits
        .iter()
        .filter(|a| a.worst() == Some(audit::Severity::Warn))
        .count();
    let ok = failed == 0 && errors == 0 && (!args.strict || warned == 0);
    let written: Vec<_> = audits.iter().filter(|a| !a.generated).collect();
    let generated = audits.len() - written.len();
    let total = written.len();
    let assuming = audits
        .iter()
        .filter(|a| a.status == audit::Status::Assuming)
        .count();
    let unchecked = audits
        .iter()
        .filter(|a| a.status == audit::Status::Unfinished)
        .count();
    if args.json {
        let json = serde_json::json!({
            "version": 2,
            "ok": ok,
            "strict": args.strict,
            "allowed_axioms": allowed,
            "searched": !args.no_search,
            "theorems": audits,
            "summary": {
                "theorems": total,
                "generated": generated,
                "failed": failed,
                "warned": warned,
                "passed": audits.len() - failed - warned,
                "assuming": assuming,
                "unfinished": unchecked,
                "errors": errors,
            },
        });
        println!("{json}");
        return exit(ok);
    }
    for a in audits {
        let mark = match a.worst() {
            Some(audit::Severity::Fail) => "✗",
            Some(audit::Severity::Warn) => "!",
            None if args.verbose => "✓",
            None => continue,
        };
        println!("{mark} {}", a.name);
        for finding in &a.findings {
            let kind = match finding.severity {
                audit::Severity::Fail => "fail",
                audit::Severity::Warn => "warn",
            };
            println!("    {kind}: {}", finding.message);
        }
        if args.verbose {
            if a.status == audit::Status::Checked {
                let axioms = if a.axioms.is_empty() {
                    "none".to_string()
                } else {
                    a.axioms.join(", ")
                };
                println!("    axioms: {axioms}");
            }
            if let Some(search) = &a.search {
                println!("    search: {}", search.line);
                if let Some(witness) = &search.witness {
                    println!("    witness: {witness}");
                }
            }
        }
    }
    let s = if total == 1 { "" } else { "s" };
    let separated = if generated > 0 {
        let lemma = if generated == 1 { "lemma" } else { "lemmas" };
        format!(" and {generated} generated {lemma}")
    } else {
        String::new()
    };
    let strict = if args.strict && warned > 0 {
        " (--strict: warnings fail)"
    } else {
        ""
    };
    // Relying on a declaration with an error (its stand-in, D3527) is said
    // apart from relying on an open goal.
    let on_errors = (audits.iter())
        .filter(|a| a.status == audit::Status::Assuming)
        .filter(|a| !a.open_goals.is_empty() && a.open_goals.iter().all(|g| g.is_error()))
        .count();
    let mut parts = Vec::new();
    if assuming > on_errors {
        parts.push(format!("{} rely on open goals", assuming - on_errors));
    }
    if on_errors > 0 {
        parts.push(format!("{on_errors} rely on errors"));
    }
    if unchecked > 0 {
        parts.push(format!("{unchecked} not checked"));
    }
    let goals = match parts.is_empty() {
        true => String::new(),
        false => format!(" ({})", parts.join(", ")),
    };
    let in_project = match errors {
        0 => String::new(),
        1 => " (1 error in the project)".to_string(),
        n => format!(" ({n} errors in the project)"),
    };
    println!(
        "audited {total} theorem{s}{separated}: {failed} failed, {warned} with \
         warnings{strict}, {} passed{goals}{in_project}",
        audits.len() - failed - warned
    );
    exit(ok)
}

/// `fmt`: formats files or folders in place (`-` is standard input and
/// output), or with no files the project's sources.
#[inline(never)]
fn fmt_command(files: &[PathBuf], check: bool, project: Option<&Path>) -> ExitCode {
    let mut paths = Vec::new();
    let mut stdin = false;
    let mut skipped = Vec::new();
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
                for path in sw_files_in(file) {
                    if deliberately_unformatted(&path) {
                        skipped.push(path);
                    } else {
                        paths.push(path);
                    }
                }
            } else if check && deliberately_unformatted(file) {
                // Named, but --check only reports: a caller (the pre-commit
                // hook) passes whatever is staged. Formatting a named file
                // in place is still done, since the user asked for that.
                skipped.push(file.clone());
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

    if !skipped.is_empty() {
        eprintln!(
            "{} file{} skipped as deliberately unformatted",
            skipped.len(),
            if skipped.len() == 1 { "" } else { "s" }
        );
        for path in &skipped {
            eprintln!("{}", path.display());
        }
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

/// Whether `path` is one the repository keeps as written (D1019): its path
/// relative to the nearest enclosing directory that has a `.git` (a file or a
/// folder, found by walking up from the file) is under an entry of
/// [`stitchwort_fmt::DELIBERATELY_UNFORMATTED`]. A file outside a repository
/// is never skipped.
fn deliberately_unformatted(path: &Path) -> bool {
    let Ok(absolute) = std::fs::canonicalize(path) else {
        return false;
    };
    let Some(root) = absolute
        .ancestors()
        .skip(1)
        .find(|dir| dir.join(".git").exists())
    else {
        return false;
    };
    let Ok(relative) = absolute.strip_prefix(root) else {
        return false;
    };
    let relative = relative
        .to_string_lossy()
        .replace(std::path::MAIN_SEPARATOR, "/");
    stitchwort_fmt::DELIBERATELY_UNFORMATTED
        .iter()
        .any(|excluded| relative.starts_with(excluded))
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
    /// Native code: `main` and everything it reaches compiled, or the run
    /// refused (docs/proposals/native-only.md, NO5); `verbose` says what
    /// happened on standard error, and `trace` counts references through
    /// the runtime for the allocation trace.
    #[cfg_attr(not(feature = "native"), allow(dead_code))]
    Native { verbose: bool, trace: bool },
    /// The fast runtime, profiled; the report shows `top` rows.
    Profile { top: usize },
}

fn run_main(session: &mut Session, main: &Main, runner: Runner) -> ExitCode {
    #[cfg(feature = "native")]
    let native = match runner {
        Runner::Native { verbose, trace } => match compile_native(session, main, verbose, trace) {
            Ok(native) => Some(native),
            Err(code) => return code,
        },
        _ => None,
    };
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
        Runner::Profile { top } => {
            run_main_profiled(session, main, top, &mut input, &mut output, &mut terminal)
        }
        #[cfg(feature = "native")]
        Runner::Native { verbose, .. } => run_main_native(
            native.expect("compiled for `run --native`"),
            verbose,
            &mut input,
            &mut output,
            &mut terminal,
        ),
        #[cfg(not(feature = "native"))]
        Runner::Native { .. } => {
            unreachable!("`run --native` is refused without the `native` feature")
        }
    };
    // Out of keys mode before an error is shown, so it's on the normal
    // screen.
    drop(restore);
    match result {
        Ok(()) => ExitCode::SUCCESS,
        // `main` returned an `ExitStatus`.
        Err(stitchwort_cli::run::RunError::Exit(code)) => ExitCode::from(code),
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

/// `run --profile`: `main` on the fast runtime, profiled, with the profile on
/// standard error after the run, or when a signal ends it.
fn run_main_profiled(
    session: &Session,
    main: &Main,
    top: usize,
    input: &mut impl std::io::BufRead,
    output: &mut impl std::io::Write,
    terminal: &mut dyn stitchwort_cli::run::Terminal,
) -> Result<(), stitchwort_cli::run::RunError> {
    let every = std::time::Duration::from_millis(1);
    let sampling = stitchwort_rt::profile::Sampling::Every(every);
    let (result, profile) =
        session.run_main_fast_profiling_on(main, sampling, input, output, terminal, |profile| {
            #[cfg(unix)]
            {
                let profile = profile.clone();
                stitchwort_host::terminal::on_signal(move || {
                    eprint!("{}", profile.report(top));
                });
            }
            #[cfg(not(unix))]
            let _ = profile;
        });
    if let Some(profile) = profile {
        eprint!("{}", profile.report(top));
    }
    result
}

/// `main` compiled for `run --native`: the code (with its image), and the
/// stack the run reserves.
#[cfg(feature = "native")]
struct CompiledNative {
    islands: stitchwort_native::n1::Islands,
    limits: stitchwort_rt::Limits,
    stack: usize,
}

/// Compiles `main` and every body it reaches to native code for `run
/// --native` (docs/proposals/native-only.md, NO5), or says why it can't, as
/// `build --native` would, and gives the exit status: there's no machine to
/// fall back to (`stitchwort run` is the machine).
#[cfg(feature = "native")]
fn compile_native(
    session: &Session,
    main: &Main,
    verbose: bool,
    trace: bool,
) -> Result<CompiledNative, ExitCode> {
    let program = session.lower_fast(main).map_err(|err| {
        report(&session.sources, &[err.diagnostic(main)]);
        ExitCode::from(2)
    })?;
    let limits = stitchwort_rt::Limits::from_core(session.elab.options.limits);
    let image = stitchwort_rt::code::compile(&program);
    let options = stitchwort_native::n1::Options {
        trace_refcounts: trace,
        count_bodies: false,
        pc_map: false,
    };
    let compiled = stitchwort_native::n1::compile(&program, image, options).and_then(|islands| {
        let limits = limits.for_native(islands.max_frame);
        let stack = stitchwort_native::n1::stack_for(
            limits.frames as u64,
            islands.max_frame,
            &islands.widest,
        )?;
        Ok((islands, limits, stack))
    });
    let (islands, limits, stack) = compiled.map_err(|why| {
        report_native_refusal(&why);
        ExitCode::FAILURE
    })?;
    // The thread's stack is the cap, so whatever the run sizes fits.
    debug_assert!(stack <= stitchwort_host::NATIVE_STACK);
    if verbose {
        eprintln!("{}", islands.note());
    }
    Ok(CompiledNative {
        islands,
        limits,
        stack,
    })
}

/// Why `main` can't be compiled to native code (`stitchwort_native`'s
/// message, then its notes), as an error.
#[cfg(feature = "native")]
fn report_native_refusal(why: &[String]) {
    let mut lines = why.iter();
    if let Some(message) = lines.next() {
        eprintln!("error: {message}");
    }
    for note in lines {
        eprintln!("  note: {note}");
    }
}

/// `run --native`: `main` as native code, compiled by [`compile_native`],
/// with the runner on the native executor and the machine running nothing.
#[cfg(feature = "native")]
fn run_main_native(
    native: CompiledNative,
    verbose: bool,
    input: &mut impl std::io::BufRead,
    output: &mut impl std::io::Write,
    terminal: &mut dyn stitchwort_cli::run::Terminal,
) -> Result<(), stitchwort_cli::run::RunError> {
    let CompiledNative {
        islands,
        limits,
        stack,
    } = native;
    let executed_before = stitchwort_rt::machine::instructions_executed();
    // `run --native` runs on a thread whose stack is
    // `stitchwort_host::NATIVE_STACK` (`main`), and `stack` is at most that
    // (`compile_native`'s assertion); the runtime checks it against the
    // thread's real stack in any case.
    let result =
        stitchwort_rt::run_main_native(Box::new(islands), limits, stack, input, output, terminal);
    if verbose {
        eprintln!(
            "native: the machine executed {} instructions",
            stitchwort_rt::machine::instructions_executed() - executed_before
        );
    }
    result
}

/// `run --js`: writes `main` and a runner as JavaScript to a temporary
/// directory and runs it with Node, which inherits standard input, output
/// and error.
fn run_main_js(session: &mut Session, main: Main) -> ExitCode {
    use stitchwort_js::run::{EXIT_FAIL, EXIT_IO, EXIT_RESOURCE, EXIT_STATUS};
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
        .args(stitchwort_rt::host::args())
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
        // `main` returned an `ExitStatus`: its number is in the error file.
        Some(EXIT_STATUS) => ExitCode::from(message().parse::<u8>().unwrap_or(2)),
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

#[inline(never)]
fn eval(path: &Path, expr: &str, cache: &CacheArgs) -> ExitCode {
    let mut session = new_session(false);
    use_cache(&mut session, cache, Path::new("."));
    if !load_for_evaluation(&mut session, path) {
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

/// Loads `path` for `eval` and `repl`. A source file of a project (found
/// from the file's folder, as `check` and `test` find it) is loaded as its
/// namespace in the project, so its imports of other namespaces resolve, and
/// the namespace's names are imported for the expressions typed. Any other
/// file is loaded on its own.
fn load_for_evaluation(session: &mut Session, path: &Path) -> bool {
    let Ok(Some((dir, _, _))) = project_of_file(path, None) else {
        return load(session, path);
    };
    let Ok(text) = std::fs::read_to_string(path) else {
        return load(session, path);
    };
    let mut scratch = SourceMap::new();
    let id = scratch.add("<file>", text.as_str());
    let Ok(Some(line)) = parse_namespace_line(id, &text) else {
        return load(session, path);
    };
    let namespace = line.path.text;
    // The file's own `import`s, which `check` gives its namespace: an
    // expression sees what the file sees, not only the namespace's own names
    // (SW-3735).
    let (module, _) =
        stitchwort_syntax::parse_module_recovering(id, &text, session.elab.options.limits.stack);
    let imports: String = (module.imports.iter())
        .filter_map(|import| text.get(import.span.range()))
        .map(str::trim)
        .collect::<Vec<_>>()
        .join("\n");
    let project = Project {
        name: project_name(&dir),
        files: DiskFiles { root: dir.clone() },
        dir,
    };
    let Some(config) = read_project_config(&project) else {
        return false;
    };
    let target = Target::Namespaces(vec![namespace.clone()]);
    match session.load_project_for(&project.files, &project.name, &target, Load::Everything) {
        Ok(_) => {
            let mut reported = std::mem::take(&mut session.warnings);
            let goals = goals_open(&reported);
            if config.open_goals == stitchwort_cli::project::OpenGoals::Warn && goals > 0 {
                // A project that allows open goals (a course's exercises)
                // would otherwise print a box for each one on every start.
                reported.retain(|d| d.severity != Severity::Goal);
                report(&session.sources, &reported);
                eprintln!(
                    "{}; `stitchwort goal` lists them",
                    open_goals_allowed(goals)
                );
            } else {
                report(&session.sources, &reported);
            }
        }
        Err(diagnostics) => {
            report(&session.sources, &diagnostics);
            return false;
        }
    }
    let diagnostics = session.add_imports("<input>", &format!("import {namespace} (..)"));
    if !diagnostics.is_empty() {
        report(&session.sources, &diagnostics);
    }
    // The file's imports, as `check` reads them: an expression may name what
    // the file imports, which `import {namespace} (..)` alone doesn't bring.
    if !imports.is_empty() {
        let diagnostics = session.add_imports("<input>", &imports);
        if !diagnostics.is_empty() {
            report(&session.sources, &diagnostics);
            return false;
        }
    }
    true
}

/// Evaluates `expr`, or with `type_only`, shows it with its type.
fn evaluate(session: &mut Session, expr: &str, type_only: bool) -> Result<String, Diagnostic> {
    let (value, ty) = evaluate_parts(session, expr, type_only)?;
    Ok(format!("{value}: {ty}"))
}

/// [`evaluate`], as the value (or the expression, with `type_only`) and the
/// type, for showing each in its own colour.
fn evaluate_parts(
    session: &mut Session,
    expr: &str,
    type_only: bool,
) -> Result<(String, String), Diagnostic> {
    let expr = expr.trim();
    let parsed = session.parse_expression("<input>", expr)?;
    if type_only {
        let (_, ty) = session.elab.infer_expr_type_only(&parsed)?;
        return Ok((expr.to_string(), session.elab.show(&ty)));
    }
    let (value, ty) = session.elab.eval_expr(&parsed)?;
    Ok((value.to_string(), ty.to_string()))
}

/// How the REPL shows a result: plain, or with colour.
fn show_result(parts: (String, String), color: bool) -> String {
    if color {
        stitchwort_cli::repl_color::colour_result(&parts.0, &parts.1)
    } else {
        format!("{}: {}", parts.0, parts.1)
    }
}

/// Whether the REPL's own output, on stdout, is coloured: as
/// [`color_on_stderr`], by whether stdout is a terminal.
fn color_on_stdout() -> bool {
    let choice = match COLOR.load(std::sync::atomic::Ordering::Relaxed) {
        1 => ColorChoice::Always,
        2 => ColorChoice::Never,
        _ => ColorChoice::Auto,
    };
    let no_color = std::env::var("NO_COLOR").ok();
    let on = choice.enabled(std::io::stdout().is_terminal(), no_color.as_deref());
    if on {
        stitchwort_cli::theme::init();
    }
    on
}

/// The words a REPL line starts with when it is a declaration, not an
/// expression.
const DECLARATION_STARTS: [&str; 9] = [
    "def",
    "theorem",
    "type",
    "interface",
    "instance",
    "ability",
    "test",
    "export",
    "opaque",
];

/// Whether `input` begins a declaration: a keyword that starts one, or an
/// attribute (`@[…]`).
fn starts_declaration(input: &str) -> bool {
    input.starts_with("@[")
        || DECLARATION_STARTS.iter().any(|word| {
            input
                .strip_prefix(word)
                .is_some_and(|rest| rest.is_empty() || rest.starts_with(char::is_whitespace))
        })
}

/// Whether `text`, which doesn't parse, stops short: the parser got to the
/// end of what was typed and wanted more, so the REPL asks for another line.
fn needs_more_input(session: &mut Session, text: &str) -> bool {
    let id = session.sources.add("<input>", text);
    let (_, errors) =
        stitchwort_syntax::parse_module_recovering(id, text, session.elab.options.limits.stack);
    let end = text.trim_end().len() as u32;
    errors
        .first()
        .and_then(Diagnostic::primary_span)
        .is_some_and(|span| span.start >= end)
}

/// Reports what the REPL got wrong. A one-line input shows its errors as a
/// caret under the input and the message, with no box or file name; goals
/// and what spans more than the line are shown in full, as everywhere.
fn report_input(sources: &SourceMap, diagnostics: &[Diagnostic]) {
    let color = color_on_stderr();
    for diagnostic in diagnostics {
        match stitchwort_cli::render::render_compact(sources, diagnostic, color, REPL_PROMPT.len())
        {
            Some(compact) => eprint!("{compact}"),
            None => report(sources, std::slice::from_ref(diagnostic)),
        }
    }
}

const REPL_PROMPT: &str = "sw> ";

/// The REPL's `:help`.
const REPL_HELP: &str = "  expression         evaluate it and show its value and type
  :t expression      show its type, without evaluating it
  import Std (List)  bring a namespace's names into scope
  def, theorem, type, interface, instance, ability, test
                     declare it for the rest of the session; a declaration
                     that isn't finished asks for more lines (`...`), and a
                     blank line gives up. Declaring a name again replaces
                     it: definitions made earlier keep the one they used
  Tab                complete a name in scope, a member after a dot
                     (`[1, 2].` gives `length`, `map`, …; `xs.` by the type
                     of `xs`), a namespace after `import`, or a `:` command
  :help              this list
  :q                 quit";

#[inline(never)]
fn repl(path: Option<&Path>) -> ExitCode {
    let session = std::rc::Rc::new(std::cell::RefCell::new(new_session(false)));
    if let Some(path) = path
        && !load_for_evaluation(&mut session.borrow_mut(), path)
    {
        return ExitCode::FAILURE;
    }
    let color = color_on_stdout();
    let mut editor = match rustyline::Editor::<
        stitchwort_cli::repl_color::ReplHelper,
        rustyline::history::DefaultHistory,
    >::new()
    {
        Ok(mut editor) => {
            editor.set_helper(Some(stitchwort_cli::repl_color::ReplHelper {
                color,
                session: session.clone(),
            }));
            editor
        }
        Err(err) => {
            eprintln!("error: can't start the REPL: {err}");
            return ExitCode::FAILURE;
        }
    };
    println!(
        "Stitchwort {}. Enter an expression to evaluate it, or a declaration (`def`, `theorem`, `type`, …) to add it to the session; `import Std (List)` to use a namespace's names, `:t expr` for its type, `:help`, `:q` to quit.",
        env!("CARGO_PKG_VERSION")
    );

    loop {
        let line = match editor.readline(REPL_PROMPT) {
            Ok(line) => line,
            Err(ReadlineError::Interrupted | ReadlineError::Eof) => return ExitCode::SUCCESS,
            Err(err) => {
                eprintln!("error: {err}");
                return ExitCode::FAILURE;
            }
        };
        let mut input = line.trim().to_string();
        if input.is_empty() {
            continue;
        }
        if starts_declaration(&input) {
            // A declaration may take several lines: more are asked for
            // while what was typed stops in the middle.
            while needs_more_input(&mut session.borrow_mut(), &input) {
                match editor.readline("...> ") {
                    Ok(more) if more.trim().is_empty() => break,
                    Ok(more) => {
                        input.push('\n');
                        input.push_str(&more);
                    }
                    Err(ReadlineError::Interrupted) => {
                        input.clear();
                        break;
                    }
                    Err(_) => return ExitCode::SUCCESS,
                }
            }
            if input.is_empty() {
                continue;
            }
            let _ = editor.add_history_entry(input.replace('\n', " "));
            let added = session.borrow_mut().add_declarations("<input>", &input);
            match added {
                Ok((declared, reported)) => {
                    report_input(&session.borrow().sources, &reported);
                    for name in declared {
                        // What the name now stands for, as a reminder.
                        if let Ok(shown) = evaluate_parts(&mut session.borrow_mut(), &name, true) {
                            println!("{}", show_result(shown, color));
                        }
                    }
                }
                Err(diagnostics) => report_input(&session.borrow().sources, &diagnostics),
            }
            continue;
        }
        let _ = editor.add_history_entry(&input);
        let input = input.as_str();
        if input == "import" || input.starts_with("import ") {
            // Imports accumulate over the session, as a file's do.
            let diagnostics = session.borrow_mut().add_imports("<input>", input);
            if !diagnostics.is_empty() {
                report_input(&session.borrow().sources, &diagnostics);
            }
            continue;
        }
        let result = match input {
            ":q" | ":quit" => return ExitCode::SUCCESS,
            ":help" | ":h" | ":?" => {
                println!("{REPL_HELP}");
                continue;
            }
            _ => match input.strip_prefix(":t ") {
                Some(expr) => evaluate_parts(&mut session.borrow_mut(), expr, true),
                None => evaluate_parts(&mut session.borrow_mut(), input, false),
            },
        };
        match result {
            Ok(parts) => println!("{}", show_result(parts, color)),
            Err(diagnostic) => report_input(&session.borrow().sources, &[diagnostic]),
        }
    }
}

#[inline(never)]
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
    refuse_open_goals(goals_open(reported))
}

/// [`refuse_goals`], given how many goals are open.
fn refuse_open_goals(goals: usize) -> bool {
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
    let color = color_on_stderr();
    let full_goals = FULL_GOALS.load(std::sync::atomic::Ordering::Relaxed);
    static SEEN_NOTES: std::sync::Mutex<Option<stitchwort_core::collections::HashSet<String>>> =
        std::sync::Mutex::new(None);
    for diagnostic in diagnostics {
        let diagnostic = &stitchwort_cli::render::with_repeated_generic_notes_cut(
            diagnostic,
            SEEN_NOTES
                .lock()
                .unwrap()
                .get_or_insert_with(Default::default),
        );
        if diagnostic.code == "GOAL" && !full_goals {
            let cut = stitchwort_cli::render::with_long_goal_lines_cut(
                diagnostic,
                stitchwort_cli::render::GOAL_LINE_LIMIT,
            );
            eprint!("{}", render(sources, &cut, color));
        } else {
            eprint!("{}", render(sources, diagnostic, color));
        }
    }
}

/// `dev fmt-tree`: the formatter's report over files and folders.
fn fmt_tree_command(paths: &[PathBuf], print: bool) -> ExitCode {
    let mut files = Vec::new();
    for path in paths {
        if let Err(e) = sw_files(path, &mut files) {
            eprintln!("error: {}: {e}", path.display());
            return ExitCode::FAILURE;
        }
    }
    let mut total = stitchwort_fmt::printer::TreeStats::default();
    let (mut refused, mut failed, mut unstable) = (0, 0, 0);
    let (mut long_before, mut long_after) = (0, 0);
    for file in &files {
        let text = match std::fs::read_to_string(file) {
            Ok(text) => text,
            Err(e) => {
                eprintln!("error: {}: {e}", file.display());
                return ExitCode::FAILURE;
            }
        };
        let gate = match stitchwort_fmt::printer::gate(&text) {
            Ok(gate) => gate,
            Err(stitchwort_fmt::Error::Refused(_)) => {
                refused += 1;
                continue;
            }
            Err(stitchwort_fmt::Error::Internal(problem)) => {
                failed += 1;
                println!("{}: {problem}", file.display());
                continue;
            }
        };
        if print {
            print!("{}", gate.text);
        }
        total.add(&gate.stats);
        long_before += gate.long_lines.0;
        long_after += gate.long_lines.1;
        if let Err(problem) = &gate.check {
            failed += 1;
            println!("{}: {problem}", file.display());
        }
        if !gate.idempotent {
            unstable += 1;
            println!("{}: formatting twice differs from once", file.display());
        }
    }
    println!(
        "{} files ({refused} not formatted: they don't parse): {failed} fail a check, {unstable} not \
         idempotent",
        files.len()
    );
    println!("{} declarations", total.decls);
    println!(
        "parameter groups merged (D3565): {}; code lines over 120: {long_before} before, \
         {long_after} after",
        total.merged_groups
    );
    if failed > 0 || unstable > 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// `dev tokens`: the tokens with trivia after rule N, one line a token.
fn tokens_command(paths: &[PathBuf]) -> ExitCode {
    let mut files = Vec::new();
    for path in paths {
        if let Err(e) = sw_files(path, &mut files) {
            eprintln!("error: {}: {e}", path.display());
            return ExitCode::FAILURE;
        }
    }
    let id = SourceMap::new().next_id();
    let mut status = ExitCode::SUCCESS;
    for file in &files {
        let text = match std::fs::read_to_string(file) {
            Ok(text) => text,
            Err(e) => {
                eprintln!("error: {}: {e}", file.display());
                return ExitCode::FAILURE;
            }
        };
        match stitchwort_fmt::tidy::token_dump(id, &text) {
            Ok(dump) => print!("{dump}"),
            Err(message) => {
                eprintln!("error: {message}");
                status = ExitCode::FAILURE;
            }
        }
    }
    status
}

/// `dev doc`: each declaration's layout document and printed text, per file.
fn doc_command(paths: &[PathBuf]) -> ExitCode {
    let mut files = Vec::new();
    for path in paths {
        if let Err(e) = sw_files(path, &mut files) {
            eprintln!("error: {}: {e}", path.display());
            return ExitCode::FAILURE;
        }
    }
    let mut status = ExitCode::SUCCESS;
    for file in &files {
        let text = match std::fs::read_to_string(file) {
            Ok(text) => text,
            Err(e) => {
                eprintln!("error: {}: {e}", file.display());
                return ExitCode::FAILURE;
            }
        };
        match stitchwort_fmt::printer::declaration_docs(&text) {
            Ok(docs) => {
                for (n, (doc, size, printed)) in docs.iter().enumerate() {
                    println!("decl {}", n + 1);
                    println!("size {size}");
                    println!(
                        "text {}",
                        stitchwort_fmt::printer::engine::dump_escape(printed)
                    );
                    print!("{doc}");
                }
            }
            Err(e) => {
                eprintln!("error: {e}");
                status = ExitCode::FAILURE;
            }
        }
    }
    status
}

/// `dev passes`: the tree after each tidy pass, per file.
fn passes_command(paths: &[PathBuf]) -> ExitCode {
    let mut files = Vec::new();
    for path in paths {
        if let Err(e) = sw_files(path, &mut files) {
            eprintln!("error: {}: {e}", path.display());
            return ExitCode::FAILURE;
        }
    }
    let id = SourceMap::new().next_id();
    let mut status = ExitCode::SUCCESS;
    for file in &files {
        let text = match std::fs::read_to_string(file) {
            Ok(text) => text,
            Err(e) => {
                eprintln!("error: {}: {e}", file.display());
                return ExitCode::FAILURE;
            }
        };
        match stitchwort_syntax::lex_with_trivia(id, &text) {
            Ok(_) => print!("{}", stitchwort_fmt::passes::dump_after_each(id, &text)),
            Err(d) => {
                eprintln!("error: {}", d.message);
                status = ExitCode::FAILURE;
            }
        }
    }
    status
}

/// The `.sw` files under `path`, in name order.
fn sw_files(path: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if path.is_dir() {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(path)?
            .map(|entry| entry.map(|e| e.path()))
            .collect::<std::io::Result<_>>()?;
        entries.sort();
        for entry in entries {
            sw_files(&entry, out)?;
        }
    } else if path.extension().is_some_and(|e| e == "sw") {
        out.push(path.to_path_buf());
    }
    Ok(())
}

/// `dev tree --expression`: each file parsed as one expression, its tree
/// printed, or `error: MESSAGE` on standard error if it doesn't parse.
fn expression_tree_command(paths: &[PathBuf]) -> ExitCode {
    let mut files = Vec::new();
    for path in paths {
        if let Err(e) = sw_files(path, &mut files) {
            eprintln!("error: {}: {e}", path.display());
            return ExitCode::FAILURE;
        }
    }
    let id = SourceMap::new().next_id();
    let mut status = ExitCode::SUCCESS;
    for file in &files {
        let text = match std::fs::read_to_string(file) {
            Ok(text) => text,
            Err(e) => {
                eprintln!("error: {}: {e}", file.display());
                return ExitCode::FAILURE;
            }
        };
        match stitchwort_syntax::parse_expression_tree(id, &text, TREE_STACK) {
            (Ok(_), tree) => print!("{}", tree.dump(&text)),
            (Err(error), _) => {
                eprintln!("error: {}", error.message);
                status = ExitCode::FAILURE;
            }
        }
    }
    status
}

fn tree_command(
    paths: &[PathBuf],
    print: bool,
    time: Option<u32>,
    parse_only: bool,
    spans: bool,
) -> ExitCode {
    let mut files = Vec::new();
    for path in paths {
        if let Err(e) = sw_files(path, &mut files) {
            eprintln!("error: {}: {e}", path.display());
            return ExitCode::FAILURE;
        }
    }
    let mut texts = Vec::new();
    for file in &files {
        match std::fs::read_to_string(file) {
            Ok(text) => texts.push(text),
            Err(e) => {
                eprintln!("error: {}: {e}", file.display());
                return ExitCode::FAILURE;
            }
        }
    }
    let id = SourceMap::new().next_id();
    // The lossless tree alone (`lowered` false), or the compiler's tree
    // lowered from it, what `check` pays.
    let time_parse = |rounds: u32, lowered: bool| {
        (0..rounds.max(1))
            .map(|_| {
                let start = std::time::Instant::now();
                for text in &texts {
                    if lowered {
                        std::hint::black_box(stitchwort_syntax::parse_module_recovering(
                            id, text, TREE_STACK,
                        ));
                    } else {
                        std::hint::black_box(stitchwort_syntax::parse_tree(id, text, TREE_STACK));
                    }
                }
                start.elapsed()
            })
            .min()
            .unwrap_or_default()
    };
    let bytes: usize = texts.iter().map(String::len).sum();
    if let Some(rounds) = time
        && parse_only
    {
        println!(
            "{} files, {bytes} bytes, best of {rounds}: parse and lower {:.1} ms",
            files.len(),
            time_parse(rounds, true).as_secs_f64() * 1000.0
        );
        return ExitCode::SUCCESS;
    }
    let mut total = stitchwort_syntax::tree::TreeStats::default();
    let mut failed = 0;
    let mut parse_errors = 0;
    let (mut checked, mut misses, mut unparsed, mut internal) = (0, 0, 0, 0);
    let mut synthetic = std::collections::BTreeMap::new();
    for (file, text) in files.iter().zip(&texts) {
        let (module, errors, tree) = stitchwort_syntax::parse_module_and_tree(id, text, TREE_STACK);
        parse_errors += errors.len();
        // The parser's own bugs, such as a tree that lost a node.
        for error in errors.iter().filter(|e| e.code == "E-INTERNAL") {
            internal += 1;
            let at = error.primary_span().map_or(0, |span| span.start as usize);
            let line = text[..at].matches('\n').count() + 1;
            println!("{}:{line}: {}", file.display(), error.message);
        }
        if print {
            println!("{}:\n{}", file.display(), tree.dump(text));
        }
        match tree.check_round_trip(text) {
            Ok(stats) => {
                total.decls += stats.decls;
                total.errors += stats.errors;
                total.unlexed += stats.unlexed;
                total.nodes += stats.nodes;
                total.misnested += stats.misnested;
            }
            Err(problem) => {
                failed += 1;
                println!("{}: {problem}", file.display());
            }
        }
        if spans {
            let check = tree.check_spans(&module);
            checked += check.checked;
            unparsed += check.unparsed;
            misses += check.misses.len();
            for (kind, count) in check.synthetic {
                *synthetic.entry(kind).or_insert(0) += count;
            }
            for miss in &check.misses {
                let at = miss.span.start as usize;
                let line = text[..at].matches('\n').count() + 1;
                let column = at - text[..at].rfind('\n').map_or(0, |n| n + 1) + 1;
                let written: String = text[miss.span.range()]
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .join(" ")
                    .chars()
                    .take(80)
                    .collect();
                println!(
                    "{}:{line}:{column}: {} is no node: {written}",
                    file.display(),
                    miss.what
                );
            }
        }
    }
    println!(
        "{} files ({failed} not read back): {} declarations ({} not parsed, {} of them not \
         lexed), {} nodes, {} with marks that don't nest, {internal} internal errors",
        files.len(),
        total.decls,
        total.errors,
        total.unlexed,
        total.nodes,
        total.misnested
    );
    if spans {
        let made_up: Vec<String> = synthetic
            .iter()
            .map(|(kind, count)| format!("{count} {kind:?}"))
            .collect();
        println!(
            "{checked} spans of the compiler's tree checked, {misses} not a node or a token; \
             besides, {unparsed} in declarations that didn't parse, and these the lowering \
             makes up that are no node: {}",
            made_up.join(", ")
        );
    }
    if let Some(rounds) = time {
        println!(
            "{bytes} bytes, best of {rounds}: parse and lower {:.1} ms, parse to the lossless tree \
             alone {:.1} ms (the lowering is the difference)",
            time_parse(rounds, true).as_secs_f64() * 1000.0,
            time_parse(rounds, false).as_secs_f64() * 1000.0
        );
    }
    if failed > 0 || parse_errors > 0 || total.misnested > 0 || misses > 0 || internal > 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
