//! Handlers around partial code under `run --js`
//! (docs/proposals/partial-handlers.md §5, lane C): lane A's programs print
//! what the model gives with the model's ticks, a million handled
//! operations and a million ticks under a state handler run on the heap,
//! and `examples/accept/partial-handlers.sw` prints the same on all three
//! runners. The native machine's tests are in `crates/rt/tests`
//! (`tick_counts.rs`, `partial_handlers.rs`).
//!
//! Requires `node` on the PATH (the Nix dev shell provides it).

use std::path::Path;
use std::process::Command;
use std::time::Instant;

use stitchwort_cli::driver::Session;
use stitchwort_cli::render::render;
use stitchwort_js::Options;

/// Lane A's handled programs, in Stitchwort.
const HANDLER_DEFINITIONS: &str = include_str!("../../driver/tests/partial_handlers.sw");

/// Loops for the stack tests, as in `crates/rt/tests/partial_handlers.rs`.
const LOOPS: &str = r#"
def bump: Nat → {Counter} ()
  | 0 => ()
  | Succ below =>
    incr ()
    bump below

def rounds (n: Nat): {Counter, Partial} Nat :=
  if n == 0 then get () else
    bump 1000
    rounds (n - 1)

def countUp (n: Nat): {Counter, Partial} Nat :=
  if n == 0 then get () else
    incr ()
    countUp (n - 1)
"#;

fn source(body: &str) -> String {
    format!("{HANDLER_DEFINITIONS}\n{LOOPS}\ndef main (): {{IO, Partial}} () :=\n  {body}\n")
}

/// What a `run --js` run printed, and its counts.
struct Run {
    stdout: String,
    ticks: u64,
    captured: u64,
    seconds: f64,
}

/// Generates `run --js`'s program for `main` of `text`, with the runner
/// counting, and runs it under Node as `run --js` does.
fn run_js(name: &str, text: &str) -> Run {
    let mut session = Session::new();
    if let Err(diagnostics) = session.load("handlers.sw", text) {
        let rendered: String = diagnostics
            .iter()
            .map(|d| render(&session.sources, d, false))
            .collect();
        panic!("doesn't check:\n{rendered}");
    }
    let main = session.main().expect("a `main`");
    let options = Options {
        effect_counters: true,
        ..Options::default()
    };
    let program = stitchwort_js::run::generate_program_with(
        &session.elab.globals,
        session.elab.limits,
        main.term(),
        options,
    )
    .expect("generation succeeds");
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-partial-handlers-{}-{name}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    std::fs::write(dir.join("program.mjs"), &program.module).expect("write program");
    std::fs::write(dir.join("run.mjs"), &program.launcher).expect("write launcher");
    let start = Instant::now();
    let result = Command::new("node")
        .args(["run.mjs", "error.txt"])
        .current_dir(&dir)
        .output()
        .expect("run `node` (is it on the PATH? `nix develop` provides it)");
    let seconds = start.elapsed().as_secs_f64();
    let stdout = String::from_utf8_lossy(&result.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&result.stderr).into_owned();
    assert!(result.status.success(), "node failed:\n{stderr}");
    let _ = std::fs::remove_dir_all(&dir);
    let counts = stderr
        .lines()
        .find_map(|l| l.strip_prefix("stitchwort-route-counts "))
        .unwrap_or_else(|| panic!("no counts:\n{stderr}"));
    let field = |key: &str| {
        let start = counts.find(&format!("\"{key}\":")).expect("the key") + key.len() + 3;
        let rest = &counts[start..];
        let end = rest.find([',', '}']).expect("the value ends");
        rest[..end].parse::<u64>().expect("a number")
    };
    Run {
        stdout,
        ticks: field("ticks"),
        captured: field("captured"),
        seconds,
    }
}

/// `stitchwort run --reference` on `text`: what it printed. Lane B's
/// `handled_traces_agree_with_the_model` (`crates/driver/tests/partial.rs`)
/// checks that the reference runner's traces are the model's.
fn run_reference(name: &str, text: &str) -> String {
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-partial-handlers-ref-{}-{name}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("handlers.sw");
    std::fs::write(&path, text).expect("write source");
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["run", "--no-cache", "--reference"])
        .arg(&path)
        .output()
        .expect("run stitchwort");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("text")
}

/// Lane A's programs print what the reference runner prints, with the
/// ticks the model's own tests expect (`table.rs`, section 9).
#[test]
fn handled_programs_print_the_same_with_the_models_ticks() {
    let cases: [(&str, &str, u64); 10] = [
        (
            "IO.print (showResult (toResult (() => countdown 5)))",
            "Err three",
            2,
        ),
        (
            "IO.print (showResult (toResult (() => countdown 2)))",
            "Ok 0",
            2,
        ),
        ("IO.print (showResult (toResult stopThenSpin))", "Err no", 0),
        (
            "IO.print (Nat.toText (fromLines [\"n\", \"e\", \"s\", \"w\", \"q\"] (() => play 0)))",
            "5",
            5,
        ),
        (
            "IO.print (showList (collectIn (() => search 2)))",
            "3,1,2,0",
            6,
        ),
        ("IO.print (Nat.toText (walk 2))", "7", 5),
        ("IO.print (Nat.toText (walk 12))", "442", 12 * 13 / 2 + 12),
        (
            "IO.print (showResult (toResult (() => (runCounter 0 (() => climb 0)).fst)))",
            "Err three",
            2,
        ),
        (
            "let (result, count) := runCounter 0 (() => toResult (() => climb 0))\n  \
             IO.print (showResult result ++ \" \" ++ Nat.toText count)",
            "Err three 3",
            2,
        ),
        ("IO.print (Nat.toText (answered ()))", "401", 4),
    ];
    for (i, (body, last, ticks)) in cases.into_iter().enumerate() {
        let text = source(body);
        let run = run_js(&format!("trace-{i}"), &text);
        assert_eq!(
            run.stdout,
            run_reference(&format!("trace-{i}"), &text),
            "{body}"
        );
        assert_eq!(run.stdout.lines().last(), Some(last), "{body}");
        assert_eq!(run.ticks, ticks, "{body}: ticks");
    }
}

/// A million handled operations under `run --js`, a thousand at a time
/// between ticks: the frames are on the heap.
#[test]
fn run_js_a_million_handled_operations() {
    let run = run_js(
        "million-operations",
        &source("IO.print (Nat.toText (runCounter 0 (() => rounds 1000)).fst)"),
    );
    assert_eq!(run.stdout, "1000000\n");
    assert_eq!(run.captured, 1_000_001);
    assert_eq!(run.ticks, 1000);
    println!(
        "a million handled operations, run --js: {:.3} s",
        run.seconds
    );
}

/// A million ticks under a state handler under `run --js`, a handled
/// operation each.
#[test]
fn run_js_a_million_ticks_under_a_state_handler() {
    let run = run_js(
        "million-ticks",
        &source("IO.print (Nat.toText (runCounter 0 (() => countUp 1000000)).fst)"),
    );
    assert_eq!(run.stdout, "1000000\n");
    assert_eq!(run.captured, 1_000_001);
    assert_eq!(run.ticks, 1_000_000);
    println!(
        "a million ticks under a state handler, run --js: {:.3} s",
        run.seconds
    );
}

/// `stitchwort run`, `run --reference` and `run --js` print the same for the
/// example.
#[test]
fn the_example_prints_the_same_on_all_three_runners() {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/accept/partial-handlers.sw");
    let outputs: Vec<String> = [&[][..], &["--reference"], &["--js"]]
        .iter()
        .map(|flags| {
            let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
                .args(["run", "--no-cache"])
                .args(*flags)
                .arg(&path)
                .output()
                .expect("run stitchwort");
            assert!(
                output.status.success(),
                "{flags:?}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            String::from_utf8(output.stdout).expect("text")
        })
        .collect();
    assert_eq!(
        outputs[0],
        "Err three\nOk 0\nErr no\nrolls until a six: 6\n"
    );
    assert_eq!(outputs[1], outputs[0], "run --reference");
    assert_eq!(outputs[2], outputs[0], "run --js");
}
