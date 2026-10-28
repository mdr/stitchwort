//! `stitchwort run` (the fast runtime, `crates/rt`) against `stitchwort run
//! --reference` (the type checker's evaluator, the oracle): the same program
//! with the same standard input must print the same and end the same way,
//! through the built command. `crates/rt/tests/machine.rs` compares the two
//! as libraries, on more programs; this covers the command itself.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use stitchwort_cli::driver::par_map;

/// Stack for the threads that run the examples (they only wait on child
/// processes).
const STACK: usize = 8 * 1024 * 1024;

/// Writes `source` to a temporary file called `name`.
fn source_file(name: &str, source: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-run-ref-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join(name);
    std::fs::write(&path, source).expect("write source");
    path
}

fn examples() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/accept")
}

/// Runs `stitchwort run [--reference] args...` with `input` piped to it.
fn run_args(args: &[&std::ffi::OsStr], reference: bool, input: &[u8]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
    command.args(["run", "--no-cache"]);
    if reference {
        command.arg("--reference");
    }
    let mut child = command
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start stitchwort");
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    // A program that stops early doesn't read it all, so writing may fail.
    let writer = std::thread::spawn(move || {
        let _ = stdin.write_all(&input);
    });
    let output = child.wait_with_output().expect("run stitchwort");
    writer.join().unwrap();
    output
}

fn run(path: &Path, reference: bool, input: &[u8]) -> Output {
    run_args(&[path.as_os_str()], reference, input)
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// Runs `path` both ways with `input`: the same output and exit code, and,
/// if `same_errors`, the same error text. The default run's output.
fn same_both_ways(path: &Path, input: &[u8], same_errors: bool) -> Output {
    let fast = run(path, false, input);
    let reference = run(path, true, input);
    let context = || {
        format!(
            "{} with input {:?}\n--- run stderr ---\n{}\n--- run --reference stderr ---\n{}",
            path.display(),
            text(input),
            text(&fast.stderr),
            text(&reference.stderr)
        )
    };
    assert_eq!(text(&fast.stdout), text(&reference.stdout), "{}", context());
    assert_eq!(fast.status.code(), reference.status.code(), "{}", context());
    if same_errors {
        assert_eq!(text(&fast.stderr), text(&reference.stderr), "{}", context());
    }
    fast
}

/// Every example with a `main`, with input that the interactive ones read.
#[test]
fn examples_print_the_same_both_ways() {
    let mut entries: Vec<_> = std::fs::read_dir(examples())
        .expect("read examples")
        .map(|e| e.expect("read entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "sw"))
        .collect();
    entries.sort();
    // Each example (three inputs, two runs each) is a few child processes:
    // they run on the thread pool.
    let ran = par_map(STACK, &entries, |path| {
        let source = std::fs::read_to_string(path).expect("read example");
        if !(source.contains("def main()") || source.contains("def main ()")) {
            return false;
        }
        // These end in an unhandled `Fail` on purpose; see below.
        if source.contains("(run: fails)") || source.contains("(run: random)") {
            return false;
        }
        for input in [&b""[..], b"Ada\n3\n4\n\n", b"one\ntwo\r\nthree"] {
            let fast = same_both_ways(path, input, true);
            assert!(
                fast.status.success(),
                "{}: {}",
                path.display(),
                text(&fast.stderr)
            );
        }
        true
    })
    .into_iter()
    .filter(|ran| *ran)
    .count();
    assert!(ran >= 5, "only {ran} examples have a main");
}

/// What `examples/accept/terminal-ops.sw` prints, piped, with
/// [`TERMINAL_OPS_INPUT`]: no terminals, `write` with no line ending, and
/// `readBytes` giving the rest of the input in one read. The playground's
/// test (crates/web) expects the same.
const TERMINAL_OPS_OUTPUT: &str = "terminals: no no\nsize: 0x0\ndrawn, no line ending\nfirst\n\
                                   104,195,169,10,120,10\nnone\nnone\n";
const TERMINAL_OPS_INPUT: &[u8] = "first\nhé\nx\n".as_bytes();

/// The four terminal operations (docs/proposals/terminal-io.md §4.2), used
/// directly, piped: both ways print the same.
#[test]
fn the_terminal_operations_print_the_same_both_ways() {
    let fast = same_both_ways(
        &examples().join("terminal-ops.sw"),
        TERMINAL_OPS_INPUT,
        true,
    );
    assert!(fast.status.success(), "{}", text(&fast.stderr));
    assert_eq!(text(&fast.stdout), TERMINAL_OPS_OUTPUT);
}

/// A project function, by its full name, runs both ways too: AoC day 4 on
/// its example input.
#[test]
fn a_project_function_prints_the_same_both_ways() {
    let aoc = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    let input = std::fs::read(aoc.join("examples/2025/day04.txt")).expect("the example input");
    let args: [&std::ffi::OsStr; 3] = [
        "Aoc.Year2025.Day04.main".as_ref(),
        "--project".as_ref(),
        aoc.as_os_str(),
    ];
    let fast = run_args(&args, false, &input);
    let reference = run_args(&args, true, &input);
    assert!(fast.status.success(), "{}", text(&fast.stderr));
    assert_eq!(text(&fast.stdout), text(&reference.stdout));
    assert_eq!(fast.status.code(), reference.status.code());
    assert!(text(&fast.stdout).starts_with("Part 1: "));
}

/// `readLine` and `readAll` at the edges of the input: line endings, the
/// last line without one, the end, and invalid UTF-8 (E-IO, with the same
/// line number).
#[test]
fn reading_matches_the_reference_runner() {
    let path = source_file(
        "reading.sw",
        r#"
import Std (Nat, Text)

def show : Option Text -> Text
  | None => "<none>"
  | Some t  => "[" ++ t ++ "]"

def main () : {IO} () :=
  IO.print (show (IO.readLine ()))
  IO.print (show (IO.readLine ()))
  let rest := IO.readAll ()
  IO.print ("rest " ++ Nat.toText (Text.length rest) ++ ": [" ++ rest ++ "]")
  IO.print (show (IO.readLine ()))
  IO.print ("again [" ++ IO.readAll () ++ "]")
"#,
    );
    let inputs: &[&[u8]] = &[
        b"",
        b"\n",
        b"a",
        b"a\r\nb\r\n",
        b"a\nb\r",
        b"\n\nx\ny",
        "h\u{e9}llo\nw\u{f6}rld\n\u{1f600}\n".as_bytes(),
        b"\xff\n",
        b"a\n\xc3\n",
        b"a\nb\nc\nd\xffe\n",
    ];
    for input in inputs {
        same_both_ways(&path, input, true);
    }
}

/// Non-tail recursion a million calls deep: the fast runtime keeps its
/// frames on the heap.
#[test]
fn deep_recursion_runs_on_the_fast_runtime() {
    let path = source_file(
        "deep.sw",
        r#"
import Std (Nat)

def count : Nat -> Nat
  | 0      => 0
  | Succ n => 1 + count n

def main () : {IO} () := IO.print (Nat.toText (count (1000 * 1000)))
"#,
    );
    let fast = run(&path, false, b"");
    assert!(fast.status.success(), "{}", text(&fast.stderr));
    assert_eq!(text(&fast.stdout), "1000000\n");
}

/// `Partial` mixed with other forwarded abilities
/// (`examples/accept/partial-forwarding.sw`, docs/proposals/effect-runtime.md
/// stage 4c), deeper than the examples test runs it: 1,000 levels of non-tail
/// partial recursion, each printing through handlers that forward `IO`.
#[test]
fn partial_with_forwarded_abilities_prints_the_same_both_ways() {
    let fast = same_both_ways(&examples().join("partial-forwarding.sw"), b"1000\n", true);
    let stdout = text(&fast.stdout);
    assert_eq!(stdout.lines().count(), 1_001);
    assert!(stdout.starts_with("1000\n999\n"), "{stdout}");
}

/// Running out of resources is E-RESOURCE, pointing at `main`, exit code 2,
/// after what was printed before, whichever runner: a recursion the frame
/// limit stops.
#[test]
fn running_out_of_resources_is_reported_alike() {
    let path = source_file(
        "runaway.sw",
        r#"
import Std (Nat)

def count : Nat -> Nat
  | 0      => 0
  | Succ n => 1 + count n

def main () : {IO} () :=
  IO.print "before"
  IO.print (Nat.toText (count (5 * 1000 * 1000)))
"#,
    );
    for reference in [false, true] {
        let output = run(&path, reference, b"");
        assert_eq!(output.status.code(), Some(2), "{}", text(&output.stderr));
        assert_eq!(text(&output.stdout), "before\n");
        let stderr = text(&output.stderr);
        assert!(stderr.contains("[E-RESOURCE]"), "{stderr}");
        assert!(stderr.contains("while running this program"), "{stderr}");
        // ...and says which function recursed.
        assert!(
            stderr.contains("the recursion was deepest in") && stderr.contains("count"),
            "{stderr}"
        );
    }
}

/// A program that doesn't check isn't run, either way.
#[test]
fn type_errors_stop_it_before_running() {
    let path = source_file("bad.sw", "def main () : {IO} () := IO.print 3\n");
    let fast = same_both_ways(&path, b"", true);
    assert_eq!(fast.status.code(), Some(1));
}

/// `--reference` and `--js` choose different runners.
#[test]
fn reference_and_js_conflict() {
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["run", "--no-cache", "--reference", "--js"])
        .arg(examples().join("collatz.sw"))
        .output()
        .expect("run stitchwort");
    assert_eq!(output.status.code(), Some(2));
    assert!(
        text(&output.stderr).contains("cannot be used with"),
        "{}",
        text(&output.stderr)
    );
}

/// D922 (test A0): a definition with type or proof parameters, used as a
/// value, is called by code that knows only its type, which passes those
/// arguments too. The fast runtime must print what the reference evaluator
/// prints (the same program is in `run_js.rs`, against JS).
#[test]
fn functions_with_erased_parameters_work_as_values() {
    let path = source_file(
        "erased_params.sw",
        r#"
import Std (Nat, List)

def seven (a: Type): Nat := 7
def pick (a: Type) (n: Nat): Nat := n + 1
def pickLate (n: Nat) (a: Type): Nat := n + 2
def withProof (n: Nat) (h: n = n) (m: Nat): Nat := n + m
def mid (n: Nat) (a: Type) (m: Nat): Nat := n * 10 + m
def proofOnly (n: Nat) (h: n = n): Nat := n + 100
def tag2 (k: Nat) (j: Nat) (a: Type) (n: Nat): Nat := k * 100 + j * 10 + n

def app (f: Type -> Nat): Nat := f Nat
def app2 (f: Type -> Nat -> Nat): Nat := f Nat 41
def app2Late (f: Nat -> Type -> Nat): Nat := f 40 Nat
def app3 (f: Nat -> Nat): Nat := f 41
def appProof (f: (n: Nat) -> n = n -> Nat -> Nat): Nat := f 5 rfl 6
def appMid (f: Nat -> Type -> Nat -> Nat): Nat := f 4 Nat 2

type Box = { run: (n: Nat) -> n = n -> Nat }

def main () : {IO} () :=
  IO.print (Nat.toText (app seven))
  IO.print (Nat.toText (app2 pick))
  IO.print (Nat.toText (app2Late pickLate))
  IO.print (Nat.toText (appProof withProof))
  IO.print (Nat.toText (appMid mid))
  IO.print (Nat.toText (app (a => 8)))
  IO.print (Nat.toText (app2 (a n => n + 3)))
  IO.print (Nat.toText (app3 (pick Nat)))
  IO.print (Nat.toText (app3 (withProof 4 rfl)))
  IO.print (Nat.toText (({ run = proofOnly }: Box).run 9 rfl))
  IO.print (Nat.toText (List.sum (List.map [proofOnly, proofOnly] (f => f 2 rfl))))
  IO.print (Nat.toText (app2 (tag2 (1 + 1) (2 + 1))))
"#,
    );
    let fast = same_both_ways(&path, b"", true);
    assert!(fast.status.success(), "{}", text(&fast.stderr));
    assert_eq!(
        text(&fast.stdout),
        "7\n42\n42\n11\n42\n8\n44\n42\n45\n109\n204\n271\n"
    );
}

/// An unhandled `Fail` in `main` (docs/proposals/errors.md §3.5): `run` and
/// `run --reference` print what came before, then `error: <msg>` on
/// standard error, and exit with 1; a `main` that doesn't fail exits with 0.
#[test]
fn an_unhandled_failure_is_reported_alike() {
    let pure = source_file(
        "fail-only.sw",
        "import Std (Fail)\n\ndef main(): {Fail} () := Fail.fail \"nothing to do\"\n",
    );
    let cases = [
        (
            examples().join("main-fail.sw"),
            "reading the numbers\n",
            "error: expected a whole number, got 'x3'\n",
            1,
        ),
        (
            examples().join("main-fail-ok.sw"),
            "reading the numbers\ntotal 6\n",
            "",
            0,
        ),
        (pure, "", "error: nothing to do\n", 1),
    ];
    for (path, stdout, stderr, code) in cases {
        let fast = same_both_ways(&path, b"", true);
        assert_eq!(text(&fast.stdout), stdout, "{}", path.display());
        assert_eq!(text(&fast.stderr), stderr, "{}", path.display());
        assert_eq!(fast.status.code(), Some(code), "{}", path.display());
    }
}

/// `IO.randomSeed` gives a fresh 64-bit number each run, in the reference
/// evaluator and on the machine.
#[test]
fn the_random_seed_is_fresh_each_run() {
    let path = source_file(
        "seed.sw",
        "import Std (IO, Nat)\ndef main () : {IO} () := IO.print (Nat.toText (IO.randomSeed ()))\n",
    );
    for reference in [false, true] {
        let seeds: Vec<u64> = (0..3)
            .map(|_| {
                let output = run(&path, reference, b"");
                assert!(output.status.success(), "{}", text(&output.stderr));
                text(&output.stdout)
                    .trim()
                    .parse()
                    .expect("a 64-bit number")
            })
            .collect();
        assert!(seeds[0] != seeds[1] || seeds[1] != seeds[2], "{seeds:?}");
    }
}

/// `IO.args` gives the arguments after `--`, in the reference evaluator and
/// on the machine.
#[test]
fn the_arguments_after_a_double_dash_are_the_programs() {
    let path = source_file(
        "args.sw",
        "import Std (IO, List, Text)\ndef main () : {IO} () := IO.print (Text.joinWith (IO.args ()) \"|\")\n",
    );
    for reference in [false, true] {
        let args = ["--", "1", "two words"].map(std::ffi::OsStr::new);
        let mut all = vec![path.as_os_str()];
        all.extend(args);
        let output = run_args(&all, reference, b"");
        assert!(output.status.success(), "{}", text(&output.stderr));
        assert_eq!(text(&output.stdout), "1|two words\n");
    }
}
