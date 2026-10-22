//! `stitchwort run` (the fast runtime, `crates/rt`) against `stitchwort run
//! --reference` (the type checker's evaluator, the oracle): the same program
//! with the same standard input must print the same and end the same way,
//! through the built command. `crates/rt/tests/machine.rs` compares the two
//! as libraries, on more programs; this covers the command itself.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

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
    let mut ran = 0;
    for path in entries {
        let source = std::fs::read_to_string(&path).expect("read example");
        if !(source.contains("def main()") || source.contains("def main ()")) {
            continue;
        }
        for input in [&b""[..], b"Ada\n3\n4\n\n", b"one\ntwo\r\nthree"] {
            let fast = same_both_ways(&path, input, true);
            assert!(
                fast.status.success(),
                "{}: {}",
                path.display(),
                text(&fast.stderr)
            );
        }
        ran += 1;
    }
    assert!(ran >= 5, "only {ran} examples have a main");
}

/// A project function, by its full name, runs both ways too: AoC day 4 on
/// its example input.
#[test]
fn a_project_function_prints_the_same_both_ways() {
    let aoc = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    let input = std::fs::read(aoc.join("examples/day04.txt")).expect("the example input");
    let args: [&std::ffi::OsStr; 3] = [
        "Aoc.Day04.main".as_ref(),
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
