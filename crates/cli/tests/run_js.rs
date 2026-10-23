//! `stitchwort run --js` against `stitchwort run`: the same program, run
//! both ways with the same standard input, must print the same and end the
//! same way. Requires `node` on the PATH (the Nix dev shell, and the
//! flake's checks, provide it).

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

/// Writes `source` to a temporary file called `name`.
fn source_file(name: &str, source: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-run-js-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join(name);
    std::fs::write(&path, source).expect("write source");
    path
}

fn examples() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/accept")
}

/// Runs `stitchwort run [--js] path` with `input` piped to it.
fn run(path: &Path, js: bool, input: &[u8]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
    command.args(["run", "--no-cache"]);
    if js {
        command.arg("--js");
    }
    let mut child = command
        .arg(path)
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

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// Runs `path` both ways with `input`: both must print the same, exit the
/// same way, and, unless `same_errors` is false, report the same errors.
/// What `run --js` printed.
fn same_both_ways(path: &Path, input: &[u8], same_errors: bool) -> Output {
    let rust = run(path, false, input);
    let js = run(path, true, input);
    let context = || {
        format!(
            "{} with input {:?}\n--- run stderr ---\n{}\n--- run --js stderr ---\n{}",
            path.display(),
            text(input),
            text(&rust.stderr),
            text(&js.stderr)
        )
    };
    assert_eq!(text(&rust.stdout), text(&js.stdout), "{}", context());
    assert_eq!(rust.status.code(), js.status.code(), "{}", context());
    if same_errors {
        assert_eq!(text(&rust.stderr), text(&js.stderr), "{}", context());
    }
    js
}

/// Every example with a `main`, with input that the interactive ones read.
#[test]
fn examples_print_the_same_both_ways() {
    let mut ran = Vec::new();
    let mut entries: Vec<_> = std::fs::read_dir(examples())
        .expect("read examples")
        .map(|e| e.expect("read entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "sw"))
        .collect();
    entries.sort();
    for path in entries {
        let source = std::fs::read_to_string(&path).expect("read example");
        if !(source.contains("def main()") || source.contains("def main ()")) {
            continue;
        }
        for input in [&b""[..], b"Ada\n3\n4\n\n", b"one\ntwo\r\nthree"] {
            let js = same_both_ways(&path, input, true);
            assert!(
                js.status.success(),
                "{}: {}",
                path.display(),
                text(&js.stderr)
            );
        }
        ran.push(path.file_name().unwrap().to_string_lossy().into_owned());
    }
    // The examples this covers, so that losing one is noticed.
    if std::env::var("EXAMPLES").map_or(true, |v| v.is_empty()) {
        for name in [
            "adder.sw",
            "adder-fuel.sw",
            "cat.sw",
            "collatz.sw",
            "partial.sw",
        ] {
            assert!(ran.iter().any(|r| r == name), "{name} wasn't run: {ran:?}");
        }
    }
}

/// `readLine` and `readAll` at the edges of the input: line endings, the
/// last line without one, the end, and invalid UTF-8 (E-IO, with the same
/// line number).
#[test]
fn reading_matches_the_rust_runner() {
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
        b"a\n",
        b"a\r\nb\r\n",
        b"a\rb",
        b"a\nb\r",
        b"\n\nx\ny",
        b"a\nb\nc\r\nd",
        "h\u{e9}llo\nw\u{f6}rld\n\u{1f600}\n".as_bytes(),
        "\u{feff}bom\n".as_bytes(),
        b"\xff\n",
        b"a\n\xc3\n",
        b"a\nb\nc\nd\xffe\n",
        b"a\nb\nc\nd\ne\xf0\x9f\x98",
    ];
    for input in inputs {
        same_both_ways(&path, input, true);
    }
}

/// Long input, read a line at a time by a partial loop.
#[test]
fn a_long_input_is_read_line_by_line() {
    let input: String = (0..20_000).map(|i| format!("line {i}\n")).collect();
    let js = same_both_ways(&examples().join("cat.sw"), input.as_bytes(), true);
    assert_eq!(text(&js.stdout), input);
}

/// Non-tail recursion over a 500,000-element list would overflow Node's
/// default stack: the program runs in a worker with a large one.
#[test]
fn deep_recursion_over_a_long_list_runs() {
    let path = source_file(
        "long.sw",
        r#"
import Std (List, Nat)

def total : List Nat -> Nat
  | Nil       => 0
  | Cons x xs => x + total xs

def main () : {IO} () :=
  let xs := List.map (i => (i * 7919) % 500000) (List.range 500000)
  IO.print (Nat.toText (total xs))
  IO.print (Nat.toText (total (List.take 3 (List.sort xs))))
"#,
    );
    let js = run(&path, true, b"");
    assert!(js.status.success(), "{}", text(&js.stderr));
    assert_eq!(text(&js.stdout), "124999750000\n3\n");
}

/// Running out of the engine's resources (here, a string too long for it)
/// is E-RESOURCE, pointing at `main`, after what was printed before. The
/// length comes from the input, so the checker can't compute it first.
/// (`stitchwort run` would take all the memory it could.)
#[test]
fn running_out_of_resources_is_reported() {
    let path = source_file(
        "grow.sw",
        r#"
import Std (Nat, Text)

def grow : Nat -> Text -> Text
  | 0,      t => t
  | Succ n, t => grow n (t ++ t)

def main () : {IO} () :=
  IO.print "before"
  let n := Text.length (IO.readAll ())
  IO.print (Nat.toText (Text.length (grow n "x")))
"#,
    );
    let js = run(&path, true, &[b'.'; 40]);
    assert_eq!(js.status.code(), Some(2), "{}", text(&js.stderr));
    assert_eq!(text(&js.stdout), "before\n");
    let stderr = text(&js.stderr);
    assert!(stderr.contains("[E-RESOURCE]"), "{stderr}");
    assert!(stderr.contains("while running this program"), "{stderr}");
}

/// Without Node, `run --js` says what's missing.
#[test]
fn a_missing_node_is_reported() {
    let path = examples().join("collatz.sw");
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["run", "--no-cache", "--js"])
        .arg(&path)
        .env("PATH", "")
        .output()
        .expect("run stitchwort");
    assert_eq!(output.status.code(), Some(1));
    assert!(
        text(&output.stderr).contains("needs Node.js"),
        "{}",
        text(&output.stderr)
    );
}

/// A program that doesn't check isn't run.
#[test]
fn type_errors_stop_it_before_node() {
    let path = source_file("bad.sw", "def main () : {IO} () := IO.print 3\n");
    let js = same_both_ways(&path, b"", true);
    assert_eq!(js.status.code(), Some(1));
}

/// `SafeNat` and `SafeInt` are ordinary records inside a program, so
/// `run --js` prints what `run` does: the `number` codec only applies at an
/// export's boundary (SW-337).
#[test]
fn safe_numbers_print_the_same_both_ways() {
    let path = source_file(
        "safe-numbers.sw",
        r#"
import Std (Int, Nat, Option, SafeInt, SafeNat, Text)

def show : Option SafeNat -> Text
  | None   => "too big"
  | Some n => Nat.toText n.value

def showInt : Option SafeInt -> Text
  | None   => "out of range"
  | Some n => Int.toText n.value

def main () : {IO} () :=
  IO.print (show (SafeNat.ofNat 5))
  IO.print (show (SafeNat.ofNat 9007199254740991))
  IO.print (show (SafeNat.ofNat 9007199254740992))
  IO.print (showInt (SafeInt.ofInt (-9007199254740991)))
  IO.print (showInt (SafeInt.ofInt (-9007199254740992)))
"#,
    );
    let js = same_both_ways(&path, b"", true);
    assert!(js.status.success(), "{}", text(&js.stderr));
    assert_eq!(
        text(&js.stdout),
        "5\n9007199254740991\ntoo big\n-9007199254740991\nout of range\n"
    );
}

/// D922 (test A0): a definition with type or proof parameters, used as a
/// value, is called by code that knows only its type, which passes those
/// arguments too. The output is what the reference evaluator prints (checked
/// in `run_reference.rs`, which has the same program).
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
  IO.print (Nat.toText (List.sum (List.map (f => f 2 rfl) [proofOnly, proofOnly])))
"#,
    );
    let js = same_both_ways(&path, b"", true);
    assert!(js.status.success(), "{}", text(&js.stderr));
    assert_eq!(
        text(&js.stdout),
        "7\n42\n42\n11\n42\n8\n44\n42\n45\n109\n204\n"
    );
}
