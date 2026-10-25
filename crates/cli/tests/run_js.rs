//! `stitchwort run --js` against `stitchwort run`: the same program, run
//! both ways with the same standard input, must print the same and end the
//! same way. Requires `node` on the PATH (the Nix dev shell, and the
//! flake's checks, provide it).

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use stitchwort_cli::driver::par_map;

/// Stack for the pool threads that wait on child processes.
const STACK: usize = 8 * 1024 * 1024;

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
    let mut entries: Vec<_> = std::fs::read_dir(examples())
        .expect("read examples")
        .map(|e| e.expect("read entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "sw"))
        .collect();
    entries.sort();
    // Each example (three inputs, two runs each) is a few child processes:
    // they run on the thread pool, and the names of those that ran come back
    // in order.
    let ran: Vec<String> = par_map(STACK, &entries, |path| {
        let source = std::fs::read_to_string(path).expect("read example");
        if !(source.contains("def main()") || source.contains("def main ()")) {
            return None;
        }
        // These end in an unhandled `Fail` on purpose; see below.
        if source.contains("(run: fails)") {
            return None;
        }
        for input in [&b""[..], b"Ada\n3\n4\n\n", b"one\ntwo\r\nthree"] {
            let js = same_both_ways(path, input, true);
            assert!(
                js.status.success(),
                "{}: {}",
                path.display(),
                text(&js.stderr)
            );
        }
        Some(path.file_name().unwrap().to_string_lossy().into_owned())
    })
    .into_iter()
    .flatten()
    .collect();
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
  let xs := List.map (List.range 500000) (i => (i * 7919) % 500000)
  IO.print (Nat.toText (total xs))
  IO.print (Nat.toText (total (List.take (List.sort xs) 3)))
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

/// D922: the arguments supplied before the erased parameter are computed
/// once, outside the adapter closure, not on every call of it. Purity hides
/// this from the output, so this checks the generated JS: `slow n` is the
/// argument of a binding wrapped around the closure, and is not inside it.
#[test]
fn supplied_arguments_of_an_adapter_are_computed_once() {
    let path = source_file(
        "once.sw",
        r#"
import Std (Nat)

def slow (n: Nat): Nat := n * n * n
def tagged (k: Nat) (a: Type) (n: Nat): Nat := k + n
def app2 (f: Type -> Nat -> Nat): Nat := f Nat 41

export def total (n: Nat): Nat := app2 (tagged (slow n))
"#,
    );
    let out = path.parent().unwrap().join("once-out");
    let built = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["build", "--js", "--no-cache", "-o"])
        .arg(&out)
        .arg(&path)
        .output()
        .expect("run stitchwort build");
    assert!(built.status.success(), "{}", text(&built.stderr));
    let js = std::fs::read_to_string(out.join("once.js")).expect("read once.js");
    let line = js
        .lines()
        .find(|l| l.starts_with("const $Main$dtotal"))
        .expect("total is generated");
    assert!(
        line.ends_with(")($Main$dslow(v0)));"),
        "the argument isn't bound outside the closure: {line}"
    );
    assert!(line.contains("$Main$dtagged($s0, $p2)"), "{line}");
}

/// D1173: a definition with two or more runtime parameters takes them in
/// one call, so every other use goes through a closure: partial application
/// (with and without erased parameters left), over-application of a
/// definition whose result is a function, a native used as a value, a
/// definition passed as a value (made once, `f$c`), recursion and mutual
/// recursion. The output is the reference evaluator's.
#[test]
fn uncurried_definitions_work_every_way_they_are_used() {
    let path = source_file(
        "uncurried.sw",
        r#"
import Std (Nat, List)

def add3 (a: Nat) (b: Nat) (c: Nat): Nat := a * 100 + b * 10 + c
def adder (a: Nat) (b: Nat): Nat -> Nat := add3 a b
def withType (a: Nat) (t: Type) (b: Nat): Nat := a * 10 + b
def twice (f: Nat -> Nat) (x: Nat): Nat := f (f x)
def apply3 (f: Nat -> Nat -> Nat -> Nat): Nat := f 1 2 3
def applyT (f: Nat -> Type -> Nat -> Nat): Nat := f 4 Nat 5
def sumTo (acc: Nat): Nat -> Nat
  | 0 => acc
  | Succ m => sumTo (acc + Succ m) m
def isEven (k: Nat): Nat -> Nat
  | 0 => k
  | Succ m => isOdd (k + 1) m
def isOdd (k: Nat): Nat -> Nat
  | 0 => k * 1000
  | Succ m => isEven (k + 1) m

def main () : {IO} () :=
  IO.print (Nat.toText (add3 1 2 3))
  IO.print (Nat.toText (twice (add3 1 2) 3))
  IO.print (Nat.toText (twice (add3 0 (1 + 1)) 3))
  IO.print (Nat.toText (adder 1 2 3))
  IO.print (Nat.toText (twice (adder 0 0) 7))
  IO.print (Nat.toText (apply3 add3))
  IO.print (Nat.toText (applyT withType))
  IO.print (Nat.toText (twice (withType 3 Nat) 4))
  IO.print (Nat.toText (List.sum (List.zipWith [1, 2] [30, 40] Nat.add)))
  IO.print (Nat.toText (List.sum (List.map [4, 5] (add3 1 2))))
  IO.print (Nat.toText (sumTo 0 100000))
  IO.print (Nat.toText (isEven 0 7))
"#,
    );
    let js = same_both_ways(&path, b"", true);
    assert!(js.status.success(), "{}", text(&js.stderr));
    assert_eq!(
        text(&js.stdout),
        "123\n243\n43\n123\n7\n123\n45\n64\n73\n249\n5000050000\n7000\n"
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
    let js = same_both_ways(&path, b"", true);
    assert!(js.status.success(), "{}", text(&js.stderr));
    assert_eq!(
        text(&js.stdout),
        "7\n42\n42\n11\n42\n8\n44\n42\n45\n109\n204\n271\n"
    );
}

/// An unhandled `Fail` in `main` (docs/proposals/errors.md §3.5): `run` and
/// `run --js` prints what came before, then `error: <msg>` on
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
        let js = same_both_ways(&path, b"", true);
        assert_eq!(text(&js.stdout), stdout, "{}", path.display());
        assert_eq!(text(&js.stderr), stderr, "{}", path.display());
        assert_eq!(js.status.code(), Some(code), "{}", path.display());
    }
}

/// The runner steps computations with the effect runtime's loop
/// (docs/proposals/effect-runtime.md §9.3, stage 4a): an `IO` operation on
/// every element of an effectful `map`, so each crosses as many pending
/// `bind`s as there are elements left, and a `Fail` handler it's forwarded
/// through. Before stage 4a this was quadratic (16,000 elements took
/// seconds); a million now take about a second, natively too (since stage
/// 4b). Checked both ways on a short list and on the long one.
#[test]
fn io_across_many_binds_runs_in_linear_time() {
    let source = |count: usize| {
        format!(
            r#"
import Std (Fail, List, Nat, Result, Text)

def echo (x: Nat): {{IO, Fail}} Nat :=
  IO.print (Nat.toText x)
  if x < 100000000 then x else Fail.fail "too big"

def main(): {{IO}} () :=
  match Fail.toResult (() => List.map (List.range {count}) echo) with
    | Ok xs => IO.print "total ${{List.sum xs}}"
    | Err message => IO.print message
"#
        )
    };
    let short = source_file("io-short.sw", &source(2_000));
    let js = same_both_ways(&short, b"", true);
    assert!(text(&js.stdout).ends_with("1999\ntotal 1999000\n"));

    let long = source_file("io-long.sw", &source(1_000_000));
    let js = same_both_ways(&long, b"", true);
    assert!(js.status.success(), "{}", text(&js.stderr));
    let stdout = text(&js.stdout);
    assert_eq!(stdout.lines().count(), 1_000_001);
    assert!(stdout.ends_with("999999\ntotal 499999500000\n"));
}

/// `Partial` mixed with other forwarded abilities, deeper than the examples
/// test runs it (`examples/accept/partial-forwarding.sw`, 50 levels there):
/// 2,000 levels of non-tail partial recursion, each printing through
/// handlers that forward `IO`. A million levels are in
/// `crates/cli/tests/effect_runtime.rs` (JS) and
/// `crates/rt/tests/effect_runtime.rs` (native).
#[test]
fn partial_with_forwarded_abilities_prints_the_same_both_ways() {
    let js = same_both_ways(&examples().join("partial-forwarding.sw"), b"2000\n", true);
    let stdout = text(&js.stdout);
    assert_eq!(stdout.lines().count(), 2_001);
    assert!(stdout.starts_with("2000\n1999\n"), "{stdout}");
}

/// `Partial` mixed with another ability: a handler inside a partial function
/// (so its carrier is a `Delay`, and the runtime resumes by calling), which
/// forwards `IO` to the runner, between recursion requests that the runner's
/// `Tie` frames answer.
#[test]
fn a_handler_inside_a_partial_function_prints_the_same_both_ways() {
    let path = source_file(
        "partial-forward.sw",
        r#"
import Std (Nat, Text)

ability Env where
  ask: () -> {Env} Nat

def next (n: Nat): Nat := if n % 2 == 0 then n / 2 else 3 * n + 1

def shown (n: Nat): {IO, Env} Nat :=
  IO.print (Nat.toText n)
  Env.ask()

-- Prints each number, asking for the step to add to the count.
def steps: Nat -> {IO, Partial} Nat
  | 1 => 0
  | n =>
    let step :=
      handle shown n with
        | return x => x
        | Env.ask u, k => k 1
    step + steps (next n)

def main(): {IO, Partial} () :=
  IO.print "27 reaches 1 in ${steps 27} steps"
"#,
    );
    let js = same_both_ways(&path, b"", true);
    assert!(
        text(&js.stdout).ends_with("27 reaches 1 in 111 steps\n"),
        "{}",
        text(&js.stdout)
    );
}

/// Calls each of `exports` (a function from `Nat` to `Nat` of the program
/// at `path`) on 100,000 (`stack_safe_everywhere_at`: on `n`). The program's
/// `main` prints the same, one line each, natively and with `run --js`; then
/// the module that `build --js` makes is called from a plain Node, with its
/// default stack, and must print that too. (`run --js` hides recursion depth
/// in a worker with a large stack.)
fn stack_safe_everywhere(path: &Path, exports: &[&str]) {
    stack_safe_everywhere_at(path, exports, 100_000);
}

fn stack_safe_everywhere_at(path: &Path, exports: &[&str], n: u64) {
    let js = same_both_ways(path, b"", true);
    assert!(js.status.success(), "{}", text(&js.stderr));
    let expected = text(&js.stdout);
    assert_eq!(expected.lines().count(), exports.len(), "{expected}");

    let stem = path.file_stem().unwrap().to_str().unwrap();
    let out = path.parent().unwrap().join(format!("{stem}-out"));
    let built = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["build", "--js", "--no-cache", "-o"])
        .arg(&out)
        .arg(path)
        .output()
        .expect("run stitchwort build");
    assert!(built.status.success(), "{}", text(&built.stderr));
    let script = out.join("call.mjs");
    let names: Vec<String> = exports.iter().map(|name| format!("{name:?}")).collect();
    std::fs::write(
        &script,
        format!(
            "import * as m from \"./{stem}.js\";\nfor (const name of [{}]) {{\n  console.log(String(m[name]({n}n)));\n}}\n",
            names.join(", ")
        ),
    )
    .expect("write call.mjs");
    let node = Command::new("node")
        .arg(&script)
        .output()
        .expect("run `node` (is it on the PATH? `nix develop` provides it)");
    assert!(node.status.success(), "{}", text(&node.stderr));
    assert_eq!(text(&node.stdout), expected);
}

/// The source of a program exporting `defs` (each `name (n: Nat): Nat`),
/// whose `main` prints each one's value at 100,000 (`exports_program_at`: at
/// `n`).
fn exports_program(imports: &str, helpers: &str, defs: &[(&str, &str)]) -> String {
    exports_program_at(imports, helpers, defs, 100_000)
}

fn exports_program_at(imports: &str, helpers: &str, defs: &[(&str, &str)], n: u64) -> String {
    let mut source = format!("import Std ({imports})\n\n{helpers}\n");
    for (name, body) in defs {
        source.push_str(&format!("export def {name} (n: Nat): Nat := {body}\n\n"));
    }
    source.push_str("def main () : {IO} () :=\n");
    for (name, _) in defs {
        source.push_str(&format!("  IO.print (Nat.toText ({name} {n}))\n"));
    }
    source
}

/// Std functions that fold a long list are stack-safe: `Map.indexBy`,
/// `Map.groupBy`, `List.foldRight`, `Map.foldRight` and `Set.foldRight` (once
/// `foldRight`s that recursed once per element), and the `foldLeft` builders
/// `Map.fromListWith`, `Map.counts` and `Set.fromList`, on 100,000 elements.
/// A plain Node's default stack overflowed at about 8,000 elements. Native
/// and JS print the same.
#[test]
fn std_folds_over_long_lists_are_stack_safe() {
    let defs = [
        (
            "indexed",
            "Map.size (Map.indexBy (input n) (x => x % 1000))",
        ),
        (
            "indexedFirst",
            "Map.getOr (Map.map (Map.indexBy (input n) (x => x % 1000)) (x => x)) 0 7",
        ),
        (
            "grouped",
            "List.foldLeft (Map.getOr (Map.groupBy (input n) (x => x % 10)) [] 3) 0 (acc x => acc * 3 + x) % 1000003",
        ),
        (
            "summed",
            "Map.size (Map.fromListWith (List.map (input n) (x => (x % 500, x))) (a b => a + b))",
        ),
        ("setSize", "Set.size (Set.fromList (input n))"),
        (
            "counted",
            "Map.getOr (Map.counts (List.map (input n) (x => x % 7))) 0 3",
        ),
        ("listRight", "List.foldRight (input n) 0 (x acc => x + acc)"),
        (
            "mapRight",
            "Map.foldRight (Map.indexBy (input n) (x => x)) 0 (k v acc => v + acc)",
        ),
        (
            "setRight",
            "Set.foldRight (Set.fromList (input n)) 0 (k acc => k + acc)",
        ),
    ];
    let source = exports_program(
        "IO, List, Map, Nat, Set",
        "def input (n: Nat): List Nat := List.range n\n",
        &defs,
    );
    let names: Vec<&str> = defs.iter().map(|(name, _)| *name).collect();
    stack_safe_everywhere(&source_file("folds.sw", &source), &names);
}

/// Std list functions that recursed once per element, on 100,000 elements,
/// natively, with `run --js`, and from a plain Node, whose default stack
/// overflowed at 2,000 to 11,000 elements. The JS backend makes loops of
/// calls modulo addition (`List.length`'s `Succ (List.length xs)`,
/// `List.occurrences`, `List.indexOf`) and modulo append (`List.concat`'s
/// `List.append xs (List.concat xss)`, `List.concatMap`): with them
/// `List.flatMap`, `List.cross`, `List.padRight`, `List.dropRight`,
/// `List.transpose`, `Text.repeat`, `Text.padRight` and `Vec.fromList`,
/// which use them. `List.maxLength` and `List.splitGroups` (so
/// `List.transposeFill` and `List.splitBy`) are right folds, `Text.words` a
/// loop over the reversed characters, `List.mapAccumLeft` a loop with an
/// accumulator, `List.unzip` two maps, `List.span` `takeWhile` and
/// `dropWhile`, and `Vec.ofList` checks the length, then `Vec.fromListN`.
#[test]
fn std_list_functions_over_long_lists_are_stack_safe() {
    let defs = [
        ("length", "List.length (input n)"),
        ("indexOf", "List.indexOf (input n) n"),
        (
            "occurrences",
            "List.occurrences (input n) (x => x % 3 == 0)",
        ),
        (
            "concat",
            "size (List.concat (List.map (input n) (x => [x, x])))",
        ),
        ("concatMap", "size (List.concatMap (input n) (x => [x]))"),
        ("flatMap", "List.sum (List.flatMap (input n) (x => [x, 1]))"),
        ("cross", "size (List.cross (input n) [1, 2])"),
        ("padRight", "size (List.padRight (input n) (n + 5) 0)"),
        ("dropRight", "List.sum (List.dropRight (input n) 3)"),
        ("transpose", "size (List.transpose [input n, input n])"),
        (
            "transposeFill",
            "size (List.transposeFill (List.map (input n) (x => [x])) 0)",
        ),
        (
            "maxLength",
            "List.maxLength (List.map (input n) (x => List.replicate (x % 5) x))",
        ),
        (
            "splitBy",
            "size (List.splitBy (input n) (x => x % 10 == 0))",
        ),
        (
            "mapAccumLeft",
            "List.sum (Pair.snd (List.mapAccumLeft (input n) 0 (s x => (s + x, s % 7))))",
        ),
        (
            "unzip",
            "List.sum (Pair.snd (List.unzip (List.map (input n) (x => (x, x % 3)))))",
        ),
        (
            "span",
            "size (Pair.fst (List.span (input n) (x => x < n - 2)))",
        ),
        (
            "words",
            "size (Text.words (Text.fromList (List.map (input n) (i => if i % 10 == 9 then ' ' else 'a'))))",
        ),
        ("repeat", "Text.length (Text.repeat \"ab\" n)"),
        (
            "textPadRight",
            "Text.length (Text.padRight (Text.repeat \"a\" n) (n + n) 'x')",
        ),
        ("vecFromList", "Vec.sum (Vec.fromList (input n))"),
        (
            "vecOfList",
            "Option.getOrElse (Option.map (Vec.ofList n (input n)) Vec.sum) 0",
        ),
    ];
    let source = exports_program(
        "IO, List, Nat, Option, Pair, Text, Vec",
        "def input (n: Nat): List Nat := List.range n\n\n\
         def size (xs: List a): Nat := List.foldLeft xs 0 (count x => count + 1)\n",
        &defs,
    );
    let names: Vec<&str> = defs.iter().map(|(name, _)| *name).collect();
    stack_safe_everywhere(&source_file("lists.sw", &source), &names);
}

/// `List.distinct` (SW-454) is a loop with a `Set` of what it has seen: on
/// 1,000,000 elements, 100,000 of them different, natively, with `run --js`
/// and from a plain Node. The fold over the result depends on its order, so
/// the backends must agree on which occurrence each keeps.
#[test]
fn std_distinct_over_a_million_elements_is_stack_safe() {
    let defs = [(
        "distinctFold",
        "List.foldLeft (List.distinct (List.map (List.range n) (x => (x * 7) % 100000))) 0 (acc x => (acc * 31 + x) % 1000003)",
    )];
    let source = exports_program_at("IO, List, Nat", "", &defs, 1_000_000);
    stack_safe_everywhere_at(
        &source_file("distinct.sw", &source),
        &["distinctFold"],
        1_000_000,
    );
}

/// `Result.traverse` and `Vec.traverseOption` (SW-460) are loops that stop at
/// the first failure: on 1,000,000 elements, all succeeding and failing at
/// the last, natively, with `run --js` and from a plain Node, whose default
/// stack overflowed on the recursive forms.
#[test]
fn std_traversals_over_a_million_elements_are_stack_safe() {
    let defs = [
        (
            "traverseOk",
            "Result.getOrElse (Result.map (Result.traverse (List.range n) (x => if x < n then Ok (x % 7) else Err \"big\")) List.sum) 0",
        ),
        (
            "traverseErr",
            "Text.length (Result.errorOrElse (Result.traverse (List.range n) (x => if x + 1 < n then Ok x else Err (Nat.toText x))) \"none\")",
        ),
        (
            "traverseOption",
            "Option.getOrElse (Option.map (Vec.traverseOption (Vec.fromList (List.range n)) (x => if x < n then Some (x % 7) else None)) Vec.sum) 0",
        ),
        (
            "traverseOptionNone",
            "Option.getOrElse (Option.map (Vec.traverseOption (Vec.fromList (List.range n)) (x => if x + 1 < n then Some x else None)) Vec.sum) 7",
        ),
    ];
    let source = exports_program_at(
        "IO, List, Nat, Option, Result, Text, Vec",
        "",
        &defs,
        1_000_000,
    );
    let names: Vec<&str> = defs.iter().map(|(name, _)| *name).collect();
    stack_safe_everywhere_at(&source_file("traversals.sw", &source), &names, 1_000_000);
}

/// `List.flatMap`, with a pure callback and with a `Fail` one, and the
/// `List.concat` under it, on 1,000,000 elements (two million in the
/// result), natively, with `run --js` and from a plain Node
/// (docs/proposals/effect-polymorphic-list.md §3). The results are folded
/// with loops, so only `flatMap` itself is measured.
#[test]
fn std_flat_map_over_a_million_elements_is_stack_safe() {
    let defs = [
        (
            "flatMapped",
            "List.sum (List.flatMap (List.range n) (x => [x, x]))",
        ),
        (
            "flatMappedSize",
            "size (List.flatMap (List.range n) (x => [x, 1]))",
        ),
        (
            "concatenated",
            "size (List.concat (List.map (List.range n) (x => [x, x])))",
        ),
        (
            "flatMappedFail",
            "Result.getOrElse (Result.map (Fail.toResult (() => List.flatMap (List.range n) checked)) List.sum) 0",
        ),
    ];
    let source = exports_program_at(
        "Fail, IO, List, Nat, Result",
        "def size (xs: List a): Nat := List.foldLeft xs 0 (count x => count + 1)\n\n\
         def checked (x: Nat): {Fail} (List Nat) := if x > 1000000000 then Fail.fail \"too big\" else [x, 1]\n",
        &defs,
        1_000_000,
    );
    let names: Vec<&str> = defs.iter().map(|(name, _)| *name).collect();
    stack_safe_everywhere_at(&source_file("flat-map.sw", &source), &names, 1_000_000);
}
