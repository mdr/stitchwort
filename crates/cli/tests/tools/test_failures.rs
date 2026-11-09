//! A failed comparison test shows both sides (SW-216), with the built
//! command, on a file written to a temporary folder.

use std::path::Path;
use std::path::PathBuf;
use std::process::{Command, Stdio};

const SOURCE: &str = r#"import Std (List)

def part1 (n: Nat): Nat := n + 1

test "equal" := part1 1 == 2
test "part 1 on the example" := part1 1 == 3
test "not equal" := part1 1 != 2
test "less" := part1 5 < 3
test "greater or equal" := 2 >= part1 5
test "greater" := 1 > part1 5
test "proposition" := part1 1 = 3
test "long value" := List.range 0 1000 == []
test "huge value" := List.range 0 100000 == []
test "not a comparison" := List.all [1, 2, 3] (n => n < 3)
"#;

fn folder(name: &str) -> PathBuf {
    folder_with(name, SOURCE)
}

fn folder_with(name: &str, source: &str) -> PathBuf {
    let dir =
        std::env::temp_dir().join(format!("stitchwort-failures-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("t.sw"), source).unwrap();
    dir
}

fn run(dir: &Path, args: &[&str]) -> String {
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("test")
        .arg("t.sw")
        .args(args)
        .current_dir(dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn a_failed_comparison_shows_both_sides() {
    let dir = folder("sides");
    insta::assert_snapshot!("failed_comparisons", run(&dir, &["--no-cache"]));
}

#[test]
fn a_cached_failure_still_shows_both_sides() {
    let dir = folder("cached");
    let first = run(&dir, &[]);
    let second = run(&dir, &[]);
    assert!(second.contains("cached"), "{second}");
    // Only the "ran" / "cached" column and the summary differ.
    let lines = |s: &str| -> Vec<String> {
        s.lines()
            .filter(|l| l.contains("left:") || l.contains("right:"))
            .map(str::to_string)
            .collect()
    };
    assert_eq!(lines(&first), lines(&second));
    assert!(!lines(&second).is_empty());
}

/// Tests run on the fast runtime by default and on the reference evaluator
/// with `--reference` (SW-412): the same outcomes and failures, and each
/// runner's results are cached apart.
#[test]
fn the_reference_evaluator_gives_the_same_results() {
    let dir = folder("reference");
    let fast = run(&dir, &[]);
    let reference = run(&dir, &["--reference"]);
    assert!(!reference.contains("cached"), "{reference}");
    assert_eq!(fast, reference);
    assert!(run(&dir, &["--reference"]).contains("cached"));
}

/// What a failure says about the part of the test that is false (D601):
/// through `let`s and `&&`, with where the first difference of two lists or
/// texts is.
const PARTS: &str = r##"import Std (List, Option, Text)

def part1 (n: Nat): Nat := n + 1
def nums (n: Nat): List Nat := [1, 2, n]

type Point = { x: Nat, y: Nat }
type Item = { id: Text, tags: List Nat }
type Shape = | Circle (r: Nat) | Square (side: Nat)

def item (n: Nat): Item := { id = "x", tags = [1, 2, n] }

test "let block" :=
  let a := part1 1
  let b := a + 5
  b == 3
test "and" := part1 1 == 2 && part1 2 == 4
test "and, first false" := part1 1 == 5 && part1 2 == 4
test "and three" := part1 1 == 2 && part1 2 == 3 && part1 3 == 5
test "and, a proposition" := part1 1 == 2 && 7 < 3
test "and let" :=
  let a := part1 1
  a == 2 && a < 1
test "and, not a comparison" := part1 1 == 2 && List.all [1, 2] (n => n < 2)
test "list" := nums 4 == [1, 2, 3]
test "list shorter" := nums 3 == [1, 2]
test "list longer" := [1] == nums 3
test "text" := "hello world" == "hello there"
test "text prefix" := "hello" == "hello!"
test "record" := ({ x = 1, y = 2 } : Point) == { x = 1, y = 3 }
test "option" := (Option.Some 1) == Option.None
test "list of lists" := [[1, 2], [3]] == [[1, 2], [4]]
test "long list, late difference" := List.range 0 1000 == List.append (List.range 0 500) (List.range 0 500)
test "long and" := List.range 0 1000 == List.range 0 1000 && List.range 0 300 == List.range 0 299
test "unequal, so no difference" := nums 3 != nums 3
test "and, a bracketed operand" := part1 1 == 2 && (nums 3).length == 2
test "nested records in lists" := [item 3] == [item 4]
test "second record, deep path" := [item 3, item 3] == [item 3, item 5]
test "constructor mismatch" := [Shape.Circle 1] == [Shape.Square 1]
test "constructor mismatch in a tuple" := (Option.Some 1, Option.Some 2) == (Option.Some 1, Option.None)
test "constructor field" := Option.Some (item 3) == Option.Some (item 9)
test "list length mismatch inside a record" := item 3 == { id = "x", tags = [1, 2, 3, 4] }
test "tuple part" := (1, [2, 3], "a") == (1, [2, 4], "a")
test "text in a record" := ({ id = "abc", tags = [] } : Item) == { id = "abd", tags = [] }
test "text lines" := "one\ntwo\nthree" == "one\n2\nthree\nfour"
test "a game frame, shown as lines" := Text.join ["+--------+", "|  .  @  |", "|  .     |", "+--------+"] '\n' == Text.join ["+--------+", "|  .     |", "|  .  @  |", "+--------+"] '\n'
test "long text, excerpt" := Text.join (List.replicate 20 "abc") ' ' == Text.join (List.append (List.replicate 10 "abc") (List.replicate 10 "abd")) ' '
test "a long frame, shown whole" :=Text.join (List.replicate 30 (Text.join (List.replicate 30 "#.") ' ')) '\n' == Text.join (List.append (List.replicate 29 (Text.join (List.replicate 30 "#.") ' ')) ["end"]) '\n'
"##;

#[test]
fn a_failed_test_names_the_false_part_and_where_values_differ() {
    let dir = folder_with("parts", PARTS);
    insta::assert_snapshot!("failed_parts", run(&dir, &["--no-cache"]));
}

/// SW-1000: `Float`s inside a list or a record print as literals, as a lone
/// one does, not as `{ bits = …, valid = ?1 }`.
#[test]
fn floats_inside_data_print_as_literals() {
    let source = "import Std (List, Float)\n\n\
                  type Stop = { name: Text, at: Float }\n\n\
                  test \"floats\" := [0.5, 1.5] == [0.5, 2.5]\n\
                  test \"stops\" := [{ name = \"a\", at = 0.5 }] == [{ name = \"a\", at = 0.25 }]\n";
    let dir = folder_with("floats", source);
    let out = run(&dir, &["--no-cache"]);
    assert!(out.contains("left:  [0.5, 1.5]"), "{out}");
    assert!(out.contains("at = 0.5"), "{out}");
    assert!(!out.contains("bits"), "{out}");
}

#[test]
fn a_cached_failure_still_names_the_false_part() {
    let dir = folder_with("parts-cached", PARTS);
    let first = run(&dir, &[]);
    let second = run(&dir, &[]);
    assert!(second.contains("cached"), "{second}");
    let lines = |s: &str| -> Vec<String> {
        s.lines()
            .filter(|l| l.contains("in: ") || l.contains("first difference"))
            .map(str::to_string)
            .collect()
    };
    assert_eq!(lines(&first), lines(&second));
    assert!(!lines(&second).is_empty());
}

/// Tests that run partial code (D1183): stepped as a partial `main` is, on
/// either runner, with plain pass or fail results, cached like any test.
const PARTIAL: &str = r#"def collatzSteps: Nat -> {Partial} Nat
  | 0 => 0
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

def check27(): {Partial} Bool := collatzSteps 27 == 111

test "27 takes 111 steps" := collatzSteps 27 == 111
test "through a partial helper" := check27 ()
test "a block" :=
  let steps := collatzSteps 6
  steps == 8 && collatzSteps 1 == 0
test "a wrong claim fails" := collatzSteps 27 == 110
test "a total test beside them" := 1 + 1 == 2
"#;

#[test]
fn partial_tests_pass_or_fail_on_both_runners_and_are_cached() {
    let dir = folder_with("partial", PARTIAL);
    let fast = run(&dir, &[]);
    let reference = run(&dir, &["--reference"]);
    let expected = "  ✓ 27 takes 111 steps        ran
  ✓ through a partial helper  ran
  ✓ a block                   ran
  ✗ a wrong claim fails       ran  (evaluated to False)
  ✓ a total test beside them  ran
5 test(s): 4 passed, 1 failed (0 from the cache)
";
    assert_eq!(fast, expected);
    assert_eq!(reference, expected);
    let again = run(&dir, &[]);
    assert!(again.contains("(5 from the cache)"), "{again}");
}

/// Checking never runs a test, so a test that loops forever (a bug, D1183)
/// can't hang `stitchwort check`.
#[test]
fn checking_never_runs_a_looping_test() {
    let dir = folder_with(
        "looping",
        "def spin (n: Nat): {Partial} Nat := spin (n + 1)\n\ntest \"loops\" := spin 0 == 0\n",
    );
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("check")
        .arg("t.sw")
        .current_dir(&dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    assert!(output.status.success(), "{output:?}");
}

/// What `test --native` is checked on: passing, failing and partial tests,
/// and one that recurses too deeply for the machine (which hands it to the
/// reference evaluator, which reports it) but not for native code.
const NATIVE: &str = r#"import Std (List)

def collatzSteps: Nat -> {Partial} Nat
  | 0 => 0
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

def deeper: Nat -> Nat
  | 0 => 0
  | Succ k => deeper k * 2

test "passes" := List.sum (List.range 0 100) == 4950
test "fails" := List.sum (List.range 0 100) == 4951
test "partial, passes" := collatzSteps 27 == 111
test "partial, fails" := collatzSteps 27 == 110
test "too deep" := deeper 3000000 == 0
"#;

/// `test --native` (SW-2543): the same outcomes and messages as `test`,
/// except where native code's deeper recursion limit (SW-2471) lets a test
/// pass that runs out on the machine; and a cache of its own.
#[test]
fn native_code_gives_the_machines_results_but_for_the_depth_limit_and_keeps_its_own_cache() {
    let dir = folder_with("native", NATIVE);
    let machine = run(&dir, &["--no-cache"]);
    let native = run(&dir, &["--no-cache", "--native"]);
    assert!(machine.contains("1 ran out of resources"), "{machine}");
    assert!(!native.contains("ran out of resources"), "{native}");
    // Every other test has the same outcome.
    let others = |out: &str| -> Vec<String> {
        out.lines()
            .filter(|line| {
                line.contains("passes") || line.contains("fails") || line.contains("partial")
            })
            .map(str::to_owned)
            .collect()
    };
    assert_eq!(others(&machine), others(&native));

    // `--verbose` says what ran where, on standard error.
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["test", "t.sw", "--no-cache", "--native", "--verbose"])
        .current_dir(&dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    let notes = String::from_utf8(output.stderr).unwrap();
    assert!(notes.contains("native: compiled 5 test(s)"), "{notes}");
    assert!(
        notes.contains("native: 5 test(s) ran natively, 0 on the machine"),
        "{notes}"
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), native);

    // Each runner's results are its own: a machine run doesn't satisfy a
    // native one, nor the reverse.
    let machine_first = run(&dir, &[]);
    assert!(
        machine_first.contains("(0 from the cache)"),
        "{machine_first}"
    );
    let native_first = run(&dir, &["--native"]);
    assert!(
        native_first.contains("(0 from the cache)"),
        "{native_first}"
    );
    // The machine's run kept 4 (running out isn't cached), native code's 5.
    assert!(run(&dir, &[]).contains("(4 from the cache)"));
    assert!(run(&dir, &["--native"]).contains("(5 from the cache)"));
}

/// The `test` file of the partial tests above, natively: each partial test
/// is stepped as the machine steps it.
#[test]
fn partial_tests_run_natively() {
    let dir = folder_with("partial-native", PARTIAL);
    assert_eq!(
        run(&dir, &["--no-cache", "--native"]),
        run(&dir, &["--no-cache"])
    );
}
