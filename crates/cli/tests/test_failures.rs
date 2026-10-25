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
test "long value" := List.range 1000 == []
test "huge value" := List.range 100000 == []
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
const PARTS: &str = r#"import Std (List, Option)

def part1 (n: Nat): Nat := n + 1
def nums (n: Nat): List Nat := [1, 2, n]

type Point = { x: Nat, y: Nat }

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
test "long list, late difference" := List.range 1000 == List.append (List.range 500) (List.range 500)
test "long and" := List.range 1000 == List.range 1000 && List.range 300 == List.range 299
test "unequal, so no difference" := nums 3 != nums 3
test "and, a bracketed operand" := part1 1 == 2 && (nums 3).length == 2
"#;

#[test]
fn a_failed_test_names_the_false_part_and_where_values_differ() {
    let dir = folder_with("parts", PARTS);
    insta::assert_snapshot!("failed_parts", run(&dir, &["--no-cache"]));
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
