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
test "not a comparison" := part1 1 == 2 && part1 2 == 4
"#;

fn folder(name: &str) -> PathBuf {
    let dir =
        std::env::temp_dir().join(format!("stitchwort-failures-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("t.sw"), SOURCE).unwrap();
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
