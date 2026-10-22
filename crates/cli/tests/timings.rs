//! `STITCHWORT_TIMINGS`: the per-declaration table
//! (crates/elab/src/timings.rs, docs/proposals/proof-check-speed.md).

use std::path::PathBuf;
use std::process::Command;

/// Writes `source` to a temporary file called `name`.
fn source_file(name: &str, source: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-timings-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join(name);
    std::fs::write(&path, source).expect("write source");
    path
}

/// A row of the declaration table: name, elaboration ms, kernel ms, steps,
/// nodes.
struct Row {
    name: String,
    ms: f64,
    steps: u64,
    nodes: u64,
}

/// Checks `path` with `STITCHWORT_TIMINGS=value`; the declaration table's
/// rows, and the line after them.
fn declaration_rows(path: &PathBuf, value: &str) -> (Vec<Row>, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--no-cache"])
        .arg(path)
        .env("STITCHWORT_TIMINGS", value)
        .output()
        .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(out.status.success(), "check failed:\n{stderr}");
    let mut lines = stderr
        .lines()
        .skip_while(|l| !l.starts_with("declaration "))
        .skip(1);
    let mut rows = Vec::new();
    let mut after = String::new();
    for line in lines.by_ref() {
        // The name may contain spaces (`Main.test "x"`, `Main.a, Main.b`):
        // the four numbers are the last four columns.
        let words: Vec<&str> = line.split_whitespace().collect();
        let numbers: Option<Vec<f64>> = words
            .iter()
            .rev()
            .take(4)
            .map(|w| w.parse::<f64>().ok())
            .collect();
        match numbers {
            Some(n) if words.len() > 4 => rows.push(Row {
                name: words[..words.len() - 4].join(" "),
                ms: n[3] + n[2],
                steps: n[1] as u64,
                nodes: n[0] as u64,
            }),
            _ => {
                after = line.to_string();
                break;
            }
        }
    }
    (rows, after)
}

#[test]
fn declarations_are_listed_slowest_first_with_full_names() {
    // `slow` computes a long list while checking; the rest are trivial.
    let mut source = String::from(
        "import Std (List, Nat)\n\n\
         theorem slow: List.length (List.range 3000) = 3000 := rfl\n\n\
         def even: Nat -> Bool\n  | Zero => True\n  | Succ n => odd n\n\n\
         def odd: Nat -> Bool\n  | Zero => False\n  | Succ n => even n\n\n\
         test \"small\" := 1 + 1 == 2\n",
    );
    for i in 0..25 {
        source.push_str(&format!("\ndef small{i}: Nat := {i}\n"));
    }
    let path = source_file("timings.sw", &source);

    // Every declaration checked is listed, the core's and the library's
    // too, slowest first.
    let (all, after) = declaration_rows(&path, "decls");
    assert_eq!(after, "");
    for pair in all.windows(2) {
        // Each time is rounded to 0.1 ms on its own.
        assert!(
            pair[0].ms + 0.11 >= pair[1].ms,
            "{} before {}",
            pair[0].name,
            pair[1].name
        );
    }
    assert!(all.iter().any(|r| r.name == "Std.List.length"));
    // This file's, by their full names; a mutually recursive pair is one row.
    let rows: Vec<&Row> = all.iter().filter(|r| r.name.starts_with("Main.")).collect();
    let names: Vec<&str> = rows.iter().map(|r| r.name.as_str()).collect();
    assert_eq!(rows.len(), 28, "{names:?}");
    assert_eq!(names[0], "Main.slow", "{names:?}");
    assert!(names.contains(&"Main.even, Main.odd"), "{names:?}");
    assert!(names.contains(&"Main.test \"small\""), "{names:?}");
    assert!(names.contains(&"Main.small24"), "{names:?}");
    // `slow` took evaluation steps; a constant made one small term.
    assert!(rows[0].steps > 3000, "{}", rows[0].steps);
    let small = rows.iter().find(|r| r.name == "Main.small3").unwrap();
    assert!(small.nodes > 0 && small.nodes < 10, "{}", small.nodes);

    // By default, the 20 slowest, and a count of the rest.
    let (rows, after) = declaration_rows(&path, "1");
    assert_eq!(rows.len(), 20);
    assert_eq!(
        after,
        format!(
            "({} more; STITCHWORT_TIMINGS=decls lists every declaration)",
            all.len() - 20
        )
    );
}
