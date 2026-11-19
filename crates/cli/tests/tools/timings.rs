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

/// A row of the declaration table: name, elaboration ms, kernel ms, total ms, steps,
/// nodes, largest read-back, most frames.
struct Row {
    name: String,
    ms: f64,
    steps: u64,
    nodes: u64,
    readback: u64,
    frames: u64,
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
        // the seven numbers are the last seven columns.
        let words: Vec<&str> = line.split_whitespace().collect();
        let numbers: Option<Vec<f64>> = words
            .iter()
            .rev()
            .take(7)
            .map(|w| w.parse::<f64>().ok())
            .collect();
        match numbers {
            Some(n) if words.len() > 7 => rows.push(Row {
                name: words[..words.len() - 7].join(" "),
                ms: n[4],
                steps: n[3] as u64,
                nodes: n[2] as u64,
                readback: n[1] as u64,
                frames: n[0] as u64,
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
         theorem slow: List.length (List.range 0 3000) = 3000 := byComputing\n\n\
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
    assert!(names.contains(&"Main.slow"), "{names:?}");
    assert!(names.contains(&"Main.even, Main.odd"), "{names:?}");
    assert!(names.contains(&"Main.test \"small\""), "{names:?}");
    assert!(names.contains(&"Main.small24"), "{names:?}");
    // The table is sorted by wall-clock time, so under load a descheduled
    // trivial declaration can overtake `slow`; the sortedness loop above
    // checks the order itself. `slow`'s work is deterministic: it took
    // evaluation steps, more than any other row from this file, where a
    // constant made one small term.
    let slow = rows.iter().find(|r| r.name == "Main.slow").expect("slow");
    assert!(slow.steps > 3000, "{}", slow.steps);
    assert!(
        rows.iter().all(|r| r.steps <= slow.steps),
        "{} is not the most steps: {:?}",
        slow.name,
        rows.iter().map(|r| (&r.name, r.steps)).collect::<Vec<_>>()
    );
    let small = rows.iter().find(|r| r.name == "Main.small3").unwrap();
    assert!(small.nodes > 0 && small.nodes < 10, "{}", small.nodes);

    // By default, the 20 slowest, and a count of the rest.
    let (rows, after) = declaration_rows(&path, "1");
    assert_eq!(rows.len(), 20);
    assert_eq!(
        after,
        format!(
            "({} more; --timings=all lists every declaration)",
            all.len() - 20
        )
    );
}

/// A theorem that unfolds an opaque definition reads its body back whole
/// (docs/proposals/term-sharing.md, stage 0c): `replicate k n` is `4k + 5`
/// nodes by `Limits::size`'s count, and `k` frames deep to compute.
#[test]
fn the_largest_read_back_and_deepest_frames_are_reported() {
    let source = |k: usize| {
        format!(
            "import Std (List, Nat, Eq)\n\n\
             def replicate : Nat -> a -> List a\n  | Zero,   x => Nil\n  \
             | Succ n, x => Cons x (replicate n x)\n\n\
             opaque def big (n: Nat): List Nat := replicate {k} n\n\n\
             theorem t (n: Nat): big n = big n unfolding big := \
             rewrite (byComputing: big n = big n)\n"
        )
    };
    let theorem = |k: usize| {
        let path = source_file(&format!("readback{k}.sw"), &source(k));
        let (rows, _) = declaration_rows(&path, "decls");
        let row = rows.into_iter().find(|r| r.name == "Main.t").expect("t");
        (row.readback, row.frames)
    };
    let (small, small_frames) = theorem(50);
    let (large, large_frames) = theorem(100);
    assert_eq!(small, 4 * 50 + 5);
    assert_eq!(large, 4 * 100 + 5);
    assert!(small_frames > 0 && large_frames > 0);
    // Frames follow how deeply a check recurses: checking a list literal
    // holds one per element.
    let list = |n: usize| {
        let items: Vec<String> = (1..=n).map(|i| i.to_string()).collect();
        let list = format!("[{}]", items.join(", "));
        let path = source_file(
            &format!("frames{n}.sw"),
            &format!("import Std (List, Nat)\n\ntheorem l: {list} = {list} := byComputing\n"),
        );
        let (rows, _) = declaration_rows(&path, "decls");
        rows.into_iter()
            .find(|r| r.name == "Main.l")
            .expect("l")
            .frames
    };
    assert_eq!((list(10), list(20)), (10, 20));
    // Declarations that read nothing back say so.
    let path = source_file("readback_none.sw", "def one: Nat := 1\n");
    let (rows, _) = declaration_rows(&path, "decls");
    let one = rows.iter().find(|r| r.name == "Main.one").expect("one");
    assert_eq!(one.readback, 0);
    // The summary table lists the declaration among the largest read-backs;
    // std's own derived instances read back more, so it isn't the largest.
    let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--no-cache"])
        .arg(source_file("readback_summary.sw", &source(50)))
        .env("STITCHWORT_TIMINGS", "decls")
        .output()
        .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let row = stderr
        .lines()
        .rfind(|l| l.trim_start().starts_with("Main.t "))
        .unwrap_or_else(|| panic!("{stderr}"));
    assert_eq!(
        row.split_whitespace().collect::<Vec<_>>(),
        ["Main.t", "205", "5"]
    );
}

/// `check --timings[=all|N]`: the namespace table, then the declaration
/// table with elaboration, kernel and total times, slowest first. Asserts
/// on the layout, not the numbers.
#[test]
fn check_timings_lists_namespaces_and_declarations() {
    let base = std::env::temp_dir().join(format!("stitchwort-timings-flag-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let dir = base.join("proj");
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), "").unwrap();
    std::fs::write(
        dir.join("src/a.sw"),
        "namespace A\n\ndef one: Nat := 1\n\ndef two: Nat := 2\n\ndef three: Nat := 3\n",
    )
    .unwrap();
    let run = |args: &[&str]| {
        let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .arg("check")
            .args(args)
            .current_dir(&dir)
            .output()
            .expect("run stitchwort");
        assert!(out.status.success(), "{out:?}");
        String::from_utf8_lossy(&out.stderr).into_owned()
    };

    // Cold: the project's own declarations, by full name.
    let stderr = run(&["--no-cache", "--timings=all", "A"]);
    let table: Vec<&str> = stderr
        .lines()
        .skip_while(|l| !l.starts_with("declaration "))
        .collect();
    let header: Vec<&str> = table[0].split_whitespace().collect();
    assert_eq!(
        header[..8],
        [
            "declaration",
            "elab",
            "ms",
            "kernel",
            "ms",
            "total",
            "ms",
            "steps"
        ]
    );
    for name in ["A.one", "A.two", "A.three"] {
        assert!(
            table.iter().any(|l| l.starts_with(&format!("{name} "))),
            "{name} missing:\n{stderr}"
        );
    }
    assert!(stderr.lines().any(|l| l.starts_with("A ")), "{stderr}");
    assert!(stderr.lines().any(|l| l.starts_with("total ")), "{stderr}");

    // A count limits the table and says how many it left out.
    let stderr = run(&["--no-cache", "--timings=2", "A"]);
    assert!(
        stderr.contains("more; --timings=all lists every declaration)"),
        "{stderr}"
    );
    // Without the flag, nothing is printed.
    let stderr = run(&["--no-cache", "A"]);
    assert!(!stderr.contains("declaration "), "{stderr}");

    // Warm: the namespace comes from the cache, and is marked, not timed.
    run(&["A"]);
    let stderr = run(&["--timings", "A"]);
    assert!(stderr.contains("A (cached)"), "{stderr}");
    // Its declarations weren't checked, so they have no rows.
    let stderr = run(&["--timings=all", "A"]);
    assert!(!stderr.contains("A.one"), "{stderr}");
}
