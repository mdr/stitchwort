//! `stitchwort uses` (SW-4158): who refers to a declaration, read off the
//! checked terms, so a short name defined in two namespaces is told apart.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

fn stitchwort(cwd: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .arg("--no-cache")
        .current_dir(cwd)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

/// Namespaces `A` and `B` both define `x`; `A.useA` and `A.alsoA` refer to
/// `A.x`, `B.useB` to `B.x`, and `B.lonely` to nothing. In `B`, the theorem
/// `lonelyFact` is used by nothing, `testedFact` only by a test (through
/// `pick`), and `lonelyExample` is a closed example. `deadPing` and
/// `deadPong` refer only to each other, so `--unused` counts both as used
/// while `--dead` reports both unless one is a root.
fn project(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-uses-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::write(
        dir.join("src/a.sw"),
        "namespace A\n\n\
         def x: Nat := 1\n\n\
         def useA: Nat := x + 1\n\n\
         theorem alsoA: x = 1 := byComputing\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("src/b.sw"),
        "namespace B\n\n\
         def x: Nat := 2\n\n\
         def useB: Nat := x + 2\n\n\
         def lonely: Nat := 3\n\n\
         theorem lonelyFact: x = 2 := byComputing\n\n\
         theorem testedFact: x = 2 := byComputing\n\n\
         theorem lonelyExample: x = 2 := byComputing\n\n\
         def pick (h: x = 2): Nat := 5\n\n\
         test \"facts\" := pick testedFact == 5\n\n\
         theorem deadPing ∀ (n: Nat): True := match n with\n  \
         | 0 => byComputing\n  \
         | Succ n => deadPong n\n\n\
         theorem deadPong ∀ (n: Nat): True := match n with\n  \
         | 0 => byComputing\n  \
         | Succ n => deadPing n\n",
    )
    .unwrap();
    dir
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).to_string()
}

#[test]
fn uses_lists_only_the_users_of_the_named_declaration() {
    let dir = project("full");
    let out = stitchwort(&dir, &["uses", "A.x"]);
    let json = stitchwort(&dir, &["uses", "B.x", "--json"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = text(&out.stdout);
    assert_eq!(out.status.code(), Some(0), "{stdout}{}", text(&out.stderr));
    assert!(stdout.contains("`A.x` is used by 2:"), "{stdout}");
    assert!(stdout.contains("/src/a.sw:5"), "{stdout}");
    assert!(stdout.contains("/src/a.sw:7"), "{stdout}");
    assert!(!stdout.contains("B.useB"), "{stdout}");
    let json = text(&json.stdout);
    assert!(json.contains(r#""declaration":"B.useB""#), "{json}");
    assert!(!json.contains("A.useA"), "{json}");
}

#[test]
fn a_short_name_in_two_namespaces_is_ambiguous_and_a_unique_one_works() {
    let dir = project("short");
    let ambiguous = stitchwort(&dir, &["uses", "x"]);
    let unique = stitchwort(&dir, &["uses", "lonely"]);
    let unused = stitchwort(&dir, &["uses", "--unused", "B"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&ambiguous.stderr);
    assert_eq!(ambiguous.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("`A.x`") && stderr.contains("`B.x`"),
        "{stderr}"
    );
    assert!(text(&unique.stdout).contains("`B.lonely` is used by nothing"));
    let unused = text(&unused.stdout);
    assert!(
        unused.contains("B.lonely") && unused.contains("B.useB"),
        "{unused}"
    );
    assert!(!unused.contains("B.x  "), "{unused}");
    assert!(unused.contains("B.lonelyFact"), "{unused}");
    assert!(!unused.contains("B.testedFact"), "{unused}");
    assert!(!unused.contains("B.lonelyExample"), "{unused}");
}

#[test]
fn dead_lists_a_pair_of_theorems_that_only_refer_to_each_other() {
    let dir = project("dead");
    let unused = stitchwort(&dir, &["uses", "--unused", "B"]);
    let dead = stitchwort(&dir, &["uses", "--unused", "--dead", "B"]);
    let rooted = stitchwort(
        &dir,
        &["uses", "--unused", "--dead", "B", "--root", "B.deadPing"],
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(unused.status.code(), Some(0), "{}", text(&unused.stderr));
    assert_eq!(dead.status.code(), Some(0), "{}", text(&dead.stderr));
    assert_eq!(rooted.status.code(), Some(0), "{}", text(&rooted.stderr));
    let unused = text(&unused.stdout);
    assert!(
        !unused.contains("B.deadPing") && !unused.contains("B.deadPong"),
        "{unused}"
    );
    let dead = text(&dead.stdout);
    assert!(
        dead.contains("B.deadPing") && dead.contains("B.deadPong"),
        "{dead}"
    );
    let rooted = text(&rooted.stdout);
    assert!(
        !rooted.contains("B.deadPing") && !rooted.contains("B.deadPong"),
        "{rooted}"
    );
}
