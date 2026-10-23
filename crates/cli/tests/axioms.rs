//! `stitchwort axioms` (docs/proposals/map-equality.md §10, D864 and D925;
//! test A9), end to end with the built command.

use std::path::Path;
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

fn example() -> String {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/accept/quot-axioms.sw")
        .display()
        .to_string()
}

/// What `axioms` prints for `name` in the example, after checking it
/// succeeded.
fn report(name: &str) -> String {
    let output = stitchwort(Path::new("."), &["axioms", &example(), name]);
    assert!(
        output.status.success(),
        "{name}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

/// A9: `Quot.sound` is reported for a `def` with the node inline, and for
/// one that reaches it only through a theorem's proof (directly, or through
/// another `def`).
#[test]
fn a9_quot_sound_is_reported_wherever_it_is_reached() {
    for name in ["inline", "viaTheorem", "viaDef", "same"] {
        assert_eq!(report(name), "Quot.sound\n", "{name}");
    }
}

/// A9: nothing is reported for a definition using neither, including one
/// that uses `Quot.ind` and `Quot.lift`, which are rules, not axioms.
#[test]
fn a9_nothing_is_reported_without_quot_sound() {
    for name in ["plain", "usesLift", "usesInd"] {
        assert_eq!(report(name), "", "{name}");
    }
}

#[test]
fn an_unknown_name_is_an_error() {
    let output = stitchwort(Path::new("."), &["axioms", &example(), "nope"]);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("there's no definition `nope`"));
}

/// In a project the name is given in full, as for `run`.
#[test]
fn a_project_name_is_given_in_full() {
    let base = std::env::temp_dir().join(format!("stitchwort-axioms-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let dir = base.join("proj");
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), "").unwrap();
    std::fs::write(
        dir.join("src/a.sw"),
        "namespace Proof\n\ndef AllTrue (x: Bool) (y: Bool): Prop := Unit\ndef Q: Type := Quot Bool AllTrue\n\ntheorem same: (Quot.mk False: Q) = Quot.mk True := Quot.sound Trivial\n\ndef plain: Nat := 1\n",
    )
    .unwrap();
    let same = stitchwort(&dir, &["axioms", "Proof.same"]);
    let plain = stitchwort(&dir, &["axioms", "Proof.plain"]);
    let _ = std::fs::remove_dir_all(&base);
    assert_eq!(
        String::from_utf8_lossy(&same.stderr),
        "",
        "stdout: {}",
        String::from_utf8_lossy(&same.stdout)
    );
    assert_eq!(String::from_utf8_lossy(&same.stdout), "Quot.sound\n");
    assert_eq!(String::from_utf8_lossy(&plain.stdout), "");
}
