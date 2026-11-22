//! `STITCHWORT_DUMP_KERNEL`: the type and value the kernel is given for one
//! declaration (crates/elab/src/kernel.rs). `STITCHWORT_BIG_READBACK`: every
//! read-back over a node count, with a backtrace (crates/core/src/budget.rs).

use std::process::Command;

#[test]
fn dumps_the_named_declarations_type_and_value_once() {
    let dir = std::env::temp_dir().join(format!("stitchwort-kernel-dump-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("dump.sw");
    std::fs::write(&path, "def double (n: Nat): Nat := n\n").expect("write source");

    let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--no-cache"])
        .arg(&path)
        .env("STITCHWORT_DUMP_KERNEL", "Main.double")
        .output()
        .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "check failed:\n{stderr}");
    assert!(
        stderr
            .lines()
            .any(|line| line == "kernel dump: Main.double"),
        "{stderr}"
    );
    assert!(stderr.contains("  type: Nat → Nat"), "{stderr}");
    assert!(stderr.contains("  value: "), "{stderr}");
    assert_eq!(
        stderr.matches("kernel dump: ").count(),
        1,
        "printed once:\n{stderr}"
    );
}

#[test]
fn reports_readbacks_over_the_given_node_count() {
    let dir = std::env::temp_dir().join(format!("stitchwort-big-readback-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("readback.sw");
    // Unfolding `big` reads its body back: four nodes a `replicate`, plus
    // the argument.
    let source = "import Std (List, Nat, Eq)\n\n\
         def replicate: Nat -> a -> List a\n  \
         | Zero, x => Nil\n  \
         | Succ n, x => Cons x (replicate n x)\n\n\
         opaque def big (n: Nat): List Nat := replicate 1 n\n\n\
         theorem t (n: Nat): big n = big n unfolding big := \
         rewrite (byComputing: big n = big n)\n";
    std::fs::write(&path, source).expect("write source");

    let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--no-cache"])
        .arg(&path)
        .env("STITCHWORT_BIG_READBACK", "1")
        .output()
        .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "check failed:\n{stderr}");
    assert!(
        stderr
            .lines()
            .any(|line| line.starts_with("big readback: ") && line.contains("nodes in Main.t")),
        "no report for Main.t:\n{stderr}"
    );

    let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--no-cache"])
        .arg(&path)
        .env_remove("STITCHWORT_BIG_READBACK")
        .output()
        .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "check failed:\n{stderr}");
    assert!(
        !stderr
            .lines()
            .any(|line| line.starts_with("big readback: ")),
        "reported with the variable unset:\n{stderr}"
    );
}
