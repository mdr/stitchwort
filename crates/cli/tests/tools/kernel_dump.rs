//! `STITCHWORT_DUMP_KERNEL`: the type and value the kernel is given for one
//! declaration (crates/elab/src/kernel.rs).

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
