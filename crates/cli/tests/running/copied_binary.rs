//! A copy of the binary kept outside the checkout (a "before" binary in a
//! scratch folder) finds the standard library in the tree it was built from
//! (SW-4789).

#[test]
fn a_copied_binary_finds_the_library_it_was_built_from() {
    // Not under `CARGO_TARGET_TMPDIR`: that is inside the checkout, where the
    // executable's own ancestors would find the library without the fallback.
    let dir = std::env::temp_dir().join(format!("sw-4789-copied-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("make the test's folder");
    let copy = dir.join("stitchwort-copy");
    std::fs::copy(env!("CARGO_BIN_EXE_stitchwort"), &copy).expect("copy the binary");
    let program = dir.join("tiny.sw");
    std::fs::write(&program, "def main : Nat := 1 + 2\n").expect("write the program");

    let out = std::process::Command::new(&copy)
        .arg("check")
        .arg("--no-cache")
        .arg(&program)
        .current_dir(&dir)
        .env_remove("STITCHWORT_STD_DIR")
        .output()
        .expect("run the copy");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}
