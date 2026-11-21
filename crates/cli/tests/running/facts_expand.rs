//! `check --expand-facts` end to end: the terms it writes for every
//! `byFacts` of `examples/accept/facts-probes.sw` and `facts-forms.sw` check
//! again (docs/syntax.md, "byFacts").

use std::path::Path;
use std::process::{Command, Output, Stdio};

use crate::common;

fn output(mut command: Command, dir: &Path) -> Output {
    command
        .current_dir(dir)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("start stitchwort")
}

#[test]
fn facts_expansions_check_again() {
    // `facts-forms.sw`'s `someEqual` used a constructor equation's field,
    // which has no written form, so one `byFacts` stays there.
    for (file, name, kept) in [
        ("facts-probes.sw", "facts_probes_expand", 0),
        ("facts-forms.sw", "facts_forms_expand", 1),
    ] {
        let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("make the test's folder");
        let source = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../examples/accept")
            .join(file);
        std::fs::copy(&source, dir.join(file)).expect("copy the example");

        let expand = output(common::cli_with("check", &["--expand-facts", file]), &dir);
        let stderr = String::from_utf8_lossy(&expand.stderr);
        assert!(expand.status.success(), "--expand-facts failed:\n{stderr}");
        let expanded = std::fs::read_to_string(dir.join(file)).expect("read the expansion");
        let left = (expanded.lines())
            .filter(|l| !l.trim_start().starts_with("--") && l.contains("byFacts"))
            .count();
        assert_eq!(left, kept, "unexpected byFacts left:\n{expanded}");
        insta::assert_snapshot!(format!("{name}_text"), expanded);

        let check = output(common::cli_with("check", &["--no-cache", file]), &dir);
        assert!(
            check.status.success(),
            "the expansion of {file} doesn't check:\n{}{}",
            String::from_utf8_lossy(&check.stdout),
            String::from_utf8_lossy(&check.stderr)
        );
    }
}
