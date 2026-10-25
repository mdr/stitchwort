//! The kernel's conversion check, and the elaborator's unification,
//! recognise identical closures without running them (`value.rs`,
//! `same_closure`), and, comparing two definitions by their case trees,
//! answer a pair of calls already found equal from a record
//! (`same_stuck_trees`, SW-395; `reject/case-tree-chains-*.sw` exercise it,
//! one with a metavariable solved and then taken back). Both are turned off
//! together. That may only skip work, never change a verdict. The
//! shortcuts can only answer "equal", so the risk is a program wrongly
//! accepted: every rejected example (the soundness suite included) must get
//! exactly the same diagnostics with the shortcut turned off. Accepted
//! examples are left out to keep the gate fast (D74, 20 Oct 2026): the
//! shortcut can't turn an acceptance into a rejection.

use std::path::Path;

use stitchwort_core::value::set_shortcuts_disabled;
use stitchwort_driver::driver::{Session, par_map, with_stack};

const STACK: usize = 64 * 1024 * 1024;

fn examples() -> Vec<(String, String)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut found = Vec::new();
    for dir in ["reject", "soundness"] {
        let mut paths: Vec<_> = std::fs::read_dir(root.join(dir))
            .expect("examples directory")
            .map(|e| e.expect("entry").path())
            .filter(|p| p.extension().is_some_and(|e| e == "sw"))
            .collect();
        paths.sort();
        for path in paths {
            let name = format!("{dir}/{}", path.file_name().unwrap().to_string_lossy());
            found.push((name, std::fs::read_to_string(&path).expect("readable")));
        }
    }
    found
}

/// The outcome of checking `text`, prelude included, with the shortcut on or
/// off: every diagnostic, in full. The switch is per thread, so examples can
/// be checked side by side (`par_map`).
fn verdict(name: &str, text: &str, shortcuts: bool) -> String {
    set_shortcuts_disabled(!shortcuts);
    let mut session = Session::for_stack(STACK);
    let result = session.load(name, text).map(|_| ());
    set_shortcuts_disabled(false);
    format!("{result:?}")
}

#[test]
fn every_rejected_example_gets_the_same_verdict_without_the_shortcut() {
    with_stack(STACK, || {
        let examples = examples();
        assert!(examples.len() > 250, "only {} examples", examples.len());
        let verdicts = par_map(STACK, &examples, |(name, text)| {
            let with = verdict(name, text, true);
            let without = verdict(name, text, false);
            assert_eq!(with, without, "{name}: the verdict depends on the shortcut");
            with.starts_with("Err")
        });
        let rejected = verdicts.iter().filter(|rejected| **rejected).count();
        assert!(rejected > 200, "only {rejected} rejections compared");
    });
}
