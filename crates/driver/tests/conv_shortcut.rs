//! The kernel's conversion check recognises identical closures without
//! running them (`value.rs`, `same_closure`). That may only skip work, never
//! change a verdict: every example, accepted or rejected (the soundness suite
//! included), must get exactly the same result, the same diagnostics, with
//! the shortcut turned off.

use std::path::Path;

use stitchwort_core::value::set_shortcuts_disabled;
use stitchwort_driver::driver::{Session, with_stack};

const STACK: usize = 64 * 1024 * 1024;

fn examples() -> Vec<(String, String)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut found = Vec::new();
    for dir in ["accept", "extract", "reject", "soundness"] {
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
/// off: every diagnostic, in full.
fn verdict(name: &str, text: &str, shortcuts: bool) -> String {
    set_shortcuts_disabled(!shortcuts);
    let mut session = Session::for_stack(STACK);
    let result = session.load(name, text).map(|_| ());
    set_shortcuts_disabled(false);
    format!("{result:?}")
}

#[test]
fn every_example_gets_the_same_verdict_without_the_shortcut() {
    with_stack(STACK, || {
        let examples = examples();
        assert!(examples.len() > 300, "only {} examples", examples.len());
        let mut rejected = 0;
        for (name, text) in &examples {
            let with = verdict(name, text, true);
            let without = verdict(name, text, false);
            assert_eq!(with, without, "{name}: the verdict depends on the shortcut");
            if with.starts_with("Err") {
                rejected += 1;
            }
        }
        assert!(rejected > 200, "only {rejected} rejections compared");
    });
}
