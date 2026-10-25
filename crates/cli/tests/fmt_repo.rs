//! The repo stays formatted (docs/proposals/formatter.md §5.4, D1019, D1061):
//! every tracked `.sw` file (every one in the source, in the Nix build) outside the excluded paths is already what
//! `stitchwort fmt` would write. Run `stitchwort fmt` on the files you touched.

use std::path::PathBuf;

#[path = "../../fmt/tests/support/repo_files.rs"]
mod repo_files;

/// Paths (prefixes, or whole files) the formatter leaves alone.
const EXCLUDED: [&str; 5] = [
    // D1019: files that exist to be rejected.
    "examples/reject/",
    "examples/soundness/",
    "examples/projects/reject/",
    // Formatter test data.
    "crates/fmt/tests/golden/",
    // Exercises layouts the formatter normalises.
    "examples/accept/list-literal-layout.sw",
];

#[test]
fn tracked_sw_files_are_formatted() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let files: Vec<String> = repo_files::repo_files(&root, &[".sw"])
        .into_iter()
        .filter(|p| !EXCLUDED.iter().any(|e| p.starts_with(e)))
        .collect();
    assert!(files.len() > 300, "found only {} files", files.len());

    let mut unformatted = Vec::new();
    for path in &files {
        let text = std::fs::read_to_string(root.join(path)).expect("read file");
        match stitchwort_fmt::format(&text) {
            Ok(formatted) if formatted == text => {}
            Ok(_) => unformatted.push(format!("{path} (would change)")),
            Err(e) => unformatted.push(format!("{path} (refused: {e:?})")),
        }
    }
    assert!(
        unformatted.is_empty(),
        "run `stitchwort fmt` on these files:\n{}",
        unformatted.join("\n")
    );
}
