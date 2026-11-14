//! Every tracked `.sw` file outside D1019's excluded folders either formats,
//! passing the §4.1 checks and formatting to itself again, or is refused for
//! a syntax error (docs/proposals/formatter-style.md).

use std::path::Path;
use stitchwort_fmt::{Error, Stats, format_with_stats};

use crate::support::repo_files;

/// Folders whose layout may be what's tested (D1019), and the formatter's
/// own test data, some of which it leaves as written.
const EXCLUDED: [&str; 4] = [
    "examples/reject/",
    "examples/soundness/",
    "examples/projects/reject/",
    "crates/fmt/tests/it/golden/",
];

#[test]
fn every_repo_file_formats_idempotently_or_is_refused() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let files: Vec<String> = repo_files::repo_files(&root, &[".sw"])
        .into_iter()
        .filter(|path| !EXCLUDED.iter().any(|folder| path.starts_with(folder)))
        .collect();
    assert!(files.len() > 100, "found only {} files", files.len());

    let (mut formatted, mut unchanged, mut refused) = (0, 0, 0);
    let mut total = Stats::default();
    let mut failures = Vec::new();
    for path in &files {
        let text = std::fs::read_to_string(root.join(path)).expect("readable");
        match format_with_stats(&text) {
            Ok(result) => {
                total.decls += result.stats.decls;
                total.unruled_nodes += result.stats.unruled_nodes;
                total.verbatim_decls += result.stats.verbatim_decls;
                if result.text == text {
                    unchanged += 1;
                } else {
                    formatted += 1;
                }
                match format_with_stats(&result.text) {
                    Ok(again) if again.text == result.text => {}
                    Ok(_) => failures.push(format!("{path}: not idempotent")),
                    Err(e) => failures.push(format!("{path}: second run: {e}")),
                }
            }
            Err(Error::Refused(_)) => refused += 1,
            Err(e @ Error::Internal(_)) => failures.push(format!("{path}: {e}")),
        }
    }
    println!(
        "{} files: {formatted} formatted, {unchanged} unchanged, {refused} refused; {} \
         declarations, {} kept as written, {} nodes without a rule",
        files.len(),
        total.decls,
        total.verbatim_decls,
        total.unruled_nodes,
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!(
        total.unruled_nodes, 0,
        "constructs are printed as written, with no rule"
    );
    assert_eq!(
        total.verbatim_decls, 0,
        "declarations failed their checks and were kept as written"
    );
}
