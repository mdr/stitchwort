//! Every tracked `.sw` file outside D1019's excluded folders either formats,
//! passing the §4.1 checks and formatting to itself again, or is refused for
//! a syntax error (docs/proposals/formatter.md §4.2).

use std::path::Path;
use std::process::Command;

use stitchwort_fmt::{Error, Stats, format_with_stats};

/// Folders whose layout may be what's tested (D1019).
const EXCLUDED: [&str; 3] = [
    "examples/reject/",
    "examples/soundness/",
    "examples/projects/reject/",
];

#[test]
fn every_repo_file_formats_idempotently_or_is_refused() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let listing = Command::new("git")
        .args(["ls-files", "*.sw"])
        .current_dir(&root)
        .output()
        .expect("git ls-files runs");
    assert!(listing.status.success(), "git ls-files failed");
    let files: Vec<String> = String::from_utf8(listing.stdout)
        .expect("file names are UTF-8")
        .lines()
        .filter(|path| !EXCLUDED.iter().any(|folder| path.starts_with(folder)))
        .map(str::to_string)
        .collect();
    assert!(files.len() > 100, "found only {} files", files.len());

    let (mut formatted, mut unchanged, mut refused) = (0, 0, 0);
    let mut total = Stats::default();
    let mut failures = Vec::new();
    for path in &files {
        let text = std::fs::read_to_string(root.join(path)).expect("readable");
        match format_with_stats(&text) {
            Ok(result) => {
                total.copied_lines += result.stats.copied_lines;
                total.copied_gaps += result.stats.copied_gaps;
                total.unconverted_decls += result.stats.unconverted_decls;
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
        "{} files: {formatted} formatted, {unchanged} unchanged, {refused} refused; \
         copy path: {} lines, {} gaps; {} declarations without bracket conversion, \
         {} kept verbatim",
        files.len(),
        total.copied_lines,
        total.copied_gaps,
        total.unconverted_decls,
        total.verbatim_decls,
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!(
        (total.copied_lines, total.copied_gaps),
        (0, 0),
        "constructs are left on the copy path"
    );
    assert_eq!(
        total.verbatim_decls, 0,
        "declarations failed their checks and were kept as written"
    );
}
