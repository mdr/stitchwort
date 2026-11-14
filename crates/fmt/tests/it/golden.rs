//! Golden tests (docs/proposals/formatter-style.md): each
//! `golden/NAME.before.sw` formats to `golden/NAME.after.sw`, and both
//! format to the same text again (idempotence). Run with `BLESS=1` to write
//! the `.after.sw` files from the formatter's output, then review the diff.

use std::path::Path;

use stitchwort_fmt::{format, format_with_stats};

/// Files with declarations the formatter leaves as written because the
/// comments in them sit where no rule places them (a comment before a
/// leading comma, a comment that would move to the other side of one): the
/// number of such declarations in each. Their `.after.sw` is the input.
const LEFT_AS_WRITTEN: [(&str, usize); 2] = [("brackets-comments", 1), ("brackets-edge", 1)];

#[test]
fn golden_files_format_as_expected_and_idempotently() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/it/golden");
    let bless = std::env::var_os("BLESS").is_some();
    let mut names: Vec<String> = std::fs::read_dir(&dir)
        .expect("the golden folder exists")
        .filter_map(|entry| {
            let name = entry.ok()?.file_name().into_string().ok()?;
            name.strip_suffix(".before.sw").map(str::to_string)
        })
        .collect();
    names.sort();
    assert!(!names.is_empty(), "no golden files in {}", dir.display());
    let mut failures = Vec::new();
    for name in &names {
        let before =
            std::fs::read_to_string(dir.join(format!("{name}.before.sw"))).expect("readable");
        let after_path = dir.join(format!("{name}.after.sw"));
        let got = match format_with_stats(&before) {
            Ok(result)
                if result.stats.verbatim_decls
                    != LEFT_AS_WRITTEN
                        .iter()
                        .find(|(file, _)| file == name)
                        .map_or(0, |(_, n)| *n) =>
            {
                failures.push(format!("{name}: a declaration failed its checks"));
                continue;
            }
            Ok(result) => result.text,
            Err(e) => {
                failures.push(format!("{name}: {e}"));
                continue;
            }
        };
        if bless {
            std::fs::write(&after_path, &got).expect("writable");
        }
        let want = std::fs::read_to_string(&after_path).unwrap_or_default();
        if got != want {
            failures.push(format!("{name}: got\n{got}\n--- want\n{want}"));
        }
        for (what, text) in [("output", &got), ("expected output", &want)] {
            match format(text) {
                Ok(again) if again == *text => {}
                Ok(again) => failures.push(format!("{name}: the {what} formats to\n{again}")),
                Err(e) => failures.push(format!("{name}: the {what}: {e}")),
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
