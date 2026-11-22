//! No Stitchwort code gives warnings (Matt, 16 Nov 2026). The standard
//! library's are pinned in `crates/driver/tests/library/warning_pins.rs`;
//! this checks the projects of the repo the same way, against the same
//! table (`warning_pins.tsv`: project, file, code, count; a count is a
//! ceiling, a project or file not listed gives none, and the table only ever
//! goes down).
//!
//! Each project is checked without the cache (a cached file has no warnings
//! to give) and its `[W-…]` diagnostics are counted by file and code. Open
//! goals (`[GOAL]`) are not warnings of this kind: `sf/` and `plus/` keep
//! theirs on purpose (`check: open-goals: warn`). Examples whose purpose is
//! to show a warning (`examples/`, `docs/guide/examples/errors/`) are not
//! checked. AoC is checked a year at a time (about 30 s each), never as a
//! whole.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

type Counts = BTreeMap<(String, String), usize>;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The pinned ceilings for one project: (file, code) to count.
fn pins(project: &str) -> Counts {
    include_str!("../../../driver/tests/library/warning_pins.tsv")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .filter_map(|l| {
            let c: Vec<&str> = l.split('\t').collect();
            let [p, file, code, n] = c[..] else {
                panic!("a pin line has four tab-separated columns: {l:?}")
            };
            (p == project).then(|| ((file.into(), code.into()), n.parse().expect("a count")))
        })
        .collect()
}

/// `stitchwort check --no-cache` in `dir` with `args`: its standard output
/// and error together, which must have succeeded.
fn check(dir: &Path, args: &[String]) -> String {
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .current_dir(dir)
        .args(["check", "--no-cache", "--color", "never"])
        .args(args)
        .output()
        .expect("run stitchwort");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.status.success(),
        "check failed in {}:\n{text}",
        dir.display()
    );
    text
}

/// The warnings in a check's output as (file, code), the file as printed
/// without its leading project folder, or `only` for a single-file check.
fn warnings(text: &str, only: Option<&str>) -> Counts {
    let mut counts = Counts::new();
    let mut lines = text.lines();
    while let Some(line) = lines.next() {
        let Some(rest) = line.strip_prefix("[W-") else {
            continue;
        };
        let code = format!("W-{}", rest.split(']').next().unwrap_or(""));
        let place = lines.by_ref().find_map(|l| {
            l.split_once("╭─[ ")
                .map(|(_, p)| p.split(" ]").next().unwrap_or("").to_string())
        });
        let file = match (only, place) {
            (Some(file), _) => file.to_string(),
            (None, Some(place)) => {
                let path = place.rsplitn(3, ':').last().unwrap_or("").to_string();
                path.split_once('/')
                    .map_or(path.clone(), |(_, f)| f.to_string())
            }
            (None, None) => "?".to_string(),
        };
        *counts.entry((file, code)).or_default() += 1;
    }
    counts
}

fn within_pins(project: &str, counts: &Counts) {
    let pinned = pins(project);
    let over: Vec<String> = counts
        .iter()
        .filter(|(key, n)| **n > pinned.get(*key).copied().unwrap_or(0))
        .map(|((file, code), n)| {
            format!(
                "{project} {file} {code}: {n} (pinned {})",
                pinned.get(&(file.clone(), code.clone())).unwrap_or(&0)
            )
        })
        .collect();
    assert!(
        over.is_empty(),
        "warnings above their pins in warning_pins.tsv (fix the code, or the \
         warning if it is wrong; never raise a pin):\n{}",
        over.join("\n")
    );
}

fn project_within_pins(name: &str, folder: &str) {
    let dir = root().join(folder);
    within_pins(name, &warnings(&check(&dir, &[]), None));
}

/// Every `.sw` file under `folder` (not in `skip`), relative to it.
fn sw_files(folder: &Path, skip: &[&str]) -> Vec<String> {
    fn walk(base: &Path, dir: &Path, out: &mut Vec<String>) {
        for entry in std::fs::read_dir(dir).expect("read dir").flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(base, &path, out);
            } else if path.extension().is_some_and(|e| e == "sw") {
                out.push(
                    path.strip_prefix(base)
                        .unwrap()
                        .to_string_lossy()
                        .into_owned(),
                );
            }
        }
    }
    let mut out = Vec::new();
    walk(folder, folder, &mut out);
    out.retain(|f| !skip.iter().any(|s| f.starts_with(s)));
    out.sort();
    out
}

fn files_within_pins(name: &str, folder: &str, skip: &[&str]) {
    let dir = root().join(folder);
    let mut counts = Counts::new();
    for file in sw_files(&dir, skip) {
        for (key, n) in warnings(&check(&dir, std::slice::from_ref(&file)), Some(&file)) {
            *counts.entry(key).or_default() += n;
        }
    }
    within_pins(name, &counts);
}

#[test]
fn rogue_warnings_stay_within_their_pins() {
    project_within_pins("rogue", "games/rogue");
}

#[test]
fn sf_warnings_stay_within_their_pins() {
    project_within_pins("sf", "sf");
}

#[test]
fn guide_example_warnings_stay_within_their_pins() {
    files_within_pins(
        "guide-examples",
        "docs/guide/examples",
        &["errors/", "project/"],
    );
}

#[test]
fn guide_project_warnings_stay_within_their_pins() {
    project_within_pins("guide-project", "docs/guide/examples/project");
}

#[test]
fn web_guide_warnings_stay_within_their_pins() {
    files_within_pins("web-guide", "web/guide", &[]);
}

/// The namespaces of `aoc/src/Aoc/<year>`, named as `check` takes them.
fn aoc_namespaces(year: &str) -> Vec<String> {
    let folder = root().join("aoc/src/Aoc").join(year);
    let mut names: Vec<String> = sw_files(&folder, &[])
        .iter()
        .filter_map(|f| {
            let text = std::fs::read_to_string(folder.join(f)).expect("read");
            text.lines()
                .find_map(|l| l.strip_prefix("namespace ").map(|n| n.trim().to_string()))
        })
        .collect();
    names.sort();
    names.dedup();
    names
}

/// A year's folder, or `Common`.
fn aoc_year_within_pins(year: &str) {
    let dir = root().join("aoc");
    let text = check(&dir, &aoc_namespaces(year));
    let project = format!("aoc-{}", year.trim_start_matches("Year").to_lowercase());
    within_pins(&project, &warnings(&text, None));
}

#[test]
fn aoc_common_warnings_stay_within_their_pins() {
    aoc_year_within_pins("Common");
}

#[test]
fn aoc_2020_warnings_stay_within_their_pins() {
    aoc_year_within_pins("Year2020");
}

#[test]
fn aoc_2021_warnings_stay_within_their_pins() {
    aoc_year_within_pins("Year2021");
}

#[test]
fn aoc_2024_warnings_stay_within_their_pins() {
    aoc_year_within_pins("Year2024");
}

#[test]
fn aoc_2025_warnings_stay_within_their_pins() {
    aoc_year_within_pins("Year2025");
}
