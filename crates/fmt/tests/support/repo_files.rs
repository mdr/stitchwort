//! The repo's files of some kinds, for the tests that check every one of
//! them (`crates/fmt/tests/repo.rs`, `crates/cli/tests/fmt_repo.rs`,
//! `crates/driver/tests/fmt_hashes.rs`, which include this file by path).
//!
//! In a git checkout these are the tracked files (`git ls-files`). The Nix
//! build's source is a copy of the tracked files the flake selects, with no
//! `.git`, so there they are every matching file under the root instead:
//! the same files, less any the flake leaves out.

use std::path::Path;
use std::process::Command;

/// The paths, relative to `root` with `/` between folders and sorted, of
/// the files whose names end with one of `suffixes` (`".sw"`,
/// `"stitchwort.yaml"`).
pub fn repo_files(root: &Path, suffixes: &[&str]) -> Vec<String> {
    let pathspecs: Vec<String> = suffixes.iter().map(|s| format!("*{s}")).collect();
    let listed = Command::new("git")
        .arg("-C")
        .arg(root)
        .arg("ls-files")
        .arg("-z")
        .args(&pathspecs)
        .output();
    let mut files: Vec<String> = match listed {
        Ok(output) if output.status.success() => String::from_utf8(output.stdout)
            .expect("file names are UTF-8")
            .split('\0')
            .filter(|path| !path.is_empty())
            .map(str::to_string)
            .collect(),
        _ => {
            eprintln!("not a git checkout (or no git): listing the files under {root:?} instead");
            let mut found = Vec::new();
            walk(root, "", suffixes, &mut found);
            found
        }
    };
    files.sort();
    files
}

/// Adds the matching files under `dir` (which is `prefix` relative to the
/// root) to `out`, skipping build output and hidden folders.
fn walk(dir: &Path, prefix: &str, suffixes: &[&str], out: &mut Vec<String>) {
    let entries = std::fs::read_dir(dir).unwrap_or_else(|e| panic!("reading {dir:?}: {e}"));
    for entry in entries {
        let entry = entry.expect("a directory entry");
        let name = entry
            .file_name()
            .into_string()
            .expect("file names are UTF-8");
        let path = format!("{prefix}{name}");
        let kind = entry.file_type().expect("a file type");
        if kind.is_dir() {
            if !name.starts_with('.') && !matches!(name.as_str(), "target" | "node_modules") {
                walk(&entry.path(), &format!("{path}/"), suffixes, out);
            }
        } else if kind.is_file() && suffixes.iter().any(|s| name.ends_with(s)) {
            out.push(path);
        }
    }
}
