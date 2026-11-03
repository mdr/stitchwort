//! The build fingerprint's hash ([`crate::driver::FINGERPRINT`]), from its
//! inputs: shared by `build.rs`, which gathers them, and the test that the
//! fingerprint changes with each.

/// The fingerprint of a build: `Cargo.lock`, the hashed source files (name
/// and contents), and the Rust toolchain (`rustc -vV`) and target it is built
/// with. The toolchain is there because the checker's floats depend on it:
/// literals are parsed by the standard library's `str::parse::<f64>`, and
/// the float primitives are compiled by it (docs/proposals/float.md §3.3).
pub fn fingerprint(
    lock: Option<&[u8]>,
    files: &[(String, Vec<u8>)],
    rustc: &str,
    target: &str,
) -> String {
    let mut hasher = blake3::Hasher::new();
    // Each input with its length, so adjacent ones can't run together.
    let mut field = |bytes: &[u8]| {
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(bytes);
    };
    if let Some(lock) = lock {
        field(b"Cargo.lock");
        field(lock);
    }
    for (name, text) in files {
        field(name.as_bytes());
        field(text);
    }
    field(b"rustc");
    field(rustc.as_bytes());
    field(b"target");
    field(target.as_bytes());
    hasher.finalize().as_bytes()[..12]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// The crates whose source the fingerprint covers: `start` (a crate's
/// directory, relative to the workspace root `root`) and every workspace
/// crate it depends on to build and run, transitively, as directories
/// relative to `root`, sorted. Read from the manifests, so a new dependency
/// is covered without a list here to update (SW-1123: the runtime, which
/// runs the tests, wasn't).
///
/// A crate's dependencies are the `stitchwort-*` entries of its
/// `[dependencies]` and `[target.….dependencies]` tables, not its dev- or
/// build-dependencies; where each is comes from the workspace manifest's
/// `[workspace.dependencies]`. The test `the_fingerprint_covers_the_crate_graph`
/// checks this against `cargo metadata`.
pub fn source_crates(root: &std::path::Path, start: &str) -> Vec<String> {
    let read =
        |dir: &str| std::fs::read_to_string(root.join(dir).join("Cargo.toml")).unwrap_or_default();
    let paths = workspace_paths(&read(""));
    let mut crates = vec![start.to_string()];
    let mut next = 0;
    while next < crates.len() {
        for name in dependencies(&read(&crates[next])) {
            let path = paths
                .iter()
                .find(|(n, _)| *n == name)
                .map(|(_, p)| p.clone())
                .unwrap_or_else(|| panic!("{name} isn't in [workspace.dependencies]"));
            if !crates.contains(&path) {
                crates.push(path);
            }
        }
        next += 1;
    }
    crates.sort();
    crates
}

/// The files of `crate_dir` (relative to `root`) that the fingerprint
/// hashes: its manifest (features change what's compiled), its build
/// script, and the Rust sources under `src`, by path
/// relative to `root`, sorted.
pub fn source_files(root: &std::path::Path, crate_dir: &str) -> Vec<std::path::PathBuf> {
    let dir = root.join(crate_dir);
    let mut files: Vec<_> = ["Cargo.toml", "build.rs"]
        .iter()
        .map(|f| dir.join(f))
        .filter(|f| f.is_file())
        .collect();
    collect(&dir.join("src"), &mut files);
    files.sort();
    files
        .into_iter()
        .map(|f| f.strip_prefix(root).map(|r| r.to_path_buf()).unwrap_or(f))
        .collect()
}

/// The Rust sources under `dir`, recursively. Not the standard library's
/// `.sw` files: they aren't compiled in, and the caches key on the text read
/// ([`crate::driver::build_fingerprint`]).
fn collect(dir: &std::path::Path, files: &mut Vec<std::path::PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect(&path, files);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            files.push(path);
        }
    }
}

/// `[workspace.dependencies]`' `stitchwort-*` entries with a path: each
/// crate's name and directory.
fn workspace_paths(manifest: &str) -> Vec<(String, String)> {
    entries(manifest, |table| table == "workspace.dependencies")
        .filter_map(|(name, rest)| {
            let path = rest.split("path").nth(1)?.split('"').nth(1)?;
            Some((name, path.to_string()))
        })
        .collect()
}

/// The workspace crates a manifest's crate depends on to build and run.
fn dependencies(manifest: &str) -> Vec<String> {
    entries(manifest, |table| {
        table == "dependencies"
            || (table.starts_with("target.") && table.ends_with(".dependencies"))
    })
    .map(|(name, _)| name)
    .collect()
}

/// The `stitchwort-*` keys of the tables `wanted` picks, each with the rest
/// of its line.
fn entries<'a>(
    manifest: &'a str,
    wanted: impl Fn(&str) -> bool + 'a,
) -> impl Iterator<Item = (String, &'a str)> + 'a {
    let mut inside = false;
    manifest.lines().filter_map(move |line| {
        let line = line.trim();
        if let Some(table) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
            inside = wanted(table.trim());
            return None;
        }
        if !inside || !line.starts_with("stitchwort-") {
            return None;
        }
        let end = line
            .find(|c: char| c == '.' || c == '=' || c.is_whitespace())
            .unwrap_or(line.len());
        Some((line[..end].to_string(), &line[end..]))
    })
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    fn root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .expect("the workspace root")
    }

    /// The crates the build's fingerprint covered are this crate's
    /// workspace dependencies (not dev- or build-), transitively, as Cargo
    /// sees them: a crate whose code the tests run can't be left out
    /// (SW-1123).
    #[test]
    fn the_fingerprint_covers_the_crate_graph() {
        let root = root();
        let out = std::process::Command::new(env!("CARGO"))
            .args([
                "metadata",
                "--no-deps",
                "--format-version",
                "1",
                "--offline",
            ])
            .current_dir(&root)
            .output()
            .expect("run cargo metadata");
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let metadata: serde_json::Value = serde_json::from_slice(&out.stdout).expect("JSON");
        let packages = metadata["packages"].as_array().expect("packages");
        let dir_of = |manifest: &str| {
            Path::new(manifest)
                .parent()
                .and_then(|d| d.strip_prefix(&root).ok())
                .map(|d| d.to_string_lossy().into_owned())
                .expect("a workspace crate")
        };
        let mut expected = vec!["stitchwort-driver".to_string()];
        let mut next = 0;
        while next < expected.len() {
            let package = packages
                .iter()
                .find(|p| p["name"] == expected[next].as_str())
                .expect("a workspace package");
            for dep in package["dependencies"].as_array().expect("dependencies") {
                let name = dep["name"].as_str().expect("a name").to_string();
                if dep["kind"].is_null() && dep["path"].is_string() && !expected.contains(&name) {
                    expected.push(name);
                }
            }
            next += 1;
        }
        let mut expected: Vec<String> = expected
            .iter()
            .map(|name| {
                let package = packages
                    .iter()
                    .find(|p| p["name"] == name.as_str())
                    .unwrap();
                dir_of(package["manifest_path"].as_str().expect("a manifest"))
            })
            .collect();
        expected.sort();
        let built: Vec<&str> = crate::driver::FINGERPRINT_CRATES.split(',').collect();
        assert_eq!(built, expected);
        assert_eq!(super::source_crates(&root, "crates/driver"), expected);
        assert!(
            built.contains(&"crates/rt"),
            "the runtime that runs the tests"
        );
    }

    /// Each covered crate's manifest, build script and sources are hashed:
    /// the runtime's, say.
    #[test]
    fn a_crates_manifest_build_script_and_sources_are_hashed() {
        let files = super::source_files(&root(), "crates/rt");
        for file in [
            "crates/rt/Cargo.toml",
            "crates/rt/build.rs",
            "crates/rt/src/prims.rs",
        ] {
            assert!(files.contains(&PathBuf::from(file)), "{file} in {files:?}");
        }
    }
}
