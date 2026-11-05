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

/// Workspace crates that `core` and `rt` are built with but that can't change
/// what a test computes once its term is fixed: `syntax` is the parser, which
/// `core` uses for spans and diagnostics only. Listed so that a new
/// dependency of `core` or `rt` is fingerprinted by default, not left out.
pub const NOT_EVALUATION: &[&str] = &["crates/syntax"];

/// Files outside the evaluation crates that decide a test's outcome: the
/// driver's test runner, and the manifests that choose which features of the
/// evaluation crates are compiled.
pub const EVALUATION_FILES: &[&str] = &[
    "crates/driver/src/test_run.rs",
    "crates/driver/Cargo.toml",
    "Cargo.toml",
];

/// The crates the evaluation fingerprint covers: `core` and `rt` (with the
/// crates they're built with, except [`NOT_EVALUATION`]) and `dev-features`,
/// which turns on features of both in dev builds.
pub fn evaluation_crates(root: &std::path::Path) -> Vec<String> {
    let mut crates = source_crates(root, "crates/core");
    crates.extend(source_crates(root, "crates/rt"));
    crates.push("crates/dev-features".to_string());
    crates.retain(|c| !NOT_EVALUATION.contains(&c.as_str()));
    crates.sort();
    crates.dedup();
    crates
}

/// The files the evaluation fingerprint hashes, relative to `root`, sorted.
pub fn evaluation_files(root: &std::path::Path) -> Vec<std::path::PathBuf> {
    let mut files: Vec<_> = evaluation_crates(root)
        .iter()
        .flat_map(|dir| source_files(root, dir))
        .chain(EVALUATION_FILES.iter().map(std::path::PathBuf::from))
        .collect();
    files.sort();
    files.dedup();
    files
}

/// The fingerprint of what evaluates tests ([`evaluation_files`]), with
/// `Cargo.lock`, the toolchain and the target: the part of the test cache's
/// key that stands for the compiler. A test's content hash covers the
/// program and everything it uses, the standard library included, so this
/// covers only the Rust that runs a term (docs/proposals/test-cache-key.md).
pub fn evaluation_fingerprint(root: &std::path::Path, rustc: &str, target: &str) -> String {
    let lock = std::fs::read(root.join("Cargo.lock")).ok();
    let files: Vec<(String, Vec<u8>)> = evaluation_files(root)
        .into_iter()
        .map(|f| {
            let text = std::fs::read(root.join(&f)).unwrap_or_default();
            (f.to_string_lossy().into_owned(), text)
        })
        .collect();
    fingerprint(lock.as_deref(), &files, rustc, target)
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
        let expected = metadata_graph(&root, "stitchwort-driver");
        let built: Vec<&str> = crate::driver::FINGERPRINT_CRATES.split(',').collect();
        assert_eq!(built, expected);
        assert_eq!(super::source_crates(&root, "crates/driver"), expected);
        assert!(
            built.contains(&"crates/rt"),
            "the runtime that runs the tests"
        );
    }

    /// The bundle-staleness fingerprint covers web's graph, not just the
    /// driver's: editing `crates/web` (or the formatter, which only the web
    /// crate uses) must mark `web/pkg` stale (SW-1132).
    #[test]
    fn the_source_fingerprint_covers_the_web_crate() {
        let root = root();
        let expected = metadata_graph(&root, "stitchwort-web");
        let built: Vec<&str> = crate::driver::SOURCE_FINGERPRINT_CRATES
            .split(',')
            .collect();
        assert_eq!(built, expected);
        assert_eq!(super::source_crates(&root, "crates/web"), expected);
        for dir in ["crates/web", "crates/driver", "crates/fmt"] {
            assert!(built.contains(&dir), "{dir} in {built:?}");
        }
        // The web crate's own manifest, build script and sources are hashed,
        // so a change to any of them changes the fingerprint.
        let files = super::source_files(&root, "crates/web");
        for file in [
            "crates/web/Cargo.toml",
            "crates/web/build.rs",
            "crates/web/src/lib.rs",
        ] {
            assert!(files.contains(&PathBuf::from(file)), "{file} in {files:?}");
        }
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

    /// A workspace of the shape that matters: `core` and `rt` (which depend
    /// on `syntax` and `core`), `elab` (which they don't depend on), and the
    /// driver's test runner.
    fn fake_workspace() -> Scratch {
        let dir = Scratch::new();
        let write = |path: &str, text: &str| {
            let path = dir.path().join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        };
        write(
            "Cargo.toml",
            "[workspace.dependencies]\nstitchwort-syntax = { path = \"crates/syntax\" }\n\
             stitchwort-core = { path = \"crates/core\" }\n\
             stitchwort-rt = { path = \"crates/rt\" }\n\
             stitchwort-elab = { path = \"crates/elab\" }\n",
        );
        write("Cargo.lock", "lock");
        write("crates/syntax/Cargo.toml", "[dependencies]\n");
        write(
            "crates/core/Cargo.toml",
            "[dependencies]\nstitchwort-syntax.workspace = true\n",
        );
        write(
            "crates/rt/Cargo.toml",
            "[dependencies]\nstitchwort-core.workspace = true\nstitchwort-syntax.workspace = true\n",
        );
        write(
            "crates/elab/Cargo.toml",
            "[dependencies]\nstitchwort-core.workspace = true\n",
        );
        write("crates/dev-features/Cargo.toml", "[dependencies]\n");
        write("crates/driver/Cargo.toml", "[dependencies]\n");
        for file in [
            "crates/syntax/src/lib.rs",
            "crates/core/src/lib.rs",
            "crates/rt/src/lib.rs",
            "crates/elab/src/lib.rs",
            "crates/dev-features/src/lib.rs",
            "crates/driver/src/test_run.rs",
            "crates/driver/src/driver.rs",
        ] {
            write(file, "// 1");
        }
        dir
    }

    /// A fresh directory, removed when dropped.
    struct Scratch(PathBuf);

    impl Scratch {
        fn new() -> Self {
            static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
            let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let dir = std::env::temp_dir().join(format!("sw-evalfp-{}-{n}", std::process::id()));
            let _ = std::fs::remove_dir_all(&dir);
            std::fs::create_dir_all(&dir).unwrap();
            Scratch(dir)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// Whether appending a line to `file` of the fake workspace changes the
    /// evaluation fingerprint.
    fn changes_the_fingerprint(file: &str) -> bool {
        let dir = fake_workspace();
        let before = super::evaluation_fingerprint(dir.path(), "rustc", "t");
        let path = dir.path().join(file);
        let mut text = std::fs::read_to_string(&path).unwrap();
        text.push_str("\n# edited\n");
        std::fs::write(path, text).unwrap();
        before != super::evaluation_fingerprint(dir.path(), "rustc", "t")
    }

    /// The test cache's key stands for the Rust that evaluates a term: a
    /// change there starts a fresh cache, one anywhere else (the elaborator,
    /// the parser, the rest of the driver) keeps it, since it can only change
    /// a result by changing the test's term and so its hash.
    #[test]
    fn the_evaluation_fingerprint_changes_with_what_evaluates_tests() {
        for file in [
            "crates/core/src/lib.rs",
            "crates/core/Cargo.toml",
            "crates/rt/src/lib.rs",
            "crates/dev-features/src/lib.rs",
            "crates/driver/src/test_run.rs",
            "Cargo.lock",
            "Cargo.toml",
        ] {
            assert!(changes_the_fingerprint(file), "{file}");
        }
        for file in [
            "crates/elab/src/lib.rs",
            "crates/syntax/src/lib.rs",
            "crates/driver/src/driver.rs",
        ] {
            assert!(!changes_the_fingerprint(file), "{file}");
        }
    }

    /// The toolchain and target are part of it (float primitives).
    #[test]
    fn the_evaluation_fingerprint_has_the_toolchain_and_target() {
        let dir = fake_workspace();
        let at = |rustc, target| super::evaluation_fingerprint(dir.path(), rustc, target);
        assert_ne!(at("rustc 1", "t"), at("rustc 2", "t"));
        assert_ne!(at("rustc 1", "t"), at("rustc 1", "u"));
    }

    /// Everything `core` and `rt` are built with is covered, bar the crates
    /// named as unable to change a result: so a new dependency fails here,
    /// or is fingerprinted, instead of going unnoticed.
    #[test]
    fn the_evaluation_fingerprint_covers_core_and_rt_graphs() {
        let root = root();
        let built: Vec<&str> = crate::driver::EVAL_FINGERPRINT_CRATES.split(',').collect();
        let mut expected: Vec<String> = metadata_graph(&root, "stitchwort-core");
        expected.extend(metadata_graph(&root, "stitchwort-rt"));
        expected.push("crates/dev-features".into());
        expected.retain(|c| !super::NOT_EVALUATION.contains(&c.as_str()));
        expected.sort();
        expected.dedup();
        assert_eq!(built, expected);
        assert_eq!(super::evaluation_crates(&root), expected);
        for dir in ["crates/core", "crates/rt", "crates/dev-features"] {
            assert!(built.contains(&dir), "{dir} in {built:?}");
        }
        for dir in ["crates/elab", "crates/driver", "crates/fmt", "crates/js"] {
            assert!(!built.contains(&dir), "{dir} in {built:?}");
        }
        let files = super::evaluation_files(&root);
        assert!(files.contains(&PathBuf::from("crates/driver/src/test_run.rs")));
    }

    /// The directories of `start`'s package and every workspace crate it
    /// depends on (not dev- or build-), transitively, as `cargo metadata`
    /// sees them, sorted.
    fn metadata_graph(root: &Path, start: &str) -> Vec<String> {
        let out = std::process::Command::new(env!("CARGO"))
            .args([
                "metadata",
                "--no-deps",
                "--format-version",
                "1",
                "--offline",
            ])
            .current_dir(root)
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
                .and_then(|d| d.strip_prefix(root).ok())
                .map(|d| d.to_string_lossy().into_owned())
                .expect("a workspace crate")
        };
        let mut expected = vec![start.to_string()];
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
        expected
    }
}
