//! Where the standard library's text comes from: files, read when the
//! process first asks for it. No build embeds the library, so editing a
//! `.sw` file compiles nothing (SW-1136, docs/proposals/std-as-data.md).
//!
//! The directory is, first match wins:
//!
//! 1. the CLI's `--std-dir` ([`use_std_dir`]), then the environment variable
//!    [`STD_DIR_VAR`] (`STITCHWORT_STD_DIR`);
//! 2. an installed binary's `../share/stitchwort/std`, relative to the
//!    executable;
//! 3. the checkout's `crates/elab/src/std`: the first ancestor of the
//!    executable (cargo's `target/` is inside it, so test binaries find it),
//!    then of the current directory, that has one;
//! 4. the tree the binary was built from (the executable names it, from its
//!    `CARGO_MANIFEST_DIR`, with [`set_build_tree`]), if it is still on disk,
//!    so a copy of the binary kept elsewhere
//!    (a "before" binary in a scratch folder) still finds the library
//!    (SW-4789).
//!
//! WebAssembly has no files: the host gives the library's files as a bundle
//! ([`use_std_bundle`]) before anything uses it.
//!
//! It is read once per process. Everything else (the library index, the
//! check cache's keys, the build fingerprint) is computed from the text read,
//! so caches key on what is actually on disk.
//!
//! The core's files are read in the order `core/order.txt` lists. Library
//! files are every other `.sw` file.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// The environment variable naming a directory to read `std/` from.
pub const STD_DIR_VAR: &str = "STITCHWORT_STD_DIR";

/// The core's manifest, under `std/`: the names of the core's files (no
/// extension), one per line, in dependency order; `#` starts a comment.
pub const CORE_ORDER: &str = "core/order.txt";

/// Where an installed binary keeps `std/`, relative to its directory.
const INSTALLED: &str = "../share/stitchwort/std";

/// Where the checkout keeps it, relative to the checkout's root.
const CHECKOUT: &str = "crates/elab/src/std";

/// The standard library's text, as this process reads it.
pub struct StdText {
    /// The directory it was read from; `None` for a bundle (WebAssembly).
    pub dir: Option<PathBuf>,
    /// The core's files, joined.
    pub prelude: &'static str,
    /// Each core file's path under `std/` and length, in order.
    pub core_layout: &'static [(&'static str, usize)],
    /// The library files, `(path under std/, text)`, sorted by path.
    pub library: &'static [(&'static str, &'static str)],
}

static STD: OnceLock<StdText> = OnceLock::new();

/// The checkout's root as of the build, given by the executable
/// ([`set_build_tree`]).
static BUILD_TREE: OnceLock<PathBuf> = OnceLock::new();

/// Names the checkout this binary was built in, for the last place `locate`
/// looks. The executable passes it (from its own `CARGO_MANIFEST_DIR`)
/// rather than this crate reading it at compile time: that variable's
/// absolute path is part of the compiler cache's key, so every checkout
/// recompiled this crate and everything built on it (SW-4952).
pub fn set_build_tree(root: &Path) {
    let _ = BUILD_TREE.set(root.to_path_buf());
}

/// The standard library's text, from where the module's documentation says.
/// Panics, saying where it looked, if there is none or it can't be read: a
/// fault in the installation or the developer's setup, not in a program.
/// The CLI and the language server call [`load_std_text`] first, so that
/// this fault is reported rather than panicking.
pub fn std_text() -> &'static StdText {
    load_std_text_inner().unwrap_or_else(|e| panic!("{e}"))
}

/// Reads the standard library now, or says what it looked for and where.
/// The CLI and the language server call this at startup, before anything
/// uses the library, so that a missing or unreadable copy is an error, not
/// a panic.
pub fn load_std_text() -> Result<(), String> {
    load_std_text_inner().map(|_| ())
}

fn load_std_text_inner() -> Result<&'static StdText, String> {
    if let Some(text) = STD.get() {
        return Ok(text);
    }
    let dir = locate()?;
    let text = StdText::read(&dir).map_err(|e| {
        format!(
            "the standard library at {}: {e}. Give its directory with `--std-dir` or \
             {STD_DIR_VAR}.",
            dir.display()
        )
    })?;
    // Another thread may have read it in the meantime; either copy is the
    // one this process uses.
    let _ = STD.set(text);
    Ok(STD.get().expect("the standard library was just set"))
}

/// Reads the standard library from `dir` (the CLI's `--std-dir`). It must
/// come before anything uses the library.
pub fn use_std_dir(dir: &Path) -> Result<(), String> {
    let text = StdText::read(dir).map_err(|e| format!("--std-dir {}: {e}", dir.display()))?;
    STD.set(text)
        .map_err(|_| "the standard library was read before --std-dir was applied".to_string())
}

/// Uses the library given as a bundle: for each file, a line `path bytes`
/// and then that many bytes of text, back to back (`web/bundle-std.sh`
/// writes it). It must come before anything uses the library.
pub fn use_std_bundle(bundle: &[u8]) -> Result<(), String> {
    let text = StdText::from_files(None, parse_bundle(bundle)?)?;
    STD.set(text)
        .map_err(|_| "the standard library was read before the bundle was applied".to_string())
}

fn parse_bundle(mut rest: &[u8]) -> Result<Vec<(String, String)>, String> {
    let mut files = Vec::new();
    while !rest.is_empty() {
        let end = rest
            .iter()
            .position(|&b| b == b'\n')
            .ok_or("the bundle ends inside a header")?;
        let header = std::str::from_utf8(&rest[..end]).map_err(|e| e.to_string())?;
        let (path, len) = header
            .rsplit_once(' ')
            .ok_or_else(|| format!("bad bundle header `{header}`"))?;
        let len: usize = len
            .parse()
            .map_err(|_| format!("bad length in the bundle header `{header}`"))?;
        let body = rest
            .get(end + 1..end + 1 + len)
            .ok_or_else(|| format!("the bundle ends inside `{path}`"))?;
        let text = std::str::from_utf8(body).map_err(|e| format!("`{path}`: {e}"))?;
        files.push((path.to_string(), text.to_string()));
        rest = &rest[end + 1 + len..];
    }
    Ok(files)
}

/// The directory [`STD_DIR_VAR`] names, if it names one. A variable set to
/// nothing (`STITCHWORT_STD_DIR=`) is unset, not a request to read the
/// current directory (SW-3091).
fn env_dir() -> Option<PathBuf> {
    std_dir_from(std::env::var_os(STD_DIR_VAR))
}

/// [`env_dir`]'s rule for one variable value, so it can be tested without
/// changing the test process's environment.
fn std_dir_from(value: Option<std::ffi::OsString>) -> Option<PathBuf> {
    value.filter(|v| !v.is_empty()).map(PathBuf::from)
}

/// The directory to read, by the rules in the module's documentation.
fn locate() -> Result<PathBuf, String> {
    if cfg!(target_arch = "wasm32") {
        return Err(
            "the standard library wasn't given to this WebAssembly build \
                    (the host calls `load_std` first)"
                .into(),
        );
    }
    if let Some(dir) = env_dir() {
        return Ok(dir);
    }
    let exe = std::env::current_exe().and_then(std::fs::canonicalize).ok();
    let mut tried = Vec::new();
    if let Some(bin) = exe.as_deref().and_then(Path::parent) {
        let dir = bin.join(INSTALLED);
        if dir.join(CORE_ORDER).is_file() {
            return Ok(dir);
        }
        tried.push(dir);
    }
    let cwd = std::env::current_dir().ok();
    for start in [exe.as_deref(), cwd.as_deref()].into_iter().flatten() {
        if let Some(dir) = start
            .ancestors()
            .map(|a| a.join(CHECKOUT))
            .find(|d| d.join(CORE_ORDER).is_file())
        {
            return Ok(dir);
        }
    }
    if let Some(root) = BUILD_TREE.get() {
        let build_tree = root.join(CHECKOUT);
        if build_tree.join(CORE_ORDER).is_file() {
            return Ok(build_tree);
        }
        tried.push(build_tree);
    }
    let tried: Vec<String> = tried.iter().map(|d| d.display().to_string()).collect();
    Err(format!(
        "can't find the standard library: not at {} (an installed binary's, then the tree this binary was built from), nor in a \
         checkout's `{CHECKOUT}` above the executable or the current directory. Give its directory with \
         `--std-dir` or {STD_DIR_VAR}.",
        tried.join(", ")
    ))
}

impl StdText {
    /// The library as it is in `dir` now. The text lives for the rest of
    /// the process.
    pub fn read(dir: &Path) -> Result<StdText, String> {
        let dir = std::path::absolute(dir).map_err(|e| e.to_string())?;
        let mut paths = Vec::new();
        collect(&dir, &dir, &mut paths)?;
        let full: Vec<PathBuf> = paths.iter().map(|p| dir.join(p)).collect();
        let mut files = Vec::new();
        for (path, text) in paths.into_iter().zip(read_files(&full)) {
            let text = text.map_err(|e| format!("can't read `{path}`: {e}"))?;
            files.push((path, text));
        }
        StdText::from_files(Some(dir), files)
    }

    /// The library from its files (`.sw` files and the core's manifest, by
    /// path under `std/`).
    fn from_files(dir: Option<PathBuf>, files: Vec<(String, String)>) -> Result<StdText, String> {
        let mut by_path: std::collections::BTreeMap<String, String> = files.into_iter().collect();
        let order = by_path
            .remove(CORE_ORDER)
            .ok_or_else(|| format!("there is no `{CORE_ORDER}`, the core's file list"))?;
        let mut prelude = String::new();
        let mut layout = Vec::new();
        for name in order
            .lines()
            .map(|l| l.split('#').next().unwrap_or("").trim())
            .filter(|l| !l.is_empty())
        {
            let path = format!("core/{name}.sw");
            let text = by_path.remove(&path).ok_or_else(|| {
                format!("`{CORE_ORDER}` lists `{path}`, which is missing or listed twice")
            })?;
            layout.push((leak(path), text.len()));
            prelude.push_str(&text);
        }
        let library = by_path
            .into_iter()
            .filter(|(path, _)| path.ends_with(".sw") && !path.starts_with("core/"))
            .map(|(path, text)| (leak(path), leak(text)))
            .collect::<Vec<_>>();
        Ok(StdText {
            dir,
            prelude: leak(prelude),
            core_layout: Vec::leak(layout),
            library: Vec::leak(library),
        })
    }

    /// How a file of the library (its path under `std/`) is named to the
    /// reader: `std/List/Sort.sw`, wherever the copy was read from. Output,
    /// caches and hashes use this logical name; a host that must open the
    /// file joins the path to [`StdText::dir`] itself.
    pub fn shown_path(&self, path: &str) -> String {
        format!("std/{path}")
    }

    /// Where this copy came from, for tests and tools to say.
    pub fn mode(&self) -> String {
        match &self.dir {
            None => "std from a bundle".to_string(),
            Some(dir) => format!("std from {}", dir.display()),
        }
    }
}

/// The text of each of `paths`, in the order given, read on several threads
/// (at most 8, and none for a handful of files). Each result is what
/// `std::fs::read_to_string` gives that path, so a caller that stops at the
/// first error in order stops where a sequential read would.
pub fn read_files(paths: &[PathBuf]) -> Vec<std::io::Result<String>> {
    const MIN_PARALLEL: usize = 16;
    let threads = std::thread::available_parallelism()
        .map_or(1, |n| n.get())
        .min(8)
        .min(paths.len() / 4);
    if paths.len() < MIN_PARALLEL || threads < 2 {
        return paths.iter().map(std::fs::read_to_string).collect();
    }
    let next = std::sync::atomic::AtomicUsize::new(0);
    let mut results: Vec<Option<std::io::Result<String>>> = paths.iter().map(|_| None).collect();
    std::thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                scope.spawn(|| {
                    let mut done = Vec::new();
                    loop {
                        let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(path) = paths.get(i) else { break };
                        done.push((i, std::fs::read_to_string(path)));
                    }
                    done
                })
            })
            .collect();
        for worker in workers {
            for (i, result) in worker.join().expect("a file-reading thread panicked") {
                results[i] = Some(result);
            }
        }
    });
    results
        .into_iter()
        .map(|r| r.expect("every path was read"))
        .collect()
}

fn leak(s: String) -> &'static str {
    String::leak(s)
}

/// The `.sw` files under `dir` and the core's manifest, as paths under
/// `root` with `/` separators.
fn collect(root: &Path, dir: &Path, out: &mut Vec<String>) -> Result<(), String> {
    let entries = std::fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    for entry in entries {
        let path = entry.map_err(|e| e.to_string())?.path();
        let relative = path.strip_prefix(root).expect("under the root");
        if path.is_dir() {
            collect(root, &path, out)?;
        } else if path.extension().is_some_and(|e| e == "sw") || relative == Path::new(CORE_ORDER) {
            let parts: Vec<String> = relative
                .iter()
                .map(|c| c.to_string_lossy().into_owned())
                .collect();
            out.push(parts.join("/"));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// SW-3091: a shell may export the variable with no value; that is not
    /// a directory to read.
    #[test]
    fn an_empty_std_dir_variable_is_unset() {
        assert_eq!(std_dir_from(None), None);
        assert_eq!(std_dir_from(Some(std::ffi::OsString::new())), None);
        assert_eq!(
            std_dir_from(Some("/somewhere/std".into())),
            Some(PathBuf::from("/somewhere/std"))
        );
    }
}
