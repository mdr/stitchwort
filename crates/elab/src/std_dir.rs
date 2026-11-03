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
//!    then of the current directory, that has one.
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

/// The directory to read, by the rules in the module's documentation.
fn locate() -> Result<PathBuf, String> {
    if cfg!(target_arch = "wasm32") {
        return Err(
            "the standard library wasn't given to this WebAssembly build \
                    (the host calls `load_std` first)"
                .into(),
        );
    }
    if let Some(dir) = std::env::var_os(STD_DIR_VAR).filter(|v| !v.is_empty()) {
        return Ok(PathBuf::from(dir));
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
    let tried: Vec<String> = tried.iter().map(|d| d.display().to_string()).collect();
    Err(format!(
        "can't find the standard library: not at {} (an installed binary's), nor in a checkout's \
         `{CHECKOUT}` above the executable or the current directory. Give its directory with \
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
        let mut files = Vec::new();
        for path in paths {
            let text = std::fs::read_to_string(dir.join(&path))
                .map_err(|e| format!("can't read `{path}`: {e}"))?;
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
