//! Where the standard library's text comes from: the copy embedded in the
//! binary, or, for working on the library, a directory read when the process
//! first asks for it (SW-145).
//!
//! A build embeds `std/` ([`crate::EMBEDDED_PRELUDE`],
//! [`crate::EMBEDDED_LIBRARY_FILES`]). Setting the environment variable
//! [`STD_DIR_VAR`] (`STITCHWORT_STD_DIR`) to a directory laid out as `std/`
//! is (`crates/elab/src/std` in a checkout), or passing the CLI's `--std-dir`
//! ([`use_std_dir`]), reads that directory instead, so an edited library file
//! takes effect without rebuilding the compiler. It is read once per process:
//! everything else (the library index, the check cache's keys, the test
//! cache's build fingerprint) is computed from the text read, so caches key
//! on what is actually on disk.
//!
//! The core's files are read in the order the build lists
//! ([`crate::CORE_FILES`]); a new core file needs a rebuild. Library files are
//! every `.sw` file outside `core/`, so a new one doesn't.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// The environment variable naming a directory to read `std/` from.
pub const STD_DIR_VAR: &str = "STITCHWORT_STD_DIR";

/// The standard library's text, as this process reads it.
pub struct StdText {
    /// The directory it was read from; `None` for the embedded copy.
    pub dir: Option<PathBuf>,
    /// The core's files, joined.
    pub prelude: &'static str,
    /// Each core file's path under `std/` and length, in order.
    pub core_layout: &'static [(&'static str, usize)],
    /// The library files, `(path under std/, text)`, sorted by path.
    pub library: &'static [(&'static str, &'static str)],
}

static STD: OnceLock<StdText> = OnceLock::new();

/// The standard library's text: from the directory [`use_std_dir`] gave or
/// [`STD_DIR_VAR`] names, else the embedded copy. Panics, naming the
/// directory, if a directory was asked for and can't be read: a fault in the
/// developer's setup, not in a program.
pub fn std_text() -> &'static StdText {
    STD.get_or_init(|| match dir_from_env() {
        Some(dir) => {
            StdText::read(&dir).unwrap_or_else(|e| panic!("{STD_DIR_VAR}={}: {e}", dir.display()))
        }
        None => StdText::embedded(),
    })
}

/// Reads the standard library from `dir` instead of the embedded copy (the
/// CLI's `--std-dir`). It must come before anything uses the library.
pub fn use_std_dir(dir: &Path) -> Result<(), String> {
    let text = StdText::read(dir).map_err(|e| format!("--std-dir {}: {e}", dir.display()))?;
    STD.set(text)
        .map_err(|_| "the standard library was read before --std-dir was applied".to_string())
}

fn dir_from_env() -> Option<PathBuf> {
    if cfg!(target_arch = "wasm32") {
        return None;
    }
    std::env::var_os(STD_DIR_VAR)
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
}

impl StdText {
    fn embedded() -> StdText {
        StdText {
            dir: None,
            prelude: crate::EMBEDDED_PRELUDE,
            core_layout: crate::EMBEDDED_CORE_LAYOUT,
            library: crate::EMBEDDED_LIBRARY_FILES,
        }
    }

    /// The library as it is in `dir` now. The text lives for the rest of
    /// the process, as the embedded copy does.
    pub fn read(dir: &Path) -> Result<StdText, String> {
        let dir = std::path::absolute(dir).map_err(|e| e.to_string())?;
        let mut prelude = String::new();
        let mut layout = Vec::new();
        for name in crate::CORE_FILES {
            let path = format!("core/{name}.sw");
            let text = std::fs::read_to_string(dir.join(&path))
                .map_err(|e| format!("can't read the core file `{path}`: {e}"))?;
            layout.push((leak(path), text.len()));
            prelude.push_str(&text);
        }
        let mut paths = Vec::new();
        library_paths(&dir, &dir, &mut paths)?;
        paths.sort();
        let mut library = Vec::new();
        for path in paths {
            let text = std::fs::read_to_string(dir.join(&path))
                .map_err(|e| format!("can't read `{path}`: {e}"))?;
            library.push((leak(path), leak(text)));
        }
        Ok(StdText {
            dir: Some(dir),
            prelude: leak(prelude),
            core_layout: Vec::leak(layout),
            library: Vec::leak(library),
        })
    }

    /// How a file of the library (its path under `std/`) is named to the
    /// reader: `std/List/Sort.sw` for the embedded copy, the file's own path
    /// when read from a directory, so an editor can open it.
    pub fn shown_path(&self, path: &str) -> String {
        match &self.dir {
            None => format!("std/{path}"),
            Some(dir) => dir.join(path).display().to_string(),
        }
    }

    /// Which copy this is, for tests and tools to say.
    pub fn mode(&self) -> String {
        match &self.dir {
            None => "embedded std".to_string(),
            Some(dir) => format!("std from {}", dir.display()),
        }
    }
}

fn leak(s: String) -> &'static str {
    String::leak(s)
}

/// The `.sw` files under `dir` outside `core/`, as paths under `root` with
/// `/` separators.
fn library_paths(root: &Path, dir: &Path, out: &mut Vec<String>) -> Result<(), String> {
    let entries = std::fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    for entry in entries {
        let path = entry.map_err(|e| e.to_string())?.path();
        let relative = path.strip_prefix(root).expect("under the root");
        if path.is_dir() {
            if relative != Path::new("core") {
                library_paths(root, &path, out)?;
            }
        } else if path.extension().is_some_and(|e| e == "sw") {
            let parts: Vec<String> = relative
                .iter()
                .map(|c| c.to_string_lossy().into_owned())
                .collect();
            out.push(parts.join("/"));
        }
    }
    Ok(())
}
