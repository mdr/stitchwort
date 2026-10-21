//! The code navigation index as JSON (docs/proposals/code-navigation.md),
//! for the command line and the playground.

use std::collections::HashMap;
use std::fmt::Write;

use stitchwort_elab::{LIBRARY_FILES, NavIndex, NavTarget, PRELUDE};
use stitchwort_syntax::{FileId, SourceMap, Span};

use crate::driver::Session;

/// The version of the format.
pub const VERSION: u32 = 1;

/// Where the library's files are in the repository, relative to its root.
const STD_DIR: &str = "crates/elab/src/std/";

/// The text of an embedded library file, by its path under `std/`
/// (`core.sw` is the core), as a file's `std` marker names it.
pub fn std_source(path: &str) -> Option<&'static str> {
    if path == "core.sw" {
        return Some(PRELUDE);
    }
    LIBRARY_FILES
        .iter()
        .find(|(p, _)| *p == path)
        .map(|(_, text)| *text)
}

/// The index of everything `session` has loaded, with `enable_navigation`
/// on before it loaded. `errors` is whether checking found errors; `ok`
/// adds an `"ok"` member (the playground's). `root` is a prefix of the
/// source files' names to strip, so paths are relative to the project's
/// root (`""` for none).
pub fn index_json(session: &Session, errors: bool, ok: Option<bool>, root: &str) -> String {
    let std_files = session.elab.std_file_count();
    let user = |file: FileId| file.index() >= std_files;
    let sources = &session.sources;
    let index = index_of(session);
    let mut lines = Lines::default();
    let mut files: Vec<FileId> = Vec::new();
    let mut file_index: HashMap<FileId, usize> = HashMap::new();
    let mut file_of = |file: FileId, files: &mut Vec<FileId>| {
        *file_index.entry(file).or_insert_with(|| {
            files.push(file);
            files.len() - 1
        })
    };
    let mut symbols = String::new();
    for (i, symbol) in index.symbols.iter().enumerate() {
        if i > 0 {
            symbols.push(',');
        }
        let file = file_of(symbol.span.file, &mut files);
        let _ = write!(
            symbols,
            r#"{{"name":{},"kind":"{}","file":{file},"range":{}"#,
            string(&symbol.name),
            symbol.kind,
            range(&mut lines, sources, symbol.span, None),
        );
        if let Some(full) = symbol.range {
            let _ = write!(
                symbols,
                r#","fullRange":{}"#,
                range(&mut lines, sources, full, None)
            );
        }
        if let Some(container) = symbol.container {
            let _ = write!(symbols, r#","container":{container}"#);
        }
        if let Some(ty) = &symbol.ty {
            let _ = write!(symbols, r#","type":{}"#, string(ty));
        }
        symbols.push('}');
    }

    let mut refs = String::new();
    for (i, r) in index.refs.iter().enumerate() {
        if i > 0 {
            refs.push(',');
        }
        let file = file_of(r.span.file, &mut files);
        let _ = write!(
            refs,
            r#"{{"file":{file},"range":{}"#,
            range(&mut lines, sources, r.span, r.dot.as_deref())
        );
        match &r.target {
            NavTarget::Symbol(s) => {
                let _ = write!(refs, r#","symbol":{s}"#);
            }
            NavTarget::Binder { name, span } => {
                let binder_file = file_of(span.file, &mut files);
                let _ = write!(
                    refs,
                    r#","binder":{{"name":{},"file":{binder_file},"range":{}}}"#,
                    string(name),
                    range(&mut lines, sources, *span, None)
                );
            }
        }
        if let Some(ty) = &r.ty {
            let _ = write!(refs, r#","type":{}"#, string(ty));
        }
        refs.push('}');
    }

    let mut out = format!(r#"{{"version":{VERSION},"errors":{errors}"#);
    if let Some(ok) = ok {
        let _ = write!(out, r#","ok":{ok}"#);
    }
    out.push_str(r#","files":["#);
    for (i, file) in files.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let name = &sources.get(*file).name;
        if user(*file) {
            let name = name.strip_prefix(root).unwrap_or(name);
            let _ = write!(out, r#"{{"path":{}}}"#, string(name));
        } else {
            let std = name.strip_prefix("std/").unwrap_or("core.sw");
            let _ = write!(
                out,
                r#"{{"path":{},"std":{}}}"#,
                string(&format!("{STD_DIR}{std}")),
                string(std)
            );
        }
    }
    let _ = write!(out, r#"],"symbols":[{symbols}],"refs":[{refs}]}}"#);
    out
}

/// The start of each line of each file, found when first needed.
#[derive(Default)]
struct Lines(HashMap<FileId, Vec<usize>>);

impl Lines {
    /// `(line, UTF-16 column)`, both from 0, of `offset` in `file`.
    fn position(&mut self, sources: &SourceMap, file: FileId, offset: usize) -> (usize, usize) {
        let text = &sources.get(file).text;
        let starts = self.0.entry(file).or_insert_with(|| {
            std::iter::once(0)
                .chain(text.match_indices('\n').map(|(i, _)| i + 1))
                .collect()
        });
        let line = starts.partition_point(|&s| s <= offset) - 1;
        let offset = offset.min(text.len());
        let column = text[starts[line]..offset].encode_utf16().count();
        (line, column)
    }
}

/// `[startLine, startCharacter, endLine, endCharacter]`. With `last`, the
/// span covers a dotted name whose last component is `last`: only that.
fn range(lines: &mut Lines, sources: &SourceMap, span: Span, last: Option<&str>) -> String {
    let text = &sources.get(span.file).text;
    let (mut start, end) = (span.start as usize, span.end as usize);
    if let Some(last) = last
        && let Some(written) = text.get(start..end)
        && written.len() > last.len()
        && written.ends_with(last)
    {
        start = end - last.len();
    }
    let (l1, c1) = lines.position(sources, span.file, start);
    let (l2, c2) = lines.position(sources, span.file, end);
    format!("[{l1},{c1},{l2},{c2}]")
}

/// What the index holds for the files of `session` that are the program's
/// (not the core's or the library's).
pub fn index_of(session: &Session) -> NavIndex {
    let std_files = session.elab.std_file_count();
    let sources = &session.sources;
    // Derived code is elaborated with the spans of the declaration it comes
    // from: only what's written as a name is a reference.
    let written = |span: Span, last: Option<&str>| {
        span.file.index() >= std_files
            && sources
                .get(span.file)
                .text
                .get(span.range())
                .is_some_and(|t| {
                    let t = last.map_or(t, |l| t.strip_suffix(l).map_or(t, |_| l));
                    !t.is_empty()
                        && t.chars().all(|c| {
                            c.is_alphanumeric() || matches!(c, '_' | '\'' | '.' | '!' | '?')
                        })
                })
    };
    session.elab.navigation_index(&written)
}

/// `text` as a JSON string.
pub fn string(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
