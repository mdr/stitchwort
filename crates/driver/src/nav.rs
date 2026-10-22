//! The code navigation index as JSON (docs/proposals/code-navigation.md),
//! for the command line and the playground.

use std::collections::HashMap;
use std::fmt::Write;

use stitchwort_elab::{NavIndex, NavTarget};
use stitchwort_syntax::{Diagnostic, FileId, Severity, SourceMap, Span};

use crate::driver::Session;

/// The version of the format.
pub const VERSION: u32 = 2;

/// Where the library's files are in the repository, relative to its root.
const STD_DIR: &str = "crates/elab/src/std/";

/// The text of an embedded library file, by its path under `std/`
/// (`core/Int.sw` is a file of the core), as a file's `std` marker names it.
///
/// (Looked up inside the elaborator's crate: the texts are constants, and a
/// constant used from another crate is copied into it, which in WebAssembly
/// doubles the library's size.)
pub use stitchwort_elab::std_source;

/// The index of everything `session` has loaded, with `enable_navigation`
/// on before it loaded. `errors` is whether checking found errors; `ok`
/// adds an `"ok"` member (the playground's). `root` is a prefix of the
/// source files' names to strip, so paths are relative to the project's
/// root (`""` for none).
/// `diagnostics` is everything checking reported.
pub fn index_json(
    session: &Session,
    errors: bool,
    ok: Option<bool>,
    root: &str,
    diagnostics: &[Diagnostic],
) -> String {
    let std_files = session.elab.std_file_count();
    let user = |file: FileId| file.index() >= std_files;
    let sources = &session.sources;
    let index = index_of(session);
    let mut lines = Lines::default();
    // A file of the index: a source file, or for the core, one of the files
    // it is made of (the second member; 0 for any other file).
    let mut files: Vec<(FileId, usize)> = Vec::new();
    let mut file_index: HashMap<(FileId, usize), usize> = HashMap::new();
    let mut file_of = |span: Span, files: &mut Vec<(FileId, usize)>| {
        let key = (span.file, core_part(sources, span).map_or(0, |(i, _)| i));
        *file_index.entry(key).or_insert_with(|| {
            files.push(key);
            files.len() - 1
        })
    };
    let mut symbols = String::new();
    for (i, symbol) in index.symbols.iter().enumerate() {
        if i > 0 {
            symbols.push(',');
        }
        let file = file_of(symbol.span, &mut files);
        let _ = write!(
            symbols,
            r#"{{"name":{},"kind":"{}","file":{file},"range":{}"#,
            string(&symbol.name),
            symbol.kind,
            range(&mut lines, sources, symbol.span, last_component(symbol)),
        );
        if let Some(full) = symbol.range {
            let _ = write!(
                symbols,
                r#","fullRange":{}"#,
                range(&mut lines, sources, full, None)
            );
        }
        match symbol.container {
            Some(container) => {
                let _ = write!(symbols, r#","container":{container}"#);
            }
            None => symbols.push_str(r#","container":null"#),
        }
        if let Some(ty) = &symbol.ty {
            let _ = write!(symbols, r#","type":{}"#, string(ty));
        }
        symbols.push('}');
    }

    // Sorted by the file's place in `files` (which is not the order of the
    // source map: the project's files are first), then by position.
    let mut ordered: Vec<(usize, &stitchwort_elab::NavRef)> = index
        .refs
        .iter()
        .map(|r| (file_of(r.span, &mut files), r))
        .collect();
    ordered.sort_by_key(|(file, r)| (*file, r.span.start, r.span.end));
    let mut refs = String::new();
    for (i, (file, r)) in ordered.into_iter().enumerate() {
        if i > 0 {
            refs.push(',');
        }
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
                let binder_file = file_of(*span, &mut files);
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

    let mut diags = String::new();
    for (i, d) in diagnostics.iter().enumerate() {
        if i > 0 {
            diags.push(',');
        }
        let severity = match d.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };
        let _ = write!(
            diags,
            r#"{{"severity":"{severity}","code":{},"message":{}"#,
            string(d.code),
            string(&d.message)
        );
        // The first label is where the diagnostic is; the others are
        // secondary and come in `labels` with it.
        if let Some(first) = d.labels.first() {
            let file = file_of(first.span, &mut files);
            let _ = write!(
                diags,
                r#","file":{file},"range":{}"#,
                range(&mut lines, sources, first.span, None)
            );
        }
        diags.push_str(r#","labels":["#);
        for (j, label) in d.labels.iter().enumerate() {
            if j > 0 {
                diags.push(',');
            }
            let file = file_of(label.span, &mut files);
            let _ = write!(
                diags,
                r#"{{"file":{file},"range":{},"message":{}}}"#,
                range(&mut lines, sources, label.span, None),
                string(&label.message)
            );
        }
        diags.push_str(r#"],"notes":["#);
        for (j, note) in d.notes.iter().enumerate() {
            if j > 0 {
                diags.push(',');
            }
            diags.push_str(&string(note));
        }
        diags.push_str("]}");
    }

    let mut out = format!(r#"{{"version":{VERSION},"errors":{errors}"#);
    if let Some(ok) = ok {
        let _ = write!(out, r#","ok":{ok}"#);
    }
    out.push_str(r#","files":["#);
    for (i, (file, part)) in files.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let name = &sources.get(*file).name;
        if user(*file) {
            let name = name.strip_prefix(root).unwrap_or(name);
            let _ = write!(out, r#"{{"path":{}}}"#, string(name));
        } else {
            let std = match name.strip_prefix("std/") {
                Some(std) => std,
                None => stitchwort_elab::CORE_LAYOUT
                    .get(*part)
                    .map_or("core", |(p, _)| p),
            };
            let _ = write!(
                out,
                r#"{{"path":{},"std":{}}}"#,
                string(&format!("{STD_DIR}{std}")),
                string(std)
            );
        }
    }
    let _ = write!(
        out,
        r#"],"symbols":[{symbols}],"refs":[{refs}],"diagnostics":[{diags}]}}"#
    );
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

/// The component of a symbol's name that its span covers alone: the last, in
/// `def List.length`. (A test's name is its description.)
fn last_component(symbol: &stitchwort_elab::NavSymbol) -> Option<&str> {
    (symbol.kind != "test").then(|| symbol.name.rsplit('.').next().unwrap_or_default())
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
    let (mut l1, c1) = lines.position(sources, span.file, start);
    let (mut l2, c2) = lines.position(sources, span.file, end);
    // In a file of the core, lines count from that file's start (each file
    // of the core starts at a line start).
    if let Some((_, base)) = core_part(sources, span) {
        let (before, _) = lines.position(sources, span.file, base);
        l1 -= before;
        l2 -= before;
    }
    format!("[{l1},{c1},{l2},{c2}]")
}

/// If `span` is in the core's text, the core file it is in, and where that
/// file starts in the core: the core is one source file here, and the index
/// shows it as the files it is made of.
fn core_part(sources: &SourceMap, span: Span) -> Option<(usize, usize)> {
    let file = sources.get(span.file);
    if file.name != "<prelude>" || file.text.len() != stitchwort_elab::PRELUDE.len() {
        return None;
    }
    let (_, start, part) = stitchwort_elab::core_file_at(span.start as usize);
    Some((part, start))
}

/// What the index holds for the files of `session` that are the program's
/// (not the core's or the library's).
pub fn index_of(session: &Session) -> NavIndex {
    let sources = &session.sources;
    // Derived code is elaborated with the spans of the declaration it comes
    // from: only what's written as a name is a reference.
    let written = |span: Span, last: Option<&str>| {
        sources
            .get(span.file)
            .text
            .get(span.range())
            .is_some_and(|t| {
                let t = last.map_or(t, |l| t.strip_suffix(l).map_or(t, |_| l));
                !t.is_empty()
                    && t.chars()
                        .all(|c| c.is_alphanumeric() || matches!(c, '_' | '\'' | '.' | '!' | '?'))
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
