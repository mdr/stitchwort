//! The code navigation index as JSON (docs/proposals/code-navigation.md),
//! for the command line and the playground; and as data ([`Index`]), for
//! the language server.

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

/// `[startLine, startCharacter, endLine, endCharacter]`, from 0, characters
/// in UTF-16 code units, the end exclusive (as LSP counts).
pub type Range = [u32; 4];

/// The navigation index of a session as plain data, which can cross
/// threads: what [`index_json`] prints.
#[derive(Clone, Debug, Default)]
pub struct Index {
    pub files: Vec<IndexFile>,
    pub symbols: Vec<Symbol>,
    /// Sorted by file, then position.
    pub refs: Vec<Ref>,
    /// The type of each expression of the program's files, if the session
    /// recorded them (`Elaborator::enable_expression_types`): file (of
    /// `files`), range, and the type as printed.
    pub exprs: Vec<(usize, Range, String)>,
    pub diagnostics: Vec<IndexDiagnostic>,
}

/// A file of the index.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IndexFile {
    /// A program's file: its name, less the root. A library file: where it
    /// is in the repository.
    pub path: String,
    /// A library file's path under `std/` (`List/Toolkit.sw`; `core/Data.sw`
    /// is a file of the core).
    pub std: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Symbol {
    pub name: String,
    pub kind: &'static str,
    /// Into [`Index::files`].
    pub file: usize,
    /// Its name.
    pub range: Range,
    /// The whole declaration, for the program's declarations.
    pub full_range: Option<Range>,
    /// The symbol it is declared in, by index.
    pub container: Option<usize>,
    pub ty: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Ref {
    pub file: usize,
    pub range: Range,
    pub target: RefTarget,
    pub ty: Option<String>,
}

#[derive(Clone, Debug)]
pub enum RefTarget {
    /// Into [`Index::symbols`].
    Symbol(usize),
    /// A local variable, by its binder.
    Binder {
        name: String,
        file: usize,
        range: Range,
    },
}

#[derive(Clone, Debug)]
pub struct IndexDiagnostic {
    pub severity: Severity,
    pub code: &'static str,
    pub message: String,
    /// Where it is (its first label), if anywhere.
    pub at: Option<(usize, Range)>,
    /// Every label, the first included: file, range, message.
    pub labels: Vec<(usize, Range, String)>,
    pub notes: Vec<String>,
}

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
    let index = index_data(session, root, diagnostics);
    let mut symbols = String::new();
    for (i, symbol) in index.symbols.iter().enumerate() {
        if i > 0 {
            symbols.push(',');
        }
        let _ = write!(
            symbols,
            r#"{{"name":{},"kind":"{}","file":{},"range":{}"#,
            string(&symbol.name),
            symbol.kind,
            symbol.file,
            json_range(symbol.range),
        );
        if let Some(full) = symbol.full_range {
            let _ = write!(symbols, r#","fullRange":{}"#, json_range(full));
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

    let mut refs = String::new();
    for (i, r) in index.refs.iter().enumerate() {
        if i > 0 {
            refs.push(',');
        }
        let _ = write!(
            refs,
            r#"{{"file":{},"range":{}"#,
            r.file,
            json_range(r.range)
        );
        match &r.target {
            RefTarget::Symbol(s) => {
                let _ = write!(refs, r#","symbol":{s}"#);
            }
            RefTarget::Binder { name, file, range } => {
                let _ = write!(
                    refs,
                    r#","binder":{{"name":{},"file":{file},"range":{}}}"#,
                    string(name),
                    json_range(*range)
                );
            }
        }
        if let Some(ty) = &r.ty {
            let _ = write!(refs, r#","type":{}"#, string(ty));
        }
        refs.push('}');
    }

    let mut diags = String::new();
    for (i, d) in index.diagnostics.iter().enumerate() {
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
        if let Some((file, range)) = d.at {
            let _ = write!(diags, r#","file":{file},"range":{}"#, json_range(range));
        }
        diags.push_str(r#","labels":["#);
        for (j, (file, range, message)) in d.labels.iter().enumerate() {
            if j > 0 {
                diags.push(',');
            }
            let _ = write!(
                diags,
                r#"{{"file":{file},"range":{},"message":{}}}"#,
                json_range(*range),
                string(message)
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
    for (i, file) in index.files.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        match &file.std {
            None => {
                let _ = write!(out, r#"{{"path":{}}}"#, string(&file.path));
            }
            Some(std) => {
                let _ = write!(
                    out,
                    r#"{{"path":{},"std":{}}}"#,
                    string(&file.path),
                    string(std)
                );
            }
        }
    }
    let _ = write!(
        out,
        r#"],"symbols":[{symbols}],"refs":[{refs}],"diagnostics":[{diags}]}}"#
    );
    out
}

/// What [`index_json`] prints, as data (less `errors` and `ok`).
pub fn index_data(session: &Session, root: &str, diagnostics: &[Diagnostic]) -> Index {
    index_data_of(session, root, diagnostics, true)
}

/// [`index_data`]; without `library`, leaving out the references in the
/// core's and the library's files (which a language server, whose library
/// never changes, needs only once).
pub fn index_data_of(
    session: &Session,
    root: &str,
    diagnostics: &[Diagnostic],
    library: bool,
) -> Index {
    let std_files = session.elab.std_file_count();
    let user = |file: FileId| file.index() >= std_files;
    let sources = &session.sources;
    let index = index_of_files(session, &|file| library || user(file));
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
    let mut symbols = Vec::with_capacity(index.symbols.len());
    for symbol in &index.symbols {
        let file = file_of(symbol.span, &mut files);
        let at = range(&mut lines, sources, symbol.span, last_component(symbol));
        let full_range = symbol
            .range
            .map(|full| range(&mut lines, sources, full, None));
        symbols.push(Symbol {
            name: symbol.name.clone(),
            kind: symbol.kind,
            file,
            range: at,
            full_range,
            container: symbol.container,
            ty: symbol.ty.clone(),
        });
    }

    // Sorted by the file's place in `files` (which is not the order of the
    // source map: the project's files are first), then by position.
    let mut ordered: Vec<(usize, &stitchwort_elab::NavRef)> = index
        .refs
        .iter()
        .map(|r| (file_of(r.span, &mut files), r))
        .collect();
    ordered.sort_by_key(|(file, r)| (*file, r.span.start, r.span.end));
    let mut refs = Vec::with_capacity(ordered.len());
    for (file, r) in ordered {
        let at = range(&mut lines, sources, r.span, r.dot.as_deref());
        let target = match &r.target {
            NavTarget::Symbol(s) => RefTarget::Symbol(*s),
            NavTarget::Binder { name, span } => {
                let file = file_of(*span, &mut files);
                RefTarget::Binder {
                    name: name.clone(),
                    file,
                    range: range(&mut lines, sources, *span, None),
                }
            }
        };
        refs.push(Ref {
            file,
            range: at,
            target,
            ty: r.ty.clone(),
        });
    }

    let mut exprs = Vec::new();
    for (span, ty) in &index.exprs {
        if user(span.file) {
            let file = file_of(*span, &mut files);
            let span = Span::new(
                span.file,
                span.start,
                closed(&sources.get(span.file).text, *span),
            );
            exprs.push((file, range(&mut lines, sources, span, None), ty.clone()));
        }
    }

    let mut diags = Vec::with_capacity(diagnostics.len());
    for d in diagnostics {
        let at = d.labels.first().map(|first| {
            let file = file_of(first.span, &mut files);
            (file, range(&mut lines, sources, first.span, None))
        });
        let mut labels = Vec::with_capacity(d.labels.len());
        for label in &d.labels {
            let file = file_of(label.span, &mut files);
            labels.push((
                file,
                range(&mut lines, sources, label.span, None),
                label.message.clone(),
            ));
        }
        diags.push(IndexDiagnostic {
            severity: d.severity,
            code: d.code,
            message: d.message.clone(),
            at,
            labels,
            notes: d.notes.clone(),
        });
    }

    let files = files
        .iter()
        .map(|(file, part)| {
            let name = &sources.get(*file).name;
            if user(*file) {
                IndexFile {
                    path: name.strip_prefix(root).unwrap_or(name).to_string(),
                    std: None,
                }
            } else {
                let std = match name.strip_prefix("std/") {
                    Some(std) => std,
                    None => stitchwort_elab::CORE_LAYOUT
                        .get(*part)
                        .map_or("core", |(p, _)| p),
                };
                IndexFile {
                    path: format!("{STD_DIR}{std}"),
                    std: Some(std.to_string()),
                }
            }
        })
        .collect();
    Index {
        files,
        symbols,
        refs,
        exprs,
        diagnostics: diags,
    }
}

/// Where the expression at `span` ends: a call's span ends at its last
/// argument, short of the `)` that closes a parenthesised one, so the end
/// moves over `)`s that close a `(` inside it.
fn closed(text: &str, span: Span) -> u32 {
    let Some(inside) = text.get(span.range()) else {
        return span.end;
    };
    let mut open = inside.matches('(').count() as i64 - inside.matches(')').count() as i64;
    let mut end = span.end as usize;
    while open > 0 {
        let rest = &text[end..];
        let trimmed = rest.trim_start();
        if !trimmed.starts_with(')') {
            break;
        }
        end += rest.len() - trimmed.len() + 1;
        open -= 1;
    }
    end as u32
}

fn json_range([l1, c1, l2, c2]: Range) -> String {
    format!("[{l1},{c1},{l2},{c2}]")
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

/// With `last`, the span covers a dotted name whose last component is
/// `last`: only that.
fn range(lines: &mut Lines, sources: &SourceMap, span: Span, last: Option<&str>) -> Range {
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
    [l1 as u32, c1 as u32, l2 as u32, c2 as u32]
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
    index_of_files(session, &|_| true)
}

/// [`index_of`], with only the references in the files `wanted` says.
fn index_of_files(session: &Session, wanted: &dyn Fn(FileId) -> bool) -> NavIndex {
    let sources = &session.sources;
    // Derived code is elaborated with the spans of the declaration it comes
    // from: only what's written as a name is a reference.
    let written = |span: Span, last: Option<&str>| {
        wanted(span.file)
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
