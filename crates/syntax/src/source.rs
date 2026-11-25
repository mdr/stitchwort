use std::ops::Range;

/// Identifies a file within a [`SourceMap`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FileId(u32);

impl FileId {
    /// The file of text parsed only to be elaborated and thrown away, never
    /// in any [`SourceMap`]: what is noted at its spans belongs to no real
    /// file.
    pub const SCRATCH: FileId = FileId(u32::MAX);

    /// Its position in the [`SourceMap`] it came from.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A byte range within one source file.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

thread_local! {
    /// Whether spans print as `_` in debug output, for comparing syntax
    /// trees without their positions ([`crate::equivalence`]).
    pub(crate) static HIDE_SPANS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if HIDE_SPANS.with(std::cell::Cell::get) {
            return f.write_str("_");
        }
        f.debug_struct("Span")
            .field("file", &self.file)
            .field("start", &self.start)
            .field("end", &self.end)
            .finish()
    }
}

impl Span {
    /// For placeholders that are never shown.
    pub const NOWHERE: Span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };

    pub fn new(file: FileId, start: u32, end: u32) -> Self {
        debug_assert!(start <= end, "span start {start} is after end {end}");
        Span { file, start, end }
    }

    /// An empty span at `offset`, for pointing at a position rather than a range.
    pub fn point(file: FileId, offset: u32) -> Self {
        Span::new(file, offset, offset)
    }

    /// The smallest span covering both `self` and `other` (which must be in the same file).
    pub fn to(self, other: Span) -> Span {
        Span::new(
            self.file,
            self.start.min(other.start),
            self.end.max(other.end),
        )
    }

    pub fn range(self) -> Range<usize> {
        self.start as usize..self.end as usize
    }
}

/// Whether `STITCHWORT_BIG_READBACK` is set, read once: then each
/// [`SourceMap::add`] also copies the file into a process-wide table, so that
/// [`describe_span`] can say where a span is without the source map (the
/// elaborator doesn't have it). Unset, `add` pays one cached read.
fn describing() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| crate::env_flag::env_flag("STITCHWORT_BIG_READBACK"))
}

/// Name and text of each file added since `STITCHWORT_BIG_READBACK` was set,
/// by [`FileId`] index. With several source maps in one process (the library's
/// and the project's) the latest file added at an index wins; only the debugging report reads it.
static DESCRIBED: std::sync::Mutex<Vec<(String, String)>> = std::sync::Mutex::new(Vec::new());

/// `file:line:col` and the first line of the span's text (cut to 60
/// characters), for `STITCHWORT_BIG_READBACK`'s report. `None` when the
/// variable was unset or the file is unknown.
pub fn describe_span(span: Span) -> Option<String> {
    let registry = DESCRIBED.lock().unwrap_or_else(|e| e.into_inner());
    let (name, text) = registry.get(span.file.index())?;
    let start = (span.start as usize).min(text.len());
    let before = text.get(..start)?;
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    let rest = text.get(start..)?;
    let end = (span.end as usize).saturating_sub(start).min(rest.len());
    let shown: String = rest
        .get(..end)
        .unwrap_or(rest)
        .lines()
        .next()
        .unwrap_or("")
        .chars()
        .take(60)
        .collect();
    Some(format!("{name}:{line}:{col}  {shown}"))
}

#[derive(Debug)]
pub struct SourceFile {
    /// Display name used in diagnostics, e.g. a path relative to the project.
    pub name: String,
    pub text: String,
}

/// Every source file the compiler has seen, so diagnostics can show source excerpts.
#[derive(Debug, Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    pub fn new() -> Self {
        Self::default()
    }

    /// The id the next file added gets.
    pub fn next_id(&self) -> FileId {
        FileId(u32::try_from(self.files.len()).expect("too many source files"))
    }

    pub fn add(&mut self, name: impl Into<String>, text: impl Into<String>) -> FileId {
        let id = FileId(u32::try_from(self.files.len()).expect("too many source files"));
        let (name, text) = (name.into(), text.into());
        if describing() {
            let mut registry = DESCRIBED.lock().unwrap_or_else(|e| e.into_inner());
            let index = self.files.len();
            if registry.len() <= index {
                registry.resize(index + 1, (String::new(), String::new()));
            }
            registry[index] = (name.clone(), text.clone());
        }
        self.files.push(SourceFile { name, text });
        id
    }

    pub fn get(&self, id: FileId) -> &SourceFile {
        &self.files[id.0 as usize]
    }

    pub fn iter(&self) -> impl Iterator<Item = (FileId, &SourceFile)> {
        (0..).map(FileId).zip(&self.files)
    }

    /// How many files there are.
    pub fn len(&self) -> usize {
        self.files.len()
    }

    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }

    /// Forgets the files from the `len`th on, whose ids are then given out
    /// again: for a session rewound to before they were added.
    pub fn truncate(&mut self, len: usize) {
        self.files.truncate(len);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn files_are_retrievable_by_id() {
        let mut sources = SourceMap::new();
        let a = sources.add("a.sw", "one");
        let b = sources.add("b.sw", "two");

        assert_eq!(sources.get(a).text, "one");
        assert_eq!(sources.get(b).name, "b.sw");
        assert_eq!(
            sources.iter().map(|(id, _)| id).collect::<Vec<_>>(),
            vec![a, b]
        );
    }
}
