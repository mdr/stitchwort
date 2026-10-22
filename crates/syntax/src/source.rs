use std::ops::Range;

/// Identifies a file within a [`SourceMap`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FileId(u32);

impl FileId {
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
    pub(crate) const NOWHERE: Span = Span {
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

    pub fn add(&mut self, name: impl Into<String>, text: impl Into<String>) -> FileId {
        let id = FileId(u32::try_from(self.files.len()).expect("too many source files"));
        self.files.push(SourceFile {
            name: name.into(),
            text: text.into(),
        });
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
