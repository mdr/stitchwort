use std::ops::Range;

/// Identifies a file within a [`SourceMap`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FileId(u32);

/// A byte range within one source file.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

impl Span {
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
