//! The layout document and its printer, after Wadler's "A prettier printer"
//! and Prettier (docs/proposals/formatter.md §2.3).
//!
//! A [`Doc`] says what to print and where lines may break; [`print`] decides
//! the breaks and writes the text. v1 keeps the author's line breaks
//! (D1013), so the formatter only builds [`Doc::HardLine`]s and never a
//! [`Doc::Group`] that could print flat. Groups, soft lines and the width
//! are here for width-based wrapping (stage F8, D1014): a group prints flat
//! when it fits in the width left on its line, and otherwise breaks every
//! line in it, all or nothing (which is D1012's bracket rule).

/// A layout document.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Doc {
    /// Text without line breaks.
    Text(String),
    /// Text printed exactly as given, line breaks included, with no
    /// indentation added after them: a `"""` text block, already moved to
    /// its new column.
    Raw(String),
    /// A space if its group prints flat, otherwise a line break.
    Line,
    /// Nothing if its group prints flat, otherwise a line break.
    SoftLine,
    /// Always a line break. A group containing one never prints flat.
    HardLine,
    /// The contents with line breaks indented this many more columns.
    Nest(usize, Box<Doc>),
    /// Printed flat if it fits, otherwise with every line in it broken.
    Group(Box<Doc>),
    Concat(Vec<Doc>),
}

impl Doc {
    pub fn text(text: impl Into<String>) -> Doc {
        Doc::Text(text.into())
    }

    pub fn nest(indent: usize, doc: Doc) -> Doc {
        Doc::Nest(indent, Box::new(doc))
    }

    pub fn group(doc: Doc) -> Doc {
        Doc::Group(Box::new(doc))
    }

    /// Whether printing this always breaks a line.
    fn has_hard_line(&self) -> bool {
        match self {
            Doc::HardLine => true,
            Doc::Raw(text) => text.contains('\n'),
            Doc::Text(_) | Doc::Line | Doc::SoftLine => false,
            Doc::Nest(_, doc) | Doc::Group(doc) => doc.has_hard_line(),
            Doc::Concat(docs) => docs.iter().any(Doc::has_hard_line),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Flat,
    Break,
}

/// Prints `doc`, breaking groups that don't fit in `width` columns (`None`:
/// every group fits unless it holds a hard line). Lines never end in
/// spaces: indentation is written only before text.
pub fn print(doc: &Doc, width: Option<usize>) -> String {
    let mut out = String::new();
    // The column the next character goes in, and the indentation owed
    // before the next text on a fresh line.
    let mut column = 0usize;
    let mut owed: Option<usize> = None;
    let mut stack: Vec<(usize, Mode, &Doc)> = vec![(0, Mode::Break, doc)];
    while let Some((indent, mode, doc)) = stack.pop() {
        match doc {
            Doc::Text(text) | Doc::Raw(text) => {
                if text.is_empty() {
                    continue;
                }
                if let Some(n) = owed.take() {
                    out.extend(std::iter::repeat_n(' ', n));
                    column = n;
                }
                out.push_str(text);
                column = match text.rfind('\n') {
                    Some(k) => text.len() - k - 1,
                    None => column + text.len(),
                };
            }
            Doc::Line | Doc::SoftLine if mode == Mode::Flat => {
                if *doc == Doc::Line {
                    if let Some(n) = owed.take() {
                        out.extend(std::iter::repeat_n(' ', n));
                        column = n;
                    }
                    out.push(' ');
                    column += 1;
                }
            }
            Doc::Line | Doc::SoftLine | Doc::HardLine => {
                out.push('\n');
                column = 0;
                owed = Some(indent);
            }
            Doc::Nest(more, doc) => stack.push((indent + more, mode, doc)),
            Doc::Group(inner) => {
                let flat = mode == Mode::Flat
                    || (!inner.has_hard_line()
                        && fits(inner, width.map(|w| w.saturating_sub(column))));
                let mode = if flat { Mode::Flat } else { Mode::Break };
                stack.push((indent, mode, inner));
            }
            Doc::Concat(docs) => {
                for doc in docs.iter().rev() {
                    stack.push((indent, mode, doc));
                }
            }
        }
    }
    out
}

/// Whether `doc`, printed flat, fits in `left` columns.
fn fits(doc: &Doc, left: Option<usize>) -> bool {
    let Some(mut left) = left else {
        return true;
    };
    let mut stack = vec![doc];
    while let Some(doc) = stack.pop() {
        let used = match doc {
            Doc::Text(text) | Doc::Raw(text) => text.len(),
            Doc::Line => 1,
            Doc::SoftLine => 0,
            Doc::HardLine => return false,
            Doc::Nest(_, doc) | Doc::Group(doc) => {
                stack.push(doc);
                0
            }
            Doc::Concat(docs) => {
                stack.extend(docs.iter().rev());
                0
            }
        };
        match left.checked_sub(used) {
            Some(rest) => left = rest,
            None => return false,
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn list(items: &[&str]) -> Doc {
        let mut docs = vec![Doc::text("[")];
        let mut body = Vec::new();
        for (k, item) in items.iter().enumerate() {
            body.push(Doc::SoftLine);
            body.push(Doc::text(*item));
            if k + 1 < items.len() {
                body.push(Doc::text(","));
            }
        }
        docs.push(Doc::nest(2, Doc::Concat(body)));
        docs.push(Doc::SoftLine);
        docs.push(Doc::text("]"));
        Doc::group(Doc::Concat(docs))
    }

    #[test]
    fn a_group_prints_flat_when_it_fits() {
        assert_eq!(print(&list(&["a", "b"]), Some(80)), "[a,b]");
        assert_eq!(print(&list(&["a", "b"]), None), "[a,b]");
    }

    #[test]
    fn a_group_that_does_not_fit_breaks_every_line() {
        assert_eq!(print(&list(&["a", "b"]), Some(4)), "[\n  a,\n  b\n]");
    }

    #[test]
    fn a_hard_line_breaks_its_group_and_blank_lines_have_no_spaces() {
        let doc = Doc::group(Doc::nest(
            4,
            Doc::Concat(vec![
                Doc::text("x"),
                Doc::HardLine,
                Doc::HardLine,
                Doc::text("y"),
                Doc::Line,
                Doc::text("z"),
            ]),
        ));
        assert_eq!(print(&doc, None), "x\n\n    y\n    z");
    }

    #[test]
    fn raw_text_is_not_indented() {
        let doc = Doc::nest(
            2,
            Doc::Concat(vec![
                Doc::HardLine,
                Doc::Raw("\"\"\"\n  a\n  \"\"\"".into()),
            ]),
        );
        assert_eq!(print(&doc, None), "\n  \"\"\"\n  a\n  \"\"\"");
    }
}
