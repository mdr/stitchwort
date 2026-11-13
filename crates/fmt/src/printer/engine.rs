//! The layout engine of the tree printer: a document algebra after Wadler's
//! "A prettier printer" and Prettier, and the printer that decides its line
//! breaks (docs/proposals/formatter-style.md §1, rules E1 to E5).
//!
//! A [`Doc`] says what to print and where lines may break. A [`Doc::Group`]
//! prints on one line if all of it, plus whatever must follow it on the same
//! line, fits in the width; otherwise every break point directly in it
//! breaks, and each inner group decides again for itself (E1). Width is
//! counted in characters, not bytes (E5): `∀` and `→` are one column each.
//!
//! Beyond Wadler's algebra there are the pieces a formatter of real code
//! needs: [`Doc::Fill`] (as many items a line as fit), [`Doc::Choice`] (the
//! first of several layouts whose first line fits: a body that opens on the
//! `:=` line, a call whose last argument hugs), trailing comments that wait
//! for the end of their line ([`Doc::LineSuffix`]), and text printed as
//! written but moved with its line ([`Doc::Verbatim`]). The printer never
//! leaves spaces at the end of a line: indentation is written only before
//! text.

use std::collections::BTreeMap;
use std::rc::Rc;

/// A layout document. Build groups with [`Doc::group`], which records
/// whether the group must break.
#[derive(Clone, Debug)]
pub enum Doc {
    Nil,
    /// Text without line breaks, and its width in characters.
    Text(String, usize),
    /// A space if its group prints flat, otherwise a line break.
    Line,
    /// Nothing if its group prints flat, otherwise a line break.
    SoftLine,
    /// Always a line break. A group holding one never prints flat (E3).
    HardLine,
    /// An empty line here, if this is the start of a line and the line
    /// before is not already empty: an author's kept blank line (E4).
    Blank,
    /// The contents, with line breaks indented this many more columns.
    Nest(usize, Box<Doc>),
    /// Printed flat if it fits, otherwise with every line in it broken. The
    /// flag says it holds a hard break, so it never prints flat.
    Group(Box<Doc>, bool),
    /// A group whose choice [`Doc::IfBroken`] can ask about.
    IdGroup(u32, Box<Doc>, bool),
    /// `broken` if the group with this id broke, otherwise `flat`: a body
    /// after a header that broke goes below it (S6).
    IfBroken {
        id: u32,
        broken: Box<Doc>,
        flat: Box<Doc>,
    },
    Concat(Vec<Doc>),
    /// A doc used in several places (the options of a [`Doc::Choice`]),
    /// built once; the flag is [`Doc::forces_break`]'s.
    Shared(Rc<Doc>, bool),
    /// Items separated by line breaks that break only where the next item
    /// doesn't fit on the line: a header's parameters (S7).
    Fill(Vec<Doc>),
    /// The contents printed flat whatever their width; as an option of a
    /// [`Doc::Choice`], it is taken only if it fits.
    Flat(Box<Doc>),
    /// The first option whose first line (and what follows it on that line)
    /// fits; the last if none does.
    Choice(Vec<Doc>),
    /// A trailing comment: printed, after one space, at the end of the line
    /// it is on, after any closing brackets and commas that end up on that
    /// line (S39). A group that would put anything else after it breaks.
    LineSuffix(String),
    /// Forces every group around it to break.
    BreakParent,
    /// Text printed as written, which may span lines. Lines after the first
    /// move right or left by as much as the line this starts on has moved:
    /// `src_indent` is the indentation of the source line it starts on.
    /// For constructs without a rule yet, and for text blocks (S33).
    Verbatim {
        text: String,
        src_indent: usize,
    },
    /// A `"""` text block (S33): printed as [`Doc::Verbatim`] is, but it
    /// doesn't break the groups around it: what follows its closing `"""`
    /// stays on that line.
    TextBlock {
        text: String,
        src_indent: usize,
    },
    /// Starts a new line here unless at the start of one: before an own-line
    /// comment. The printer records it when a line had to be started this
    /// way (S40: a comment no rule placed).
    LineStart,
}

impl Doc {
    pub fn text(text: impl Into<String>) -> Doc {
        let text = text.into();
        debug_assert!(!text.contains('\n'), "a text with a line break: {text:?}");
        let width = text.chars().count();
        Doc::Text(text, width)
    }

    pub fn nest(indent: usize, doc: Doc) -> Doc {
        Doc::Nest(indent, Box::new(doc))
    }

    pub fn group(doc: Doc) -> Doc {
        let hard = doc.forces_break();
        Doc::Group(Box::new(doc), hard)
    }

    pub fn shared(doc: Doc) -> Doc {
        match doc {
            Doc::Shared(..) | Doc::Nil | Doc::Text(..) => doc,
            _ => {
                let hard = doc.forces_break();
                Doc::Shared(Rc::new(doc), hard)
            }
        }
    }

    pub fn flat(doc: Doc) -> Doc {
        Doc::Flat(Box::new(doc))
    }

    pub fn concat(docs: impl IntoIterator<Item = Doc>) -> Doc {
        let docs: Vec<Doc> = docs
            .into_iter()
            .filter(|doc| !matches!(doc, Doc::Nil))
            .collect();
        match docs.len() {
            0 => Doc::Nil,
            1 => docs.into_iter().next().expect("one doc"),
            _ => Doc::Concat(docs),
        }
    }

    /// Whether printing this always breaks a line, so a group around it
    /// can't be flat.
    pub fn forces_break(&self) -> bool {
        match self {
            Doc::HardLine | Doc::BreakParent | Doc::LineStart => true,
            Doc::Verbatim { text, .. } => text.contains('\n'),
            Doc::Nil
            | Doc::Text(..)
            | Doc::Line
            | Doc::SoftLine
            | Doc::Blank
            | Doc::TextBlock { .. }
            | Doc::LineSuffix(_) => false,
            Doc::Group(_, hard) | Doc::IdGroup(_, _, hard) | Doc::Shared(_, hard) => *hard,
            Doc::IfBroken { broken, flat, .. } => broken.forces_break() && flat.forces_break(),
            Doc::Nest(_, doc) | Doc::Flat(doc) => doc.forces_break(),
            Doc::Concat(docs) | Doc::Fill(docs) => docs.iter().any(Doc::forces_break),
            Doc::Choice(options) => options.iter().all(Doc::forces_break),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mode {
    Flat,
    Break,
}

/// One step of the printer's work list.
#[derive(Clone, Copy)]
enum Cmd<'d> {
    Doc(usize, Mode, &'d Doc),
    /// Before the next item of a broken [`Doc::Fill`]: a space if the item
    /// fits on the line, otherwise a line break.
    FillSep(usize, &'d Doc),
}

/// What the printer noticed that the rules should have prevented.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Printed {
    pub text: String,
    /// Own-line comments that had to start a line no rule broke (S40).
    pub forced_comment_lines: usize,
    /// A trailing comment that would have been moved into a text block's or
    /// a verbatim construct's lines.
    pub stranded_comments: usize,
}

/// Prints `doc` in `width` columns.
pub fn print(doc: &Doc, width: usize) -> Printed {
    let mut printer = Printer {
        width,
        out: String::new(),
        column: 0,
        line_indent: 0,
        owed: None,
        at_line_start: true,
        suffixes: Vec::new(),
        modes: BTreeMap::new(),
        printed: Printed::default(),
    };
    printer.run(doc);
    printer.flush_suffixes();
    let mut printed = printer.printed;
    printed.text = printer.out;
    printed
}

struct Printer {
    width: usize,
    out: String,
    /// The column the next character goes in.
    column: usize,
    /// The indentation of the line being written.
    line_indent: usize,
    /// Indentation owed before the next text on a fresh line.
    owed: Option<usize>,
    /// Nothing but indentation written on this line yet.
    at_line_start: bool,
    suffixes: Vec<String>,
    /// How each [`Doc::IdGroup`] printed.
    modes: BTreeMap<u32, Mode>,
    printed: Printed,
}

impl Printer {
    fn run<'d>(&mut self, doc: &'d Doc) {
        let mut stack: Vec<Cmd<'d>> = vec![Cmd::Doc(0, Mode::Break, doc)];
        while let Some(cmd) = stack.pop() {
            let (indent, mode, doc) = match cmd {
                Cmd::Doc(indent, mode, doc) => (indent, mode, doc),
                Cmd::FillSep(indent, item) => {
                    let left = self.left().saturating_sub(1);
                    let item_mode = if self.suffixes.is_empty()
                        && fits_in(
                            &[Cmd::Doc(indent, Mode::Flat, item)],
                            &stack,
                            left,
                            &self.modes,
                            self.width,
                        ) {
                        self.write(" ", 1);
                        Mode::Flat
                    } else {
                        self.newline(indent);
                        Mode::Break
                    };
                    stack.push(Cmd::Doc(indent, item_mode, item));
                    continue;
                }
            };
            match doc {
                Doc::Nil | Doc::BreakParent => {}
                Doc::Text(text, width) => self.write(text, *width),
                Doc::Line | Doc::SoftLine if mode == Mode::Flat => {
                    if matches!(doc, Doc::Line) {
                        self.write(" ", 1);
                    }
                }
                Doc::Line | Doc::SoftLine | Doc::HardLine => self.newline(indent),
                Doc::Blank => {
                    if self.at_line_start && !self.out.is_empty() && !self.out.ends_with("\n\n") {
                        self.out.push('\n');
                    }
                }
                Doc::LineStart => {
                    if !self.at_line_start {
                        self.printed.forced_comment_lines += 1;
                        self.newline(indent);
                    }
                }
                Doc::Nest(more, inner) => stack.push(Cmd::Doc(indent + more, mode, inner)),
                Doc::Shared(inner, _) => stack.push(Cmd::Doc(indent, mode, inner)),
                Doc::Flat(inner) => stack.push(Cmd::Doc(indent, Mode::Flat, inner)),
                Doc::Group(inner, hard) | Doc::IdGroup(_, inner, hard) => {
                    let flat = mode == Mode::Flat
                        || (!hard
                            && fits_in(
                                &[Cmd::Doc(indent, Mode::Flat, inner)],
                                &stack,
                                self.left(),
                                &self.modes,
                                self.width,
                            ));
                    let mode = if flat { Mode::Flat } else { Mode::Break };
                    if let Doc::IdGroup(id, ..) = doc {
                        self.modes.insert(*id, mode);
                    }
                    stack.push(Cmd::Doc(indent, mode, inner));
                }
                Doc::IfBroken { id, broken, flat } => {
                    let doc = if self.modes.get(id) == Some(&Mode::Break) {
                        broken
                    } else {
                        flat
                    };
                    stack.push(Cmd::Doc(indent, mode, doc));
                }
                Doc::Concat(docs) => {
                    for doc in docs.iter().rev() {
                        stack.push(Cmd::Doc(indent, mode, doc));
                    }
                }
                Doc::Fill(items) => {
                    let Some((first, rest)) = items.split_first() else {
                        continue;
                    };
                    if mode == Mode::Flat {
                        for (k, item) in items.iter().enumerate().rev() {
                            stack.push(Cmd::Doc(indent, Mode::Flat, item));
                            if k > 0 {
                                stack.push(Cmd::Doc(indent, Mode::Flat, &Doc::Line));
                            }
                        }
                        continue;
                    }
                    for item in rest.iter().rev() {
                        stack.push(Cmd::FillSep(indent, item));
                    }
                    let first_mode = if fits_in(
                        &[Cmd::Doc(indent, Mode::Flat, first)],
                        &stack,
                        self.left(),
                        &self.modes,
                        self.width,
                    ) {
                        Mode::Flat
                    } else {
                        Mode::Break
                    };
                    stack.push(Cmd::Doc(indent, first_mode, first));
                }
                Doc::Choice(options) => {
                    let Some((last, others)) = options.split_last() else {
                        continue;
                    };
                    let chosen = if mode == Mode::Flat {
                        options.first().expect("an option")
                    } else {
                        others
                            .iter()
                            .find(|option| {
                                fits_in(
                                    &[Cmd::Doc(indent, Mode::Break, option)],
                                    &stack,
                                    self.left(),
                                    &self.modes,
                                    self.width,
                                )
                            })
                            .unwrap_or(last)
                    };
                    stack.push(Cmd::Doc(indent, mode, chosen));
                }
                Doc::LineSuffix(comment) => self.suffixes.push(comment.clone()),
                Doc::Verbatim { text, src_indent } | Doc::TextBlock { text, src_indent } => {
                    self.verbatim(text, *src_indent)
                }
            }
        }
    }

    /// Columns left on this line.
    fn left(&self) -> usize {
        let column = self.owed.unwrap_or(self.column);
        self.width.saturating_sub(column)
    }

    fn pay_indent(&mut self) {
        if let Some(n) = self.owed.take() {
            self.out.extend(std::iter::repeat_n(' ', n));
            self.column = n;
        }
    }

    fn write(&mut self, text: &str, width: usize) {
        if text.is_empty() {
            return;
        }
        self.pay_indent();
        self.out.push_str(text);
        self.column += width;
        self.at_line_start = false;
    }

    fn flush_suffixes(&mut self) {
        for comment in std::mem::take(&mut self.suffixes) {
            if !self.at_line_start {
                self.out.push(' ');
            } else {
                self.pay_indent();
            }
            self.out.push_str(&comment);
            self.at_line_start = false;
        }
    }

    fn newline(&mut self, indent: usize) {
        self.flush_suffixes();
        self.out.push('\n');
        self.column = 0;
        self.owed = Some(indent);
        self.line_indent = indent;
        self.at_line_start = true;
    }

    fn verbatim(&mut self, text: &str, src_indent: usize) {
        if text.is_empty() {
            return;
        }
        self.pay_indent();
        if text.contains('\n') && !self.suffixes.is_empty() {
            self.printed.stranded_comments += 1;
        }
        let shifted = shift_lines(text, self.line_indent as i64 - src_indent as i64);
        self.out.push_str(&shifted);
        match shifted.rfind('\n') {
            Some(k) => {
                let last = &shifted[k + 1..];
                self.column = last.chars().count();
                self.line_indent = last.len() - last.trim_start_matches(' ').len();
            }
            None => self.column += shifted.chars().count(),
        }
        self.at_line_start = false;
    }
}

/// Whether `next`, then the rest of the work list `rest` (from its top),
/// fits in `left` columns up to the first line break the work would make.
/// Groups are measured in the mode of what holds them unless they must
/// break, as Prettier's `fits` does: a group that won't fit flat breaks at
/// its first line, so measuring up to there is enough.
fn fits(next: &[Cmd<'_>], rest: &[Cmd<'_>], left: usize, modes: &BTreeMap<u32, Mode>) -> bool {
    fits_in(next, rest, left, modes, usize::MAX / 2)
}

/// [`fits`], where a text block's last line leaves `width` less its length.
fn fits_in(
    next: &[Cmd<'_>],
    rest: &[Cmd<'_>],
    left: usize,
    modes: &BTreeMap<u32, Mode>,
    width: usize,
) -> bool {
    let mut left = left as isize;
    let mut stack: Vec<(Mode, &Doc)> = next
        .iter()
        .rev()
        .filter_map(|cmd| match *cmd {
            Cmd::Doc(_, mode, doc) => Some((mode, doc)),
            Cmd::FillSep(..) => None,
        })
        .collect();
    let mut rest = rest.iter().rev();
    // A trailing comment is waiting for the end of the line: anything but
    // closing brackets and commas after it would move it.
    let mut suffix = false;
    loop {
        let Some((mode, doc)) = stack.pop() else {
            match rest.next() {
                Some(Cmd::Doc(_, mode, doc)) => {
                    stack.push((*mode, doc));
                    continue;
                }
                // The next fill item starts with a separator that may break.
                Some(Cmd::FillSep(..)) | None => return true,
            }
        };
        match doc {
            Doc::Nil | Doc::Blank => {}
            Doc::LineSuffix(_) => suffix = true,
            Doc::BreakParent => {
                if mode == Mode::Flat {
                    return false;
                }
            }
            Doc::Text(text, width) => {
                if suffix && !text.chars().all(|c| matches!(c, ')' | ']' | '}' | ',')) {
                    return false;
                }
                left -= *width as isize;
            }
            Doc::Line | Doc::SoftLine => {
                if mode == Mode::Break {
                    return true;
                }
                if suffix {
                    return false;
                }
                if matches!(doc, Doc::Line) {
                    left -= 1;
                }
            }
            Doc::HardLine | Doc::LineStart => return mode == Mode::Break,
            Doc::Nest(_, inner) => stack.push((mode, inner)),
            Doc::Shared(inner, _) => stack.push((mode, inner)),
            Doc::Flat(inner) => stack.push((Mode::Flat, inner)),
            Doc::Group(inner, hard) | Doc::IdGroup(_, inner, hard) => {
                if *hard && mode == Mode::Flat {
                    return false;
                }
                let mode = if *hard { Mode::Break } else { mode };
                stack.push((mode, inner));
            }
            // A group not printed yet is being measured flat.
            Doc::IfBroken { id, broken, flat } => {
                let doc = if modes.get(id) == Some(&Mode::Break) {
                    broken
                } else {
                    flat
                };
                stack.push((mode, doc));
            }
            Doc::Concat(docs) => stack.extend(docs.iter().rev().map(|d| (mode, d))),
            Doc::Fill(items) => {
                if mode == Mode::Break {
                    // Only the first item is sure to be on this line; the
                    // separator after it may break.
                    return items.first().is_none_or(|first| fits_flat(first, left));
                } else {
                    for (k, item) in items.iter().enumerate().rev() {
                        stack.push((mode, item));
                        if k > 0 {
                            stack.push((mode, &Doc::Line));
                        }
                    }
                }
            }
            Doc::Choice(options) => {
                let option = if mode == Mode::Flat {
                    options.first()
                } else {
                    options.last()
                };
                if let Some(option) = option {
                    stack.push((mode, option));
                }
            }
            Doc::TextBlock { text, .. } => {
                let (first, last) = match (text.split_once('\n'), text.rsplit_once('\n')) {
                    (Some((first, _)), Some((_, last))) => (first, last),
                    _ => (text.as_str(), ""),
                };
                if suffix || first.chars().count() as isize > left {
                    return false;
                }
                left = width as isize - last.chars().count() as isize;
            }
            Doc::Verbatim { text, .. } => match text.split_once('\n') {
                _ if suffix => return false,
                Some((first, _)) => {
                    left -= first.chars().count() as isize;
                    return mode == Mode::Break && left >= 0;
                }
                None => left -= text.chars().count() as isize,
            },
        }
        if left < 0 {
            return false;
        }
    }
}

/// Whether `doc`, printed flat, fits in `left` columns.
fn fits_flat(doc: &Doc, left: isize) -> bool {
    left >= 0
        && fits(
            &[Cmd::Doc(0, Mode::Flat, doc)],
            &[],
            left as usize,
            &BTreeMap::new(),
        )
}

/// `text` with every line after the first moved right by `shift` columns
/// (left if negative), as far as the least indented allows. Lines of only
/// spaces stay as they are.
pub(crate) fn shift_lines(text: &str, shift: i64) -> String {
    if shift == 0 || !text.contains('\n') {
        return text.to_string();
    }
    let blank = |line: &str| line.trim_matches([' ', '\r']).is_empty();
    let lead = |line: &str| line.len() - line.trim_start_matches(' ').len();
    let least = text
        .split('\n')
        .skip(1)
        .filter(|line| !blank(line))
        .map(lead)
        .min()
        .unwrap_or(0);
    let shift = shift.max(-(least as i64));
    let mut out = String::with_capacity(text.len());
    for (k, line) in text.split('\n').enumerate() {
        if k > 0 {
            out.push('\n');
            if !blank(line) {
                if shift >= 0 {
                    out.extend(std::iter::repeat_n(' ', shift as usize));
                } else {
                    out.push_str(&line[(-shift) as usize..]);
                    continue;
                }
            }
        }
        out.push_str(line);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t(s: &str) -> Doc {
        Doc::text(s)
    }

    /// `[a, b, …]` as a comma bracket (S31).
    fn list(items: &[&str]) -> Doc {
        let mut inner = Vec::new();
        for (k, item) in items.iter().enumerate() {
            inner.push(if k == 0 { Doc::SoftLine } else { Doc::Line });
            inner.push(t(item));
            if k + 1 < items.len() {
                inner.push(t(","));
            }
        }
        Doc::group(Doc::concat([
            t("["),
            Doc::nest(2, Doc::concat(inner)),
            Doc::SoftLine,
            t("]"),
        ]))
    }

    #[test]
    fn a_group_prints_flat_when_it_fits_and_breaks_every_line_when_not() {
        assert_eq!(print(&list(&["a", "b"]), 120).text, "[a, b]");
        assert_eq!(print(&list(&["a", "b"]), 5).text, "[\n  a,\n  b\n]");
    }

    #[test]
    fn what_follows_a_group_on_its_line_counts() {
        // `[a, b]` is 6 wide and fits in 7, but not with `:=` after it.
        let doc = Doc::concat([list(&["a", "b"]), t(" :=")]);
        assert_eq!(print(&doc, 9).text, "[a, b] :=");
        assert_eq!(print(&doc, 8).text, "[\n  a,\n  b\n] :=");
    }

    #[test]
    fn width_is_counted_in_characters() {
        let doc = Doc::group(Doc::concat([t("∀∀∀"), Doc::Line, t("→→")]));
        assert_eq!(print(&doc, 6).text, "∀∀∀ →→");
        assert_eq!(print(&doc, 5).text, "∀∀∀\n→→");
    }

    #[test]
    fn a_fill_breaks_only_before_an_item_that_does_not_fit() {
        let doc = Doc::Fill(vec![t("aaa"), t("bbb"), t("ccc"), t("d")]);
        assert_eq!(print(&doc, 8).text, "aaa bbb\nccc d");
    }

    #[test]
    fn a_choice_takes_the_first_option_whose_first_line_fits() {
        let hug = Doc::concat([
            t("f a (x =>"),
            Doc::nest(2, Doc::concat([Doc::HardLine, t("body)")])),
        ]);
        let broken = Doc::concat([
            t("f"),
            Doc::nest(
                2,
                Doc::concat([Doc::HardLine, t("a"), Doc::HardLine, t("(x => body)")]),
            ),
        ]);
        let flat = Doc::flat(t("f a (x => body)"));
        let doc = Doc::Choice(vec![flat, hug, broken]);
        assert_eq!(print(&doc, 20).text, "f a (x => body)");
        assert_eq!(print(&doc, 10).text, "f a (x =>\n  body)");
        assert_eq!(print(&doc, 5).text, "f\n  a\n  (x => body)");
    }

    #[test]
    fn a_trailing_comment_waits_for_the_end_of_its_line() {
        let doc = Doc::concat([
            t("x"),
            Doc::LineSuffix("-- c".into()),
            t(")"),
            Doc::HardLine,
            t("y"),
        ]);
        assert_eq!(print(&doc, 120).text, "x) -- c\ny");
        // A group that would put more code after the comment breaks.
        let doc = Doc::group(Doc::concat([
            t("f a"),
            Doc::LineSuffix("-- c".into()),
            Doc::Line,
            t("b"),
        ]));
        assert_eq!(print(&doc, 120).text, "f a -- c\nb");
    }

    #[test]
    fn verbatim_lines_move_with_their_line_and_blank_lines_have_no_spaces() {
        let doc = Doc::nest(
            4,
            Doc::concat([
                t("a"),
                Doc::HardLine,
                Doc::Blank,
                Doc::Verbatim {
                    text: "b\n    c".into(),
                    src_indent: 2,
                },
            ]),
        );
        assert_eq!(print(&doc, 120).text, "a\n\n    b\n      c");
    }

    #[test]
    fn a_comment_that_must_start_a_line_is_counted() {
        let doc = Doc::concat([t("f"), Doc::LineStart, t("-- c"), Doc::HardLine, t("x")]);
        let printed = print(&doc, 120);
        assert_eq!(printed.text, "f\n-- c\nx");
        assert_eq!(printed.forced_comment_lines, 1);
    }
}
