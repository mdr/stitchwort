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
//! for the end of their line ([`Doc::LineSuffix`]), and a text block printed
//! as written but moved with its line ([`Doc::TextBlock`]). The printer never
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
    /// The contents, with line breaks indented to the column this starts
    /// at: the parts of `(let x := e; body)` line up inside the bracket.
    Align(Box<Doc>),
    /// Like [`Doc::Align`], except that where this starts a line the
    /// breaks go 2 columns in rather than to the line's own column: a line
    /// ending in `;` followed by a line at its block's column ends the
    /// block instead of continuing the sequence.
    AlignInset(Box<Doc>),
    /// An element a comment moves to a line of its own (a trailing comment
    /// before it, or own-line comments): its continuation lines are
    /// indented from where its first line lands, not from the construct
    /// that holds it, since a line left of that first line would end the
    /// block the element opens there (`a` then `→ b` in column 4 after `a`
    /// in column 8).
    Displaced(Box<Doc>),
    /// Printed flat if it fits, otherwise with every line in it broken. The
    /// flag says it holds a hard break, so it never prints flat.
    Group(Box<Doc>, bool),
    /// A group that prints flat only if its line then ends within this many
    /// columns, however wide the page is: a type declaration's
    /// constructors or fields (S14, S15).
    NarrowGroup(usize, Box<Doc>, bool),
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
    /// A line below at `+2` holding the doc, printed as `nest(2, [HardLine,
    /// doc])`; as an option of a [`Doc::Choice`] it is taken only if the doc
    /// fits flat on that one line (D3571).
    OneLineBelow(Box<Doc>),
    /// A trailing comment: printed, after one space, at the end of the line
    /// it is on, after any closing brackets and commas that end up on that
    /// line (S39). A group whose flat layout has a line break after it
    /// breaks; code that still follows it on the line starts the next line
    /// instead, a comment break (S40).
    LineSuffix(String),
    /// Forces every group around it to break.
    BreakParent,
    /// A `"""` text block (S33), printed as written: its lines after the
    /// first move right or left by as much as the line it starts on has
    /// moved (`src_indent` is the indentation of the source line it starts
    /// on). It doesn't break the groups around it: what follows its closing
    /// `"""` stays on that line.
    TextBlock {
        text: String,
        src_indent: usize,
    },
    /// Starts a new line here unless at the start of one: before an own-line
    /// comment. A line started this way is a comment break (S40), and the
    /// lines up to the next code, that code's included, are indented as
    /// continuation lines.
    LineStart,
    /// Starts a new line at the indentation in force, or at the start of a
    /// line moves that line there: own-line comments before a closing
    /// bracket, at its items' indentation (S40).
    LineStartHere,
    /// Notes the indentation of the line this is on, for the
    /// [`Doc::CloserLine`] with the same key: before an opening bracket.
    Mark(usize),
    /// Starts a new line for a closing bracket that comments put on a line
    /// of its own: at the indentation in force, unless a line written since
    /// the [`Doc::Mark`] with the same key is at or left of that, which
    /// would make the bracket a line of the block that line starts; then at
    /// the indentation of the marked line (S40). At the start of a line
    /// with no trailing comment waiting (a break before it already ended
    /// the line) it moves that line there instead.
    CloserLine(usize),
}

impl Doc {
    pub fn text(text: impl Into<String>) -> Doc {
        let text = text.into();
        debug_assert!(!text.contains('\n'), "a text with a line break: {text:?}");
        let width = text.chars().count();
        Doc::Text(text, width)
    }

    pub fn displaced(doc: Doc) -> Doc {
        Doc::Displaced(Box::new(doc))
    }

    pub fn nest(indent: usize, doc: Doc) -> Doc {
        Doc::Nest(indent, Box::new(doc))
    }

    pub fn align(doc: Doc) -> Doc {
        Doc::Align(Box::new(doc))
    }

    pub fn align_inset(doc: Doc) -> Doc {
        Doc::AlignInset(Box::new(doc))
    }

    pub fn group(doc: Doc) -> Doc {
        let hard = doc.forces_break();
        Doc::Group(Box::new(doc), hard)
    }

    pub fn narrow_group(max: usize, doc: Doc) -> Doc {
        let hard = doc.forces_break();
        Doc::NarrowGroup(max, Box::new(doc), hard)
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
            Doc::HardLine
            | Doc::BreakParent
            | Doc::LineStart
            | Doc::LineStartHere
            | Doc::CloserLine(_) => true,
            Doc::Nil
            | Doc::Text(..)
            | Doc::Line
            | Doc::SoftLine
            | Doc::Blank
            | Doc::TextBlock { .. }
            | Doc::Mark(_)
            | Doc::LineSuffix(_) => false,
            Doc::Group(_, hard) | Doc::IdGroup(_, _, hard) | Doc::Shared(_, hard) => *hard,
            Doc::NarrowGroup(_, _, hard) => *hard,
            Doc::IfBroken { broken, flat, .. } => broken.forces_break() && flat.forces_break(),
            Doc::OneLineBelow(_) => true,
            Doc::Nest(_, doc)
            | Doc::Align(doc)
            | Doc::AlignInset(doc)
            | Doc::Displaced(doc)
            | Doc::Flat(doc) => doc.forces_break(),
            Doc::Concat(docs) | Doc::Fill(docs) => docs.iter().any(Doc::forces_break),
            Doc::Choice(options) => options.iter().all(Doc::forces_break),
        }
    }
}

/// The document in a plain line form for `stitchwort dev doc`: one node a
/// line in pre-order, the node's tag, its arguments, then its children as
/// the lines that follow. A text is the rest of its line, with backslash,
/// line feed and carriage return written `\\`, `\n` and `\r`. [`Doc::Shared`]
/// is written once, as `Shared ID` and the doc, and again as `Ref ID` where
/// it is used again: a doc used in several options of nested choices would
/// be exponentially long written out in full.
pub fn dump(doc: &Doc) -> String {
    let mut out = String::new();
    dump_into(doc, &mut out, &mut BTreeMap::new());
    out
}

/// The number of nodes of the document written out in full, every use of a
/// shared doc counted again (at most `u64::MAX`): how large the
/// document is for a printer that doesn't keep what is shared.
pub fn expanded_size(doc: &Doc) -> u64 {
    fn size(doc: &Doc, seen: &mut BTreeMap<*const Doc, u64>) -> u64 {
        let children: u64 = match doc {
            Doc::Nest(_, inner)
            | Doc::Align(inner)
            | Doc::AlignInset(inner)
            | Doc::Displaced(inner)
            | Doc::Group(inner, _)
            | Doc::NarrowGroup(_, inner, _)
            | Doc::IdGroup(_, inner, _)
            | Doc::Flat(inner)
            | Doc::OneLineBelow(inner) => size(inner, seen),
            Doc::IfBroken { broken, flat, .. } => {
                size(broken, seen).saturating_add(size(flat, seen))
            }
            Doc::Concat(docs) | Doc::Fill(docs) | Doc::Choice(docs) => docs
                .iter()
                .fold(0, |sum: u64, doc| sum.saturating_add(size(doc, seen))),
            Doc::Shared(inner, _) => {
                let key = Rc::as_ptr(inner);
                if let Some(known) = seen.get(&key) {
                    return *known;
                }
                let total = size(inner, seen);
                seen.insert(key, total);
                return total;
            }
            _ => 0,
        };
        children.saturating_add(1)
    }
    size(doc, &mut BTreeMap::new())
}

/// A text for a dump line: backslash, line feed and carriage return escaped.
pub fn dump_escape(text: &str) -> String {
    let mut out = String::new();
    for c in text.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            c => out.push(c),
        }
    }
    out
}

fn dump_into(doc: &Doc, out: &mut String, shared: &mut BTreeMap<*const Doc, usize>) {
    let one = |out: &mut String, shared: &mut BTreeMap<*const Doc, usize>, tag: &str, doc: &Doc| {
        out.push_str(tag);
        out.push('\n');
        dump_into(doc, out, shared);
    };
    let many =
        |out: &mut String, shared: &mut BTreeMap<*const Doc, usize>, tag: &str, docs: &[Doc]| {
            out.push_str(&format!("{tag} {}\n", docs.len()));
            for doc in docs {
                dump_into(doc, out, shared);
            }
        };
    match doc {
        Doc::Nil => out.push_str("Nil\n"),
        Doc::Text(text, _) => out.push_str(&format!("Text {}\n", dump_escape(text))),
        Doc::Line => out.push_str("Line\n"),
        Doc::SoftLine => out.push_str("SoftLine\n"),
        Doc::HardLine => out.push_str("HardLine\n"),
        Doc::Blank => out.push_str("Blank\n"),
        Doc::Nest(indent, inner) => {
            out.push_str(&format!("Nest {indent}\n"));
            dump_into(inner, out, shared);
        }
        Doc::Align(inner) => one(out, shared, "Align", inner),
        Doc::AlignInset(inner) => one(out, shared, "AlignInset", inner),
        Doc::Displaced(inner) => one(out, shared, "Displaced", inner),
        Doc::Group(inner, _) => one(out, shared, "Group", inner),
        Doc::NarrowGroup(max, inner, _) => {
            out.push_str(&format!("NarrowGroup {max}\n"));
            dump_into(inner, out, shared);
        }
        Doc::IdGroup(id, inner, _) => {
            out.push_str(&format!("IdGroup {id}\n"));
            dump_into(inner, out, shared);
        }
        Doc::IfBroken { id, broken, flat } => {
            out.push_str(&format!("IfBroken {id}\n"));
            dump_into(broken, out, shared);
            dump_into(flat, out, shared);
        }
        Doc::Concat(docs) => many(out, shared, "Concat", docs),
        Doc::Shared(inner, _) => {
            let key = Rc::as_ptr(inner);
            if let Some(id) = shared.get(&key) {
                out.push_str(&format!("Ref {id}\n"));
            } else {
                let id = shared.len() + 1;
                shared.insert(key, id);
                out.push_str(&format!("Shared {id}\n"));
                dump_into(inner, out, shared);
            }
        }
        Doc::Fill(items) => many(out, shared, "Fill", items),
        Doc::Flat(inner) => one(out, shared, "Flat", inner),
        Doc::Choice(options) => many(out, shared, "Choice", options),
        Doc::OneLineBelow(inner) => one(out, shared, "OneLineBelow", inner),
        Doc::LineSuffix(text) => out.push_str(&format!("LineSuffix {}\n", dump_escape(text))),
        Doc::BreakParent => out.push_str("BreakParent\n"),
        Doc::TextBlock { text, src_indent } => {
            out.push_str(&format!("TextBlock {src_indent} {}\n", dump_escape(text)));
        }
        Doc::LineStart => out.push_str("LineStart\n"),
        Doc::LineStartHere => out.push_str("LineStartHere\n"),
        Doc::Mark(key) => out.push_str(&format!("Mark {key}\n")),
        Doc::CloserLine(key) => out.push_str(&format!("CloserLine {key}\n")),
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

/// A printed document.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Printed {
    pub text: String,
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
        held_spaces: 0,
        comment_floor: None,
        modes: BTreeMap::new(),
        marks: BTreeMap::new(),
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
    /// Spaces after a waiting trailing comment, written only if a closing
    /// bracket or comma follows on the line, not code (which goes below).
    held_spaces: usize,
    /// After an own-line comment that had to start its line: the least
    /// indentation of the lines up to the next code (S40).
    comment_floor: Option<usize>,
    /// How each [`Doc::IdGroup`] printed.
    modes: BTreeMap<u32, Mode>,
    /// For each [`Doc::Mark`] whose [`Doc::CloserLine`] hasn't come: the
    /// marked line's indentation, and the least of the lines since.
    marks: BTreeMap<usize, (usize, usize)>,
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
                        && self.fits_here(&[Cmd::Doc(indent, Mode::Flat, item)], &stack, left)
                    {
                        self.write(" ", 1, indent);
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
                Doc::Text(text, width) => self.write(text, *width, indent),
                Doc::Line | Doc::SoftLine if mode == Mode::Flat => {
                    if matches!(doc, Doc::Line) {
                        self.write(" ", 1, indent);
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
                        let floor = self.continuation(indent);
                        self.newline(floor);
                        self.comment_floor = Some(floor);
                    }
                }
                Doc::Mark(key) => {
                    self.marks.insert(*key, (self.line_indent, usize::MAX));
                }
                Doc::CloserLine(key) => {
                    let column = match self.marks.remove(key) {
                        Some((marked, least)) if least <= indent => marked.min(indent),
                        _ => indent,
                    };
                    self.comment_floor = None;
                    if self.at_line_start && self.suffixes.is_empty() {
                        // A break before the closer already ended the line
                        // (and wrote its waiting comment): move this line,
                        // as a second break would leave an empty one.
                        self.owed = Some(column);
                        self.line_indent = column;
                        for (_, least) in self.marks.values_mut() {
                            *least = (*least).min(column);
                        }
                    } else {
                        self.newline(column);
                    }
                }
                Doc::LineStartHere => {
                    if self.at_line_start {
                        self.owed = Some(indent);
                        self.line_indent = indent;
                    } else {
                        self.newline(indent);
                    }
                }
                Doc::Nest(more, inner) => stack.push(Cmd::Doc(indent + more, mode, inner)),
                Doc::OneLineBelow(inner) => {
                    stack.push(Cmd::Doc(indent + 2, mode, inner));
                    stack.push(Cmd::Doc(indent + 2, mode, &Doc::HardLine));
                }
                Doc::Align(inner) => {
                    let column = if self.at_line_start {
                        indent
                    } else {
                        self.column
                    };
                    stack.push(Cmd::Doc(column, mode, inner));
                }
                Doc::AlignInset(inner) => {
                    let column = if self.at_line_start {
                        indent + 2
                    } else {
                        self.column
                    };
                    stack.push(Cmd::Doc(column, mode, inner));
                }
                Doc::Displaced(inner) => {
                    let column = if self.at_line_start {
                        indent.max(self.owed.unwrap_or(indent))
                    } else if !self.suffixes.is_empty() {
                        // A comment waiting on this line ends it here, at
                        // the element's own line, before the docs inside
                        // (a block's first statement, nested deeper) decide
                        // where a comment break would put their first line.
                        let column = self.continuation(indent);
                        self.newline(column);
                        column
                    } else {
                        indent
                    };
                    stack.push(Cmd::Doc(column, mode, inner));
                }
                Doc::Shared(inner, _) => stack.push(Cmd::Doc(indent, mode, inner)),
                Doc::Flat(inner) => stack.push(Cmd::Doc(indent, Mode::Flat, inner)),
                Doc::Group(inner, hard) | Doc::IdGroup(_, inner, hard) => {
                    let flat = mode == Mode::Flat
                        || (!hard
                            && self.fits_here(
                                &[Cmd::Doc(indent, Mode::Flat, inner)],
                                &stack,
                                self.left(),
                            ));
                    let mode = if flat { Mode::Flat } else { Mode::Break };
                    if let Doc::IdGroup(id, ..) = doc {
                        self.modes.insert(*id, mode);
                    }
                    stack.push(Cmd::Doc(indent, mode, inner));
                }
                Doc::NarrowGroup(max, inner, hard) => {
                    let column = self.owed.unwrap_or(self.column);
                    let flat = mode == Mode::Flat
                        || (!hard
                            && self.fits_here(
                                &[Cmd::Doc(indent, Mode::Flat, inner)],
                                &stack,
                                self.left().min(max.saturating_sub(column)),
                            ));
                    let mode = if flat { Mode::Flat } else { Mode::Break };
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
                    let first_mode = if self.fits_here(
                        &[Cmd::Doc(indent, Mode::Flat, first)],
                        &stack,
                        self.left(),
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
                                if let Doc::OneLineBelow(inner) = option {
                                    let below = Measure {
                                        // The option prints on a line of its
                                        // own below, but an IfBroken in it
                                        // must still see the groups already
                                        // printed (SW-3913).
                                        modes: &self.modes,
                                        width: self.width,
                                        suffix: false,
                                        line_indent: indent + 2,
                                        flat_break: false,
                                        held: 0,
                                    };
                                    return fits_flat(
                                        inner,
                                        indent + 2,
                                        self.width as isize - indent as isize - 2,
                                        &below,
                                    );
                                }
                                self.fits_here(
                                    &[Cmd::Doc(indent, Mode::Break, option)],
                                    &stack,
                                    self.left(),
                                )
                            })
                            .unwrap_or(last)
                    };
                    stack.push(Cmd::Doc(indent, mode, chosen));
                }
                Doc::LineSuffix(comment) => self.suffixes.push(comment.clone()),
                Doc::TextBlock { text, src_indent } => self.verbatim(text, *src_indent, indent),
            }
        }
    }

    /// [`fits_in`] from where the printer is: on its line, with any
    /// trailing comment waiting there.
    fn fits_here(&self, next: &[Cmd<'_>], rest: &[Cmd<'_>], left: usize) -> bool {
        let at = Measure {
            modes: &self.modes,
            width: self.width,
            suffix: !self.suffixes.is_empty(),
            line_indent: self.line_indent,
            flat_break: false,
            held: self.held_spaces,
        };
        fits_in(next, rest, left, &at)
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

    /// The indentation of a comment break in a construct indented `indent`:
    /// deeper than the line being broken, so what follows continues it.
    fn continuation(&self, indent: usize) -> usize {
        indent.max(self.line_indent + 2)
    }

    /// Before code text: a trailing comment waiting on this line ends it
    /// first (a comment break), unless the text is closing brackets and
    /// commas, which stay before the comment (S39). Returns false for
    /// spaces held back until that is known.
    fn before_code(&mut self, text: &str, indent: usize) -> bool {
        if self.suffixes.is_empty() || self.at_line_start {
            return true;
        }
        if text.chars().all(|c| c == ' ') {
            self.held_spaces += text.len();
            return false;
        }
        if text.chars().all(|c| matches!(c, ')' | ']' | '}' | ',')) {
            self.pay_indent();
            self.out.extend(std::iter::repeat_n(' ', self.held_spaces));
            self.column += std::mem::take(&mut self.held_spaces);
        } else {
            let floor = self.continuation(indent);
            self.newline(floor);
        }
        true
    }

    fn write(&mut self, text: &str, width: usize, indent: usize) {
        if text.is_empty() || !self.before_code(text, indent) {
            return;
        }
        if !text.starts_with("--") {
            self.comment_floor = None;
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
        let indent = self.comment_floor.map_or(indent, |floor| indent.max(floor));
        self.held_spaces = 0;
        // A space the layout put before a break it didn't plan (a comment
        // break) would end the line.
        let end = self.out.trim_end_matches(' ').len();
        self.out.truncate(end);
        self.flush_suffixes();
        self.out.push('\n');
        self.column = 0;
        self.owed = Some(indent);
        self.line_indent = indent;
        self.at_line_start = true;
        for (_, least) in self.marks.values_mut() {
            *least = (*least).min(indent);
        }
    }

    fn verbatim(&mut self, text: &str, src_indent: usize, indent: usize) {
        if text.is_empty() || !self.before_code(text, indent) {
            return;
        }
        self.comment_floor = None;
        self.pay_indent();
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

/// Where a measure starts.
struct Measure<'m> {
    /// How each [`Doc::IdGroup`] printed.
    modes: &'m BTreeMap<u32, Mode>,
    /// The page's width: a text block's last line leaves this less its
    /// length.
    width: usize,
    /// A trailing comment is already waiting on the line.
    suffix: bool,
    /// The indentation of the line being measured.
    line_indent: usize,
    /// A flat line break after the waiting comment has been measured: code
    /// that follows would start a line.
    flat_break: bool,
    /// Spaces already held back after it.
    held: usize,
}

/// Whether `next`, then the rest of the work list `rest` (from its top),
/// fits in `left` columns up to the first line break the work would make.
/// Groups are measured in the mode of what holds them unless they must
/// break, as Prettier's `fits` does: a group that won't fit flat breaks at
/// its first line, so measuring up to there is enough.
fn fits_in(next: &[Cmd<'_>], rest: &[Cmd<'_>], left: usize, at: &Measure<'_>) -> bool {
    let (modes, width) = (at.modes, at.width);
    let mut left = left as isize;
    let mut stack: Vec<(usize, Mode, &Doc)> = next
        .iter()
        .rev()
        .filter_map(|cmd| match *cmd {
            Cmd::Doc(indent, mode, doc) => Some((indent, mode, doc)),
            Cmd::FillSep(..) => None,
        })
        .collect();
    let mut rest = rest.iter().rev();
    // A trailing comment is waiting for the end of the line: a line break
    // in a group's flat layout would put code after it, and code with no
    // line break before it starts a new line (a comment break), from where
    // the measure goes on. A flat line break before only closers and
    // commas is no break: they join the comment's line, so a comment on
    // the last item of a bracket fits as one after its closer does
    // (rule N, crate::tidy).
    let mut suffix = at.suffix;
    let mut flat_break = at.flat_break;
    // The indentation of the line being measured: a comment break starts
    // a new line, which the next comment break is deeper than.
    let mut line_indent = at.line_indent;
    // Spaces held after the waiting comment, which the printer writes if a
    // closer follows and drops at a comment break.
    let mut held = at.held;
    loop {
        let Some((indent, mode, doc)) = stack.pop() else {
            match rest.next() {
                Some(Cmd::Doc(indent, mode, doc)) => {
                    stack.push((*indent, *mode, doc));
                    continue;
                }
                // The next fill item starts with a separator that may break.
                Some(Cmd::FillSep(..)) | None => return true,
            }
        };
        match doc {
            Doc::Nil | Doc::Blank => {}
            Doc::LineSuffix(_) => {
                suffix = true;
                flat_break = false;
            }
            Doc::BreakParent => {
                if mode == Mode::Flat {
                    return false;
                }
            }
            Doc::Text(text, width) => {
                if suffix {
                    if text.chars().all(|c| c == ' ') {
                        // Held back: written only before a closer.
                        held += *width;
                        continue;
                    }
                    if text.chars().all(|c| matches!(c, ')' | ']' | '}' | ',')) {
                        left -= std::mem::take(&mut held) as isize;
                    } else {
                        if flat_break {
                            return false;
                        }
                        suffix = false;
                        held = 0;
                        line_indent = indent.max(line_indent + 2);
                        left = at.width as isize - line_indent as isize;
                    }
                }
                left -= *width as isize;
            }
            Doc::Line | Doc::SoftLine => {
                if mode == Mode::Break {
                    return true;
                }
                if suffix {
                    flat_break = true;
                    continue;
                }
                if matches!(doc, Doc::Line) {
                    left -= 1;
                }
            }
            Doc::HardLine | Doc::LineStart | Doc::LineStartHere | Doc::CloserLine(_) => {
                return mode == Mode::Break;
            }
            Doc::Mark(_) => {}
            Doc::Nest(more, inner) => stack.push((indent + more, mode, inner)),
            Doc::Align(inner) | Doc::AlignInset(inner) | Doc::Displaced(inner) => {
                stack.push((indent, mode, inner))
            }
            Doc::Shared(inner, _) => stack.push((indent, mode, inner)),
            Doc::Flat(inner) => stack.push((indent, Mode::Flat, inner)),
            Doc::OneLineBelow(_) => return true,
            Doc::Group(inner, hard)
            | Doc::IdGroup(_, inner, hard)
            | Doc::NarrowGroup(_, inner, hard) => {
                if *hard && mode == Mode::Flat {
                    return false;
                }
                let mode = if *hard { Mode::Break } else { mode };
                stack.push((indent, mode, inner));
            }
            // A group not printed yet is being measured flat.
            Doc::IfBroken { id, broken, flat } => {
                let doc = if modes.get(id) == Some(&Mode::Break) {
                    broken
                } else {
                    flat
                };
                stack.push((indent, mode, doc));
            }
            Doc::Concat(docs) => stack.extend(docs.iter().rev().map(|d| (indent, mode, d))),
            Doc::Fill(items) => {
                if mode == Mode::Break {
                    // Only the first item is sure to be on this line; the
                    // separator after it may break.
                    let here = Measure {
                        // The item may hold an IfBroken, which must see the
                        // groups already printed (SW-3913).
                        modes,
                        width,
                        suffix,
                        line_indent,
                        flat_break,
                        held,
                    };
                    return items
                        .first()
                        .is_none_or(|first| fits_flat(first, indent, left, &here));
                } else {
                    for (k, item) in items.iter().enumerate().rev() {
                        stack.push((indent, mode, item));
                        if k > 0 {
                            stack.push((indent, mode, &Doc::Line));
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
                    stack.push((indent, mode, option));
                }
            }
            Doc::TextBlock { text, .. } => {
                if suffix && flat_break {
                    return false;
                }
                if suffix {
                    suffix = false;
                    line_indent = indent.max(line_indent + 2);
                    left = at.width as isize - line_indent as isize;
                }
                let (first, last) = match (text.split_once('\n'), text.rsplit_once('\n')) {
                    (Some((first, _)), Some((_, last))) => (first, last),
                    _ => (text.as_str(), ""),
                };
                left -= first.chars().count() as isize;
                if text.contains('\n') {
                    if left < 0 {
                        return false;
                    }
                    left = width as isize - last.chars().count() as isize;
                }
            }
        }
        if left < 0 {
            return false;
        }
    }
}

/// Whether `doc`, printed flat at indentation `indent`, fits in `left`
/// columns, measured from `at`.
fn fits_flat(doc: &Doc, indent: usize, left: isize, at: &Measure<'_>) -> bool {
    left >= 0 && fits_in(&[Cmd::Doc(indent, Mode::Flat, doc)], &[], left as usize, at)
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
    fn text_block_lines_move_with_their_line_and_blank_lines_have_no_spaces() {
        let doc = Doc::nest(
            4,
            Doc::concat([
                t("a"),
                Doc::HardLine,
                Doc::Blank,
                Doc::TextBlock {
                    text: "b\n    c".into(),
                    src_indent: 2,
                },
            ]),
        );
        assert_eq!(print(&doc, 120).text, "a\n\n    b\n      c");
    }

    #[test]
    fn an_own_line_comment_no_layout_broke_for_starts_a_continuation_line() {
        // S40: the comment and the code after it are deeper than the line
        // they break, here at the floor of 2 more.
        let doc = Doc::concat([t("f"), Doc::LineStart, t("-- c"), Doc::HardLine, t("x")]);
        assert_eq!(print(&doc, 120).text, "f\n  -- c\n  x");
        // Past that code, lines are indented as the layout says again.
        let doc = Doc::concat([doc, Doc::HardLine, t("y")]);
        assert_eq!(print(&doc, 120).text, "f\n  -- c\n  x\ny");
        // Where a line starts there anyway, nothing changes.
        let doc = Doc::concat([
            t("f"),
            Doc::HardLine,
            Doc::LineStart,
            t("-- c"),
            Doc::HardLine,
            t("x"),
        ]);
        assert_eq!(print(&doc, 120).text, "f\n-- c\nx");
    }

    #[test]
    fn code_after_a_trailing_comment_starts_a_continuation_line() {
        // S40: no layout here breaks after the comment, so the code goes
        // below at 2 more, without the space that was to come before it;
        // a closing bracket still stays before the comment (S39).
        let doc = Doc::flat(Doc::concat([
            t("(a +"),
            Doc::LineSuffix("-- c".into()),
            Doc::Line,
            t("b"),
            t(")"),
        ]));
        assert_eq!(print(&doc, 120).text, "(a + -- c\n  b)");
        let doc = Doc::nest(
            6,
            Doc::concat([t("x"), Doc::LineSuffix("-- c".into()), t(" "), t("y")]),
        );
        assert_eq!(print(&doc, 120).text, "x -- c\n      y");
    }

    #[test]
    fn a_comment_break_at_a_displaced_element_starts_its_own_line() {
        // SW-3728: the element's first line keeps the element's indentation
        // even when a part inside it (`f a`, a call's arguments at 4) would
        // break deeper, so the element's next line isn't left of its first.
        let first = Doc::nest(4, t("f a"));
        let block = Doc::displaced(Doc::concat([first, Doc::HardLine, t("b")]));
        let doc = Doc::nest(
            2,
            Doc::concat([t("=>"), Doc::LineSuffix("-- c".into()), t(" "), block]),
        );
        assert_eq!(print(&doc, 120).text, "=> -- c\n  f a\n  b");
    }

    #[test]
    fn a_group_after_a_waiting_comment_is_measured_with_it() {
        // SW-3444: the comment already waits when the group is measured, so
        // the group can't print flat; its line breaks, at its own indentation.
        let doc = Doc::concat([
            t("f a"),
            Doc::LineSuffix("-- c".into()),
            Doc::group(Doc::concat([Doc::Line, t("b")])),
        ]);
        assert_eq!(print(&doc, 120).text, "f a -- c\nb");
        // Code with no line break before it starts a new line anyway, so an
        // option that puts it there is measured from that line.
        let doc = Doc::concat([
            t(":="),
            Doc::LineSuffix("-- c".into()),
            Doc::Choice(vec![
                Doc::flat(Doc::concat([t(" "), t("x")])),
                Doc::nest(4, Doc::concat([Doc::HardLine, t("x")])),
            ]),
        ]);
        assert_eq!(print(&doc, 120).text, ":= -- c\n  x");
        let long = "y".repeat(119);
        let doc = Doc::concat([
            t(":="),
            Doc::LineSuffix("-- c".into()),
            Doc::Choice(vec![
                Doc::flat(Doc::concat([t(" "), t(&long)])),
                Doc::nest(1, Doc::concat([Doc::HardLine, t(&long)])),
            ]),
        ]);
        assert_eq!(print(&doc, 120).text, format!(":= -- c\n {long}"));
    }

    #[test]
    fn comments_before_a_closer_go_at_the_indentation_in_force() {
        let comments = Doc::nest(2, Doc::concat([Doc::LineStartHere, t("-- c")]));
        let doc = Doc::concat([t("[x"), comments.clone(), Doc::HardLine, t("]")]);
        assert_eq!(print(&doc, 120).text, "[x\n  -- c\n]");
        // At the start of a line, the line moves there.
        let doc = Doc::concat([t("[x"), Doc::HardLine, comments, Doc::HardLine, t("]")]);
        assert_eq!(print(&doc, 120).text, "[x\n  -- c\n]");
    }

    /// A choice between `option` and a short `alt`: the measure decides.
    fn choice(option: Doc) -> Doc {
        Doc::Choice(vec![option, t("alt")])
    }

    #[test]
    fn a_second_comment_break_is_measured_from_the_line_the_first_made() {
        // The first break puts `b` at 2, the second `c` at 4: 4 + 117 > 120.
        let c = "c".repeat(117);
        let option = Doc::concat([
            t("a"),
            Doc::LineSuffix("-- 1".into()),
            t("b"),
            Doc::LineSuffix("-- 2".into()),
            t(&c),
        ]);
        assert_eq!(print(&choice(option), 120).text, "alt");
    }

    #[test]
    fn a_fill_item_is_measured_with_the_real_width() {
        // After the comment break `y` starts at 2: 2 + 119 > 120. (The
        // break is inside the first item of a fill, measured on its own.)
        let y = "y".repeat(119);
        let option = Doc::Fill(vec![Doc::concat([
            t("a"),
            Doc::LineSuffix("-- c".into()),
            t(&y),
        ])]);
        assert_eq!(print(&choice(option), 120).text, "alt");
    }

    #[test]
    fn a_fill_item_is_measured_with_the_comment_that_waits() {
        // The comment waits when the fill's first item is measured, so the
        // item starts a line at 2: 2 + 119 > 120.
        let y = "y".repeat(119);
        let doc = Doc::concat([
            t("x"),
            Doc::LineSuffix("-- c".into()),
            choice(Doc::Fill(vec![t(&y)])),
        ]);
        assert_eq!(print(&doc, 120).text, "x -- c\n  alt");
    }

    #[test]
    fn spaces_held_before_a_closer_after_a_comment_count_in_the_measure() {
        // The printer writes the two spaces before the `}`: 4 + 2 + 1 > 5.
        let option = Doc::concat([
            t("aaaa"),
            Doc::LineSuffix("-- c".into()),
            t(" "),
            t(" "),
            t("}"),
        ]);
        assert_eq!(print(&choice(option), 5).text, "alt");
    }

    #[test]
    fn an_if_broken_in_a_one_line_below_option_sees_an_earlier_groups_mode() {
        // SW-3913: the id group breaks (22 columns at width 20), so the
        // option below must take IfBroken's broken branch. That branch is
        // 19 columns on the option's line at 2, more than the 18 there, so
        // the option doesn't fit; its flat branch would have fit.
        let wide = "w".repeat(20);
        let group = Doc::IdGroup(
            7,
            Box::new(Doc::concat([t(&wide), Doc::Line, t("z")])),
            false,
        );
        let below = Doc::OneLineBelow(Box::new(Doc::IfBroken {
            id: 7,
            broken: Box::new(t(&"b".repeat(19))),
            flat: Box::new(t("short")),
        }));
        let doc = Doc::concat([group, Doc::HardLine, Doc::Choice(vec![below, t("alt")])]);
        assert_eq!(print(&doc, 20).text, format!("{wide}\nz\nalt"));
    }
}
