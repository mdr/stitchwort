//! Showing values in messages, cut to a readable size: a failing test's
//! sides (D601) and a counterexample's (`counterexample/`).

use stitchwort_core::registry::Builtin;
use stitchwort_core::{Globals, Term};

/// The most characters of a value shown.
pub const SHOWN: usize = 200;

/// The most characters of a failing test's side shown (a whole screenful of a
/// text, or a few hundred numbers), where `SHOWN` is for the short mentions in
/// other messages.
pub const SHOWN_SIDE: usize = 4000;

/// The most nodes quoted to show one side of a failing test: a text of a
/// screenful is a few thousand characters, each several nodes.
pub const SHOWN_SIDE_NODES: u64 = 40_000;

/// The most differing lines of two texts listed.
pub const SHOWN_LINES: usize = 6;

/// The most characters of one line shown in that list.
pub const SHOWN_LINE: usize = 120;

/// The most characters of an item shown where two lists first differ.
pub const SHOWN_ITEM: usize = 40;

/// The most nodes of a value's term that are quoted to show it.
pub const SHOWN_NODES: u64 = 8000;

/// `text`, cut off with `…` if it is longer than [`SHOWN`] characters (at
/// the last `, ` before, so a list of numbers isn't cut in one).
pub fn cut(text: &str) -> String {
    cut_to(text, SHOWN)
}

/// [`cut`] at `limit` characters.
pub fn cut_to(text: &str, limit: usize) -> String {
    if text.chars().count() <= limit {
        return text.to_string();
    }
    let mut cut: String = text.chars().take(limit).collect();
    // Back to the end of a whole element, if there is one.
    if let Some(at) = cut.rfind(", ") {
        cut.truncate(at + 1);
        cut.push(' ');
    }
    cut.push('…');
    cut
}

/// The characters of a text.
fn text_chars(g: &Globals, term: &Term) -> Option<Vec<char>> {
    let is = |b: Builtin, d| g.registry.is_data(b, d);
    let Term::Ctor(d, 0, args) = term.strip_loc() else {
        return None;
    };
    if !(is(Builtin::Text, *d) && args.len() == 1) {
        return None;
    }
    let mut out = Vec::new();
    let mut rest = args[0].strip_loc();
    loop {
        match rest {
            Term::Chars(chars) => {
                out.extend(chars.as_slice().iter().copied());
                return Some(out);
            }
            Term::Ctor(d, 0, _) if is(Builtin::List, *d) => return Some(out),
            Term::Ctor(d, 1, args) if is(Builtin::List, *d) => {
                match args[0].strip_loc() {
                    Term::Ctor(c, 0, fields) if is(Builtin::Char, *c) && fields.len() == 2 => {
                        match fields[0].strip_loc() {
                            Term::Nat(k) => {
                                out.push(char::from_u32(u32::try_from(k.as_ref().clone()).ok()?)?)
                            }
                            _ => return None,
                        }
                    }
                    _ => return None,
                }
                rest = args[1].strip_loc();
            }
            _ => return None,
        }
    }
}

/// A line diff of two texts of more than one line: which lines differ, up to
/// [`SHOWN_LINES`] of them, each cut to [`SHOWN_LINE`] characters.
fn line_diff(g: &Globals, left: &Term, right: &Term) -> Option<String> {
    let a: String = text_chars(g, left)?.into_iter().collect();
    let b: String = text_chars(g, right)?.into_iter().collect();
    if !a.contains('\n') && !b.contains('\n') {
        return None;
    }
    let a: Vec<&str> = a.split('\n').collect();
    let b: Vec<&str> = b.split('\n').collect();
    let lines = a.len().max(b.len());
    let differing: Vec<usize> = (0..lines).filter(|&i| a.get(i) != b.get(i)).collect();
    let line = |lines: &[&str], i: usize| -> String {
        match lines.get(i) {
            Some(l) => format!("{:?}", cut_to(l, SHOWN_LINE)),
            None => "(no line)".to_string(),
        }
    };
    let mut out = format!(
        "{} of {lines} lines differ (left has {}, right has {}):",
        differing.len(),
        a.len(),
        b.len()
    );
    for &i in differing.iter().take(SHOWN_LINES) {
        out.push_str(&format!(
            "\n  line {}\n    left:  {}\n    right: {}",
            i + 1,
            line(&a, i),
            line(&b, i)
        ));
    }
    if differing.len() > SHOWN_LINES {
        out.push_str(&format!("\n  … and {} more", differing.len() - SHOWN_LINES));
    }
    Some(out)
}

/// Where two values first differ, in words: the path to the first
/// difference (`[0].d[2]`: element 0, its field `d`, element 2 of that) and
/// the two parts found there, each cut to [`SHOWN_ITEM`] characters. Lists
/// and texts are walked by index, records by field name, tuples by position
/// and other constructors by name and then field; a constructor mismatch
/// names the two constructors. A `Map`, number or other built-in value is
/// compared whole. `None` when the values are equal, or are a single
/// number, character or the like (the whole values already say it). Two
/// texts of several lines are followed by which lines differ.
pub fn first_difference(g: &Globals, left: &Term, right: &Term) -> Option<String> {
    let first = walk(g, left, right, &mut String::new(), 0).and_then(|found| found.render());
    match (first, line_diff(g, left, right)) {
        (Some(first), Some(lines)) => Some(format!("{first}\n{lines}")),
        (first, lines) => first.or(lines),
    }
}

/// The most levels of nesting walked; deeper than that is compared whole.
const WALK_DEPTH: usize = 200;

/// A point where two values differ.
struct Found {
    path: String,
    left: String,
    right: String,
    /// What is said after the two parts.
    note: Option<String>,
    /// A message that is the whole of what's said, in place of the parts.
    whole: Option<String>,
}

impl Found {
    fn parts(path: &str, left: String, right: String) -> Found {
        Found {
            path: path.to_string(),
            left,
            right,
            note: None,
            whole: None,
        }
    }

    fn render(self) -> Option<String> {
        let at = if self.path.is_empty() {
            "the top".to_string()
        } else {
            self.path.clone()
        };
        if let Some(whole) = self.whole {
            return Some(format!("first difference at {at}: {whole}"));
        }
        // A bare number, character or the like at the top: the sides above
        // say it all.
        if self.path.is_empty() && self.note.is_none() {
            return None;
        }
        let mut out = format!("first difference at {at}: {} vs {}", self.left, self.right);
        if let Some(note) = self.note {
            out.push_str(&format!(" ({note})"));
        }
        Some(out)
    }
}

fn short(s: &str) -> String {
    if s.chars().count() > SHOWN_ITEM {
        let mut cut: String = s.chars().take(SHOWN_ITEM).collect();
        cut.push('…');
        cut
    } else {
        s.to_string()
    }
}

fn count(noun: &str, n: usize) -> String {
    format!("{n} {noun}{}", if n == 1 { "" } else { "s" })
}

/// The elements of a list (not a text), as terms, if it is a plain chain of
/// `Cons`.
fn list_terms<'a>(g: &Globals, term: &'a Term) -> Option<Vec<&'a Term>> {
    let is = |b: Builtin, d| g.registry.is_data(b, d);
    let mut out = Vec::new();
    let mut rest = term.strip_loc();
    loop {
        match rest {
            Term::Ctor(d, 0, _) if is(Builtin::List, *d) => return Some(out),
            Term::Ctor(d, 1, args) if is(Builtin::List, *d) && args.len() == 2 => {
                out.push(args[0].strip_loc());
                rest = args[1].strip_loc();
            }
            _ => return None,
        }
    }
}

/// The parts of a tuple, `(a, b, c)` being `MkPair a (MkPair b c)`.
fn tuple_terms<'a>(g: &Globals, term: &'a Term) -> Option<Vec<&'a Term>> {
    let is = |b: Builtin, d| g.registry.is_data(b, d);
    let mut out = Vec::new();
    let mut rest = term.strip_loc();
    while let Term::Ctor(d, 0, args) = rest
        && is(Builtin::Pair, *d)
        && args.len() == 2
    {
        out.push(args[0].strip_loc());
        rest = args[1].strip_loc();
    }
    if out.is_empty() {
        return None;
    }
    out.push(rest);
    Some(out)
}

/// Whether a value of data type `d` is compared whole: a number, character,
/// text, float, map.
fn is_whole(g: &Globals, d: stitchwort_core::DataId) -> bool {
    use Builtin::*;
    [Nat, Int, SafeNat, SafeInt, Text, Char, Map, Float]
        .iter()
        .any(|b| g.registry.is_data(*b, d))
}

fn print(g: &Globals, term: &Term) -> String {
    stitchwort_core::pretty::term(g, &[], term)
}

fn walk(g: &Globals, left: &Term, right: &Term, path: &mut String, depth: usize) -> Option<Found> {
    let (left, right) = (left.strip_loc(), right.strip_loc());
    let leaf = |path: &String| -> Option<Found> {
        let (a, b) = (print(g, left), print(g, right));
        (a != b).then(|| Found::parts(path, short(&a), short(&b)))
    };
    if depth > WALK_DEPTH {
        return leaf(path);
    }
    // Lists, then texts.
    if let (Some(a), Some(b)) = (list_terms(g, left), list_terms(g, right)) {
        let mark = path.len();
        let n = a.len().min(b.len());
        for i in 0..n {
            path.push_str(&format!("[{i}]"));
            let found = walk(g, a[i], b[i], path, depth + 1);
            path.truncate(mark);
            if found.is_some() {
                return found;
            }
        }
        let (ended, extra, side) = match a.len().cmp(&b.len()) {
            std::cmp::Ordering::Less => ("left ends", b[n], "right"),
            std::cmp::Ordering::Greater => ("right ends", a[n], "left"),
            std::cmp::Ordering::Equal => return None,
        };
        return Some(Found {
            path: format!("{path}[{n}]"),
            left: String::new(),
            right: String::new(),
            note: None,
            whole: Some(format!(
                "{ended}, {side} has {} (left has {}, right has {})",
                short(&print(g, extra)),
                count("element", a.len()),
                count("element", b.len()),
            )),
        });
    }
    if let (Some(a), Some(b)) = (text_chars(g, left), text_chars(g, right)) {
        let c = |ch: char| format!("{ch:?}");
        let n = a.len().min(b.len());
        if let Some(i) = (0..n).find(|&i| a[i] != b[i]) {
            return Some(Found::parts(&format!("{path}[{i}]"), c(a[i]), c(b[i])));
        }
        let (ended, extra, side) = match a.len().cmp(&b.len()) {
            std::cmp::Ordering::Less => ("left ends", b[n], "right"),
            std::cmp::Ordering::Greater => ("right ends", a[n], "left"),
            std::cmp::Ordering::Equal => return None,
        };
        return Some(Found {
            path: format!("{path}[{n}]"),
            left: String::new(),
            right: String::new(),
            note: None,
            whole: Some(format!(
                "{ended}, {side} has {} (left has {}, right has {})",
                c(extra),
                count("character", a.len()),
                count("character", b.len()),
            )),
        });
    }
    let (Term::Ctor(d, c, a), Term::Ctor(d2, c2, b)) = (left, right) else {
        return leaf(path);
    };
    if d != d2 || is_whole(g, *d) {
        return leaf(path);
    }
    let data = g.data(*d);
    if c != c2 {
        // Two bare constructors as the whole values (`False` and `True`):
        // the sides above say it all.
        if path.is_empty() && a.is_empty() && b.is_empty() {
            return None;
        }
        return Some(Found {
            path: path.clone(),
            left: short(&print(g, left)),
            right: short(&print(g, right)),
            note: Some(format!(
                "different constructors: {} and {}",
                data.ctors.get(*c)?.name,
                data.ctors.get(*c2)?.name
            )),
            whole: None,
        });
    }
    let mark = path.len();
    // Tuples are walked by position, all the way along.
    if let (Some(a), Some(b)) = (tuple_terms(g, left), tuple_terms(g, right))
        && a.len() == b.len()
    {
        for i in 0..a.len() {
            path.push_str(&format!(".{i}"));
            let found = walk(g, a[i], b[i], path, depth + 1);
            path.truncate(mark);
            if found.is_some() {
                return found;
            }
        }
        return None;
    }
    let ctor = data.ctors.get(*c)?;
    if a.len() != b.len() || a.len() != ctor.fields.len() {
        return leaf(path);
    }
    for i in 0..a.len() {
        if ctor.field_erased.get(i) == Some(&true) {
            continue;
        }
        let field = &ctor.fields[i].0;
        if data.record {
            path.push_str(&format!(".{field}"));
        } else if field.is_empty() || field.starts_with('_') {
            path.push_str(&format!(".{}.{i}", ctor.name));
        } else {
            path.push_str(&format!(".{}.{field}", ctor.name));
        }
        let found = walk(g, &a[i], &b[i], path, depth + 1);
        path.truncate(mark);
        if found.is_some() {
            return found;
        }
    }
    None
}
