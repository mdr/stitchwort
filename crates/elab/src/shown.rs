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

/// The items of a list or the characters of a text, each printed, and the
/// noun for what they are.
fn items(g: &Globals, term: &Term) -> Option<(&'static str, Vec<String>)> {
    let is = |b: Builtin, d| g.registry.is_data(b, d);
    let char_of = |t: &Term| -> Option<char> {
        match t.strip_loc() {
            Term::Ctor(d, 0, args) if is(Builtin::Char, *d) && args.len() == 2 => {
                match args[0].strip_loc() {
                    Term::Nat(k) => char::from_u32(u32::try_from(k.as_ref().clone()).ok()?),
                    _ => None,
                }
            }
            _ => None,
        }
    };
    let mut out = Vec::new();
    let (noun, mut rest) = match term.strip_loc() {
        Term::Ctor(d, 0, args) if is(Builtin::Text, *d) && args.len() == 1 => {
            ("character", args[0].strip_loc())
        }
        t @ Term::Ctor(d, _, _) if is(Builtin::List, *d) => ("element", t),
        _ => return None,
    };
    loop {
        match rest {
            Term::Chars(chars) => {
                out.extend(chars.as_slice().iter().map(|c| format!("{c:?}")));
                return Some((noun, out));
            }
            Term::Ctor(d, 0, _) if is(Builtin::List, *d) => return Some((noun, out)),
            Term::Ctor(d, 1, args) if is(Builtin::List, *d) => {
                out.push(match char_of(&args[0]) {
                    Some(c) => format!("{c:?}"),
                    None => stitchwort_core::pretty::term(g, &[], &args[0]),
                });
                rest = args[1].strip_loc();
            }
            _ => return None,
        }
    }
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

/// Where two lists, or two texts, first differ, in words.
pub fn first_difference(g: &Globals, left: &Term, right: &Term) -> Option<String> {
    let first = first_item_difference(g, left, right);
    match (first, line_diff(g, left, right)) {
        (Some(first), Some(lines)) => Some(format!("{first}\n{lines}")),
        (first, lines) => first.or(lines),
    }
}

fn first_item_difference(g: &Globals, left: &Term, right: &Term) -> Option<String> {
    let (noun, a) = items(g, left)?;
    let (other, b) = items(g, right)?;
    if noun != other {
        return None;
    }
    let short = |s: &String| -> String {
        if s.chars().count() > SHOWN_ITEM {
            let mut cut: String = s.chars().take(SHOWN_ITEM).collect();
            cut.push('…');
            cut
        } else {
            s.clone()
        }
    };
    let count = |n: usize| format!("{n} {noun}{}", if n == 1 { "" } else { "s" });
    let at = (0..a.len().min(b.len())).find(|&i| a[i] != b[i]);
    Some(match at {
        Some(i) => format!(
            "first difference at index {i}: {} vs {}",
            short(&a[i]),
            short(&b[i])
        ),
        None if a.len() < b.len() => format!(
            "first difference at index {}: left ends, right has {} (left has {}, right has {})",
            a.len(),
            short(&b[a.len()]),
            count(a.len()),
            count(b.len())
        ),
        None if b.len() < a.len() => format!(
            "first difference at index {}: right ends, left has {} (left has {}, right has {})",
            b.len(),
            short(&a[b.len()]),
            count(a.len()),
            count(b.len())
        ),
        None => return None,
    })
}
