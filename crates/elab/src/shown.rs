//! Showing values in messages, cut to a readable size: a failing test's
//! sides (D601) and a counterexample's (`counterexample/`).

use stitchwort_core::registry::Builtin;
use stitchwort_core::{Globals, Term};

/// The most characters of a value shown.
pub const SHOWN: usize = 200;

/// The most characters of an item shown where two lists first differ.
pub const SHOWN_ITEM: usize = 40;

/// The most nodes of a value's term that are quoted to show it.
pub const SHOWN_NODES: u64 = 8000;

/// `text`, cut off with `…` if it is longer than [`SHOWN`] characters (at
/// the last `, ` before, so a list of numbers isn't cut in one).
pub fn cut(text: &str) -> String {
    if text.chars().count() <= SHOWN {
        return text.to_string();
    }
    let mut cut: String = text.chars().take(SHOWN).collect();
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

/// Where two lists, or two texts, first differ, in words.
pub fn first_difference(g: &Globals, left: &Term, right: &Term) -> Option<String> {
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
