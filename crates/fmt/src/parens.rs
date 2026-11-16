//! D2307: redundant parentheses are dropped: the pair around the type after
//! an ability row (`{Fail} (List Nat)` becomes `{Fail} List Nat`), and the
//! pair around the whole type of a header binder (`(h: (∀ …))` becomes
//! `(h: ∀ …)`), when removing it leaves the declaration parsing to the same
//! tree. Pairs around a function type after a row stay: `{e} (A -> B)` reads
//! better than `{e} A -> B`, which is easy to misread. A pair that touches a
//! comment (as rule N places it, [`crate::tidy`]) stays too, so no comment
//! changes places. A pair at a line start
//! goes like any other: the layout joins the type to the row whatever the
//! input's breaks, so keeping it would make a second pass drop it.
//!
//! This is pass P3 of docs/proposals/fmt-passes.md §2: it returns the pairs
//! as deletions, which [`crate::passes::run`] applies and re-parses.

use std::ops::Range;

use stitchwort_syntax::tree::SyntaxFile;
use stitchwort_syntax::{Tok, Token, equivalence};

use crate::passes::Edit;
use crate::spacing::{Role, roles};

/// The `)` matching the `(` at `open`, before `end`.
fn matching(tokens: &[Token], open: usize, end: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (k, t) in tokens.iter().enumerate().take(end).skip(open) {
        match t.tok {
            Tok::LParen => depth += 1,
            Tok::RParen => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(k);
                }
            }
            _ => {}
        }
    }
    None
}

/// Whether the type in the pair at `open`..`close` is a function type: an
/// arrow at its top level, or a further pair holding one.
fn holds_function(tokens: &[Token], open: usize, close: usize) -> bool {
    let mut depth = 0usize;
    for t in &tokens[open + 1..close] {
        match t.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace => depth = depth.saturating_sub(1),
            Tok::Arrow if depth == 0 => return true,
            _ => {}
        }
    }
    close > open + 2
        && tokens[open + 1].tok == Tok::LParen
        && matching(tokens, open + 1, close) == Some(close - 1)
        && holds_function(tokens, open + 1, close - 1)
}

/// The `(` starting each header binder's whole type, `(h: (TYPE))`,
/// `(h: ((TYPE)))`, in a declaration's tokens.
fn binder_types(tokens: &[Token], range: &Range<usize>) -> Vec<usize> {
    let mut found = Vec::new();
    let mut k = range.start;
    // Attributes, then `export` and `opaque`, then the keyword.
    while k < range.end && tokens[k].tok == Tok::At {
        let mut depth = 0i32;
        k += 1;
        while k < range.end {
            match tokens[k].tok {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => depth -= 1,
                _ => {}
            }
            k += 1;
            if depth <= 0 {
                break;
            }
        }
    }
    while k < range.end && matches!(tokens[k].tok, Tok::KwExport | Tok::KwOpaque) {
        k += 1;
    }
    if !tokens.get(k).is_some_and(|t| {
        matches!(
            t.tok,
            Tok::KwDef | Tok::KwTheorem | Tok::KwInstance | Tok::KwTest
        )
    }) {
        return found;
    }
    let mut depth = 0i32;
    k += 1;
    while k < range.end {
        match tokens[k].tok {
            Tok::ColonEq if depth == 0 => break,
            Tok::Pipe if depth == 0 && tokens[k].line_start => break,
            Tok::LParen if depth == 0 => {
                if let Some(close) = matching(tokens, k, range.end) {
                    let mut inner = 0i32;
                    let colon = (k + 1..close).find(|&j| match tokens[j].tok {
                        Tok::LParen | Tok::LBracket | Tok::LBrace => {
                            inner += 1;
                            false
                        }
                        Tok::RParen | Tok::RBracket | Tok::RBrace => {
                            inner -= 1;
                            false
                        }
                        Tok::Colon => inner == 0,
                        _ => false,
                    });
                    if let Some(colon) = colon {
                        let (mut open, mut offset) = (colon + 1, 1);
                        while open < close
                            && tokens[open].tok == Tok::LParen
                            && matching(tokens, open, close) == Some(close - offset)
                        {
                            found.push(open);
                            open += 1;
                            offset += 1;
                        }
                    }
                }
                depth += 1;
            }
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace => depth -= 1,
            _ => {}
        }
        k += 1;
    }
    found
}

/// P3: the redundant parentheses in `text`, as deletions; empty if there are
/// none.
pub fn drop_parens(tree: &SyntaxFile, text: &str) -> Vec<Edit> {
    let tokens = tree.tokens();
    // Comments as rule N places them, the way the printer and the checks
    // read them: a comment on a closer that N moves off it doesn't hold the
    // pair.
    let (trivia, _) = crate::tidy::place_comments(tokens, tree.trivia(), tree.eof());
    let roles = roles(tokens);
    let after_row =
        |k: usize| k > 0 && tokens[k - 1].tok == Tok::RBrace && roles[k - 1] == Role::Row;
    let mut edits = Vec::new();
    for decl in tree.decls() {
        let range = decl.token_range();
        let binders = binder_types(tokens, &range);
        // Most declarations have nothing to try, and are not parsed.
        if binders.is_empty()
            && !range
                .clone()
                .any(|k| tokens[k].tok == Tok::LParen && after_row(k))
        {
            continue;
        }
        let first = &tokens[range.start];
        let base = first.span.start as usize - first.column as usize;
        let last_end = tokens[range.end - 1].span.end as usize;
        let end = text[last_end..]
            .find('\n')
            .map_or(text.len(), |k| last_end + k);
        let before = text[base..end].trim_end_matches('\r');
        let Ok(want) = equivalence::parse_shape(before) else {
            continue;
        };
        let span = |k: usize| {
            let span = tokens[k].span;
            span.start as usize..span.end as usize
        };
        let mut dropped: Vec<(usize, usize)> = Vec::new();
        loop {
            let mut found = None;
            for k in range.clone() {
                let is_dropped = |k| dropped.iter().any(|&(open, close)| k == open || k == close);
                if is_dropped(k) {
                    continue;
                }
                // An inner pair follows the row once the pairs around it are
                // gone: look past the tokens already dropped.
                let row = {
                    let mut before = k;
                    while before > range.start && is_dropped(before - 1) {
                        before -= 1;
                    }
                    before > range.start
                        && tokens[before - 1].tok == Tok::RBrace
                        && roles[before - 1] == Role::Row
                };
                let binder = binders.contains(&k);
                if tokens[k].tok != Tok::LParen || !(row || binder) {
                    continue;
                }
                let Some(close) = matching(tokens, k, range.end) else {
                    continue;
                };
                let plain = trivia[k].leading.is_empty()
                    && trivia[k].trailing.is_none()
                    && trivia[close].leading.is_empty()
                    && trivia[close].trailing.is_none();
                if !plain || (!binder && holds_function(tokens, k, close)) {
                    continue;
                }
                let mut spans: Vec<Range<usize>> = dropped
                    .iter()
                    .flat_map(|&(open, close)| [span(open), span(close)])
                    .collect();
                spans.push(span(k));
                spans.push(span(close));
                // From the end, so the earlier spans stay valid.
                spans.sort_by_key(|s| std::cmp::Reverse(s.start));
                let mut candidate = before.to_string();
                for s in spans {
                    candidate.replace_range(s.start - base..s.end - base, "");
                }
                if equivalence::parse_shape(&candidate).is_ok_and(|got| got == want) {
                    found = Some((k, close));
                    break;
                }
            }
            match found {
                Some(pair) => dropped.push(pair),
                None => break,
            }
        }
        for (open, close) in dropped {
            for k in [open, close] {
                edits.push(Edit {
                    range: span(k),
                    text: String::new(),
                });
            }
        }
    }
    edits
}

#[cfg(test)]
mod tests {
    use stitchwort_syntax::SourceMap;

    use super::*;

    /// The text after the pass, and how many pairs it dropped.
    fn dropped(text: &str) -> (String, usize) {
        let file = SourceMap::new().add("t.sw", text);
        let tidied = crate::passes::run(file, text, &[drop_parens]);
        let pairs = tidied.edits[0] / 2;
        (tidied.text, pairs)
    }

    /// `text` after the pass, if it changed.
    fn drop(text: &str) -> Option<String> {
        let (out, _) = dropped(text);
        (out != text).then_some(out)
    }

    #[test]
    fn parentheses_after_a_row_and_around_a_binder_type_go() {
        let text = "def a: {Fail} (List Nat) := []\n\
                    def b: {Fail} ((Nat, Nat)) := (0, 0)\n\
                    theorem c ∀ (h: (∀ (i: Nat) => i = i)): True := h\n";
        let (out, pairs) = dropped(text);
        assert_eq!(pairs, 3);
        assert_eq!(
            out,
            "def a: {Fail} List Nat := []\n\
             def b: {Fail} (Nat, Nat) := (0, 0)\n\
             theorem c ∀ (h: ∀ (i: Nat) => i = i): True := h\n"
        );
    }

    #[test]
    fn nested_pairs_after_a_row_all_go_in_one_pass() {
        let text = "def a: {IO} ((halvings 100 0))\n\
                    def b: {IO} ((halvings 100 0)) := halvings 100 0\n\
                    def c: {IO} (((halvings 100 0)))\n\
                    def d: {IO} (((halvings 100 0))) := halvings 100 0\n";
        let (out, pairs) = dropped(text);
        assert_eq!(pairs, 10);
        assert_eq!(
            out,
            "def a: {IO} halvings 100 0\n\
             def b: {IO} halvings 100 0 := halvings 100 0\n\
             def c: {IO} halvings 100 0\n\
             def d: {IO} halvings 100 0 := halvings 100 0\n"
        );
    }

    #[test]
    fn function_types_tuples_and_domains_keep_theirs() {
        let text = "def a: {e} (Nat -> Nat) := id\n\
                    def b: {e} (Nat -> Nat) -> Nat := id\n\
                    def c: {Fail} (Nat, Nat) := (0, 0)\n\
                    def d: {IO} () := ()\n\
                    theorem e ∀ (h: (a ≤ b) = True): a ≤ b := h\n";
        assert_eq!(drop(text), None);
    }
}
