//! D2307: redundant parentheses are dropped: the pair around the type after
//! an ability row (`{Fail} (List Nat)` becomes `{Fail} List Nat`), and the
//! pair around the whole type of a header binder (`(h: (∀ …))` becomes
//! `(h: ∀ …)`), when removing it leaves the declaration parsing to the same
//! tree. Pairs around a function type after a row stay: `{e} (A -> B)` reads
//! better than `{e} A -> B`, which is easy to misread. A pair that starts a
//! line or touches a comment stays too, so no line break moves and no
//! comment changes places.
//!
//! Like [`super::merge`], it rewrites the text before printing, and the
//! rewrite is checked on its own.

use std::ops::Range;

use stitchwort_syntax::{SourceMap, Tok, Token, decl_ranges, equivalence, lex_with_trivia};

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

/// `text` with the redundant parentheses dropped, and how many pairs; `None`
/// if there are none.
pub(crate) fn drop_parens(text: &str) -> Option<(String, usize)> {
    let file = SourceMap::new().next_id();
    let lexed = lex_with_trivia(file, text).ok()?;
    let (tokens, trivia) = (&lexed.tokens, &lexed.trivia);
    let ranges = decl_ranges(tokens).ok()?;
    let roles = roles(tokens);
    let after_row =
        |k: usize| k > 0 && tokens[k - 1].tok == Tok::RBrace && roles[k - 1] == Role::Row;
    let mut cuts: Vec<Range<usize>> = Vec::new();
    for range in ranges {
        let binders = binder_types(tokens, &range);
        // Most declarations have nothing to try, and are not parsed.
        if !binders.iter().any(|_| true)
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
                if dropped.iter().any(|&(open, close)| k == open || k == close) {
                    continue;
                }
                let row = after_row(k) && !dropped.iter().any(|&(open, _)| open == k - 1);
                let binder = binders.contains(&k);
                if tokens[k].tok != Tok::LParen || !(row || binder) {
                    continue;
                }
                let Some(close) = matching(tokens, k, range.end) else {
                    continue;
                };
                let plain = !tokens[k].line_start
                    && !tokens[close].line_start
                    && trivia[k].leading.is_empty()
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
            cuts.push(span_of(tokens, open));
            cuts.push(span_of(tokens, close));
        }
    }
    if cuts.is_empty() {
        return None;
    }
    let pairs = cuts.len() / 2;
    cuts.sort_by_key(|c| std::cmp::Reverse(c.start));
    let mut out = text.to_string();
    for cut in cuts {
        out.replace_range(cut, "");
    }
    Some((out, pairs))
}

fn span_of(tokens: &[Token], k: usize) -> Range<usize> {
    tokens[k].span.start as usize..tokens[k].span.end as usize
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parentheses_after_a_row_and_around_a_binder_type_go() {
        let text = "def a: {Fail} (List Nat) := []\n\
                    def b: {Fail} ((Nat, Nat)) := (0, 0)\n\
                    theorem c ∀ (h: (∀ (i: Nat) => i = i)): True := h\n";
        let (out, pairs) = drop_parens(text).unwrap();
        assert_eq!(pairs, 3);
        assert_eq!(
            out,
            "def a: {Fail} List Nat := []\n\
             def b: {Fail} (Nat, Nat) := (0, 0)\n\
             theorem c ∀ (h: ∀ (i: Nat) => i = i): True := h\n"
        );
    }

    #[test]
    fn function_types_tuples_and_domains_keep_theirs() {
        let text = "def a: {e} (Nat -> Nat) := id\n\
                    def b: {e} (Nat -> Nat) -> Nat := id\n\
                    def c: {Fail} (Nat, Nat) := (0, 0)\n\
                    def d: {IO} () := ()\n\
                    theorem e ∀ (h: (a ≤ b) = True): a ≤ b := h\n";
        assert_eq!(drop_parens(text), None);
    }
}
