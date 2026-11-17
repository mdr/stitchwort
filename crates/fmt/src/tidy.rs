//! Where each comment belongs: the reading rule N of
//! docs/proposals/fmt-passes.md §2. It rewrites the trivia the lexer
//! attached, and is applied to every token sequence the formatter reads,
//! the input and its own output alike, so the layout rules and the checks
//! see one answer however the source placed its commas and closers.
//!
//! After it:
//!
//! 1. no comma, closing bracket or record update's `|` has a trailing
//!    comment, except one kept by the limits in [`place_comments`];
//! 2. no comma has any comment;
//! 3. no comment's text ends in a space;
//! 4. no `->` has a trailing comment or own-line comments after it (the
//!    type that follows has none before it): they come before the `->`.
//!
//! Applying it to its own result changes nothing.

use stitchwort_syntax::{Comment, Tok, Token, Trivia};

/// Each token's comments, and the end of file's, placed by rule N:
///
/// 1. A trailing comment on a comma, a closing bracket or a record update's
///    `|` moves to the nearest token before it that is none of those. It
///    stops early, staying on a closer or bar that starts its line, when
///    going further would pass that token's own-line comments, or the line
///    before ends with a comment (on its last token, or moved back from
///    it by this rule).
///    A bar's trailing comment that stays where it is although the base
///    before it ends its line with a comment becomes an own-line comment of
///    the token after the bar.
/// 2. A comma's own-line comments, and the trailing comment of a comma that
///    starts its line, become own-line comments of the token after it, with
///    their blank lines.
/// 3. Comment text loses its trailing spaces.
/// 4. A `->`'s trailing comment, and own-line comments between it and the
///    type after it, become own-line comments of the `->`, in order. A
///    type's operand starting its own line would open a block that ends the
///    arrow chain at the next `->`.
pub fn place_comments(tokens: &[Token], trivia: &[Trivia], eof: &Trivia) -> (Vec<Trivia>, Trivia) {
    let mut out: Vec<Trivia> = trivia.to_vec();
    let mut eof = eof.clone();
    for i in 0..out.len() {
        let movable = out[i].trailing.is_some()
            && match tokens[i].tok {
                Tok::Comma => !tokens[i].line_start,
                Tok::RParen | Tok::RBracket | Tok::RBrace => true,
                Tok::Pipe => record_update_bar(tokens, i),
                _ => false,
            };
        if !movable {
            continue;
        }
        let mut j = i;
        while j > 0 && skipped(tokens, j) {
            if tokens[j].line_start
                && (!out[j].leading.is_empty() || line_ends_with_comment(tokens, &out, j - 1))
            {
                break;
            }
            j -= 1;
        }
        if j != i {
            out[j].trailing = out[i].trailing.take();
        } else if tokens[i].tok == Tok::Pipe && i > 0 && out[i - 1].trailing.is_some() {
            // The base's comment is printed after the bar, so the bar's own
            // would run into it on one line: it starts the line below.
            if let Some(mut comment) = out[i].trailing.take() {
                comment.blank_lines_before = 0;
                out[i + 1].leading.insert(0, comment);
            }
        }
    }
    for i in 0..out.len() {
        if tokens[i].tok != Tok::Comma {
            continue;
        }
        let comma = std::mem::take(&mut out[i]);
        if comma.leading.is_empty() && comma.trailing.is_none() {
            out[i] = comma;
            continue;
        }
        let mut moved = comma.leading;
        let mut blank = comma.blank_lines_before;
        if let Some(mut comment) = comma.trailing {
            comment.blank_lines_before = blank;
            blank = 0;
            moved.push(comment);
        }
        let next = out.get_mut(i + 1).unwrap_or(&mut eof);
        if let Some(first) = next.leading.first_mut() {
            first.blank_lines_before = first.blank_lines_before.max(blank);
        } else {
            next.blank_lines_before = next.blank_lines_before.max(blank);
        }
        moved.append(&mut next.leading);
        next.leading = moved;
    }
    for i in 0..out.len().saturating_sub(1) {
        if tokens[i].tok != Tok::Arrow
            || (out[i + 1].leading.is_empty() && out[i].trailing.is_none())
        {
            continue;
        }
        let mut moved = std::mem::take(&mut out[i + 1].leading);
        if let Some(mut comment) = out[i].trailing.take() {
            comment.blank_lines_before = 0;
            moved.insert(0, comment);
        }
        out[i].leading.append(&mut moved);
    }
    // An expression `let`'s value must start on its `:=` line, or the `;`
    // after it ends a block rather than the `let` (SW-3750). A comment
    // ending that line has nowhere to go after the `:=`, so it goes before,
    // as a comment after an arrow does.
    for i in 0..tokens.len() {
        if tokens[i].tok != Tok::ColonEq
            || !expression_let_assign(tokens, i)
            || out[i].trailing.is_none()
        {
            continue;
        }
        if let Some(mut comment) = out[i].trailing.take() {
            comment.blank_lines_before = 0;
            out[i].leading.push(comment);
        }
    }
    for t in out.iter_mut().chain(std::iter::once(&mut eof)) {
        t.leading.iter_mut().for_each(trim);
        if let Some(comment) = &mut t.trailing {
            trim(comment);
        }
    }
    (out, eof)
}

/// Whether the line ending at token `end` ends with a comment: on `end`
/// itself, or on the token rule 1 has moved it back to, past the closers,
/// commas and bars before `end` (SW-3606: two closers ending two lines,
/// whose comments would both land on one token).
fn line_ends_with_comment(tokens: &[Token], out: &[Trivia], end: usize) -> bool {
    let mut k = end;
    loop {
        if out[k].trailing.is_some() {
            return true;
        }
        if k == 0 || !skipped(tokens, k) {
            return false;
        }
        k -= 1;
    }
}

/// Whether rule 1 walks past token `j`: a comma, a closer or a record
/// update's bar.
fn skipped(tokens: &[Token], j: usize) -> bool {
    match tokens[j].tok {
        Tok::Comma | Tok::RParen | Tok::RBracket | Tok::RBrace => true,
        Tok::Pipe => record_update_bar(tokens, j),
        _ => false,
    }
}

/// Whether the `:=` at `assign` is an expression `let`'s: a `let` at its
/// depth before it, and a `;` at that depth after it (`(let x := e; body)`).
fn expression_let_assign(tokens: &[Token], assign: usize) -> bool {
    let mut depth = 0usize;
    let mut let_before = false;
    for token in tokens[..assign].iter().rev() {
        match token.tok {
            Tok::RParen | Tok::RBracket | Tok::RBrace => depth += 1,
            Tok::LParen | Tok::LBracket | Tok::LBrace if depth > 0 => depth -= 1,
            Tok::LParen | Tok::LBracket | Tok::LBrace => break,
            Tok::KwLet if depth == 0 => {
                let_before = true;
                break;
            }
            Tok::Semi | Tok::FatArrow if depth == 0 => break,
            Tok::KwDef
            | Tok::KwTheorem
            | Tok::KwType
            | Tok::KwTest
            | Tok::KwExport
            | Tok::KwInstance
            | Tok::KwInterface
            | Tok::KwNamespace
            | Tok::KwImport
            | Tok::KwInclude
            | Tok::KwAbility
                if depth == 0 =>
            {
                break;
            }
            _ => {}
        }
    }
    if !let_before {
        return false;
    }
    let mut depth = 0usize;
    for token in &tokens[assign + 1..] {
        match token.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace if depth > 0 => depth -= 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace => return false,
            Tok::Semi if depth == 0 => return true,
            _ => {}
        }
    }
    false
}

fn trim(comment: &mut Comment) {
    let len = comment.text.trim_end_matches(' ').len();
    comment.text.truncate(len);
}

/// Whether the `|` at `bar` is a record update's, `{ r | … }`: the first
/// `|` at its depth after the opening brace, which opens a record
/// (SW-1015), with no comma before it. An alternative's bar (after a
/// `=>`, or with another `|` before it) is not one.
pub(crate) fn record_update_bar(tokens: &[Token], bar: usize) -> bool {
    let mut depth = 0usize;
    let mut open = None;
    for i in (0..bar).rev() {
        match tokens[i].tok {
            Tok::RParen | Tok::RBracket | Tok::RBrace => depth += 1,
            Tok::LParen | Tok::LBracket => depth = depth.saturating_sub(1),
            Tok::LBrace if depth > 0 => depth -= 1,
            Tok::LBrace => {
                open = Some(i);
                break;
            }
            _ => {}
        }
    }
    let Some(open) = open else {
        return false;
    };
    let mut depth = 0usize;
    for token in &tokens[open + 1..bar] {
        match token.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace => depth = depth.saturating_sub(1),
            Tok::Comma | Tok::Pipe | Tok::FatArrow if depth == 0 => return false,
            _ => {}
        }
    }
    stitchwort_syntax::record_braces(tokens, open)
}

#[cfg(test)]
mod tests {
    use stitchwort_syntax::{SourceMap, lex_with_trivia};

    use super::place_comments;

    /// Each comment after N, as (text, own line, the text of its token).
    fn placed(text: &str) -> Vec<(String, bool, String)> {
        let file = SourceMap::new().add("t.sw", text);
        let lexed = lex_with_trivia(file, text).expect("lexes");
        let (trivia, eof) = place_comments(&lexed.tokens, &lexed.trivia, &lexed.eof);
        let again = place_comments(&lexed.tokens, &trivia, &eof);
        assert_eq!((trivia.clone(), eof.clone()), again, "N is idempotent");
        let mut out = Vec::new();
        for (token, t) in lexed.tokens.iter().zip(&trivia) {
            let name = text[token.span.start as usize..token.span.end as usize].to_string();
            for c in &t.leading {
                out.push((c.text.clone(), true, name.clone()));
            }
            if let Some(c) = &t.trailing {
                out.push((c.text.clone(), false, name.clone()));
            }
        }
        for c in &eof.leading {
            out.push((c.text.clone(), true, String::new()));
        }
        out
    }

    fn one(text: &str, comment: &str, own_line: bool, token: &str) {
        assert_eq!(
            placed(text),
            vec![(comment.to_string(), own_line, token.to_string())],
            "{text}"
        );
    }

    #[test]
    fn a_trailing_comment_after_closers_and_commas_belongs_to_the_code_before_them() {
        one("def x := [1, 2] -- c\n", "-- c", false, "2");
        one("def x := [1, 2 -- c\n]\n", "-- c", false, "2");
        one("def x := [\n  1,\n  2\n] -- c\n", "-- c", false, "2");
        one("def x := [f (g y), -- c\n  2]\n", "-- c", false, "y");
        one("def x := { r | -- c\n  a = 1 }\n", "-- c", false, "r");
        one("def x := { (f r) | -- c\n  a = 1 }\n", "-- c", false, "r");
    }

    #[test]
    fn a_trailing_comment_stays_on_a_closer_that_would_otherwise_pass_comments() {
        let note = placed("def x := [\n  1\n  -- note\n] -- c\n");
        assert_eq!(note[1], ("-- c".to_string(), false, "]".to_string()));
        let both = placed("def x := [\n  1 -- a\n] -- b\n");
        assert_eq!(both[1], ("-- b".to_string(), false, "]".to_string()));
        // SW-3606: the inner closer's comment has already moved to `1`, so
        // the line before the outer closer still ends with a comment.
        let nested = placed("def a: Nat := (f (1) -- c1\n  ) -- c2\n");
        assert_eq!(
            nested,
            vec![
                ("-- c1".to_string(), false, "1".to_string()),
                ("-- c2".to_string(), false, ")".to_string()),
            ]
        );
    }

    #[test]
    fn a_commas_comments_go_to_the_token_after_it() {
        one("def x := [ 1\n  , 2 -- c\n  ]\n", "-- c", false, "2");
        one("def x := [ 1\n  , -- c\n  2 ]\n", "-- c", true, "2");
        one("def x := [ 1\n  -- c\n  , 2 ]\n", "-- c", true, "2");
        one("def x := [ 1,\n  -- c\n  , ]\n", "-- c", true, "]");
    }

    #[test]
    fn comment_text_loses_its_trailing_spaces() {
        one("def x := 1 -- c  \n", "-- c", false, "1");
        assert_eq!(placed("def x := 1\n-- end  \n")[0].0, "-- end");
    }
}
