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
//! 3. no comment's text ends in a space.
//!
//! Applying it to its own result changes nothing.

use stitchwort_syntax::{Comment, Tok, Token, Trivia};

/// Each token's comments, and the end of file's, placed by rule N:
///
/// 1. A trailing comment on a comma, a closing bracket or a record update's
///    `|` moves to the nearest token before it that is none of those. It
///    stops early, staying on a closer or bar that starts its line, when
///    going further would pass that token's own-line comments or land on a
///    token that already ends its line with a comment.
/// 2. A comma's own-line comments, and the trailing comment of a comma that
///    starts its line, become own-line comments of the token after it, with
///    their blank lines.
/// 3. Comment text loses its trailing spaces.
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
            if tokens[j].line_start && (!out[j].leading.is_empty() || out[j - 1].trailing.is_some())
            {
                break;
            }
            j -= 1;
        }
        if j != i {
            out[j].trailing = out[i].trailing.take();
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
    for t in out.iter_mut().chain(std::iter::once(&mut eof)) {
        t.leading.iter_mut().for_each(trim);
        if let Some(comment) = &mut t.trailing {
            trim(comment);
        }
    }
    (out, eof)
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
