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
//! Applying it to its own result changes nothing, on the texts the
//! formatter reads: those after pass P2 ([`crate::passes`]) has deleted the
//! last comma of each comma bracket. Rule 1 stops on a comma that starts
//! its line and has own-line comments above it, and rule 2 then moves those
//! comments to the token after the comma; on a last comma that is the
//! closer, so a second application finds the comments above the closer and
//! moves a trailing comment further back than the first did
//! (`g ([⏎1⏎-- above⏎, ] -- b⏎) -- c`, SW-3840). With the comma gone the
//! first application already puts everything where it stays.

use stitchwort_syntax::{Comment, Tok, Token, Trivia};

/// The file's tokens with their trivia after rule N, one line a token, for
/// the comparison harness (`task fmt:twin`, docs/proposals/self-hosted-fmt.md
/// §6): the token's kind, its text, its column, whether it starts its line,
/// the blank lines before it, each own-line comment before it (column, blank
/// lines before, text) and its trailing comment. A last line gives the end
/// of the file's trivia. A file that doesn't lex gives its diagnostic.
pub fn token_dump(file: stitchwort_syntax::FileId, text: &str) -> Result<String, String> {
    let lexed = stitchwort_syntax::lex_with_trivia(file, text).map_err(|d| d.message)?;
    let (trivia, eof) = place_comments(&lexed.tokens, &lexed.trivia, &lexed.eof);
    let comment = |c: &Comment| format!("{}:{}:{:?}", c.column, c.blank_lines_before, c.text);
    let leading = |t: &Trivia| t.leading.iter().map(comment).collect::<Vec<_>>().join(" ");
    let mut out = String::new();
    for (token, trivia) in lexed.tokens.iter().zip(&trivia) {
        let kind = format!("{:?}", token.tok);
        let kind = kind.split(['(', ' ', '{']).next().unwrap_or("");
        let source = &text[token.span.start as usize..token.span.end as usize];
        out.push_str(&format!(
            "{kind} {source:?} col={} line_start={} blank={} leading=[{}] trailing={}\n",
            token.column,
            token.line_start,
            trivia.blank_lines_before,
            leading(trivia),
            trivia.trailing.as_ref().map_or("none".to_string(), comment),
        ));
    }
    out.push_str(&format!(
        "EOF blank={} leading=[{}]\n",
        eof.blank_lines_before,
        leading(&eof)
    ));
    Ok(out)
}

/// Each token's comments, and the end of file's, placed by rule N:
///
/// 1. A trailing comment on a comma, a closing bracket or a record update's
///    `|` moves to the nearest token before it that is none of those. It
///    stops early, staying on a closer, bar or comma that starts its line,
///    when going further would pass that token's own-line comments, or the
///    line before ends with a comment (on its last token, or moved back from
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

    use super::{place_comments, token_dump};

    #[test]
    fn the_token_dump_shows_a_closer_comment_on_the_token_before_it() {
        let text = "def f := g (\n  1,\n  2\n) -- last\n";
        let file = SourceMap::new().add("t.sw", text);
        let dump = token_dump(file, text).expect("lexes");
        let lines: Vec<&str> = dump.lines().collect();
        assert_eq!(lines.len(), 10, "{dump}");
        assert_eq!(
            lines[0],
            "KwDef \"def\" col=0 line_start=true blank=0 leading=[] trailing=none"
        );
        assert!(lines[7].starts_with("Num \"2\""), "{dump}");
        assert!(lines[7].ends_with("trailing=2:0:\"-- last\""), "{dump}");
        assert_eq!(lines[9], "EOF blank=0 leading=[]");
        let bad = SourceMap::new().add("t.sw", "def y := \"abc\n");
        assert!(token_dump(bad, "def y := \"abc\n").is_err());
    }

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
    fn rule_n_is_idempotent_once_the_last_commas_are_deleted() {
        // SW-3840: rule N alone moves `-- c` again, from `)` to `1`; the
        // formatter reads the text after P2, where it stays.
        let text = "def f: T := g ([\n    1\n    -- above\n      , ] -- b\n  ) -- c\n";
        let file = SourceMap::new().add("t.sw", text);
        let tidied = crate::passes::run(file, text, &crate::passes::PASSES).text;
        assert_eq!(
            placed(&tidied)
                .iter()
                .map(|(c, own, token)| (c.as_str(), *own, token.as_str()))
                .collect::<Vec<_>>(),
            [
                ("-- above", true, "]"),
                ("-- b", false, "]"),
                ("-- c", false, ")"),
            ]
        );
    }

    #[test]
    fn comment_text_loses_its_trailing_spaces() {
        one("def x := 1 -- c  \n", "-- c", false, "1");
        assert_eq!(placed("def x := 1\n-- end  \n")[0].0, "-- end");
    }
}
