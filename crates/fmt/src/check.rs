//! The checks run on every result before it is returned
//! (docs/proposals/formatter-style.md; the comment and tree checks are in
//! `printer`): the same tokens, in the same order.

use stitchwort_syntax::Lexed;

/// Line and column (from 1) of byte `at` in `text`, for messages.
fn position(text: &str, at: usize) -> String {
    let before = &text[..at.min(text.len())];
    let line = before.matches('\n').count() + 1;
    let column = at - before.rfind('\n').map_or(0, |k| k + 1) + 1;
    format!("{line}:{column}")
}

/// The same tokens, in the same order, each with the same text (a `"""`
/// text block, whose lines move, with the same value). This catches tokens
/// glued together or split apart, and a bracket dropped where it matters.
pub(crate) fn same_tokens(
    before: &str,
    lexed_before: &Lexed,
    after: &str,
    lexed_after: &Lexed,
) -> Result<(), String> {
    let (a, b) = (&lexed_before.tokens, &lexed_after.tokens);
    for (x, y) in a.iter().zip(b) {
        let text_x = &before[x.span.range()];
        let text_y = &after[y.span.range()];
        let same_text = text_x == text_y || (text_x.contains('\n') && text_y.contains('\n'));
        if x.tok != y.tok || !same_text {
            return Err(format!(
                "the token `{text_x}` at {} became `{text_y}` at {}",
                position(before, x.span.start as usize),
                position(after, y.span.start as usize),
            ));
        }
    }
    if a.len() != b.len() {
        return Err(format!(
            "the input has {} tokens and the output {}",
            a.len(),
            b.len()
        ));
    }
    Ok(())
}

/// The same comments in the same order, read straight from the lexer: the
/// comment anchors ([`crate::printer`]) compare both texts after rule N
/// ([`crate::tidy`]) has placed their comments, so a comment N lost would be
/// lost from both and pass them (SW-3606). This check shares no code with
/// the formatter's placement. Text is compared without trailing spaces,
/// which N removes.
pub(crate) fn same_comments(before: &Lexed, after: &Lexed) -> Result<(), String> {
    let texts = |lexed: &Lexed| -> Vec<String> {
        let mut out: Vec<(u32, String)> = lexed
            .trivia
            .iter()
            .chain(std::iter::once(&lexed.eof))
            .flat_map(|t| t.leading.iter().chain(&t.trailing))
            .map(|c| (c.span.start, c.text.trim_end_matches(' ').to_string()))
            .collect();
        out.sort();
        out.into_iter().map(|(_, text)| text).collect()
    };
    let (a, b) = (texts(before), texts(after));
    let at = a
        .iter()
        .zip(&b)
        .position(|(x, y)| x != y)
        .unwrap_or(a.len().min(b.len()));
    match (a.get(at), b.get(at)) {
        (None, None) => Ok(()),
        (Some(x), Some(y)) => Err(format!(
            "comment {} is `{x}` in the input and `{y}` in the output",
            at + 1
        )),
        (Some(x), None) => Err(format!("the comment `{x}` was lost")),
        (None, Some(y)) => Err(format!("the output has a comment `{y}` the input hasn't")),
    }
}

#[cfg(test)]
mod tests {
    use stitchwort_syntax::{SourceMap, lex_with_trivia};

    use super::*;

    fn lexed(text: &str) -> Lexed {
        let file = SourceMap::new().add("t.sw", text);
        lex_with_trivia(file, text).expect("lexes")
    }

    #[test]
    fn glued_tokens_are_caught() {
        let (before, after) = ("def x := a - -b", "def x := a --b");
        let error = same_tokens(before, &lexed(before), after, &lexed(after)).unwrap_err();
        assert!(error.contains("tokens"), "{error}");
        let (before, after) = ("def x := a.b", "def x := a .b");
        assert!(same_tokens(before, &lexed(before), after, &lexed(after)).is_ok());
    }

    #[test]
    fn round_brackets_are_compared_like_every_other_token() {
        let (before, after) = ("def x := (a)\n", "def x := a\n");
        assert!(same_tokens(before, &lexed(before), after, &lexed(after)).is_err());
        let (before, after) = ("def x := ((a))\n", "def x := (a)\n");
        assert!(same_tokens(before, &lexed(before), after, &lexed(after)).is_err());
    }
}
