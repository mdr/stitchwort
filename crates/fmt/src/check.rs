//! The checks run on every result before it is returned
//! (docs/proposals/formatter.md §4.1): the same tokens, the same comments in
//! the same order, and the same syntax tree.

use stitchwort_syntax::{Comment, Lexed};

/// Line and column (from 1) of byte `at` in `text`, for messages.
fn position(text: &str, at: usize) -> String {
    let before = &text[..at.min(text.len())];
    let line = before.matches('\n').count() + 1;
    let column = at - before.rfind('\n').map_or(0, |k| k + 1) + 1;
    format!("{line}:{column}")
}

/// The same tokens, in the same order, each with the same text (a `"""`
/// text block, whose lines move, with the same value). This catches tokens
/// glued together or split apart.
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

/// Every comment, in order.
fn comments(lexed: &Lexed) -> Vec<&Comment> {
    let mut all = Vec::new();
    for trivia in lexed.trivia.iter().chain([&lexed.eof]) {
        all.extend(&trivia.leading);
        all.extend(&trivia.trailing);
    }
    all
}

pub(crate) fn same_comments(lexed_before: &Lexed, lexed_after: &Lexed) -> Result<(), String> {
    let (a, b) = (comments(lexed_before), comments(lexed_after));
    for (x, y) in a.iter().zip(&b) {
        if x.text.trim_end_matches(' ') != y.text.trim_end_matches(' ') {
            return Err(format!("the comment `{}` became `{}`", x.text, y.text));
        }
    }
    if a.len() != b.len() {
        return Err(format!(
            "the input has {} comments and the output {}",
            a.len(),
            b.len()
        ));
    }
    Ok(())
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
    fn changed_or_lost_comments_are_caught() {
        let before = lexed("-- one\ndef x := 1 -- two\n");
        assert!(same_comments(&before, &lexed("-- one\ndef x := 1 -- two   \n")).is_ok());
        assert!(same_comments(&before, &lexed("-- one\ndef x := 1\n")).is_err());
        assert!(same_comments(&before, &lexed("-- one\ndef x := 1 --  two\n")).is_err());
    }
}
