//! The checks run on every result before it is returned
//! (docs/proposals/formatter-style.md; the comment and tree checks are in
//! `printer`): the same tokens, in the same order.

use stitchwort_syntax::{Lexed, Tok, Token};

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
    // Commas are one allowed difference: D1012/D1017 add and remove
    // them at the ends of the lines of a multi-line bracket. Parentheses are
    // the other (D2307): the formatter drops the redundant ones after an
    // ability row. The tree check (§4.1, 3) catches any comma or parenthesis
    // whose removal changed the parse.
    let strip = |lexed: &Lexed| -> Vec<Token> {
        let kept = |t: &&Token| !matches!(t.tok, Tok::Comma | Tok::LParen | Tok::RParen);
        lexed.tokens.iter().filter(kept).cloned().collect()
    };
    let (a, b) = (strip(lexed_before), strip(lexed_after));
    for (x, y) in a.iter().zip(&b) {
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
}
