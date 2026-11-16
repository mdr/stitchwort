//! The REPL's colours: the line as it is typed, the prompts, and printed
//! results. The classes come from [`stitchwort_driver::marks::lexical_marks`],
//! the lexical counterpart of the language server's semantic tokens.

use std::borrow::Cow;

use rustyline::Helper;
use rustyline::completion::Completer;
use rustyline::highlight::{CmdKind, Highlighter};
use rustyline::hint::Hinter;
use rustyline::validate::Validator;
use stitchwort_driver::marks::{Lexical, lexical_marks};

const RESET: &str = "\x1b[0m";
const DIM: &str = "\x1b[2m";
const TYPE_SHOWN: &str = "\x1b[33m";

/// The SGR sequence that starts `class`.
fn style(class: Lexical) -> &'static str {
    match class {
        Lexical::Keyword => "\x1b[35m",
        Lexical::Number => "\x1b[36m",
        Lexical::Text => "\x1b[32m",
        Lexical::Name => "\x1b[33m",
        Lexical::Operator => "\x1b[34m",
        Lexical::Comment => "\x1b[90m",
    }
}

/// `text` with each token wrapped in its colour. A REPL command (`:t e`)
/// has its command word in the keyword colour and the rest as code.
pub fn colour_code(text: &str) -> String {
    if let Some(rest) = text.strip_prefix(':') {
        let word = rest.find(char::is_whitespace).unwrap_or(rest.len());
        if word > 0
            && rest[..word]
                .chars()
                .all(|c| c.is_ascii_alphabetic() || c == '?')
        {
            return format!(
                "{}:{}{RESET}{}",
                style(Lexical::Keyword),
                &rest[..word],
                colour_code(&rest[word..])
            );
        }
    }
    let mut out = String::with_capacity(text.len() * 2);
    let mut at = 0;
    for (range, class) in lexical_marks(text) {
        if range.start < at {
            continue;
        }
        out.push_str(&text[at..range.start]);
        out.push_str(style(class));
        out.push_str(&text[range.clone()]);
        out.push_str(RESET);
        at = range.end;
    }
    out.push_str(&text[at..]);
    out
}

/// A printed result, `value: type`, in colour: the value as code, the type
/// in one colour of its own.
pub fn colour_result(value: &str, ty: &str) -> String {
    format!(
        "{}{DIM}:{RESET} {TYPE_SHOWN}{ty}{RESET}",
        colour_code(value)
    )
}

/// The line editor's helper: colours the input and the prompts when `color`.
pub struct ReplHelper {
    pub color: bool,
}

impl Highlighter for ReplHelper {
    fn highlight<'l>(&self, line: &'l str, _pos: usize) -> Cow<'l, str> {
        if self.color {
            Cow::Owned(colour_code(line))
        } else {
            Cow::Borrowed(line)
        }
    }

    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        _default: bool,
    ) -> Cow<'b, str> {
        if self.color {
            Cow::Owned(format!("{DIM}{prompt}{RESET}"))
        } else {
            Cow::Borrowed(prompt)
        }
    }

    fn highlight_char(&self, _line: &str, _pos: usize, _kind: CmdKind) -> bool {
        self.color
    }
}

impl Completer for ReplHelper {
    type Candidate = String;
}
impl Hinter for ReplHelper {
    type Hint = String;
}
impl Validator for ReplHelper {}
impl Helper for ReplHelper {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn highlights_keyword_number_and_constructor() {
        let on = ReplHelper { color: true };
        assert_eq!(
            on.highlight("if Some 1", 0),
            "\x1b[35mif\x1b[0m \x1b[33mSome\x1b[0m \x1b[36m1\x1b[0m"
        );
        let off = ReplHelper { color: false };
        assert_eq!(off.highlight("if Some 1", 0), "if Some 1");
        assert_eq!(off.highlight_prompt("sw> ", true), "sw> ");
    }

    #[test]
    fn result_has_value_and_type_apart() {
        assert_eq!(
            colour_result("42", "Nat"),
            "\x1b[36m42\x1b[0m\x1b[2m:\x1b[0m \x1b[33mNat\x1b[0m"
        );
    }
}
