//! The REPL's colours: the line as it is typed, the prompts, and printed
//! results. The classes come from [`stitchwort_driver::marks::lexical_marks`],
//! the lexical counterpart of the language server's semantic tokens.

use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;

use rustyline::Context;
use rustyline::Helper;
use rustyline::completion::{Completer, Pair};
use rustyline::highlight::{CmdKind, Highlighter};
use rustyline::hint::Hinter;
use rustyline::validate::Validator;
use stitchwort_driver::driver::Session;
use stitchwort_driver::marks::{Lexical, lexical_marks};
use stitchwort_driver::palette::{self, Role};

const RESET: &str = "\x1b[0m";
const DIM: &str = "\x1b[2m";

/// The escape sequence that starts `class`, in the process's palette.
fn style(class: Lexical) -> String {
    palette::current().open(match class {
        Lexical::Keyword => Role::Keyword,
        Lexical::Number => Role::Number,
        Lexical::Text => Role::Text,
        Lexical::Name => Role::Type,
        Lexical::Operator => Role::Operator,
        Lexical::Comment => Role::Comment,
    })
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
        out.push_str(&style(class));
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
        "{}{DIM}:{RESET} {}{ty}{RESET}",
        colour_code(value),
        style(Lexical::Name)
    )
}

/// The line editor's helper: colours the input and the prompts when
/// `color`, and completes from the session the REPL evaluates in.
pub struct ReplHelper {
    pub color: bool,
    pub session: Rc<RefCell<Session>>,
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
    type Candidate = Pair;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctx: &Context<'_>,
    ) -> rustyline::Result<(usize, Vec<Pair>)> {
        // The REPL isn't evaluating while a line is read, so the session is free.
        let Ok(mut session) = self.session.try_borrow_mut() else {
            return Ok((pos, Vec::new()));
        };
        Ok(crate::repl_complete::complete(&mut session, line, pos))
    }
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
        let on = ReplHelper {
            color: true,
            session: Rc::default(),
        };
        assert_eq!(
            on.highlight("if Some 1", 0),
            "\x1b[38;2;203;166;247mif\x1b[0m \x1b[38;2;249;226;175mSome\x1b[0m \x1b[38;2;250;179;135m1\x1b[0m"
        );
        let off = ReplHelper {
            color: false,
            session: Rc::default(),
        };
        assert_eq!(off.highlight("if Some 1", 0), "if Some 1");
        assert_eq!(off.highlight_prompt("sw> ", true), "sw> ");
    }

    #[test]
    fn result_has_value_and_type_apart() {
        assert_eq!(
            colour_result("42", "Nat"),
            "\x1b[38;2;250;179;135m42\x1b[0m\x1b[2m:\x1b[0m \x1b[38;2;249;226;175mNat\x1b[0m"
        );
    }
}
