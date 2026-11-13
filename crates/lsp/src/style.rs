//! The quick fixes for how a statement is written: "Move ∀ variables before
//! the colon" for `W-THEOREM-FORALL` (docs/proposals/theorem-binders.md §6,
//! D3470) and "Write ∀ instead of ->" for `W-ARROW-FORALL`
//! (docs/proposals/forall-style-enforcement.md, D3462).
//!
//! Both are text edits worked out from the file's text and the diagnostic's
//! range, so they answer at once. The first is `stitchwort sweep
//! theorem-binders`' rewrite of that one theorem; it is offered without the
//! trial check the sweep runs on a project (the statement's hash held), since
//! the checked project lives on the checker thread. The server does not yet
//! say whether the hash held; the sweep does.

use std::collections::BTreeSet;

use lsp_types::{Range, TextEdit};
use stitchwort_driver::binder_sweep;

use super::{offset_at, position_at};

pub const THEOREM_FORALL: &str = binder_sweep::WARNING;
pub const ARROW_FORALL: &str = "W-ARROW-FORALL";

/// The title of the quick fix for `code`, if it has one.
pub fn title(code: &str) -> Option<&'static str> {
    match code {
        THEOREM_FORALL => Some("Move ∀ variables before the colon"),
        ARROW_FORALL => Some("Write ∀ instead of ->"),
        _ => None,
    }
}

/// The edits for the warning `code` at `at` in `text`, or none if the text
/// has moved on since the warning.
pub fn edits(text: &str, code: &str, at: Range) -> Vec<TextEdit> {
    let (from, to) = (offset_at(text, at.start), offset_at(text, at.end));
    match code {
        THEOREM_FORALL => theorem(text, from, to).into_iter().collect(),
        ARROW_FORALL => arrow(text, from, to),
        _ => Vec::new(),
    }
}

/// The sweep's rewrite of the theorem whose statement's `∀` is at
/// `from..to`, with its layout finished by the formatter.
fn theorem(text: &str, from: usize, to: usize) -> Option<TextEdit> {
    let outcome = binder_sweep::sweep(text, &BTreeSet::new()).ok()?;
    let c = outcome
        .converted
        .iter()
        .find(|c| c.forall == (from as u32, to as u32))?;
    let after = match stitchwort_fmt::format(&c.after) {
        Ok(formatted) => formatted.trim_end().to_string(),
        Err(_) => c.after.clone(),
    };
    let (start, end) = (c.range.0 as usize, c.range.1 as usize);
    Some(TextEdit::new(
        Range::new(position_at(text, start), position_at(text, end)),
        after,
    ))
}

/// `∀ ` before the binder group at `from..to` and `=>` for the arrow after
/// it.
fn arrow(text: &str, from: usize, to: usize) -> Vec<TextEdit> {
    let Some(rest) = text.get(to..) else {
        return Vec::new();
    };
    let skipped = rest.len() - rest.trim_start().len();
    let arrow_at = to + skipped;
    let arrow_len = if text[arrow_at..].starts_with("->") {
        2
    } else if text[arrow_at..].starts_with('→') {
        '→'.len_utf8()
    } else {
        return Vec::new();
    };
    let at = |offset| position_at(text, offset);
    vec![
        TextEdit::new(Range::new(at(from), at(from)), "∀ ".to_string()),
        TextEdit::new(
            Range::new(at(arrow_at), at(arrow_at + arrow_len)),
            "=>".to_string(),
        ),
    ]
}
