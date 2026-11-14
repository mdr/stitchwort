//! `W-ARROW-FORALL` (docs/proposals/forall-style-enforcement.md, D3462): a
//! statement written `(x: T) -> P` where `∀ (x: T) => P` is meant.
//!
//! It is one when the function type is a proposition over a type that is
//! not (`(h: P) -> Q` is an implication with a name for its proof), and a
//! bound name occurs in the body: a name nothing uses is an arrow, and
//! stays one.
//!
//! `->`, `∀ … =>` and a header's parameters give the same tree, so the
//! elaborator can only propose: [`note`] records a candidate at each
//! explicit binder group that fits, and [`keep_written_arrows`], run by
//! whoever has the file's text, keeps those whose group is followed by an
//! arrow.

use stitchwort_core::Sort;
use stitchwort_syntax::ast::{Expr, Name};
use stitchwort_syntax::{Diagnostic, FileId, Span};

use crate::Ctx;
use crate::module::{Ref, free_names_of};

pub const CODE: &str = "W-ARROW-FORALL";

/// Records a candidate for the function type over `names` (explicit, so
/// `hidden` false) whose domain ends at `dom_end`, with sorts `s1` for the
/// domain and `s2` for the body, which is `body` as written. A
/// type that isn't written (its span doesn't start before its first name)
/// is the elaborator's own.
#[allow(clippy::too_many_arguments)]
pub(crate) fn note(
    cx: &Ctx,
    names: &[Name],
    hidden: bool,
    dom_end: u32,
    body: &Expr,
    s1: Sort,
    s2: Sort,
    span: Span,
) {
    let [first, ..] = names else {
        return;
    };
    if hidden || s2 != Sort::Prop || s1 == Sort::Prop || first.span.start <= span.start {
        return;
    }
    // Read from the syntax: the elaborated body may hold unsolved
    // unknowns that mention every variable in scope.
    let used = free_names_of(body).iter().any(|r| match r {
        Ref::Name(n) | Ref::Dot(n, ..) => {
            let head = n.text.split('.').next().unwrap_or("");
            names.iter().any(|x| x.text != "_" && x.text == head)
        }
    });
    if !used {
        return;
    }
    let group = Span {
        file: span.file,
        start: span.start,
        end: dom_end + 1,
    };
    let mut seen = cx.e.attempt.lambda_warnings.borrow_mut();
    if seen
        .iter()
        .any(|w| w.code == CODE && w.labels.first().is_some_and(|l| l.span == group))
    {
        return;
    }
    seen.push(
        Diagnostic::warning(
            CODE,
            "this statement is written as a function type: `∀` is for a statement",
        )
        .with_label(group, "write `∀ (…) =>` instead of `(…) ->`")
        .with_note(
            "a statement quantified over a variable is `∀ (x: T) => P`; `(x: T) -> V` is for \
             a function type whose result is a type, and `A -> B` for an implication whose \
             hypothesis is unnamed. The quick fix \"Write ∀ instead of ->\" does it",
        ),
    );
}

/// Drops the candidates among `diagnostics` that aren't written with an
/// arrow after their binder group (a header's parameter, a `∀`).
/// `text` is the text of a file.
pub fn keep_written_arrows<'a>(
    diagnostics: &mut Vec<Diagnostic>,
    text: impl Fn(FileId) -> Option<&'a str>,
) {
    diagnostics.retain(|d| {
        d.code != CODE
            || d.labels.first().is_some_and(|l| {
                let rest = text(l.span.file).and_then(|t| t.get(l.span.end as usize..));
                rest.is_some_and(|rest| {
                    let rest = rest
                        .trim_start_matches(|c: char| c.is_whitespace() || c == ')' || c == ']');
                    rest.starts_with("->") || rest.starts_with('→')
                })
            })
    });
}
