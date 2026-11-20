//! `W-REWRITE-THEN-COMPUTING` and `W-REWRITE-THEN-REWRITE` (SW-3648): two
//! spellings of a goal `rewrite` that have a shorter one with the same
//! meaning (docs/syntax.md, `rewrite`).
//!
//! - `rewrite p then byComputing` is `rewrite p`: without `then`, the
//!   goal left by the rules is closed with `byComputing` (`rewrite_goal`).
//! - `rewrite a then rewrite b` is `rewrite a, b`: the rules apply left to
//!   right, each to what the one before left.
//!
//! Both are found in the written syntax, and only for a rewrite of the
//! goal: `rewrite … at h` and `rewrite repeatedly` close or continue
//! differently. The quick fixes (`crates/driver/src/fixes.rs`) delete or
//! replace the span of the first label.

use stitchwort_syntax::ast::{Decl, Expr, Guard};
use stitchwort_syntax::{Diagnostic, Span};

use crate::proof_chain::sub_expressions;

pub(crate) const COMPUTING: &str = "W-REWRITE-THEN-COMPUTING";
pub(crate) const REWRITE: &str = "W-REWRITE-THEN-REWRITE";
/// A rewrite a guard's refinement made pointless (`rewrite.rs`, D3701).
pub(crate) const GUARD_REFINED: &str = "W-REWRITE-GUARD-REFINED";

/// The `then` span and body of `e` if it is a rewrite of the goal that has
/// both.
fn goal_rewrite_then(e: &Expr) -> Option<(Span, &Expr)> {
    match e {
        Expr::Rewrite {
            target: None,
            repeatedly: None,
            then: Some(then),
            body: Some(body),
            ..
        } => Some((*then, body)),
        _ => None,
    }
}

fn is_goal_rewrite(e: &Expr) -> bool {
    matches!(
        e,
        Expr::Rewrite {
            target: None,
            repeatedly: None,
            ..
        }
    )
}

/// The warnings for the bodies of `equations`.
pub(crate) fn warnings(equations: &[Decl]) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut stack: Vec<&Expr> = Vec::new();
    for equation in equations {
        if let Decl::Equation { guard, rhs, .. } = equation {
            if let Some(Guard { cond, .. }) = guard {
                stack.push(cond);
            }
            stack.extend(rhs.iter());
        }
    }
    let mut children: Vec<&Expr> = Vec::new();
    while let Some(e) = stack.pop() {
        // A bracketed body (`then (rewrite b …)`) isn't joined: the brackets
        // would be left unmatched.
        if let Some((then, body)) = goal_rewrite_then(e) {
            match body {
                Expr::Var(n) if n.text == "byComputing" => {
                    out.push(computing(then, body.span()));
                }
                Expr::Rewrite { keyword, .. } if is_goal_rewrite(body) => {
                    out.push(chained(then, *keyword));
                }
                _ => {}
            }
        }
        children.clear();
        sub_expressions(e, &mut children);
        stack.extend(children.iter().copied());
    }
    out.sort_by_key(|d| d.labels.first().map_or(0, |l| l.span.start));
    out
}

fn computing(then: Span, end: Span) -> Diagnostic {
    Diagnostic::warning(
        COMPUTING,
        "`rewrite … then byComputing` is `rewrite …`: closing the goal by computing is what a rewrite without `then` does",
    )
    .with_label(
        Span {
            file: then.file,
            start: then.start,
            end: end.end,
        },
        "drop this",
    )
    .with_note("the quick fix \"Drop `then byComputing`\" does it (docs/syntax.md, `rewrite`)")
}

fn chained(then: Span, keyword: Span) -> Diagnostic {
    Diagnostic::warning(
        REWRITE,
        "`rewrite a then rewrite b` is `rewrite a, b`: the rules of one `rewrite` apply left to right",
    )
    .with_label(
        Span {
            file: then.file,
            start: then.start,
            end: keyword.end,
        },
        "write a comma here",
    )
    .with_note("the quick fix \"Join into one `rewrite`\" does it (docs/syntax.md, `rewrite`)")
}
