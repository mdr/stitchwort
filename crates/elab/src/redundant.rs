//! `W-REDUNDANT`: an arm, or an alternative of an or-pattern, that is never
//! chosen because earlier arms match every value it matches. A compiled case
//! tree has a leaf for each place an arm is chosen, so an arm that's the
//! source of no leaf (and no absurd node) is redundant. The arms a case on
//! an indexed family drops because their constructor can't be there are
//! leaves of the tree, so they're left to `W-UNREACHABLE` (`families.rs`).

use stitchwort_syntax::ast::Pattern;
use stitchwort_syntax::{Diagnostic, Span};

use crate::{Elaborator, Row, Tree};

impl Elaborator {
    /// Warns about each of `rows` (the arms as written, before or-patterns
    /// are expanded), and each alternative of their or-patterns, that no
    /// node of `tree` comes from. Arms that share a span were made by the
    /// compiler, which can't point at them, and are left alone.
    pub(crate) fn warn_redundant(&self, rows: &[Row], tree: &Tree) {
        let mut chosen = Vec::new();
        arm_spans(tree, &mut chosen);
        let reached = |outer: Span| chosen.iter().any(|&span| within(span, outer));
        let mut found = Vec::new();
        for (i, row) in rows.iter().enumerate() {
            let shared =
                (rows.iter().enumerate()).any(|(k, other)| k != i && other.span == row.span);
            if shared || row.span == Span::NOWHERE {
                continue;
            }
            if !reached(row.span) {
                let mut warning = Diagnostic::warning(
                    "W-REDUNDANT",
                    "this arm can never be chosen: earlier arms match everything it matches",
                )
                .with_label(patterns_span(row), "never chosen");
                let pats: Vec<&Pattern> = row.pats.iter().map(|p| &**p).collect();
                let covering = rows[..i].iter().find(|earlier| {
                    (earlier.pats.iter().zip(&pats)).all(|(general, p)| subsumes(general, p))
                });
                warning = match covering {
                    Some(earlier) => warning.with_label(
                        patterns_span(earlier),
                        "this arm matches everything it does",
                    ),
                    None => warning.with_note("the earlier arms together cover it"),
                };
                found.push(warning);
                continue;
            }
            for (j, pattern) in row.pats.iter().enumerate() {
                let top_level = |alternative: &Pattern| {
                    rows[..i].iter().find(|earlier| {
                        (earlier.pats.iter().enumerate()).all(|(c, general)| {
                            let p = if c == j { alternative } else { &*row.pats[c] };
                            subsumes(general, p)
                        })
                    })
                };
                redundant_alternatives(pattern, &reached, Some(&top_level), &mut found);
            }
        }
        let mut warnings = self.lambda_warnings.borrow_mut();
        for warning in found {
            let span = warning.primary_span();
            let known =
                (warnings.iter()).any(|w| w.code == warning.code && w.primary_span() == span);
            if !known {
                warnings.push(warning);
            }
        }
    }
}

/// The span from an arm's first pattern to its last, or the arm's own.
fn patterns_span(row: &Row) -> Span {
    match (row.pats.first(), row.pats.last()) {
        (Some(first), Some(last)) if first.span().file == last.span().file => {
            first.span().to(last.span())
        }
        _ => row.span,
    }
}

/// Whether `inner` lies within `outer`.
fn within(inner: Span, outer: Span) -> bool {
    inner.file == outer.file && outer.start <= inner.start && inner.end <= outer.end
}

/// The spans of the arms (or alternatives) a compiled match's leaves and
/// absurd nodes come from.
fn arm_spans(tree: &Tree, out: &mut Vec<Span>) {
    match tree {
        Tree::Leaf {
            span, alternatives, ..
        } => {
            out.push(*span);
            out.extend(alternatives);
        }
        Tree::Absurd { span, .. } => out.push(*span),
        Tree::Missing { .. } => {}
        Tree::Case { branches, .. } => branches.iter().for_each(|(_, t)| arm_spans(t, out)),
        Tree::NumCase { arms, default, .. } => {
            arms.iter().for_each(|(_, t)| arm_spans(t, out));
            arm_spans(default, out);
        }
    }
}

/// An earlier arm that matches everything the arm does with an alternative
/// in place of its or-pattern (for an or-pattern that is a whole column).
type Covering<'f, 'r> = Option<&'f dyn Fn(&Pattern) -> Option<&'r Row<'r>>>;

/// Warns about each alternative of the or-patterns in `pattern` that no
/// node of the tree comes from, and looks inside those that some do.
fn redundant_alternatives<'r>(
    pattern: &Pattern,
    reached: &dyn Fn(Span) -> bool,
    covering: Covering<'_, 'r>,
    out: &mut Vec<Diagnostic>,
) {
    let inside =
        |p: &Pattern, out: &mut Vec<Diagnostic>| redundant_alternatives(p, reached, None, out);
    match pattern {
        Pattern::Or(alternatives, _) => {
            for (a, alternative) in alternatives.iter().enumerate() {
                if reached(alternative.span()) {
                    inside(alternative, out);
                    continue;
                }
                let mut warning = Diagnostic::warning(
                    "W-REDUNDANT",
                    "this alternative can never be chosen: earlier arms or alternatives match \
                     everything it matches",
                )
                .with_label(alternative.span(), "never chosen");
                let sibling = alternatives[..a]
                    .iter()
                    .find(|earlier| subsumes(earlier, alternative));
                if let Some(earlier) = sibling {
                    warning = warning.with_label(
                        earlier.span(),
                        "this alternative matches everything it does",
                    );
                } else if let Some(row) = covering.and_then(|find| find(alternative)) {
                    warning = warning
                        .with_label(patterns_span(row), "this arm matches everything it does");
                } else {
                    warning =
                        warning.with_note("the earlier arms and alternatives together cover it");
                }
                out.push(warning);
            }
        }
        Pattern::Ctor(_, args, _) => args.iter().for_each(|p| inside(p, out)),
        Pattern::Tuple(a, b, _) | Pattern::Cons(a, b, _) => {
            inside(a, out);
            inside(b, out);
        }
        Pattern::Record { fields, .. } | Pattern::CtorFields { fields, .. } => {
            fields.iter().for_each(|(_, p)| inside(p, out))
        }
        Pattern::Named(_, p, _) => inside(p, out),
        Pattern::Var(_)
        | Pattern::Wildcard(_)
        | Pattern::Absurd(_)
        | Pattern::Num(..)
        | Pattern::NegNum(..)
        | Pattern::Char(..)
        | Pattern::Nil(_) => {}
    }
}

/// Whether `general` matches every value `specific` does, as far as can be
/// told from the patterns as written: `false` when unsure.
fn subsumes(general: &Pattern, specific: &Pattern) -> bool {
    use Pattern::*;
    match (general, specific) {
        (Var(_) | Wildcard(_), _) => true,
        (_, Or(alternatives, _)) => alternatives.iter().all(|p| subsumes(general, p)),
        (Or(alternatives, _), _) => alternatives.iter().any(|p| subsumes(p, specific)),
        (Num(m, _), Num(n, _)) | (NegNum(m, _), NegNum(n, _)) => m == n,
        (Char(a, _), Char(b, _)) => a == b,
        (Nil(_), Nil(_)) => true,
        (Ctor(c, xs, _), Ctor(d, ys, _)) => {
            c.text == d.text
                && xs.len() == ys.len()
                && xs.iter().zip(ys).all(|(x, y)| subsumes(x, y))
        }
        (Tuple(a, b, _), Tuple(c, d, _)) | (Cons(a, b, _), Cons(c, d, _)) => {
            subsumes(a, c) && subsumes(b, d)
        }
        _ => false,
    }
}
