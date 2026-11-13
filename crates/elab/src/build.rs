//! Building a test fact from a proof of its reading (D3549a,
//! docs/proposals/bool-as-proposition-building.md).
//!
//! Where a test fact `e = True` or `e = False` is expected and the term
//! given proves one of its readings (`m: x ∈ xs` where `xs.contains x` is
//! expected), the term is wrapped in the reading's way back. This is never
//! a step of the first check: the mismatch there only records where a build
//! would fit ([`site`], the diagnostic's `build` field), and the body is
//! checked again from clean state with a build allowed at that place
//! ([`Elaborator::with_local_retries`]). So a body that checks without a
//! build never meets one, and keeps its meaning whatever fall-backs it took
//! (SW-3105 §4.2, form R).
//!
//! [`Elaborator::with_local_retries`]: crate::Elaborator

use stitchwort_core::value::{Head, conv, force};
use stitchwort_core::{Icit, Term, Value};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, Result};
use crate::reading::Candidates;

/// The most places one body builds at: past it, the error is reported.
pub(crate) const CAP: usize = 8;

/// [`crate::state::Decl::builds`].
#[derive(Default)]
pub(crate) struct Builds {
    /// The places a build is allowed at, in the order the failures named
    /// them.
    pub(crate) allowed: Vec<Span>,
    /// What the current attempt built: where, and what the build was, for
    /// a later error inside it.
    pub(crate) made: Vec<(Span, String)>,
    /// The ends of the `.read`s written in the body: a term read and then
    /// built would turn one test into another with the same reading, so a
    /// written `.read` is never built from.
    pub(crate) reads: Vec<Span>,
}

impl Builds {
    pub(crate) fn is_empty(&self) -> bool {
        self.allowed.is_empty() && self.made.is_empty() && self.reads.is_empty()
    }
}

/// Notes the `.read` whose field is written at `field`.
pub(crate) fn note_read(cx: &Ctx, field: Span) {
    cx.e.decl.builds.borrow_mut().reads.push(field);
}

/// Whether `term` is `Refl`, which is the equation itself: never a proof
/// of a reading (§6.1).
fn is_refl(term: &Term) -> bool {
    matches!(term.strip_loc(), Term::Refl)
}

/// Whether the term checked at the current span is a written `.read`.
fn is_read(cx: &Ctx) -> bool {
    let at = cx.span;
    cx.e.decl
        .builds
        .borrow()
        .reads
        .iter()
        .any(|r| r.file == at.file && r.end == at.end)
}

/// Whether a value is an unknown not solved yet: nothing can be said
/// about what it fits.
fn blocked(cx: &Ctx, ty: &Value) -> Result<bool> {
    Ok(matches!(
        force(&cx.g(), ty.clone())?,
        Value::Neutral(Head::Meta(_), _)
    ))
}

/// Whether `a` and `b` could be the same type: the same kind of type with
/// the same head once computed, or one of them an unknown. Most failed
/// comparisons against a test fact are of types nothing like its readings
/// (an `auto` search trying hypotheses, say), and this keeps them from
/// unifying in depth, deep in a search, only to fail.
fn alike(cx: &Ctx, a: &Value, b: &Value) -> Result<bool> {
    let g = &cx.g();
    Ok(match (force(g, a.clone())?, force(g, b.clone())?) {
        (Value::Neutral(Head::Meta(_), _), _) | (_, Value::Neutral(Head::Meta(_), _)) => true,
        (Value::Pi(..), Value::Pi(..)) | (Value::Eq(..), Value::Eq(..)) => true,
        (Value::Data(d, _), Value::Data(e, _)) => d == e,
        (Value::Neutral(Head::Def(f), _), Value::Neutral(Head::Def(h), _)) => f == h,
        (Value::Neutral(Head::Var(l, _), _), Value::Neutral(Head::Var(m, _), _)) => l == m,
        (Value::Call(f, ..), Value::Call(h, ..)) => f == h,
        _ => false,
    })
}

/// The first of `candidates` that `found` is a proof of: the same type,
/// or one it unifies with. With `keep`, what unifying solved is kept;
/// otherwise it is taken back.
fn fitting(
    cx: &mut Ctx,
    candidates: &Candidates,
    found: &Value,
    keep: bool,
) -> Result<Option<usize>> {
    for (k, candidate) in candidates.list.iter().enumerate() {
        if !alike(cx, &candidate.prop, found)? {
            continue;
        }
        if conv(&cx.g(), cx.level(), &candidate.prop, found)? {
            return Ok(Some(k));
        }
        let fits = if keep {
            crate::undo::unify(cx, found, &candidate.prop)?
        } else {
            let snapshot = crate::undo::Snapshot::take(cx);
            let unified = cx.unify(found, &candidate.prop);
            snapshot.restore(cx);
            // A failure here only means it doesn't fit.
            matches!(unified, Ok(true))
        };
        if fits {
            return Ok(Some(k));
        }
    }
    Ok(None)
}

/// The first of `candidates` a lambda can be checked against: one that is
/// a function type (a `¬`, `≠`, `∉` or `∀` reading, or the plain
/// `¬(e = True)`).
fn for_lambda(cx: &Ctx, candidates: &Candidates) -> Result<Option<usize>> {
    for (k, candidate) in candidates.list.iter().enumerate() {
        if matches!(
            force(&cx.g(), candidate.prop.clone())?,
            Value::Pi(_, Icit::Explicit, ..)
        ) {
            return Ok(Some(k));
        }
    }
    Ok(None)
}

fn allowed(cx: &Ctx, at: Span) -> bool {
    cx.e.decl.builds.borrow().allowed.contains(&at)
}

/// What building the fact from candidate `k` means, for hover and
/// messages.
fn described(cx: &Ctx, candidates: &Candidates, k: usize) -> String {
    let candidate = &candidates.list[k];
    let by = if candidates.plain && k + 1 == candidates.list.len() {
        String::new()
    } else {
        format!(" (by {})", candidate.last(cx))
    };
    format!(
        "builds the test fact `{}` from a proof of `{}`{by}",
        cx.show(&candidates.fact),
        cx.show(&candidate.prop)
    )
}

/// Records the build of candidate `k` at `at`: before the term is
/// checked, so an error inside it can say what it was checked as.
fn record(cx: &Ctx, at: Span, hover: Span, candidates: &Candidates, k: usize) {
    let what = described(cx, candidates, k);
    cx.e.note_build(hover, what.clone());
    cx.e.decl.builds.borrow_mut().made.push((at, what));
}

/// For `compare`, once everything else has failed: where a build is
/// allowed at the current span and `term` (of type `found`) proves a
/// candidate of `expected`, the fact built from it.
pub(crate) fn build(
    cx: &mut Ctx,
    term: &Term,
    found: &Value,
    expected: &Value,
) -> Result<Option<Term>> {
    let at = cx.span;
    if !allowed(cx, at) || is_refl(term) || is_read(cx) || blocked(cx, found)? {
        return Ok(None);
    }
    let Some(candidates) = crate::reading::candidates(cx, expected)? else {
        return Ok(None);
    };
    let Some(k) = fitting(cx, &candidates, found, true)? else {
        return Ok(None);
    };
    record(cx, at, at, &candidates, k);
    Ok(Some(candidates.list[k].backward(cx, term.clone())?))
}

/// What a mismatch in `compare` says about building (§2.2, §4).
pub(crate) enum Site {
    /// A build would fit at this span: the declaration is checked again.
    At(Span),
    /// None would; a note on what would be accepted.
    Note(String),
    Nothing,
}

/// For `compare`'s mismatch, `term` (of type `found`) where `expected` is
/// expected. Nothing it unifies is kept.
pub(crate) fn site(cx: &mut Ctx, term: &Term, found: &Value, expected: &Value) -> Result<Site> {
    if !cx.e.options.build || is_refl(term) {
        return Ok(Site::Nothing);
    }
    let Some(candidates) = crate::reading::candidates(cx, expected)? else {
        return Ok(Site::Nothing);
    };
    let fits = !blocked(cx, found)? && fitting(cx, &candidates, found, false)?.is_some();
    if fits && is_read(cx) {
        return Ok(Site::Note(format!(
            "`.read` gives the proposition, and it isn't built back into the test fact \
             `{}`: give the proof of `{}` itself",
            cx.show(&candidates.fact),
            cx.show(found)
        )));
    }
    if fits {
        return Ok(Site::At(cx.span));
    }
    Ok(match no_fit_note(cx, &candidates)? {
        Some(note) => Site::Note(note),
        None => Site::Nothing,
    })
}

/// For a mismatch where a test fact is expected and what is given fits
/// none of its candidates: what it can be built from, named by the first
/// candidate that isn't a test fact again. None where every reading is
/// (`n < m`, which is `Nat.leq (Succ n) m = True`, reads as `Succ n ≤ m`:
/// saying so would only confuse).
fn no_fit_note(cx: &Ctx, candidates: &Candidates) -> Result<Option<String>> {
    let mut first = None;
    for (k, candidate) in candidates.list.iter().enumerate() {
        if crate::reading::test_fact(cx, &candidate.prop)?.is_none() {
            first = Some((k, &candidate.prop));
            break;
        }
    }
    let Some((k, first)) = first else {
        return Ok(None);
    };
    let fact = cx.show(&candidates.fact);
    if candidates.plain && k + 1 == candidates.list.len() {
        return Ok(Some(format!(
            "this expects the test fact `{fact}`: a proof of `{}` is accepted here",
            cx.show(first)
        )));
    }
    let compound = match force(&cx.g(), first.clone())? {
        Value::Data(d, _) if crate::reading::readable_data(cx, d) => {
            Some(crate::reading::constructors_shown(cx, d))
        }
        _ => None,
    };
    Ok(Some(match compound {
        Some(ctor) => format!(
            "this expects the test fact `{fact}`, which reads as `{}`: build it part by part \
             with {ctor}, each part from a proof of its own reading",
            cx.show(first)
        ),
        None => format!(
            "this expects the test fact `{fact}`, which reads as `{}`: a proof of that is \
             accepted here",
            cx.show(first)
        ),
    }))
}

/// For a lambda checked against `expected`, which isn't a function type:
/// where `expected` is a test fact with a candidate that is one, the
/// lambda built into the fact if a build is allowed at `at`, or else the
/// error `error` with the place recorded. What it built shows on hover
/// over `first_binder`.
pub(crate) fn lambda(
    cx: &mut Ctx,
    at: Span,
    first_binder: Span,
    expected: &Value,
    error: Diagnostic,
    check: impl FnOnce(&mut Ctx, &Value) -> Result<Term>,
) -> Result<Term> {
    if !cx.e.options.build {
        return Err(error);
    }
    let Some(candidates) = crate::reading::candidates(cx, expected)? else {
        return Err(error);
    };
    let Some(k) = for_lambda(cx, &candidates)? else {
        return Err(error);
    };
    if !allowed(cx, at) {
        return Err(error.with_build(at));
    }
    // Hover shows it on the first binder: the lambda as a whole is no
    // reference.
    record(cx, at, first_binder, &candidates, k);
    let proof = check(cx, &candidates.list[k].prop.clone())?;
    candidates.list[k].backward(cx, proof)
}

/// Before an attempt at a body: forgets what the last one built and read.
pub(crate) fn start_attempt(e: &crate::Elaborator) {
    let mut builds = e.decl.builds.borrow_mut();
    builds.made.clear();
    builds.reads.clear();
}

/// After an attempt at a body failed with `d`: `Ok(())` if it is to be
/// checked again with a build allowed at the place `d` names, or else the
/// error to report, with a note where it is inside something built.
pub(crate) fn again(e: &crate::Elaborator, d: Diagnostic) -> std::result::Result<(), Diagnostic> {
    let mut builds = e.decl.builds.borrow_mut();
    let mut d = d;
    if let Some(at) = d.build_site()
        && !builds.allowed.contains(&at)
    {
        if builds.allowed.len() < CAP {
            builds.allowed.push(at);
            return Ok(());
        }
        d = d.with_note(format!(
            "the compiler built {CAP} test facts in this declaration and stops there: build \
             this one by hand"
        ));
    }
    let d = d.without_build();
    let inside = d.primary_span().and_then(|p| {
        builds
            .made
            .iter()
            .find(|(s, _)| s.file == p.file && s.start <= p.start && p.end <= s.end)
    });
    Err(match inside {
        Some((_, what)) => d.with_note(format!("here, the compiler {what}")),
        None => d,
    })
}
