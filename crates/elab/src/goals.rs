//! Goal holes, `?` (docs/proposals/lsp-goal-holes.md §4).
//!
//! A `?` checked against a type `T` becomes a fresh *frozen* metavariable
//! (`Globals::frozen_metas`) applied to the variables in scope: unification
//! never solves it, so nothing fills the hole in by accident. The goal (where
//! it is, `T`, and the names in scope) is noted, and checking carries on, so
//! every hole in a declaration is reported.
//!
//! The goals are printed at the end of the declaration, while the
//! metavariables in them are solved, as the navigation recorder prints
//! types (`nav.rs`); the ones an undone attempt noted are dropped with it
//! (`undo.rs`), and a hole checked twice keeps the last.
//!
//! A declaration with an open goal can never be finished: zonking a term
//! that still has a goal's metavariable in it fails with
//! [`UNFINISHED`] ([`Elaborator::zonk_around`]), so it's never sent to the
//! kernel. The module then reports the declaration as *unfinished*, not as
//! an error (`module.rs`); what uses it is unfinished too.

use stitchwort_core::globals::HashKey;
use stitchwort_core::globals::State;
use stitchwort_core::value::{Head, force};
use stitchwort_core::{Globals, Name, Term, Value, pretty};
use stitchwort_syntax::{Diagnostic, Span};

use crate::Elaborator;
use crate::check::Ctx;

/// The code of the error that stands for "unfinished": a term with an open
/// goal in it, or one that uses an unfinished declaration. The module turns
/// it into the declaration being unfinished, and never reports it as an
/// error; where it can't (an expression typed into `eval`), it reads as
/// one.
pub(crate) const UNFINISHED: &str = "E-UNFINISHED";

/// A goal noted, not printed yet.
#[derive(Clone)]
pub(crate) struct Pending {
    span: Span,
    /// The frozen metavariable standing for the hole.
    meta: usize,
    expected: Value,
    /// The context's display names, for printing.
    names: Vec<Name>,
    /// The entries of the context shown.
    context: Vec<Entry>,
    /// What the hole is in: "`addZero`".
    owner: String,
}

#[derive(Clone)]
struct Entry {
    /// As shown: `n`, or `n✝` for one that can't be referred to here.
    name: String,
    ty: Value,
    /// For a `let` of data, its value.
    value: Option<Value>,
}

/// The goals of the declaration being checked.
#[derive(Clone, Default)]
pub(crate) struct Goals {
    pending: Vec<Pending>,
    /// Printed, each with its span: one per span, the last checked there.
    found: Vec<(Span, Diagnostic)>,
}

/// The goal of a `match reify` `return` clause's `?`, written in terms of
/// the statement: its folded form, with the computation replaced by the
/// variable the clause binds, and the thunk by one that returns it. Only
/// what is shown: the hole's type, as checked, is the computed goal.
fn display_goal(cx: &Ctx) -> Option<Value> {
    let shown = cx.reify_display.as_ref()?;
    if shown.hole != cx.span {
        return None;
    }
    let result = cx.lookup(&shown.result)?;
    let level = cx.level();
    let base = shown.base;
    let done =
        |under: usize| Term::ctor(shown.comp, 0, vec![Term::Var(level + under - 1 - result)]);
    let hook = |t: &Term, under: usize| {
        if crate::matching::same_shifted(&shown.computation, t, under, 0) {
            return Some(done(under));
        }
        // A thunk of the computation: `() => y`.
        let Term::Lam(_, icit, body) = t.strip_loc() else {
            return None;
        };
        let applied_thunk = match (shown.thunk, body.strip_loc()) {
            (Some(thunk), Term::App(f, _, _)) => {
                matches!(f.strip_loc(), Term::Var(ix) if *ix == under + base - thunk)
            }
            _ => false,
        };
        (applied_thunk || crate::matching::same_shifted(&shown.computation, body, under + 1, 0))
            .then(|| Term::Lam("()".into(), *icit, std::rc::Rc::new(done(under + 1))))
    };
    let term = crate::lift::replace_with(
        cx.g(),
        &shown.folded,
        base,
        &|l| Ok(Term::Var(level - 1 - l)),
        &hook,
    )
    .ok()?;
    cx.eval(&term).ok()
}

/// `?` checked against `expected`: the hole's frozen metavariable, applied
/// to the variables in scope (those a case split hasn't replaced), as a
/// term. Notes the goal.
pub(crate) fn hole(cx: &Ctx, expected: &Value) -> Term {
    let g = cx.g();
    let m = g.new_meta(cx.span);
    g.freeze_meta(m);
    let mut term = Term::Meta(m);
    let mut context = Vec::new();
    for (level, value) in cx.env.iter().enumerate() {
        let own =
            matches!(value, Value::Neutral(Head::Var(l, _), s) if *l == level && s.is_empty());
        if own {
            term = Term::app(term, Term::Var(cx.level() - 1 - level));
        }
        let is_let = cx.lets[level].is_some();
        let name = &cx.names[level];
        // A variable a case split has replaced by a constructor is gone; a
        // compiler-made one (`%…`), or one bound as `_`, means nothing to the
        // reader.
        if !(own || is_let) || name.starts_with('%') || &**name == "_" {
            continue;
        }
        let name = match cx.name_of_level(level) {
            Some(n) => n.to_string(),
            None if name.ends_with('✝') => name.to_string(),
            None => format!("{name}✝"),
        };
        let ty = cx.types[level].clone();
        // A proof's value is its proof term: only its statement is shown.
        let shows_value = is_let && !crate::rewrite::is_proof_type(cx, &ty).unwrap_or(false);
        context.push(Entry {
            name,
            ty,
            value: shows_value.then(|| value.clone()),
        });
    }
    let shown = display_goal(cx);
    cx.e.goals.borrow_mut().pending.push(Pending {
        span: cx.span,
        meta: m,
        expected: shown.unwrap_or_else(|| expected.clone()),
        names: cx.names.clone(),
        context,
        owner: cx.e.goal_owner(),
    });
    term
}

/// The error a term with an open goal in it gives when it's finished
/// ([`UNFINISHED`]).
pub(crate) fn open_goal(span: Span) -> Diagnostic {
    Diagnostic::error(UNFINISHED, "this isn't finished: it has an open goal, `?`")
        .with_label(span, "write what goes here in place of the `?`")
}

/// The error for something that uses an unfinished declaration, at `span`
/// if known ([`UNFINISHED`]).
pub(crate) fn uses_unfinished(span: Option<Span>) -> Diagnostic {
    let d = Diagnostic::error(
        UNFINISHED,
        "this isn't finished: it uses a declaration with an open goal, `?`",
    );
    match span {
        Some(span) => d.with_label(span, "this uses a declaration that isn't finished"),
        None => d,
    }
}

/// The kernel refused a declaration because `terms` (its body, or type)
/// use a failed declaration: if every failed declaration they use is
/// unfinished, the refusal becomes [`UNFINISHED`]. `own` are the
/// declarations being admitted, failed by the refusal itself.
pub(crate) fn unfinished_dependency<'t>(
    g: &Globals,
    terms: impl IntoIterator<Item = &'t Term>,
    own: &[HashKey],
    error: Diagnostic,
) -> Diagnostic {
    if error.code != "E-FAILED-DEPENDENCY" || g.unfinished.borrow().is_empty() {
        return error;
    }
    let unfinished = g.unfinished.borrow();
    let mut any = false;
    for term in terms {
        for (t, _) in term.subterms() {
            let (key, state) = match t {
                Term::Def(id) if id.0 < g.defs.len() => (HashKey::Def(*id), g.def(*id).state()),
                Term::Data(d, _) | Term::Ctor(d, _, _) | Term::Case(_, d, _)
                    if d.0 < g.datas.len() =>
                {
                    (HashKey::Data(*d), g.data(*d).state())
                }
                _ => continue,
            };
            if state != State::Failed || own.contains(&key) {
                continue;
            }
            if !unfinished.contains(&key) {
                return error;
            }
            any = true;
        }
    }
    if any {
        uses_unfinished(error.primary_span())
    } else {
        error
    }
}

impl Elaborator {
    /// Whether metavariable `m` is an open goal's.
    pub(crate) fn is_goal(&self, m: usize) -> bool {
        self.goals.borrow().pending.iter().any(|p| p.meta == m)
    }

    /// Whether a goal noted, not printed yet, is at `span`.
    pub(crate) fn has_goal_at(&self, span: Span) -> bool {
        self.goals.borrow().pending.iter().any(|p| p.span == span)
    }

    /// How many goals are noted and not printed: a
    /// [`crate::undo::Snapshot`] keeps it, to drop the ones an undone
    /// attempt noted.
    pub(crate) fn pending_goals(&self) -> usize {
        self.goals.borrow().pending.len()
    }

    /// Drops the goals noted after the first `len`: their attempt was
    /// undone, and their metavariables with it.
    pub(crate) fn drop_goals_since(&self, len: usize) {
        self.goals.borrow_mut().pending.truncate(len);
    }

    /// What a goal noted now is in, for its heading.
    fn goal_owner(&self) -> String {
        let item = self.module.item.or(self.module.current.first().copied());
        match item.and_then(|i| self.module.items.get(i)) {
            Some(item) if item.kind == crate::module::Kind::Test => item.name.clone(),
            Some(item) => format!("`{}`", item.name),
            None => "this expression".to_string(),
        }
    }

    /// Prints the goals noted, while the metavariables in them still have
    /// their solutions. A goal at a span already printed replaces it.
    pub(crate) fn flush_goals(&self) {
        let pending = std::mem::take(&mut self.goals.borrow_mut().pending);
        if pending.is_empty() {
            return;
        }
        let g = &self.globals;
        // Printing a goal that mentions a failed declaration isn't an error
        // message showing it (`Globals::failed_mentioned`).
        let mentioned = g.failed_mentioned.get();
        let printed: Vec<(Span, Diagnostic)> = pending
            .iter()
            .map(|p| {
                // With gluing, as while checking: calls stay folded, also
                // under binders.
                let was = g.glue.replace(self.glue);
                let printed = self.print_goal(p);
                g.glue.set(was);
                (p.span, printed)
            })
            .collect();
        g.failed_mentioned.set(mentioned);
        let mut goals = self.goals.borrow_mut();
        for (span, d) in printed {
            goals.found.retain(|(s, _)| *s != span);
            goals.found.push((span, d));
        }
    }

    fn print_goal(&self, p: &Pending) -> Diagnostic {
        let g = &self.globals;
        let show = |v: &Value| pretty::value_for_goal(g, self, &p.names, v);
        let mut lines: Vec<String> = p
            .context
            .iter()
            .map(|e| match &e.value {
                Some(value) => format!("{}: {} := {}", e.name, show(&e.ty), show(value)),
                None => format!("{}: {}", e.name, show(&e.ty)),
            })
            .collect();
        // Forcing leaves a metavariable only if it's unsolved.
        let known = !matches!(
            force(g, p.expected.clone()),
            Ok(Value::Neutral(Head::Meta(_), _))
        );
        lines.push(if known {
            format!("⊢ {}", show(&p.expected))
        } else {
            "⊢ (the type here isn't known yet)".to_string()
        });
        Diagnostic::goal(format!("in {}", p.owner)).with_label(p.span, lines.join("\n"))
    }

    /// The goals printed since this was last called, in source order.
    pub(crate) fn take_goals(&self) -> Vec<Diagnostic> {
        self.flush_goals();
        let mut found = std::mem::take(&mut self.goals.borrow_mut().found);
        found.sort_by_key(|(s, _)| (s.file.index(), s.start));
        found.into_iter().map(|(_, d)| d).collect()
    }

    /// Forgets every goal, noted or printed.
    pub(crate) fn clear_goals(&self) {
        *self.goals.borrow_mut() = Goals::default();
    }
}
