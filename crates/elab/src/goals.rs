//! Goal holes, `?` (docs/proposals/lsp-goal-holes.md §4).
//!
//! A `?` checked against a type `T` becomes a fresh *frozen* metavariable
//! (`MetaStore::frozen_metas`) applied to the variables in scope: unification
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
use stitchwort_core::pretty::{Declaration, NameScope};
use stitchwort_core::value::{Head, force, quote_shown};
use stitchwort_core::{Ev, Icit, Name, Sort, Term, Value, pretty};
use stitchwort_syntax::{Diagnostic, FileId, GoalData, Hypothesis, Span};

use crate::Elaborator;
use crate::check::Ctx;
use crate::scope::Resolved;
use crate::state::Tables;

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
    /// The type checked against, as it is (`expected` may be a display
    /// form of it), for [`GoalSnapshot`].
    target: Value,
    /// The context's display names, for printing.
    names: Vec<Name>,
    /// The entries of the context shown.
    context: Vec<Entry>,
    /// The context's own variables not shown (a compiler-made `%x`, a `_`):
    /// each one's level and type, for [`GoalSnapshot`].
    hidden: Vec<(usize, Value)>,
    /// How many hypotheses a later one of the same name replaced, and
    /// nothing shown mentions, aren't listed ([`drop_superseded`]).
    superseded: usize,
    /// What the hole is in: "`addZero`".
    owner: String,
    /// What a lemma of the goal is named after: the declaration's name less
    /// its namespace (`addZero`); `None` in a test or an expression, or for
    /// a name that isn't a plain one.
    lemma_base: Option<String>,
    /// Whether the goal is a proposition, if that was known when the hole
    /// was checked: a lemma of it is then a `theorem`, else a `def`.
    prop: Option<bool>,
    /// The definition being elaborated, whose recursive call is the
    /// induction hypothesis at the goal (SW-993).
    owner_def: Option<stitchwort_core::DefId>,
    /// What the definition's parameters stand for at the goal: the
    /// context's first variables as they are there (`Cons x rest` for a
    /// list a case split took apart), at most one for each of its type's
    /// binders.
    owner_args: Vec<Value>,
}

#[derive(Clone)]
struct Entry {
    /// As shown: `n`, or `n✝` for one that can't be referred to here.
    name: String,
    ty: Value,
    /// For a `let` of data, its value.
    value: Option<Value>,
    /// Its level in the context.
    level: usize,
}

/// A goal printed: its diagnostic, and the lemma it makes, less the
/// lemma's name ([`Elaborator::take_goals`] numbers them).
#[derive(Clone)]
struct Found {
    span: Span,
    diagnostic: Diagnostic,
    /// [`Pending::lemma_base`].
    base: Option<String>,
    /// The lemma's keyword, and what follows its name.
    lemma: Option<(&'static str, String)>,
}

/// The goals of the declaration being checked.
#[derive(Clone, Default)]
pub(crate) struct Goals {
    pending: Vec<Pending>,
    /// Printed: one per span, the last checked there.
    found: Vec<Found>,
    /// The context asked for at a position ([`Elaborator::probe_context`]).
    probe: Probe,
}

/// The context at a position, asked for before checking: the smallest
/// expression containing it notes its type and the names in scope, printed
/// at the end of the declaration with the goals.
#[derive(Clone, Default)]
struct Probe {
    want: Option<(FileId, u32)>,
    pending: Option<ProbePending>,
    found: Option<ContextAt>,
    /// Completion after a `.`: where the name after it starts
    /// ([`Elaborator::probe_members`]), and what can be written there.
    members_at: Option<(FileId, u32)>,
    members: Option<Vec<crate::nav::ScopeName>>,
}

#[derive(Clone)]
struct ProbePending {
    span: Span,
    ty: Value,
    checked: bool,
    names: Vec<Name>,
    context: Vec<Entry>,
}

/// What is known at a position of a file: see [`Elaborator::probe_context`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContextAt {
    /// The smallest expression containing the position (or touching it).
    pub span: Span,
    /// Its type: the one it was checked against (`checked`), else the one
    /// found for it.
    pub ty: String,
    pub checked: bool,
    /// The names in scope there, as a goal lists them (a variable before
    /// anything whose type mentions it).
    pub locals: Vec<Hypothesis>,
}

/// The names in scope where a goal at `span` is printed: the file's, as for
/// a message, and also what `a == b` elaborates to there, so that a decided
/// equation is printed as the `a == b` that gives it back.
struct GoalScope<'e> {
    e: &'e Elaborator,
    span: Span,
}

impl NameScope for GoalScope<'_> {
    fn names(&self, written: &str, declaration: Declaration) -> bool {
        self.e.names(written, declaration)
    }

    fn full_name(&self, declaration: Declaration) -> String {
        self.e.full_name(declaration)
    }

    fn aliases(&self, full: &str) -> Vec<String> {
        self.e.aliases(full)
    }

    fn method(
        &self,
        projection: stitchwort_core::DefId,
    ) -> Option<(stitchwort_core::DefId, String)> {
        self.e.method_of(projection)
    }

    /// What `a == b` decides `a = b` by, for a `ty` that mentions no
    /// variable: `decide_eq_of`, as `a == b` finds it
    /// (`numbers::equation`, `bind::decide_written`), on placeholder
    /// sides; what it applies to the sides (`Nat.decEq`, or `List.decEq
    /// [Nat] (x y => Nat.decEq x y)` with the items' decision), if that's
    /// all it is and the placeholders are nowhere else. Everything the
    /// search did is undone.
    fn eq_decision(&self, ty: &Term) -> Option<Term> {
        let closed = ty.subterms().all(|(t, binders)| match t {
            Term::Var(i) | Term::Case(i, ..) | Term::NumCase(i, ..) => *i < binders,
            Term::Meta(_) => false,
            _ => true,
        });
        if !closed {
            return None;
        }
        let mut cx = Ctx::new(self.e, self.span);
        let mut found = None;
        crate::undo::transaction(&mut cx, |cx| {
            let ty = cx.eval(ty)?;
            let side = Term::Sort(Sort::Prop);
            let decision = crate::interfaces::decide_eq_of(cx, &ty, side.clone(), side.clone())?;
            let decision = cx.e.zonk(&decision, 0)?;
            let is_side = |t: &Term| matches!(t, Term::Sort(_));
            if let Term::App(f, y, Icit::Explicit) = decision.strip_loc()
                && let Term::App(f, x, Icit::Explicit) = f.strip_loc()
                && is_side(x.strip_loc())
                && is_side(y.strip_loc())
                && matches!(f.spine().0.strip_loc(), Term::Def(_))
                && !f.subterms().any(|(t, _)| is_side(t))
            {
                found = Some((**f).clone());
            }
            Ok(None::<()>)
        })
        .ok()?;
        found
    }
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
        &cx.g(),
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
    let m = cx.metas().new_meta(cx.span);
    cx.metas().freeze_meta(m);
    let mut term = Term::Meta(m);
    // Each variable as its hypothesis is named, `n✝` for one that can't be
    // referred to here, numbered where two would be alike (SW-1000).
    let shown_names = cx.shown_names(true);
    for (level, value) in cx.env.iter().enumerate() {
        let own =
            matches!(value, Value::Neutral(Head::Var(l, _), s) if *l == level && s.is_empty());
        if own {
            term = Term::app(term, Term::Var(cx.level() - 1 - level));
        }
    }
    let (mut context, mut hidden) = scope_entries(cx, &shown_names);
    let superseded = drop_superseded(cx, expected, &mut context, &mut hidden);
    let context = dependency_order(&g, cx.level(), context);
    let prop = match force(&g, expected.clone()) {
        Ok(Value::Neutral(Head::Meta(_), _)) | Err(_) => None,
        Ok(_) => crate::rewrite::is_proof_type(cx, expected).ok(),
    };
    let shown = display_goal(cx);
    let (owner, lemma_base) = cx.e.goal_owner();
    let owner_def = cx.e.owner_def();
    let owner_args = match owner_def {
        Some(d) => {
            let mut binders = 0;
            let mut t = g.def(d).ty().strip_loc();
            while let Term::Pi(_, _, _, cod) = t {
                binders += 1;
                t = cod.strip_loc();
            }
            cx.env.iter().take(binders).cloned().collect()
        }
        None => Vec::new(),
    };
    cx.e.goals.borrow_mut().pending.push(Pending {
        span: cx.span,
        meta: m,
        expected: shown.unwrap_or_else(|| expected.clone()),
        target: expected.clone(),
        names: shown_names,
        context,
        hidden,
        superseded,
        owner,
        lemma_base,
        prop,
        owner_def,
        owner_args,
    });
    term
}

/// The variables in scope at `cx` as a goal lists them (not yet in
/// dependency order), and the context's own variables it leaves out:
/// each one's level and type.
fn scope_entries(cx: &Ctx, shown_names: &[Name]) -> (Vec<Entry>, Vec<(usize, Value)>) {
    let mut context = Vec::new();
    let mut hidden = Vec::new();
    for (level, value) in cx.env.iter().enumerate() {
        let own =
            matches!(value, Value::Neutral(Head::Var(l, _), s) if *l == level && s.is_empty());
        let is_let = cx.lets[level].is_some();
        let name = &cx.names[level];
        // A variable a case split has replaced by a constructor is gone; a
        // compiler-made one (`%…`), or one bound as `_`, means nothing to the
        // reader.
        if !(own || is_let) || name.starts_with('%') || &**name == "_" {
            if own {
                hidden.push((level, cx.types[level].clone()));
            }
            continue;
        }
        let name = shown_names[level].to_string();
        let ty = cx.types[level].clone();
        // A proof's value is its proof term: only its statement is shown.
        let shows_value = is_let && !crate::rewrite::is_proof_type(cx, &ty).unwrap_or(false);
        context.push(Entry {
            name,
            ty,
            value: shows_value.then(|| value.clone()),
            level,
        });
    }
    (context, hidden)
}

/// Takes out of `context` the hypotheses a later one of the same name
/// replaced (a `match` on them, or `rewrite … at`, binds a new one:
/// `cases::stale`) that neither the target nor a hypothesis listed
/// mentions, so that a goal after several `match`es lists each hypothesis
/// once, not every earlier version as `read✝` (SW-1000). How many were
/// taken out. Those bound by a `λ` stay in `hidden`, for [`GoalSnapshot`].
fn drop_superseded(
    cx: &Ctx,
    expected: &Value,
    context: &mut Vec<Entry>,
    hidden: &mut Vec<(usize, Value)>,
) -> usize {
    let g = cx.g();
    let level = cx.level();
    let stale: Vec<usize> = (context.iter())
        .filter(|e| crate::cases::stale(cx, e.level))
        .map(|e| e.level)
        .collect();
    if stale.is_empty() {
        return 0;
    }
    // The levels the target and the other hypotheses mention; all of them
    // if one can't be read back.
    let mut mentioned: Vec<usize> = Vec::new();
    let mut values = vec![expected];
    for e in context.iter().filter(|e| !stale.contains(&e.level)) {
        values.push(&e.ty);
        values.extend(e.value.as_ref());
    }
    for v in values {
        match quote_shown(&g, level, v)
            .ok()
            .and_then(|t| levels_in(&t, level))
        {
            Some(levels) => mentioned.extend(levels),
            None => return 0,
        }
    }
    let before = context.len();
    context.retain(|e| {
        let keep = !stale.contains(&e.level) || mentioned.contains(&e.level);
        if !keep && e.value.is_none() && cx.lets[e.level].is_none() {
            hidden.push((e.level, e.ty.clone()));
        }
        keep
    });
    before - context.len()
}

/// The context's entries in an order that shows a variable before a
/// hypothesis whose type (or value) mentions it, keeping the context's own
/// order elsewhere. A `match`'s equation is bound before the pattern
/// variables it mentions, and a case split can refine a hypothesis with a
/// later variable; either way, the goal must not read as if the variable
/// were free in it. This is the order [`GoalSnapshot`] uses.
fn dependency_order(g: &Ev, level: usize, context: Vec<Entry>) -> Vec<Entry> {
    let known: Vec<usize> = context.iter().map(|e| e.level).collect();
    let mut needs: Vec<Vec<usize>> = Vec::with_capacity(context.len());
    for e in &context {
        let mut need = match quote_shown(g, level, &e.ty)
            .ok()
            .and_then(|term| levels_in(&term, level))
        {
            Some(levels) => levels,
            None => return context,
        };
        if let Some(value) = &e.value {
            let Some(levels) = quote_shown(g, level, value)
                .ok()
                .and_then(|term| levels_in(&term, level))
            else {
                return context;
            };
            need.extend(levels);
        }
        need.retain(|l| *l != e.level && known.contains(l));
        needs.push(need);
    }
    let mut slots: Vec<Option<Entry>> = context.into_iter().map(Some).collect();
    let mut order = Vec::with_capacity(slots.len());
    let mut placed: Vec<usize> = Vec::new();
    while order.len() < slots.len() {
        let Some(next) = (0..slots.len())
            .find(|i| slots[*i].is_some() && needs[*i].iter().all(|l| placed.contains(l)))
        else {
            // Not well-founded (which a well-typed context isn't): keep
            // what is left in its own order rather than lose it.
            order.extend(slots.into_iter().flatten());
            break;
        };
        let entry = slots[next].take().expect("chosen unfilled");
        placed.push(entry.level);
        order.push(entry);
    }
    order
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
    g: &Ev,
    tables: &Tables,
    terms: impl IntoIterator<Item = &'t Term>,
    own: &[HashKey],
    error: Diagnostic,
) -> Diagnostic {
    if error.code != "E-FAILED-DEPENDENCY" || tables.unfinished_count() == 0 {
        return error;
    }
    let mut any = false;
    for term in terms {
        for (t, _) in term.subterms() {
            let (key, state) = match t {
                Term::Def(id) if id.0 < g.env.defs().len() => {
                    (HashKey::Def(*id), g.def(*id).state())
                }
                Term::Data(d, _) | Term::Ctor(d, _, _) | Term::Case(_, d, _)
                    if d.0 < g.env.datas().len() =>
                {
                    (HashKey::Data(*d), g.data(*d).state())
                }
                _ => continue,
            };
            if state != State::Failed || own.contains(&key) {
                continue;
            }
            if !tables.is_unfinished(key) {
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

    /// What a goal noted now is in, for its heading; and what a lemma of it
    /// is named after (`Pending::lemma_base`).
    fn goal_owner(&self) -> (String, Option<String>) {
        let item = self
            .unit
            .module
            .item
            .or(self.unit.module.current.first().copied());
        match item.and_then(|i| self.unit.module.items.get(i)) {
            Some(item) if item.kind == crate::module::Kind::Test => (item.name.clone(), None),
            Some(item) => {
                let last = item.name.rsplit('.').next().unwrap_or(&item.name);
                let base = is_identifier(last).then(|| last.to_string());
                (format!("`{}`", item.name), base)
            }
            None => ("this expression".to_string(), None),
        }
    }

    /// The definition of the item being elaborated: the first its
    /// declaration made (not a lifted helper), if it is a definition.
    fn owner_def(&self) -> Option<stitchwort_core::DefId> {
        let item = self.unit.module.item?;
        if self.unit.module.items.get(item)?.kind != crate::module::Kind::Def {
            return None;
        }
        (self.unit.module.def_items.iter())
            .filter(|(_, i)| **i == item)
            .map(|(id, _)| *id)
            .min_by_key(|id| id.0)
    }

    /// Prints the goals noted, while the metavariables in them still have
    /// their solutions. A goal at a span already printed replaces it.
    pub(crate) fn flush_goals(&self) {
        self.flush_probe();
        let pending = std::mem::take(&mut self.goals.borrow_mut().pending);
        if pending.is_empty() {
            return;
        }
        let g = &self.ev();
        // Printing a goal that mentions a failed declaration isn't an error
        // message showing it (`Decl::failed_mentioned`).
        let mentioned = self.decl.failed_mentioned.get();
        let printed: Vec<Found> = pending
            .iter()
            .map(|p| {
                // With gluing, as while checking: calls stay folded, also
                // under binders.
                let was = g.machine.glue.replace(self.gluing());
                let printed = self.print_goal(p);
                let snapshot = self.goal_snapshot_of(p);
                g.machine.glue.set(was);
                if let Some(snapshot) = snapshot {
                    let mut kept = self.present.goal_snapshots.borrow_mut();
                    kept.retain(|(span, _)| *span != p.span);
                    if kept.len() >= MAX_SNAPSHOTS {
                        kept.remove(0);
                    }
                    kept.push((p.span, std::rc::Rc::new(snapshot)));
                }
                printed
            })
            .collect();
        self.decl.failed_mentioned.set(mentioned);
        let mut goals = self.goals.borrow_mut();
        for found in printed {
            goals.found.retain(|f| f.span != found.span);
            goals.found.push(found);
        }
    }

    /// By level, whether each variable of the context (shown or `hidden`)
    /// has a type ending in `Prop`, for the printer to write a quantifier
    /// over `p n` as `∀`. Each type is read back at the whole context's
    /// depth, not its variable's level: a match refines a hypothesis to
    /// mention the branch's fields, bound after it.
    fn predicate_flags(
        &self,
        depth: usize,
        context: &[Entry],
        hidden: &[(usize, Value)],
    ) -> Vec<bool> {
        let g = &self.ev();
        let mut flags = vec![false; depth];
        let typed = context
            .iter()
            .map(|e| (e.level, &e.ty))
            .chain(hidden.iter().map(|(l, t)| (*l, t)));
        for (level, ty) in typed {
            if level < depth {
                flags[level] = pretty::is_predicate_type(g, depth, ty);
            }
        }
        flags
    }

    /// `context` printed, each type with the alias it was named by, if any
    /// (`counts: Counts`, SW-858).
    fn print_hypotheses(
        &self,
        scope: &GoalScope,
        names: &[Name],
        context: &[Entry],
    ) -> Vec<Hypothesis> {
        let g = &self.ev();
        let predicates = self.predicate_flags(names.len(), context, &[]);
        let show = |v: &Value| pretty::value_for_goal(g, scope, names, &predicates, v);
        context
            .iter()
            .map(|e| Hypothesis {
                name: e.name.clone(),
                ty: show(
                    &(crate::dot::meta_name_in(self, names.len(), &e.ty)
                        .ok()
                        .flatten())
                    .unwrap_or_else(|| e.ty.clone()),
                ),
                value: e.value.as_ref().map(show),
            })
            .collect()
    }

    /// Asks for the context at byte `offset` of `file` (docs/proposals/
    /// editor-and-playground-roadmap.md §2, item 2): while the file is
    /// checked, the smallest expression containing the offset notes its
    /// type and the names in scope there, as a goal does. Call before
    /// loading the file; read the answer with
    /// [`Elaborator::take_probed_context`] after.
    pub fn probe_context(&self, file: FileId, offset: u32) {
        let mut goals = self.goals.borrow_mut();
        goals.probe = Probe {
            want: Some((file, offset)),
            ..Probe::default()
        };
    }

    /// Asks for what can follow the `.` before byte `offset` of `file`, the
    /// start of the name after it (completion; the editor writes a dummy
    /// name there so that the text parses): while the file is checked, the
    /// receiver's members, or the namespace's ([`crate::dot`]'s rule). Call
    /// before loading the file; read the answer with
    /// [`Elaborator::take_probed_members`] after.
    pub fn probe_members(&self, file: FileId, offset: u32) {
        let mut goals = self.goals.borrow_mut();
        goals.probe = Probe {
            members_at: Some((file, offset)),
            ..Probe::default()
        };
    }

    /// What [`Elaborator::probe_members`] found, once: none if checking
    /// never reached the `.`.
    pub fn take_probed_members(&self) -> Option<Vec<crate::nav::ScopeName>> {
        std::mem::take(&mut self.goals.borrow_mut().probe).members
    }

    /// Whether the name at `span` (a name after a `.`, or a dotted name
    /// it ends) is the one after the probed `.`: if so, the probe is taken,
    /// so the receiver's own names, elaborated next, aren't.
    pub(crate) fn take_members_probe(&self, span: Span) -> bool {
        let mut goals = self.goals.borrow_mut();
        let Some((file, at)) = goals.probe.members_at else {
            return false;
        };
        let hit = span.file == file && span.start <= at && at <= span.end;
        if hit {
            goals.probe.members_at = None;
        }
        hit
    }

    pub(crate) fn found_members(&self, members: Vec<crate::nav::ScopeName>) {
        self.goals.borrow_mut().probe.members = Some(members);
    }

    /// Whether a context, or the members after a `.`, are asked for in one
    /// of `files`.
    pub(crate) fn probes_one_of(&self, files: &[crate::project::SourceUnit]) -> bool {
        let probe = &self.goals.borrow().probe;
        let Some((probed, _)) = probe.want.or(probe.members_at) else {
            return false;
        };
        files.iter().any(|f| f.file == Some(probed))
    }

    /// What [`Elaborator::probe_context`] found, once: none if no
    /// expression checked contains the position (it is in a signature, a
    /// comment, a pattern, a declaration that didn't parse).
    pub fn take_probed_context(&self) -> Option<ContextAt> {
        self.flush_goals();
        std::mem::take(&mut self.goals.borrow_mut().probe).found
    }

    /// The expression at `span`, of type `ty` (checked against it if
    /// `checked`), in `cx`: kept if it is the smallest so far to contain
    /// the probed position.
    pub(crate) fn note_probe(&self, cx: &Ctx, span: Span, ty: &Value, checked: bool) {
        let Some((file, at)) = self.goals.borrow().probe.want else {
            return;
        };
        if span.file != file || span.start > at || at > span.end {
            return;
        }
        // What a declaration generates is written nowhere.
        if (self.present.nav.as_ref()).is_some_and(|nav| nav.borrow().generated > 0) {
            return;
        }
        let mut goals = self.goals.borrow_mut();
        if let Some(p) = &goals.probe.pending
            && p.span.end - p.span.start < span.end - span.start
        {
            return;
        }
        let names = cx.shown_names(true);
        let (mut context, mut hidden) = scope_entries(cx, &names);
        drop_superseded(cx, ty, &mut context, &mut hidden);
        let context = dependency_order(&cx.g(), cx.level(), context);
        goals.probe.pending = Some(ProbePending {
            span,
            ty: ty.clone(),
            checked,
            names,
            context,
        });
    }

    /// Prints the context a probe noted, while its metavariables have their
    /// solutions.
    fn flush_probe(&self) {
        let Some(p) = self.goals.borrow_mut().probe.pending.take() else {
            return;
        };
        let g = &self.ev();
        let scope = GoalScope {
            e: self,
            span: p.span,
        };
        let was = g.machine.glue.replace(self.gluing());
        let locals = self.print_hypotheses(&scope, &p.names, &p.context);
        let predicates = self.predicate_flags(p.names.len(), &p.context, &[]);
        let ty = pretty::value_for_goal(g, &scope, &p.names, &predicates, &p.ty);
        g.machine.glue.set(was);
        self.goals.borrow_mut().probe.found = Some(ContextAt {
            span: p.span,
            ty,
            checked: p.checked,
            locals,
        });
    }

    fn print_goal(&self, p: &Pending) -> Found {
        let g = &self.ev();
        let scope = GoalScope {
            e: self,
            span: p.span,
        };
        let predicates = self.predicate_flags(p.names.len(), &p.context, &p.hidden);
        let show = |v: &Value| pretty::value_for_goal(g, &scope, &p.names, &predicates, v);
        let hypotheses = self.print_hypotheses(&scope, &p.names, &p.context);
        let mut lines: Vec<String> = hypotheses
            .iter()
            .map(|h| match &h.value {
                Some(value) => format!("{}: {} := {}", h.name, h.ty, value),
                None => format!("{}: {}", h.name, h.ty),
            })
            .collect();
        // Forcing leaves a metavariable only if it's unsolved.
        let known = !matches!(
            force(g, p.expected.clone()),
            Ok(Value::Neutral(Head::Meta(_), _))
        );
        let target = if known {
            show(&p.expected)
        } else {
            "(the type here isn't known yet)".to_string()
        };
        lines.push(format!("⊢ {target}"));
        let lemma = if known {
            self.lemma_of(p, &hypotheses, &target).ok()
        } else {
            None
        };
        let mut diagnostic =
            Diagnostic::goal(format!("in {}", p.owner)).with_label(p.span, lines.join("\n"));
        if p.superseded > 0 {
            let (n, are, them) = match p.superseded {
                1 => ("1 earlier hypothesis".to_string(), "isn't", "it"),
                n => (format!("{n} earlier hypotheses"), "aren't", "them"),
            };
            diagnostic = diagnostic.with_note(format!(
                "{n} hidden by a later one of the same name (as a `match` or `rewrite … \
                 at` binds) {are} listed, as nothing shown mentions {them}"
            ));
        }
        diagnostic.detail_mut().goal = Some(GoalData {
            hypotheses,
            target,
            lemma: None,
        });
        Found {
            span: p.span,
            diagnostic,
            base: p.lemma_base.clone(),
            lemma,
        }
    }

    /// The goal `p`, printed as `hypotheses` and `target`, as a declaration
    /// of its own less its name: its keyword, and what follows the name
    /// (` (n: Nat): n + 0 = n := ?`). Or why not, if it might not mean the
    /// same at the top level of the file (docs/proposals/code-navigation.md,
    /// "Goals"): a `let` of data is in scope (its value would be lost); a
    /// name in it can't be written there (`n✝`, a compiler-made `%x`, a
    /// declaration or constructor that needs an import); it mentions a
    /// variable the goal doesn't show (a `_`), or a hypothesis mentions a
    /// later one; a part isn't shown in full (`…`) or isn't known (`?`);
    /// or whether it's a proposition wasn't known.
    fn lemma_of(
        &self,
        p: &Pending,
        hypotheses: &[Hypothesis],
        target: &str,
    ) -> Result<(&'static str, String), &'static str> {
        let keyword = match p.prop {
            Some(true) => "theorem",
            Some(false) => "def",
            None => return Err("prop unknown"),
        };
        if p.context.iter().any(|e| e.value.is_some()) {
            return Err("let of data");
        }
        if !hypotheses.iter().all(|h| is_identifier(&h.name)) {
            return Err("unwritable hypothesis name");
        }
        // `%` before a name: a compiler-made one (`n % 2` is fine).
        let unwritable = |text: &str| {
            text.contains(['✝', '?', '…', '\n'])
                || text.contains("(body of ")
                || text
                    .split('%')
                    .skip(1)
                    .any(|after| after.starts_with(|c: char| c.is_alphanumeric() || c == '_'))
        };
        if unwritable(target) || hypotheses.iter().any(|h| unwritable(&h.ty)) {
            return Err("unwritable text");
        }
        // Every variable the goal mentions is one it shows, a hypothesis's
        // type mentioning only those before it (a case split can refine an
        // earlier one's type with a later one).
        let g = &self.ev();
        let level = p.names.len();
        let levels: Vec<usize> = p.context.iter().map(|e| e.level).collect();
        let mut declarations = Vec::new();
        let mut ctors = Vec::new();
        let mut writable = |v: &Value, shown: &[usize]| {
            let Ok(term) = quote_shown(g, level, v) else {
                return false;
            };
            term.subterms().all(|(t, binders)| match t {
                Term::Var(i) | Term::Case(i, ..) | Term::NumCase(i, ..) => {
                    *i < binders
                        || (i - binders < level && shown.contains(&(level - 1 - (i - binders))))
                }
                Term::Meta(_) => false,
                Term::Def(id) if id.0 < g.env.defs().len() => {
                    declarations.push(Declaration::Def(*id));
                    true
                }
                Term::Data(d, _) if d.0 < g.env.datas().len() => {
                    declarations.push(Declaration::Data(*d));
                    true
                }
                Term::Ctor(d, c, _) if d.0 < g.env.datas().len() => {
                    ctors.push((*d, *c));
                    true
                }
                Term::Def(_) | Term::Data(..) | Term::Ctor(..) => false,
                _ => true,
            })
        };
        if !writable(&p.expected, &levels) {
            return Err("target mentions a hidden variable");
        }
        if !(p.context.iter().enumerate()).all(|(k, e)| writable(&e.ty, &levels[..k])) {
            return Err("hypothesis mentions a hidden or later variable");
        }
        // Every declaration it names, it names as the top level of the file
        // can. The printer names one by the shortest part of its name that
        // means it here, else by its whole name (`Std.List.count`), which
        // only a declaration the file can't name at all (one internal to the
        // library) fails. One shown as notation (`+`, a record update) isn't
        // named.
        let text: Vec<&str> = std::iter::once(target)
            .chain(hypotheses.iter().map(|h| h.ty.as_str()))
            .collect();
        for declaration in declarations {
            let full = self.full_name(declaration);
            let parts: Vec<&str> = full.split('.').collect();
            let resolves = (0..parts.len()).any(|start| {
                let written = parts[start..].join(".");
                self.names(&written, declaration)
                    && matches!(self.resolve(&written), Resolved::Found { .. })
            });
            let shown = |t: &&str| {
                (0..parts.len()).any(|start| mentions_name(t, &parts[start..].join(".")))
            };
            if !resolves && text.iter().any(shown) {
                return Err("names a declaration it can't");
            }
        }
        // A constructor is shown by its own name (`Done y`), unless as a
        // literal or a record.
        for (d, c) in ctors {
            let name = &*g.data(d).ctors()[c].name;
            let resolves = matches!(
                self.resolve(name),
                Resolved::Found { global: crate::Global::Ctor(e, k), .. } if e == d && k == c
            );
            if !resolves && text.iter().any(|t| mentions_name(t, name)) {
                return Err("names a constructor it can't");
            }
        }
        // A type that starts with a record update, `{ p | gold = 3 } = p`,
        // reads after a `:` as a block: it goes in brackets.
        let bracketed = |ty: &str| {
            if ty.starts_with('{') {
                format!("({ty})")
            } else {
                ty.to_string()
            }
        };
        let mut rest = String::new();
        for h in hypotheses {
            rest.push_str(&format!(" ({}: {})", h.name, bracketed(&h.ty)));
        }
        rest.push_str(&format!(": {} := ?", bracketed(target)));
        Ok((keyword, rest))
    }

    /// The goals printed since this was last called, in source order, each
    /// lemma named after its declaration and its place among the
    /// declaration's goals (`addZeroGoal2`; `goal1` in a test).
    pub(crate) fn take_goals(&self) -> Vec<Diagnostic> {
        self.flush_goals();
        let mut found = std::mem::take(&mut self.goals.borrow_mut().found);
        found.sort_by_key(|f| (f.span.file.index(), f.span.start));
        let mut counts: Vec<(Option<String>, usize)> = Vec::new();
        found
            .into_iter()
            .map(|f| {
                let n = match counts.iter_mut().find(|(b, _)| *b == f.base) {
                    Some((_, n)) => {
                        *n += 1;
                        *n
                    }
                    None => {
                        counts.push((f.base.clone(), 1));
                        1
                    }
                };
                let mut d = f.diagnostic;
                if let (Some((keyword, rest)), Some(goal)) =
                    (f.lemma, d.detail.as_mut().and_then(|x| x.goal.as_mut()))
                {
                    let name = match &f.base {
                        Some(base) => format!("{base}Goal{n}"),
                        None => format!("goal{n}"),
                    };
                    goal.lemma = Some(format!("{keyword} {name}{rest}"));
                }
                d
            })
            .collect()
    }

    /// Forgets every goal, noted or printed.
    pub(crate) fn clear_goals(&self) {
        // The probe outlives the goals: it spans the declarations of a file.
        let mut goals = self.goals.borrow_mut();
        let probe = std::mem::take(&mut goals.probe);
        *goals = Goals {
            probe,
            ..Goals::default()
        };
    }
}

/// Whether `text` has `name` in it as a whole name: `List.count` is in
/// `List.count xs`, but not in `Std.List.counts`.
fn mentions_name(text: &str, name: &str) -> bool {
    let part_of_name = |c: char| c.is_alphanumeric() || matches!(c, '_' | '\'' | '.' | '%');
    text.match_indices(name).any(|(at, _)| {
        !text[..at].ends_with(part_of_name) && !text[at + name.len()..].starts_with(part_of_name)
    })
}

/// Whether `name` can be written as a plain name: `n`, `xs'`, `h_1`.
fn is_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(|c| c.is_alphabetic() || c == '_')
        && chars.all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
        && name != "_"
}

/// How many goals' [`GoalSnapshot`]s an elaborator keeps, the latest.
const MAX_SNAPSHOTS: usize = 256;

/// A goal as the elaborator had it at its `?` (SW-989), for `search --at`:
/// the context's variables and the target as terms, not as printed text, so
/// a goal is searched, and proofs checked at it, whether or not its printed
/// form reads back as the same statement (a hypothesis refined to mention a
/// later pattern variable, a `✝` or compiler-made name, a lifted `%match`,
/// a lambda whose binder the printer captured).
pub struct GoalSnapshot {
    /// The variables, each one's type mentioning only those before it:
    /// the context's order, except that a hypothesis a case split refined
    /// to mention a later variable (`h: line < 3` before `line`) comes
    /// after it.
    pub(crate) vars: Vec<SnapVar>,
    /// The number of variables in scope at the `?`: the terms below are in
    /// that context.
    pub(crate) level: usize,
    pub(crate) target: Term,
    /// The definition the goal is in (SW-993): a call of it is the
    /// induction hypothesis.
    pub(crate) owner: Option<stitchwort_core::DefId>,
    /// What its parameters stand for at the goal (`Pending::owner_args`),
    /// in this context; empty if one couldn't be kept.
    pub(crate) owner_args: Vec<Term>,
}

impl GoalSnapshot {
    /// The definition the goal is in, if it is in one.
    pub fn owner(&self) -> Option<stitchwort_core::DefId> {
        self.owner
    }
}

pub(crate) struct SnapVar {
    /// Its level at the `?`.
    pub(crate) level: usize,
    /// As shown: `n`, or `n✝`, `%x`, `_` for one a proof can't name.
    pub(crate) name: Name,
    /// Whether a proof can refer to it by `name`.
    pub(crate) writable: bool,
    pub(crate) ty: Term,
    /// For a `let` of data, its value.
    pub(crate) value: Option<Term>,
}

/// The levels `term`, in a context of `level` variables, mentions; `None`
/// if it has an unknown in it.
fn levels_in(term: &Term, level: usize) -> Option<Vec<usize>> {
    let mut out = Vec::new();
    for (t, binders) in term.subterms() {
        match t {
            Term::Var(i) | Term::Case(i, ..) | Term::NumCase(i, ..) if *i >= binders => {
                out.push(level.checked_sub(1 + (i - binders))?);
            }
            Term::Meta(_) => return None,
            _ => {}
        }
    }
    Some(out)
}

impl Elaborator {
    /// The goal `p` as terms ([`GoalSnapshot`]), if it can be: every part
    /// known (no unknown left in it), mentioning only variables of the
    /// context, in an order where each type mentions only those before.
    fn goal_snapshot_of(&self, p: &Pending) -> Option<GoalSnapshot> {
        let g = &self.ev();
        let level = p.names.len();
        let quote = |v: &Value| stitchwort_core::value::quote_folded(g, level, v).ok();
        let mut vars: Vec<SnapVar> = Vec::new();
        for e in &p.context {
            vars.push(SnapVar {
                level: e.level,
                writable: is_identifier(&e.name),
                name: e.name.as_str().into(),
                ty: quote(&e.ty)?,
                value: match &e.value {
                    Some(v) => Some(quote(v)?),
                    None => None,
                },
            });
        }
        for (l, ty) in &p.hidden {
            vars.push(SnapVar {
                level: *l,
                name: p.names[*l].clone(),
                writable: false,
                ty: quote(ty)?,
                value: None,
            });
        }
        let target = quote(&p.target)?;
        // What each mentions, of the variables kept.
        let known: Vec<usize> = vars.iter().map(|v| v.level).collect();
        let owner_args: Vec<Term> = (p.owner_args.iter())
            .map(|v| {
                let t = quote(v)?;
                levels_in(&t, level)?
                    .iter()
                    .all(|l| known.contains(l))
                    .then_some(t)
            })
            .collect::<Option<Vec<Term>>>()
            .unwrap_or_default();
        let mut needs: Vec<Vec<usize>> = Vec::new();
        for v in &vars {
            let mut n = levels_in(&v.ty, level)?;
            if let Some(value) = &v.value {
                n.extend(levels_in(value, level)?);
            }
            n.retain(|l| *l != v.level);
            if !n.iter().all(|l| known.contains(l)) {
                return None;
            }
            needs.push(n);
        }
        if !levels_in(&target, level)?.iter().all(|l| known.contains(l)) {
            return None;
        }
        // Each in turn: the lowest level whose needs are placed.
        let mut order: Vec<usize> = Vec::new();
        let mut placed: Vec<usize> = Vec::new();
        while order.len() < vars.len() {
            let next = (0..vars.len())
                .filter(|i| !order.contains(i))
                .filter(|i| needs[*i].iter().all(|l| placed.contains(l)))
                .min_by_key(|i| vars[*i].level)?;
            order.push(next);
            placed.push(vars[next].level);
        }
        let mut slots: Vec<Option<SnapVar>> = vars.into_iter().map(Some).collect();
        let vars = (order.into_iter())
            .map(|i| slots[i].take().expect("placed once"))
            .collect();
        Some(GoalSnapshot {
            vars,
            level,
            target,
            owner: p.owner_def,
            owner_args,
        })
    }

    /// The snapshot of the goal whose `?` is at `span`, if one was taken
    /// (among the latest goals this elaborator printed).
    pub fn goal_snapshot(&self, span: Span) -> Option<std::rc::Rc<GoalSnapshot>> {
        (self.present.goal_snapshots.borrow().iter())
            .rev()
            .find(|(s, _)| *s == span)
            .map(|(_, snapshot)| snapshot.clone())
    }

    /// A context with `snapshot`'s variables bound in its order (a `let` of
    /// data as the `let`; one a proof can't name, hidden), its target there,
    /// and how each was bound.
    pub(crate) fn enter_snapshot<'e>(
        &'e self,
        snapshot: &GoalSnapshot,
        span: Span,
    ) -> crate::Result<(Ctx<'e>, Value, Vec<SnapBinder>)> {
        let g = &self.ev();
        let mut cx = Ctx::new(self, span);
        // What stands for each variable at the `?`, by its level there.
        let mut env: Vec<Value> = vec![Value::Sort(Sort::Prop); snapshot.level];
        let mut binders = Vec::new();
        for v in &snapshot.vars {
            let ty = stitchwort_core::value::eval(g, &env, &v.ty)?;
            let ty_term = cx.quote(&ty)?;
            match &v.value {
                Some(value) => {
                    let value = stitchwort_core::value::eval(g, &env, value)?;
                    let value = cx.quote(&value)?;
                    let name = v.writable.then_some(&*v.name);
                    cx.define(name, v.name.clone(), ty, ty_term.clone(), value.clone())?;
                    binders.push(SnapBinder::Let(v.name.clone(), ty_term, value));
                }
                None => {
                    if v.writable {
                        cx.bind(&v.name, ty);
                    } else {
                        cx.bind_hidden(v.name.clone(), ty);
                    }
                    binders.push(SnapBinder::Lam(v.name.clone(), ty_term));
                }
            }
            env[v.level] = cx.env.last().expect("just bound").clone();
        }
        let target = stitchwort_core::value::eval(g, &env, &snapshot.target)?;
        Ok((cx, target, binders))
    }
}

/// How [`Elaborator::enter_snapshot`] bound a variable, for the closed term
/// the kernel checks.
pub(crate) enum SnapBinder {
    Lam(Name, Term),
    Let(Name, Term, Term),
}

/// `body`, of type `ty`, terms under `binders`, as one closed term:
/// `((x: A) => let y: B := v; body) : (x: A) → let y: B := v; ty`.
pub(crate) fn close_over(binders: &[SnapBinder], body: Term, ty: Term) -> Term {
    let (mut body, mut ty) = (body, ty);
    for b in binders.iter().rev() {
        match b {
            SnapBinder::Lam(name, a) => {
                body = Term::Lam(name.clone(), Icit::Explicit, std::rc::Rc::new(body));
                ty = Term::Pi(
                    name.clone(),
                    Icit::Explicit,
                    std::rc::Rc::new(a.clone()),
                    std::rc::Rc::new(ty),
                );
            }
            SnapBinder::Let(name, a, v) => {
                body = Term::let_(name.clone(), a.clone(), v.clone(), body);
                ty = Term::let_(name.clone(), a.clone(), v.clone(), ty);
            }
        }
    }
    Term::Ann(std::rc::Rc::new(body), std::rc::Rc::new(ty))
}
