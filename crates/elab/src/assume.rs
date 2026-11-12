//! Open goals as kernel assumptions (docs/proposals/using-unfinished-proofs.md,
//! option A, D3504; docs/core.md "Assumptions (open goals)").
//!
//! At the end of a declaration's body, before its `match`es are lifted and
//! it is zonked, each `?` whose goal can be stated becomes a kernel
//! assumption: a constant whose type is the goal closed over the variables
//! the hole's metavariable is applied to. The metavariable is then solved
//! with that constant, so the declaration, and everything that uses it, is
//! checked by the kernel as usual, assuming the goal holds.
//!
//! A goal that can't be stated keeps today's behaviour: its metavariable
//! stays unsolved, so zonking fails with `E-UNFINISHED` and the declaration
//! isn't sent to the kernel. That is the case when its type still has an
//! unknown in it, mentions a declaration that isn't final (a member of the
//! declaration's own group, the declaration itself, a `match` lifted from
//! it), or mentions a variable the hole can't take.
//!
//! A `def` or `theorem` whose statement checked but whose body didn't is
//! stood in for the same way (docs/proposals/tests-with-errors.md §3.3,
//! D3527): [`Elaborator::stand_in`] makes an assumption of its declared
//! type, labelled with its error, and the module binds its name to it, so
//! its users are checked against the statement and rely on it.
//!
//! Nothing that relies on an assumption counts as finished.
//! `Elaborator::is_unfinished` reads which declarations do off their
//! checked terms (`assumption::relies_on`, remembered per final
//! declaration), so every command treats them as it treated a declaration
//! with a `?` until the reporting stage names the goals, however they were
//! made. The component's items are also marked unfinished (`module.rs`),
//! for their status and the check cache.

use std::cell::Cell;

use stitchwort_core::assumption::{self, Decl};
use stitchwort_core::globals::{Assumption, HashKey};
use stitchwort_core::value::{eval, quote_as_written};
use stitchwort_core::{DataId, DefId, Icit, Name, Term};

use crate::Elaborator;

/// Where the assumptions this session made start: every declaration before
/// `floor` was final before any of them existed, so relies on none.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Floor {
    /// The earliest assumption: while it is still there, `floor` holds. A
    /// rewind that takes it takes every later one too.
    first: DefId,
    floor: usize,
}

/// [`Floor`], kept by the session. Not part of a rewind mark: it checks on
/// use that its assumption is still there.
#[derive(Default)]
pub(crate) struct Assumed(Cell<Option<Floor>>);

/// The budget for stating a goal, or comparing it with an earlier one's
/// (which may compute: the two statements are compared by conversion): a
/// goal that would take more falls back, without running out the
/// declaration's own budget.
fn side_limits() -> stitchwort_core::Limits {
    stitchwort_core::Limits {
        work: 1_000_000,
        size: 50_000,
        frames: 10_000,
        ..stitchwort_core::Limits::default()
    }
}

impl Elaborator {
    /// The session's [`Floor`], if any assumption is still in the kernel.
    fn floor(&self) -> Option<Floor> {
        let f = self.session.assumed.0.get()?;
        let defs = self.kernel.env.defs();
        (f.first.0 < defs.len() && defs[f.first.0].assumption().is_some()).then_some(f)
    }

    /// Whether the kernel holds any assumption this session made.
    pub(crate) fn any_assumption(&self) -> bool {
        self.floor().is_some()
    }

    /// An open goal's assumption declaration `d` relies on, read off the
    /// checked terms (`assumption::relies_on`, remembered for final
    /// declarations), or `None` if it relies on none.
    pub(crate) fn goal_relied_on(&self, d: impl Into<Decl>) -> Option<DefId> {
        let floor = self.floor()?;
        assumption::relies_on(
            &self.ev(),
            d.into(),
            &|d| matches!(d, Decl::Def(id) if id.0 < floor.floor),
        )
    }

    /// Whether definition `id` relies on an open goal's assumption.
    pub fn relies_on_goal(&self, id: DefId) -> bool {
        self.goal_relied_on(id).is_some()
    }

    /// Whether `term` mentions a definition or data type that isn't
    /// finished (`Elaborator::is_unfinished`): for an expression typed in,
    /// which has no status of its own.
    pub(crate) fn mentions_unfinished(&self, term: &Term) -> bool {
        term.subterms().any(|(t, _)| match t {
            Term::Def(id) => self.is_unfinished(*id),
            Term::Data(d, _) | Term::Ctor(d, _, _) | Term::Case(_, d, _) | Term::Proj(d, ..) => {
                self.tables.is_unfinished(HashKey::Data(*d)) || self.goal_relied_on(*d).is_some()
            }
            _ => false,
        })
    }

    /// The declaration whose `?` assumption `id` stands for, by its full
    /// name as the reader wrote it: a `decreasing` definition's goals are
    /// made under its step (`f.%step`) and a lifted `match` under its
    /// helper, which the reader never wrote.
    pub fn assumption_owner(&self, id: DefId) -> Option<String> {
        let a = self.kernel.env.defs().get(id.0)?.assumption()?;
        let owner = a.owner.as_ref();
        Some(
            owner
                .split_once(".%")
                .map_or(owner, |(head, _)| head)
                .to_string(),
        )
    }

    /// Where assumption `id`'s `?` is written, or its stand-in's error.
    pub fn assumption_span(&self, id: DefId) -> stitchwort_syntax::Span {
        self.kernel.def(id).span()
    }

    /// The assumptions of this session still in the kernel, oldest first.
    pub fn assumptions(&self) -> Vec<DefId> {
        let Some(floor) = self.floor() else {
            return Vec::new();
        };
        let defs = self.kernel.env.defs();
        (floor.first.0..defs.len())
            .filter(|&i| defs[i].assumption().is_some())
            .map(DefId)
            .collect()
    }

    /// Every assumption declaration `d` relies on, read off its checked
    /// terms.
    pub fn goals_relied_on(&self, d: impl Into<Decl>) -> std::collections::BTreeSet<DefId> {
        let Some(floor) = self.floor() else {
            return Default::default();
        };
        let d = d.into();
        // Most declarations rely on none, and that is remembered (see
        // `goal_relied_on`); only one that does is walked for all of them.
        if self.goal_relied_on(d).is_none() {
            return Default::default();
        }
        assumption::relied_on_skipping(
            &self.ev(),
            &[d],
            &|d| matches!(d, Decl::Def(id) if id.0 < floor.floor),
        )
    }

    /// The open goals' assumptions definition `id` waits on: it wasn't
    /// checked, because something it computes with is stuck on them
    /// (docs/proposals/using-unfinished-proofs.md §4, "Blocked users").
    /// Empty for any other definition.
    pub fn blocked_on(&self, id: DefId) -> Vec<DefId> {
        if self.kernel.def(id).state() == stitchwort_core::globals::State::Final
            || !self.tables.is_unfinished(HashKey::Def(id))
        {
            return Vec::new();
        }
        (self.session.blocked.borrow().get(&id)).map_or_else(Vec::new, |g| g.to_vec())
    }

    /// The declarations that wait for open goals but have no definition (a
    /// signature that waited), by full name, with the goals' assumptions:
    /// [`Self::blocked_on`] for the rest.
    pub fn waiting_without_definition(&self) -> Vec<(String, Vec<DefId>)> {
        (self.session.waiting_names.borrow().iter())
            .filter(|(key, _)| matches!(self.scope.stored(key), Some((crate::Global::Failed, _))))
            .map(|(key, goals)| (key.clone(), goals.to_vec()))
            .collect()
    }

    /// Makes each open goal of the declaration being elaborated an
    /// assumption, where it can be, and solves its metavariable with it.
    /// The others are left as they are (see the module's documentation).
    pub(crate) fn assume_goals(&mut self) {
        let Some(key) = self.decl.owner.borrow().first().cloned() else {
            return;
        };
        // A test's key already starts with the namespace.
        let owner =
            if key.starts_with(self.root()) && key[self.root().len()..].starts_with("test \"") {
                Name::from(key.as_str())
            } else {
                self.unit.path(&Name::from(key.as_str()))
            };
        // Numbered in source order, so a goal's label doesn't depend on
        // the order the elaborator met them in.
        let mut order: Vec<usize> = (0..self.goals.borrow().pending.len()).collect();
        order.sort_by_key(|&i| {
            let s = self.goals.borrow().pending[i].span;
            s.start
        });
        for (n, i) in order.into_iter().enumerate() {
            let p = self.goals.borrow().pending[i].clone();
            if self.attempt.store.metas.borrow()[p.meta].solution.is_some() {
                continue;
            }
            let hole = u32::try_from(n + 1).expect("holes fit");
            let name: Name = format!("{owner}.?{hole}").into();
            let label = Assumption::goal(owner.clone(), hole);
            let stated = (self.kernel.machine.budget).aside(side_limits(), || self.goal_type(&p));
            let Some((ty, order)) = stated else {
                continue;
            };
            let Some(id) = self.assumption_for(&name, &name, &ty, label, false, p.span) else {
                continue;
            };
            // `λ x₁ … xₙ. a xᵢ …`, over the variables the metavariable is
            // applied to, passing those it takes in its order.
            let k = p.applied.len();
            let mut solution = Term::Def(id);
            for i in order {
                solution = Term::app(solution, Term::Var(k - 1 - i));
            }
            for _ in 0..k {
                solution = Term::Lam("x".into(), Icit::Explicit, std::rc::Rc::new(solution));
            }
            let Ok(value) = eval(&self.ev(), &[], &solution) else {
                continue;
            };
            self.metas().solve_meta(p.meta, value);
        }
    }

    /// The stand-in for definition `failed` (docs/proposals/tests-with-errors.md
    /// §3.3, D3527): its statement checked but its body didn't, so it
    /// becomes an assumption of that statement, labelled as its error, and
    /// its users are checked against it and rely on it. `span` is where the
    /// error is. `None`, so its users wait, if the kernel refuses the
    /// statement: it mentions a declaration that isn't final (another
    /// member of its failed group, say).
    ///
    /// It takes the failed definition's name and path, so a term that uses
    /// it reads as the declaration the user wrote.
    pub(crate) fn stand_in(
        &mut self,
        failed: DefId,
        span: stitchwort_syntax::Span,
    ) -> Option<DefId> {
        let def = self.kernel.def(failed);
        if def.state() != stitchwort_core::globals::State::Failed {
            return None;
        }
        let (name, path, ty) = (def.name().clone(), def.path().clone(), def.ty().clone());
        let theorem = def.theorem();
        let label = Assumption::error(path.clone());
        self.assumption_for(&name, &path, &ty, label, theorem, span)
    }

    /// Whether assumption `id` is a stand-in for a declaration with an
    /// error, not an open goal's.
    pub fn is_error_stand_in(&self, id: DefId) -> bool {
        (self.kernel.env.defs().get(id.0))
            .and_then(|d| d.assumption())
            .is_some_and(Assumption::is_error)
    }

    /// The goal `p` as a closed type: a `Π` over the variables its
    /// metavariable is applied to (a compiler-made one only if the goal
    /// needs it), ordered so that each type mentions only those before it,
    /// ending in the goal. With it, the variables taken, in that order, as
    /// positions in `p.applied`. `None` if it can't be stated.
    fn goal_type(&self, p: &crate::goals::Pending) -> Option<(Term, Vec<usize>)> {
        let g = &self.ev();
        let level = p.level;
        // As written: read back folded, a call that steps at once would be
        // computed (`countDown 100000 [] = []` as the whole list).
        let term = |v| {
            let t = quote_as_written(g, level, v).ok()?;
            self.zonk(&t, level).ok()
        };
        let types: Vec<Term> = (p.applied.iter())
            .map(|(_, ty, _)| term(ty))
            .collect::<Option<_>>()?;
        let target = term(&p.target)?;
        let levels: Vec<usize> = p.applied.iter().map(|(l, _, _)| *l).collect();
        let mut needs: Vec<Vec<usize>> = Vec::new();
        for (ty, l) in types.iter().zip(&levels) {
            let mut n = crate::goals::levels_in(ty, level)?;
            n.retain(|m| m != l);
            needs.push(n);
        }
        let wanted = crate::goals::levels_in(&target, level)?;
        if !wanted.iter().all(|l| levels.contains(l)) {
            return None;
        }
        // Every variable the reader has, with its hypotheses, as the goal
        // shows them; one the compiler made (a `decreasing` definition's
        // stand-in for its recursive call, `%rec`) only if the goal needs it.
        let mut kept: Vec<bool> = p.applied.iter().map(|(_, _, made)| !made).collect();
        let mut more: Vec<usize> = wanted;
        more.extend(
            (0..levels.len())
                .filter(|i| kept[*i])
                .flat_map(|i| needs[i].clone()),
        );
        while let Some(l) = more.pop() {
            let i = levels.iter().position(|m| *m == l)?;
            if !kept[i] {
                kept[i] = true;
                more.extend(needs[i].iter().copied());
            }
        }
        let count = kept.iter().filter(|k| **k).count();
        // Each in turn: the earliest whose needs are placed.
        let mut order: Vec<usize> = Vec::new();
        let mut placed: Vec<usize> = Vec::new();
        while order.len() < count {
            let next = (0..levels.len())
                .filter(|i| kept[*i] && !order.contains(i))
                .find(|i| needs[*i].iter().all(|l| placed.contains(l)))?;
            order.push(next);
            placed.push(levels[next]);
        }
        // `t`, at the hole, under the first `bound` variables placed.
        let under = |t: &Term, bound: usize| {
            crate::lift::replace_with(
                g,
                t,
                level,
                &|l| match placed[..bound].iter().position(|m| *m == l) {
                    Some(pos) => Ok(Term::Var(bound - 1 - pos)),
                    None => Err(stitchwort_syntax::Diagnostic::error(
                        "E-MALFORMED",
                        "a goal's variable isn't one it can take",
                    )),
                },
                &|_, _| None,
            )
            .ok()
        };
        let mut ty = under(&target, order.len())?;
        for (pos, &i) in order.iter().enumerate().rev() {
            let name = p
                .names
                .get(levels[i])
                .cloned()
                .unwrap_or_else(|| "x".into());
            ty = Term::Pi(
                name,
                Icit::Explicit,
                std::rc::Rc::new(under(&types[i], pos)?),
                std::rc::Rc::new(ty),
            );
        }
        Some((ty, order))
    }

    /// The assumption `label` with type `ty`: a new one, or the one an
    /// earlier attempt at the same declaration made, if its type is the
    /// same. `None` if the kernel refuses it (a type that mentions a
    /// declaration that isn't final), or the label is taken by an
    /// assumption of another type (a declaration checked again in the same
    /// session with its goal changed).
    fn assumption_for(
        &mut self,
        name: &Name,
        path: &Name,
        ty: &Term,
        label: Assumption,
        theorem: bool,
        span: stitchwort_syntax::Span,
    ) -> Option<DefId> {
        let existing = (self.kernel.env.defs().iter().enumerate())
            .find(|(_, d)| d.assumption() == Some(&label))
            .map(|(i, _)| DefId(i));
        if let Some(id) = existing {
            let g = &self.ev();
            let same = g.machine.budget.aside(side_limits(), || {
                let new = eval(g, &[], ty).ok()?;
                stitchwort_core::value::conv(g, 0, g.def(id).ty_value(), &new).ok()
            })?;
            return same.then_some(id);
        }
        // Before the assumption is made: a stale floor is taken back.
        let floor = self.floor();
        let id =
            crate::kernel::assume(&mut self.kernel, name, path, ty, label, theorem, span).ok()?;
        let at = self.unit.module.first_def.min(id.0);
        self.session.assumed.0.set(Some(match floor {
            Some(f) => Floor {
                first: f.first,
                floor: f.floor.min(at),
            },
            None => Floor {
                first: id,
                floor: at,
            },
        }));
        Some(id)
    }

    /// Marks the declarations the component just checked that rely on an
    /// open goal's assumption as unfinished, as a declaration with a `?`
    /// was before assumptions: those of its `items`, and the definitions
    /// from `defs` on and data types from `datas` on. Whether any of its
    /// own do: a definition made in passing for another item (a waiting
    /// instance) doesn't count. `is_unfinished` reads reliance off the
    /// terms whatever is marked; the marks are for the component's status
    /// and the check cache.
    pub(crate) fn mark_relying(&mut self, items: &[usize], defs: usize, datas: usize) -> bool {
        if !self.any_assumption() {
            return false;
        }
        let module = &self.unit.module;
        let own = |id: &DefId| module.def_items.get(id).is_none_or(|i| items.contains(i));
        let mut def_ids: Vec<DefId> = (items.iter())
            .flat_map(|i| module.item_defs.get(i).into_iter().flatten().copied())
            .filter(|id| id.0 < defs)
            .collect();
        def_ids.extend((defs..self.kernel.env.defs().len()).map(DefId));
        let data_ids = (datas..self.kernel.env.datas().len()).map(DataId);
        let relying_defs: Vec<(DefId, bool)> = (def_ids.into_iter())
            .filter(|id| self.goal_relied_on(*id).is_some())
            .map(|id| (id, own(&id)))
            .collect();
        let relying_datas: Vec<DataId> = data_ids
            .filter(|d| self.goal_relied_on(*d).is_some())
            .collect();
        let owners = &self.session.owners;
        for &(id, _) in &relying_defs {
            if !self.tables.is_unfinished(HashKey::Def(id)) {
                self.tables.unfinished_defs.insert(owners, id, ());
            }
        }
        for &d in &relying_datas {
            if !self.tables.is_unfinished(HashKey::Data(d)) {
                self.tables.unfinished_datas.insert(owners, d, ());
            }
        }
        !relying_datas.is_empty() || relying_defs.iter().any(|(_, own)| *own)
    }
}
