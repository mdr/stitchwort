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
//! Nothing that relies on an assumption counts as finished. Which
//! declarations do is read off their checked terms
//! (`assumption::relied_on`), and they are marked unfinished as before
//! (`module.rs`), so every command treats them as it treated a declaration
//! with a `?` until the reporting stage names the goals.

use std::cell::Cell;

use stitchwort_core::assumption::{self, Decl};
use stitchwort_core::globals::{Assumption, HashKey};
use stitchwort_core::value::{eval, quote_folded};
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

    /// The assumptions the definitions `defs` and data types `datas` rely
    /// on, read off their checked terms.
    pub(crate) fn relied_on(
        &self,
        defs: impl IntoIterator<Item = DefId>,
        datas: impl IntoIterator<Item = DataId>,
    ) -> std::collections::BTreeSet<DefId> {
        let Some(floor) = self.floor() else {
            return Default::default();
        };
        let roots: Vec<Decl> = (defs.into_iter().map(Decl::Def))
            .chain(datas.into_iter().map(Decl::Data))
            .collect();
        assumption::relied_on_skipping(
            &self.ev(),
            &roots,
            &|d| matches!(d, Decl::Def(id) if id.0 < floor.floor),
        )
    }

    /// Whether definition `id` relies on an open goal's assumption.
    pub fn relies_on_goal(&self, id: DefId) -> bool {
        !self.relied_on([id], []).is_empty()
    }

    /// The declaration whose `?` assumption `id` stands for, by its full
    /// name.
    pub fn assumption_owner(&self, id: DefId) -> Option<String> {
        let a = self.kernel.env.defs().get(id.0)?.assumption()?;
        Some(a.owner.to_string())
    }

    /// Makes each open goal of the declaration being elaborated an
    /// assumption, where it can be, and solves its metavariable with it.
    /// The others are left as they are (see the module's documentation).
    pub(crate) fn assume_goals(&mut self) {
        let Some(key) = self.decl.owner.borrow().first().cloned() else {
            return;
        };
        let owner = self.unit.path(&Name::from(key.as_str()));
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
            let label = Assumption {
                owner: owner.clone(),
                hole,
            };
            let Some((ty, order)) = self.goal_type(&p) else {
                continue;
            };
            let Some(id) = self.assumption_for(&ty, label, p.span) else {
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

    /// The goal `p` as a closed type: a `Π` over the variables its
    /// metavariable is applied to (a compiler-made one only if the goal
    /// needs it), ordered so that each type mentions only those before it,
    /// ending in the goal. With it, the variables taken, in that order, as
    /// positions in `p.applied`. `None` if it can't be stated.
    fn goal_type(&self, p: &crate::goals::Pending) -> Option<(Term, Vec<usize>)> {
        let g = &self.ev();
        let level = p.level;
        let term = |v| {
            let t = quote_folded(g, level, v).ok()?;
            self.zonk_keeping(&t, level, &|_| false).ok()
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
        ty: &Term,
        label: Assumption,
        span: stitchwort_syntax::Span,
    ) -> Option<DefId> {
        let existing = (self.kernel.env.defs().iter().enumerate())
            .find(|(_, d)| d.assumption() == Some(&label))
            .map(|(i, _)| DefId(i));
        if let Some(id) = existing {
            let g = &self.ev();
            let new = eval(g, &[], ty).ok()?;
            let same = stitchwort_core::value::conv(g, 0, g.def(id).ty_value(), &new).ok()?;
            return same.then_some(id);
        }
        // Before the assumption is made: a stale floor is taken back.
        let floor = self.floor();
        let name: Name = format!("{}.?{}", label.owner, label.hole).into();
        let id = crate::kernel::assume(&mut self.kernel, &name, &name, ty, label, span).ok()?;
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

    /// Marks what the component just checked relies on an open goal's
    /// assumption as unfinished, as a declaration with a `?` was before
    /// assumptions: its definitions from `defs` on and data types from
    /// `datas` on, and those of its `items`. Whether it does.
    pub(crate) fn mark_relying(&mut self, items: &[usize], defs: usize, datas: usize) -> bool {
        if !self.any_assumption() {
            return false;
        }
        let g = &self.ev();
        let mut def_ids: Vec<DefId> = (self.unit.module.def_items.iter())
            .filter(|(id, item)| items.contains(item) && id.0 < g.env.defs().len())
            .map(|(id, _)| *id)
            .collect();
        def_ids.extend((defs..g.env.defs().len()).map(DefId));
        let data_ids: Vec<DataId> = (datas..g.env.datas().len()).map(DataId).collect();
        if self
            .relied_on(def_ids.iter().copied(), data_ids.iter().copied())
            .is_empty()
        {
            return false;
        }
        let owners = &self.session.owners;
        for id in def_ids {
            if !self.tables.is_unfinished(HashKey::Def(id)) {
                self.tables.unfinished_defs.insert(owners, id, ());
            }
        }
        for d in data_ids {
            if !self.tables.is_unfinished(HashKey::Data(d)) {
                self.tables.unfinished_datas.insert(owners, d, ());
            }
        }
        true
    }
}
