//! Opaque definitions in the elaborator (docs/proposals/opaque-definitions.md
//! §6): `opaque def f …`, the `unfolding f, g` clause, and the generated
//! equation `f.unfold`. The kernel enforces opacity (`Def::opaque`,
//! `check::mark_opaque`, `check::set_unfolding`); here:
//!
//! - **The clause.** Its names are resolved once the declaration's group
//!   can be named, and refused with the clause's own spans where the kernel
//!   would refuse them: a definition that isn't opaque
//!   (`E-UNFOLDING-TRANSPARENT`), a theorem, whose proof is sealed
//!   (`E-UNFOLDING-THEOREM`), a name that isn't an opaque definition
//!   (`E-NOT-OPAQUE`), a member of the same group (`E-UNFOLDING-GROUP`).
//!   A theorem's proof is sealed by rule F, not by the opaque flag: a
//!   theorem is opaque only through a list, which the kernel allows it. The names are also dependency edges (`module::decl_refs`), so a
//!   group-mate is found.
//! - **The body.** It's elaborated under the same transparency set the
//!   kernel will check it under ([`Elaborator::in_body_of`]), so the
//!   elaborator and the kernel agree on what unfolds (§6.4). Glued calls
//!   remember their unfoldings by metavariable epoch, so the epoch moves
//!   whenever the set does. The helpers lifted from such a body (a `match`,
//!   a local definition) are opaque with the same clause and the helpers
//!   before them, and the body unfolds each from when it is admitted
//!   (`lift.rs`).
//! - **`f.unfold`.** Every opaque `f` without a clause gets the theorem
//!   `f.unfold (x…): f x… = f.%body x…`, proved by `byComputing` with `unfolding f`,
//!   where `f.%body` is a folded transparent copy of the body
//!   ([`Elaborator::opaque_unfold`]). One with a clause gets none, as its
//!   statement may need the clause to be well-typed; naming it is
//!   `E-NO-UNFOLD-EQUATION` ([`no_unfold_equation`]).

use std::rc::Rc;

use stitchwort_core::globals::State;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::{DefId, Ev, Icit, Name, Term};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{self, Decl};

use crate::decreasing::{Binder, apps, lams, pis, split_pis};
use crate::{Elaborator, Global, Result, kernel};

impl Elaborator {
    /// `E-UNFOLDING-TRANSPARENT` for a signature with an `unfolding` clause
    /// that isn't opaque and isn't a theorem, before anything is declared.
    pub(crate) fn check_unfolding_clause(&self, signature: &Decl) -> Result<()> {
        let Decl::Signature {
            name,
            opaque,
            theorem,
            unfolding,
            ..
        } = signature
        else {
            return Ok(());
        };
        let (Some(first), Some(last)) = (unfolding.first(), unfolding.last()) else {
            return Ok(());
        };
        if *opaque || *theorem {
            return Ok(());
        }
        let listed: Vec<String> = unfolding.iter().map(|n| format!("`{}`", n.text)).collect();
        Err(Diagnostic::error(
            "E-UNFOLDING-TRANSPARENT",
            format!(
                "`{}` unfolds {}, but isn't opaque",
                name.text,
                listed.join(", ")
            ),
        )
        .with_label(
            first.span.to(last.span),
            "a definition that always unfolds can't unfold opaque ones",
        )
        .with_note(format!(
            "write `opaque def {}`, or rewrite with `{}.unfold` instead",
            name.text, first.text
        )))
    }

    /// Marks the just-declared definition `id` opaque if it's written
    /// `opaque def`. A theorem isn't marked: rule F seals it.
    pub(crate) fn mark_opaque_signature(&mut self, signature: &Decl, id: DefId) {
        if let Decl::Signature { opaque, .. } = signature
            && *opaque
        {
            kernel::mark_opaque(&mut self.kernel, id);
        }
    }

    /// Resolves the `unfolding` clause of pending definition `id` (declared
    /// from `signature`, in group `ids`) and gives it to the kernel. Called
    /// once every member of the group can be named.
    pub(crate) fn resolve_unfolding(
        &mut self,
        signature: &Decl,
        id: DefId,
        ids: &[DefId],
    ) -> Result<()> {
        let Decl::Signature {
            name: def_name,
            unfolding,
            ..
        } = signature
        else {
            return Ok(());
        };
        if unfolding.is_empty() {
            return Ok(());
        }
        let mut found = Vec::new();
        for name in unfolding {
            self.note_name(name);
            let other = match self.named(&name.text) {
                None => return Err(self.not_found(name)),
                Some((Global::Def(other), _)) => *other,
                Some((Global::Unchecked(item), _)) => return Err(self.unchecked(name, *item)),
                Some(_) => {
                    return Err(Diagnostic::error(
                        "E-NOT-OPAQUE",
                        format!("`{}` isn't an opaque definition", name.text),
                    )
                    .with_label(name.span, "only an opaque definition can be unfolded")
                    .with_note(format!("remove `{}` from `unfolding`", name.text)));
                }
            };
            if self.kernel.def(other).theorem() {
                return Err(unfolding_theorem(name));
            }
            if ids.contains(&other) {
                return Err(Diagnostic::error(
                    "E-UNFOLDING-GROUP",
                    format!(
                        "`{}` can't unfold `{}`: they are checked together, so neither has a \
                         body yet",
                        def_name.text, name.text
                    ),
                )
                .with_label(name.span, format!("`{}` is in the same group", name.text))
                .with_note("prove what needs the body in a theorem after both"));
            }
            let def = self.kernel.def(other);
            if def.state() == State::Final && !def.opaque() {
                return Err(Diagnostic::error(
                    "E-NOT-OPAQUE",
                    format!("`{}` isn't opaque, so it always unfolds", name.text),
                )
                .with_label(name.span, "nothing to unfold")
                .with_note(format!("remove `{}` from `unfolding`", name.text)));
            }
            found.push(other);
        }
        kernel::set_unfolding(&mut self.kernel, id, &found);
        Ok(())
    }

    /// Runs `body`, the elaboration of pending definition `id`'s body (`id`
    /// a member of group `ids`), under the transparency set the kernel will
    /// check that body under (§6.4). With no `unfolding` clause that's the
    /// empty set, as everywhere else, and nothing changes. With one, the
    /// helpers lifted from the body are opaque with the same clause, and
    /// those admitted before `id` are added to its clause, so its body
    /// unfolds them as it would have before.
    pub(crate) fn in_body_of<T>(
        &mut self,
        id: DefId,
        ids: &[DefId],
        body: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<T> {
        let unfolding = self.kernel.def(id).unfolding().clone();
        if unfolding.is_empty() {
            return body(self);
        }
        let set = kernel::transparency_set(&self.ev(), id, ids)?;
        *self.decl.owner_unfolding.borrow_mut() = Some(unfolding.clone());
        self.decl.owner_helpers.borrow_mut().clear();
        // A glued call keeps its unfolding for as long as the metavariable
        // epoch stands; a different set may unfold it differently.
        self.attempt.store.metas_taken_back();
        let guard = self.kernel.machine.transparent.set(set);
        let result = body(self);
        drop(guard);
        self.attempt.store.metas_taken_back();
        *self.decl.owner_unfolding.borrow_mut() = None;
        let helpers = std::mem::take(&mut *self.decl.owner_helpers.borrow_mut());
        if result.is_ok() && !helpers.is_empty() {
            let mut list: Vec<DefId> = unfolding.to_vec();
            list.extend(helpers);
            kernel::set_unfolding(&mut self.kernel, id, &list);
        }
        result
    }

    /// A helper lifted from the body being elaborated, just declared: opaque
    /// with its owner's clause, if the owner has one (§6.4: it may use what
    /// the owner's body may, so it must be opaque), and the helpers admitted
    /// before it, which are part of the same body: a `match` proving
    /// something about an earlier `let`'s `match` unfolds that one, as the
    /// owner does ([`Self::opaque_helper_admitted`]).
    pub(crate) fn opaque_helper(&mut self, id: DefId) {
        let Some(unfolding) = self.decl.owner_unfolding.borrow().clone() else {
            return;
        };
        let mut list = unfolding.to_vec();
        list.extend(self.decl.owner_helpers.borrow().iter().copied());
        kernel::mark_opaque(&mut self.kernel, id);
        kernel::set_unfolding(&mut self.kernel, id, &list);
    }

    /// Helper `id` (made opaque by [`Self::opaque_helper`]) was admitted
    /// on its own: its owner unfolds it, from now on in the body being
    /// elaborated too (a retry after a local definition was admitted early
    /// must see its body, as the kernel will). Its own set is the owner's
    /// list and the helpers before it, closed: already in the set. A local
    /// theorem's helper stays sealed, as any theorem.
    pub(crate) fn opaque_helper_admitted(&mut self, id: DefId) {
        let def = self.kernel.def(id);
        if self.decl.owner_unfolding.borrow().is_some() && def.opaque() && !def.theorem() {
            self.decl.owner_helpers.borrow_mut().push(id);
            self.kernel.machine.transparent.insert(id);
            self.attempt.store.metas_taken_back();
        }
    }

    /// After opaque definition `f` (named `def_name`) is final, with no
    /// `unfolding` clause: its equation, a theorem with `unfolding f` named
    /// from outside as `f.unfold` (§6.3). It has the small statement
    /// `f.unfold (x…): f x… = f.%body x…`, where `f.%body` is a transparent
    /// copy of the body that stays folded, as a dictionary does, until
    /// something looks inside it: stating the body itself made one
    /// `rewrite f.unfold` read the whole body back unfolded, past the
    /// resource limits for the roguelike's generator (§9 lane 2's size
    /// tests). A case tree (arms) couldn't be written in a type anyway.
    ///
    /// The proof is `byComputing`; for a case tree it follows the tree, with `byComputing`
    /// at each leaf, since a call of `f` stuck on a variable isn't equal to
    /// one of `f.%body` by conversion, but in each branch both take the same
    /// step.
    pub(crate) fn opaque_unfold(&mut self, def_name: &ast::Name, f: DefId) -> Result<()> {
        let g = &self.ev();
        let def = g.def(f);
        if !def.opaque()
            || def.theorem()
            || !def.unfolding().is_empty()
            || def.state() != State::Final
        {
            return Ok(());
        }
        let Some(body) = def.body().cloned() else {
            return Ok(());
        };
        let key = self.declaration_key(def_name)?;
        let display = crate::scope::display(&key).to_string();
        let span = def.span();
        let def_ty = def.ty().clone();
        let arity = def.arity();
        // The parameters the body's lambdas bind, as far as the type shows
        // them (a synonym for a function type shows none).
        let (binders, _) = split_pis(&def_ty, Some(arity));
        let n = binders.len();
        let inner = Term::peel_lams_rc(&body, n);
        let args = |head: Term| {
            apps(
                head,
                binders
                    .iter()
                    .enumerate()
                    .map(|(i, b): (usize, &Binder)| (Term::Var(n - 1 - i), b.icit)),
            )
        };
        let proof = if has_case(&inner) {
            // The tree is at the top of the body, under all its parameters.
            if n != arity {
                return Ok(());
            }
            match refl_tree(g, &inner)? {
                Some(proof) => proof,
                None => return Ok(()),
            }
        } else {
            Term::Refl
        };
        let name: Name = format!("{display}.%body").into();
        let copy = kernel::declare_def(
            &mut self.kernel,
            &self.tables,
            &self.unit,
            &name,
            &def_ty,
            false,
            false,
            span,
        )?;
        kernel::mark_folded(&mut self.kernel, copy);
        kernel::define_group(&mut self.kernel, &self.tables, &[(copy, (*body).clone())])?;
        let ty = pis(
            &binders,
            Term::Eq(
                None,
                Rc::new(args(Term::Def(f))),
                Rc::new(args(Term::Def(copy))),
            ),
        );
        let name: Name = format!("{display}.unfold").into();
        let unfold = kernel::declare_def(
            &mut self.kernel,
            &self.tables,
            &self.unit,
            &name,
            &ty,
            true,
            false,
            span,
        )?;
        kernel::mark_opaque(&mut self.kernel, unfold);
        kernel::set_unfolding(&mut self.kernel, unfold, &[f]);
        let names: Vec<(Name, Icit)> = binders.iter().map(|b| (b.name.clone(), b.icit)).collect();
        kernel::define_group(
            &mut self.kernel,
            &self.tables,
            &[(unfold, lams(&names, proof))],
        )?;
        if let Some(item) = self.unit.module.item {
            for id in [copy, unfold] {
                self.unit.module.note_def(id, item);
            }
        }
        let unfold_key = format!("{key}.unfold");
        self.scope
            .insert(&unfold_key, Global::Def(unfold), def_name.span, false);
        self.tables.helper_keys.add(unfold_key);
        Ok(())
    }
}

/// How many numbers deep a number pattern's proof splits (below):
/// `| 100 => …` needs 101 levels. A larger one gets no `f.unfold`.
const MAX_NUMBER_SPLIT: usize = 64;

/// A proof that case tree `tree` (`f`'s body) gives what its copy does:
/// the same tree with `byComputing` at each leaf. A `NumCase` doesn't do: in its
/// default nothing is known about the number, so both calls stay stuck. It
/// becomes the `Zero`/`Succ` cases it stands for (docs/core.md, `NumCase`),
/// down to one past its largest number, where both calls take the default.
/// `None` if a number is too large for that.
fn refl_tree(g: &Ev, tree: &Term) -> Result<Option<Term>> {
    g.machine.budget.nesting("elaborator")?;
    Ok(Some(match tree {
        Term::Loc(span, inner) => match refl_tree(g, inner)? {
            Some(proof) => Term::Loc(*span, Rc::new(proof)),
            None => return Ok(None),
        },
        Term::Case(ix, d, branches) => {
            let mut out = Vec::new();
            for b in branches.iter() {
                let body = match &b.body {
                    Some(body) => match refl_tree(g, body)? {
                        Some(proof) => Some(Rc::new(proof)),
                        None => return Ok(None),
                    },
                    None => None,
                };
                out.push(Branch {
                    names: b.names.clone(),
                    body,
                });
            }
            Term::Case(*ix, *d, out.into())
        }
        Term::NumCase(ix, arms, default) => {
            let (Some(nat), Some((_, zero)), Some((_, succ))) = (
                g.env.registry().data(Builtin::Nat),
                g.env.registry().ctor(Builtin::Zero),
                g.env.registry().ctor(Builtin::Succ),
            ) else {
                return Ok(None);
            };
            let mut values = Vec::new();
            let mut proofs = Vec::new();
            for arm in arms.iter() {
                let Some(value) = usize::try_from(&*arm.value)
                    .ok()
                    .filter(|v| *v < MAX_NUMBER_SPLIT)
                else {
                    return Ok(None);
                };
                let Some(proof) = refl_tree(g, &arm.body)? else {
                    return Ok(None);
                };
                values.push(value);
                proofs.push(proof);
            }
            let Some(default) = refl_tree(g, default)? else {
                return Ok(None);
            };
            let largest = values.iter().copied().max().unwrap_or(0);
            // From the deepest level up: below `j` `Succ`s, the number is
            // `j` plus the newest variable, and `j` binders are new.
            let mut proof = default.shift(g, largest + 1, 0)?;
            for j in (0..=largest).rev() {
                let at = match values.iter().position(|v| *v == j) {
                    Some(k) => &proofs[k],
                    None => &default,
                };
                let at_zero = at.shift(g, j, 0)?;
                let scrutinee = if j == 0 { *ix } else { 0 };
                let mut branches = vec![
                    Branch {
                        names: Vec::new(),
                        body: None,
                    },
                    Branch {
                        names: Vec::new(),
                        body: None,
                    },
                ];
                branches[zero] = Branch {
                    names: Vec::new(),
                    body: Some(Rc::new(at_zero)),
                };
                branches[succ] = Branch {
                    names: vec!["n".into()],
                    body: Some(Rc::new(proof)),
                };
                proof = Term::Case(scrutinee, nat, branches.into());
            }
            proof
        }
        _ => Term::Refl,
    }))
}

/// Whether `term` has a `case` in it: a case tree.
fn has_case(term: &Term) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        match term {
            Term::Case(..) | Term::NumCase(..) => return true,
            _ => term.for_each_child(|t, _| pending.push(t)),
        }
    }
    false
}

/// The opaque definitions that stay folded in `terms` (read back from the
/// values of a failing comparison): each has a body, but the declaration
/// being checked may not use it ([`stitchwort_core::value::hidden`]). In
/// order of first appearance. Only called on the error path
/// (docs/proposals/opaque-definitions.md §6.10); a generated helper
/// (`f.%body`, `f.unfold`, a lifted helper) is never named.
///
/// A theorem is named only where a computation waits on its proof: the
/// proof a `J` transports along, a projection's subject, or an argument of
/// a lifted `match` (`f.%match1`). Elsewhere a call of one is just a proof
/// passed on, which hiding its body doesn't change, and theorem calls are
/// everywhere in types. And only when the theorem's arguments are all
/// closed: with a variable among them (`h.left`, `h` a hypothesis) the
/// computation would wait on the variable even if the proof were unsealed.
pub(crate) fn declined_in<'t>(g: &Ev, terms: impl IntoIterator<Item = &'t Term>) -> Vec<DefId> {
    if !g.env.defs().iter().any(|d| d.opaque()) {
        return Vec::new();
    }
    let mut found = Vec::new();
    let note = |id: DefId, found: &mut Vec<DefId>| {
        let def = g.def(id);
        if def.opaque()
            && def.body().is_some()
            && !def.name().contains('%')
            && stitchwort_core::value::hidden(g, id)
            && !found.contains(&id)
        {
            found.push(id);
        }
    };
    let mut pending: Vec<&Term> = terms.into_iter().collect();
    pending.reverse();
    while let Some(term) = pending.pop() {
        match term {
            Term::Def(id) if !g.def(*id).theorem() => note(*id, &mut found),
            Term::J(_, _, proof, _) | Term::Proj(_, _, proof) => {
                if let (Term::Def(id), args) = proof.spine()
                    && (!g.def(*id).theorem() || args.iter().all(|a| is_closed(a)))
                {
                    note(*id, &mut found);
                }
            }
            Term::App(..) => {
                let (head, args) = term.spine();
                if let Term::Def(h) = head
                    && g.def(*h).name().contains("%match")
                {
                    for arg in args {
                        if let (Term::Def(id), args) = arg.spine()
                            && g.def(*id).theorem()
                            && args.iter().all(|a| is_closed(a))
                        {
                            note(*id, &mut found);
                        }
                    }
                }
            }
            _ => {}
        }
        let first = pending.len();
        term.for_each_child(|t, _| pending.push(t));
        pending[first..].reverse();
    }
    found
}

/// Whether `term` mentions no variable bound outside it.
fn is_closed(term: &Term) -> bool {
    term.subterms().all(|(t, binders)| match t {
        Term::Var(i) | Term::Case(i, ..) | Term::NumCase(i, ..) => *i < binders,
        _ => true,
    })
}

/// Of the opaque definitions declined in `terms` ([`declined_in`]), those
/// whose body applies `pattern`'s head function: where a `rewrite` rule
/// that found nothing may have its pattern, hidden.
pub(crate) fn declined_holding(g: &Ev, terms: &[Term], pattern: &Term) -> Vec<DefId> {
    let Term::Def(head) = pattern.strip_loc().spine().0.strip_loc() else {
        return Vec::new();
    };
    declined_in(g, terms)
        .into_iter()
        .filter(|id| {
            let Some(body) = g.def(*id).body() else {
                return false;
            };
            let mut pending: Vec<&Term> = vec![body];
            while let Some(term) = pending.pop() {
                if matches!(term, Term::Def(d) if d == head) {
                    return true;
                }
                term.for_each_child(|t, _| pending.push(t));
            }
            false
        })
        .collect()
}

impl Elaborator {
    /// Whether the declaration being checked may have an `unfolding` clause:
    /// it is a theorem or an `opaque def`. True if it isn't known.
    pub(crate) fn current_may_unfold(&self) -> bool {
        let Some(item) = self.unit.module.item else {
            return true;
        };
        let mut found = false;
        for (id, owner) in &self.unit.module.def_items {
            let def = self.kernel.def(*id);
            if *owner == item && !def.name().contains('%') {
                if def.theorem() || def.opaque() {
                    return true;
                }
                found = true;
            }
        }
        !found
    }
}

/// `E-UNFOLDING-THEOREM`: theorem `name` in an `unfolding` list. Every
/// theorem is sealed (D3722, rule F), so nothing can depend on its proof.
fn unfolding_theorem(name: &ast::Name) -> Diagnostic {
    Diagnostic::error(
        "E-UNFOLDING-THEOREM",
        format!(
            "`{}` is a theorem, so its proof can't be unfolded",
            name.text
        ),
    )
    .with_label(name.span, "a theorem's proof is sealed")
    .with_note(format!(
        "use what `{}` states, and remove it from `unfolding`",
        name.text
    ))
}

/// The notes of §6.10 for the opaque definitions `ids` that were declined:
/// which are opaque, and the fixes (`unfolding f`, or `rewrite f.unfold`
/// where `f` has that equation). A theorem among them gets its own note
/// instead: its proof is sealed, so there's no fix that uses it.
pub(crate) fn opaque_notes(e: &Elaborator, ids: &[DefId]) -> Vec<String> {
    let g = &e.ev();
    let (theorems, ids): (Vec<DefId>, Vec<DefId>) =
        ids.iter().partition(|id| g.def(**id).theorem());
    let mut notes = Vec::new();
    if !theorems.is_empty() {
        let quoted: Vec<String> = theorems
            .iter()
            .map(|id| format!("`{}`", g.def(*id).name()))
            .collect();
        let list = join_and(&quoted, "and");
        notes.push(if theorems.len() == 1 {
            format!("{list} is a theorem: its proof is sealed, so only its statement is used")
        } else {
            format!(
                "{list} are theorems: their proofs are sealed, so only their statements are used"
            )
        });
    }
    if ids.is_empty() {
        return notes;
    }
    let quoted: Vec<String> = ids
        .iter()
        .map(|id| format!("`{}`", g.def(*id).name()))
        .collect();
    let list = join_and(&quoted, "and");
    let first = if ids.len() == 1 {
        format!("{list} is opaque, so its body isn't used here")
    } else {
        format!("{list} are opaque, so their bodies aren't used here")
    };
    notes.push(first);
    // A local definition (`f.go`) can't be named in a clause; unfolding its
    // owner unfolds it, unless the owner is a theorem, whose proof is
    // sealed.
    let mut unfolded: Vec<DefId> = Vec::new();
    let mut sealed = Vec::new();
    for &id in &ids {
        let shown = match local_owner(g, &e.tables, id) {
            None => id,
            // Its owner's clause didn't take it in: the owner failed.
            Some(None) => continue,
            Some(Some(owner)) if g.def(owner).theorem() => {
                let owner = g.def(owner).name();
                sealed.push(format!(
                    "`{}` is a local definition of the theorem `{owner}`, so only `{owner}`'s \
                     proof unfolds it; to use its body elsewhere, make it a top-level \
                     definition",
                    g.def(id).name(),
                ));
                continue;
            }
            Some(Some(owner)) => owner,
        };
        if !unfolded.contains(&shown) {
            unfolded.push(shown);
        }
    }
    if !unfolded.is_empty() {
        let unfolding = join_and(
            &unfolded
                .iter()
                .map(|id| format!("`unfolding {}`", g.def(*id).name()))
                .collect::<Vec<_>>(),
            "and",
        );
        let equations: Vec<String> = unfolded
            .iter()
            .filter_map(|id| {
                let name = format!("{}.unfold", g.def(*id).name());
                g.env
                    .defs()
                    .iter()
                    .any(|d| d.theorem() && d.name().as_ref() == name.as_str())
                    .then(|| format!("`{name}`"))
            })
            .collect();
        // A transparent `def` can't have the clause (`E-UNFOLDING-TRANSPARENT`).
        let add = if e.current_may_unfold() {
            format!("add {unfolding} after this declaration's signature")
        } else {
            format!("make this an `opaque def` and add {unfolding} after its signature")
        };
        notes.push(if equations.is_empty() {
            add
        } else {
            format!("{add}, or rewrite with {}", join_and(&equations, "or"))
        });
    }
    notes.extend(sealed);
    notes
}

/// The declaration whose body local definition `id` (`f.go`, lifted and
/// made opaque by its owner's `unfolding` clause) was written in: the one
/// that isn't itself a local definition and whose clause took `id` in
/// (`Elaborator::in_body_of`), if any. `None` if `id` isn't a local
/// definition.
fn local_owner(g: &Ev, tables: &crate::state::Tables, id: DefId) -> Option<Option<DefId>> {
    let is_local = |id: DefId| {
        let name = g.def(id).name();
        tables.helper_keys.contains_key(name.as_ref())
            || tables.helper_keys.contains_key(&format!("Std.{name}"))
    };
    if !is_local(id) {
        return None;
    }
    Some((0..g.env.defs().len()).map(DefId).find(|&owner| {
        let def = g.def(owner);
        def.unfolding().contains(&id) && !def.name().contains('%') && !is_local(owner)
    }))
}

fn join_and(items: &[String], word: &str) -> String {
    match items {
        [] => String::new(),
        [one] => one.clone(),
        [init @ .., last] => format!("{} {word} {last}", init.join(", ")),
    }
}

/// `E-NO-UNFOLD-EQUATION` if `name` is `f.unfold` for an opaque `f` with an
/// `unfolding` clause, which has no equation (§6.3).
pub(crate) fn no_unfold_equation(e: &Elaborator, name: &ast::Name) -> Option<Diagnostic> {
    let owner = name.text.strip_suffix(".unfold")?;
    let Some((Global::Def(f), _)) = e.named(owner) else {
        return None;
    };
    let def = e.kernel.def(*f);
    if !def.opaque() || def.unfolding().is_empty() || def.theorem() {
        return None;
    }
    let unfolded: Vec<String> = def
        .unfolding()
        .iter()
        .map(|id| e.kernel.def(*id).name())
        // Not the helpers lifted from its body, which it unfolds too.
        .filter(|n| !n.contains('%'))
        .map(|n| format!("`{n}`"))
        .collect();
    Some(
        Diagnostic::error(
            "E-NO-UNFOLD-EQUATION",
            format!("`{}` has no `unfold` equation", def.name()),
        )
        .with_label(
            name.span,
            format!(
                "`{}.unfold` can't be stated without unfolding {}",
                def.name(),
                unfolded.join(", ")
            ),
        )
        .with_note(format!(
            "prove what you need in a theorem with `unfolding {}`",
            def.name()
        )),
    )
}
