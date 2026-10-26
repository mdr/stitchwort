//! Opaque definitions in the elaborator (docs/proposals/opaque-definitions.md
//! §6): `opaque def f …`, the `unfolding f, g` clause, and the generated
//! equation `f.unfold`. The kernel enforces opacity (`Def::opaque`,
//! `check::mark_opaque`, `check::set_unfolding`); here:
//!
//! - **The clause.** Its names are resolved once the declaration's group
//!   can be named, and refused with the clause's own spans where the kernel
//!   would refuse them: a definition that isn't opaque
//!   (`E-UNFOLDING-TRANSPARENT`), a name that isn't an opaque definition
//!   (`E-NOT-OPAQUE`), a member of the same group (`E-UNFOLDING-GROUP`).
//!   A theorem with a clause is made opaque (§6.4, rule 3). The names are
//!   also dependency edges (`module::decl_refs`), so a group-mate is found.
//! - **The body.** It's elaborated under the same transparency set the
//!   kernel will check it under ([`Elaborator::in_body_of`]), so the
//!   elaborator and the kernel agree on what unfolds (§6.4). Glued calls
//!   remember their unfoldings by metavariable epoch, so the epoch moves
//!   whenever the set does. The helpers lifted from such a body (a `match`,
//!   a local definition) are opaque with the same clause, and the body
//!   unfolds those admitted before it (`lift.rs`).
//! - **`f.unfold`.** Every opaque `f` without a clause gets the theorem
//!   `f.unfold (x…): f x… = f.%body x…`, proved by `rfl` with `unfolding f`,
//!   where `f.%body` is a folded transparent copy of the body
//!   ([`Elaborator::opaque_unfold`]). One with a clause gets none, as its
//!   statement may need the clause to be well-typed; naming it is
//!   `E-NO-UNFOLD-EQUATION` ([`no_unfold_equation`]).

use std::rc::Rc;

use stitchwort_core::globals::State;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::{DefId, Globals, Icit, Name, Term};
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
    /// `opaque def`, or is a theorem with an `unfolding` clause (§6.4, rule 3).
    pub(crate) fn mark_opaque_signature(&mut self, signature: &Decl, id: DefId) {
        if let Decl::Signature {
            opaque,
            theorem,
            unfolding,
            ..
        } = signature
            && (*opaque || (*theorem && !unfolding.is_empty()))
        {
            kernel::mark_opaque(&mut self.globals, id);
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
            let def = self.globals.def(other);
            if def.state() == State::Final && !def.opaque {
                return Err(Diagnostic::error(
                    "E-NOT-OPAQUE",
                    format!("`{}` isn't opaque, so it always unfolds", name.text),
                )
                .with_label(name.span, "nothing to unfold")
                .with_note(format!("remove `{}` from `unfolding`", name.text)));
            }
            found.push(other);
        }
        kernel::set_unfolding(&mut self.globals, id, &found);
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
        let unfolding = self.globals.def(id).unfolding.clone();
        if unfolding.is_empty() {
            return body(self);
        }
        let set = kernel::transparency_set(&self.globals, id, ids)?;
        *self.owner_unfolding.borrow_mut() = Some(unfolding.clone());
        self.owner_helpers.borrow_mut().clear();
        // A glued call keeps its unfolding for as long as the metavariable
        // epoch stands; a different set may unfold it differently.
        self.globals.metas_taken_back();
        let guard = self.globals.transparent.set(set);
        let result = body(self);
        drop(guard);
        self.globals.metas_taken_back();
        *self.owner_unfolding.borrow_mut() = None;
        let helpers = std::mem::take(&mut *self.owner_helpers.borrow_mut());
        if result.is_ok() && !helpers.is_empty() {
            let mut list: Vec<DefId> = unfolding.to_vec();
            list.extend(helpers);
            kernel::set_unfolding(&mut self.globals, id, &list);
        }
        result
    }

    /// A helper lifted from the body being elaborated, just declared: opaque
    /// with its owner's clause, if the owner has one (§6.4: it may use what
    /// the owner's body may, so it must be opaque). `admitted` if it's
    /// admitted on its own, before the owner, which then unfolds it.
    pub(crate) fn opaque_helper(&mut self, id: DefId) {
        let Some(unfolding) = self.owner_unfolding.borrow().clone() else {
            return;
        };
        kernel::mark_opaque(&mut self.globals, id);
        kernel::set_unfolding(&mut self.globals, id, &unfolding);
    }

    /// Helper `id` (made opaque by [`Self::opaque_helper`]) was admitted
    /// on its own: its owner unfolds it.
    pub(crate) fn opaque_helper_admitted(&mut self, id: DefId) {
        if self.owner_unfolding.borrow().is_some() && self.globals.def(id).opaque {
            self.owner_helpers.borrow_mut().push(id);
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
    /// The proof is `rfl`; for a case tree it follows the tree, with `rfl`
    /// at each leaf, since a call of `f` stuck on a variable isn't equal to
    /// one of `f.%body` by conversion, but in each branch both take the same
    /// step.
    pub(crate) fn opaque_unfold(&mut self, def_name: &ast::Name, f: DefId) -> Result<()> {
        let g = &self.globals;
        let def = g.def(f);
        if !def.opaque || def.theorem || !def.unfolding.is_empty() || def.state() != State::Final {
            return Ok(());
        }
        let Some(body) = def.body().cloned() else {
            return Ok(());
        };
        let key = self.declaration_key(def_name)?;
        let display = crate::scope::display(&key).to_string();
        let span = def.span;
        let def_ty = def.ty.clone();
        let arity = def.arity;
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
        let copy = kernel::declare_def(&mut self.globals, &name, &def_ty, false, false, span)?;
        kernel::mark_folded(&mut self.globals, copy);
        kernel::define_group(&mut self.globals, &[(copy, (*body).clone())])?;
        let ty = pis(
            &binders,
            Term::Eq(
                None,
                Rc::new(args(Term::Def(f))),
                Rc::new(args(Term::Def(copy))),
            ),
        );
        let name: Name = format!("{display}.unfold").into();
        let unfold = kernel::declare_def(&mut self.globals, &name, &ty, true, false, span)?;
        kernel::mark_opaque(&mut self.globals, unfold);
        kernel::set_unfolding(&mut self.globals, unfold, &[f]);
        let names: Vec<(Name, Icit)> = binders.iter().map(|b| (b.name.clone(), b.icit)).collect();
        kernel::define_group(&mut self.globals, &[(unfold, lams(&names, proof))])?;
        if let Some(item) = self.module.item {
            for id in [copy, unfold] {
                self.module.def_items.insert(id, item);
            }
        }
        let unfold_key = format!("{key}.unfold");
        self.scope
            .insert(&unfold_key, Global::Def(unfold), def_name.span, false);
        self.helper_keys.insert(unfold_key);
        Ok(())
    }
}

/// How many numbers deep a number pattern's proof splits (below):
/// `| 100 => …` needs 101 levels. A larger one gets no `f.unfold`.
const MAX_NUMBER_SPLIT: usize = 64;

/// A proof that case tree `tree` (`f`'s body) gives what its copy does:
/// the same tree with `rfl` at each leaf. A `NumCase` doesn't do: in its
/// default nothing is known about the number, so both calls stay stuck. It
/// becomes the `Zero`/`Succ` cases it stands for (docs/core.md, `NumCase`),
/// down to one past its largest number, where both calls take the default.
/// `None` if a number is too large for that.
fn refl_tree(g: &Globals, tree: &Term) -> Result<Option<Term>> {
    g.budget.nesting("elaborator")?;
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
                g.registry.data(Builtin::Nat),
                g.registry.ctor(Builtin::Zero),
                g.registry.ctor(Builtin::Succ),
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

/// `E-NO-UNFOLD-EQUATION` if `name` is `f.unfold` for an opaque `f` with an
/// `unfolding` clause, which has no equation (§6.3).
pub(crate) fn no_unfold_equation(e: &Elaborator, name: &ast::Name) -> Option<Diagnostic> {
    let owner = name.text.strip_suffix(".unfold")?;
    let Some((Global::Def(f), _)) = e.named(owner) else {
        return None;
    };
    let def = e.globals.def(*f);
    if !def.opaque || def.unfolding.is_empty() || def.theorem {
        return None;
    }
    let unfolded: Vec<String> = def
        .unfolding
        .iter()
        .map(|id| &e.globals.def(*id).name)
        // Not the helpers lifted from its body, which it unfolds too.
        .filter(|n| !n.contains('%'))
        .map(|n| format!("`{n}`"))
        .collect();
    Some(
        Diagnostic::error(
            "E-NO-UNFOLD-EQUATION",
            format!("`{}` has no `unfold` equation", def.name),
        )
        .with_label(
            name.span,
            format!(
                "`{}.unfold` can't be stated without unfolding {}",
                def.name,
                unfolded.join(", ")
            ),
        )
        .with_note(format!(
            "prove what you need in a theorem with `unfolding {}`",
            def.name
        )),
    )
}
