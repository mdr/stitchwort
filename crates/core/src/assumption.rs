//! Which open goals' assumptions a declaration relies on
//! (docs/core.md "Assumptions (open goals)").
//!
//! Reliance is read off the checked terms, never off the elaborator's
//! bookkeeping: a declaration relies on an assumption exactly when the
//! assumption is reachable through the types and bodies of the declarations
//! it refers to, transitively. So whatever the elaborator records or
//! forgets, nothing whose checked terms reach an assumption can be reported
//! as relying on none. This is the walk `stitchwort axioms` does for
//! `Quot.sound`, over the same terms, plus the parts of a declaration that
//! can bring in a term the walk would otherwise miss: a run body (what the
//! runtimes run), an `unfolding` list, validators.

use std::collections::BTreeSet;

use crate::collections::{HashMap, HashSet};
use crate::ev::Ev;
use crate::globals::State;
use crate::term::{DataId, DefId, Term};

/// A declaration the walk starts from or reaches.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Decl {
    Def(DefId),
    Data(DataId),
}

impl From<DefId> for Decl {
    fn from(id: DefId) -> Self {
        Decl::Def(id)
    }
}

impl From<DataId> for Decl {
    fn from(id: DataId) -> Self {
        Decl::Data(id)
    }
}

/// The assumptions `roots` rely on, together: every assumption reachable
/// from their checked types and bodies (a root that is itself one
/// included). Empty means none is used. Declarations that aren't final are
/// walked as far as they have terms.
pub fn relied_on(g: &Ev, roots: &[Decl]) -> BTreeSet<DefId> {
    relied_on_skipping(g, roots, &|_| false)
}

/// [`relied_on`], not walking into the declarations `skip` names: the
/// caller knows they rely on no assumption (they were final before any
/// assumption was made, say). A skipped declaration that does rely on one
/// hides it, so `skip` must be sure.
pub fn relied_on_skipping(g: &Ev, roots: &[Decl], skip: &dyn Fn(Decl) -> bool) -> BTreeSet<DefId> {
    let mut found = BTreeSet::new();
    let mut seen: HashSet<Decl> = HashSet::default();
    let mut pending: Vec<Decl> = roots.to_vec();
    while let Some(node) = pending.pop() {
        if !seen.insert(node) || skip(node) {
            continue;
        }
        if let Decl::Def(id) = node
            && g.def(id).assumption.is_some()
        {
            found.insert(id);
        }
        mentions(g, node, &mut |d| pending.push(d));
    }
    found
}

/// One assumption `root` relies on, or `None` if it relies on none: the
/// question [`relied_on_skipping`] answers, remembered for final
/// declarations (in the kernel's caches, cut by a rewind), so that asking
/// it of every declaration walks each final one once. Which assumption is
/// found, when there are several, is unspecified.
pub fn relies_on(g: &Ev, root: Decl, skip: &dyn Fn(Decl) -> bool) -> Option<DefId> {
    let memo = &g.caches.reliance;
    if let Some(known) = memo.borrow().get(&root) {
        return *known;
    }
    let is_final = |d: Decl| match d {
        Decl::Def(id) => g.def(id).state() == State::Final,
        Decl::Data(id) => g.data(id).state() == State::Final,
    };
    // Each declaration reached, with the one that first mentioned it.
    let mut reached: HashMap<Decl, Option<Decl>> = HashMap::default();
    let mut pending: Vec<(Decl, Option<Decl>)> = vec![(root, None)];
    let mut all_final = true;
    let mut found: Option<(Decl, DefId)> = None;
    while let Some((node, from)) = pending.pop() {
        if reached.contains_key(&node) {
            continue;
        }
        reached.insert(node, from);
        if skip(node) {
            continue;
        }
        let known = memo.borrow().get(&node).copied();
        match known {
            Some(Some(a)) => {
                found = Some((node, a));
                break;
            }
            Some(None) => continue,
            None => {}
        }
        if let Decl::Def(id) = node
            && g.def(id).assumption.is_some()
        {
            found = Some((node, id));
            break;
        }
        all_final &= is_final(node);
        mentions(g, node, &mut |d| pending.push((d, Some(node))));
    }
    let mut memo = memo.borrow_mut();
    match found {
        // Everything on the way from `root` to it relies on it.
        Some((mut node, a)) => {
            loop {
                if is_final(node) {
                    memo.insert(node, Some(a));
                }
                match reached[&node] {
                    Some(from) => node = from,
                    None => break,
                }
            }
            Some(a)
        }
        // Everything reached was walked to the end: none relies on one.
        // Unless something wasn't final, whose terms may not be all there.
        None => {
            if all_final {
                memo.extend(reached.into_keys().map(|d| (d, None)));
            }
            None
        }
    }
}

/// Calls `each` on every declaration `node`'s checked terms mention: its
/// type, body, run body, validators and `unfolding` list for a definition;
/// parameters, indices, fields and validators for a data type.
fn mentions(g: &Ev, node: Decl, each: &mut dyn FnMut(Decl)) {
    let builtins = g.env.builtins();
    let mut terms: Vec<&Term> = Vec::new();
    match node {
        Decl::Def(id) => {
            let def = g.def(id);
            terms.push(&def.ty);
            terms.extend(def.body.as_deref());
            terms.extend(def.run_body.as_deref());
            terms.extend(def.validators.iter().map(|v| &v.decision));
            def.unfolding.iter().for_each(|d| each(Decl::Def(*d)));
        }
        Decl::Data(id) => {
            let data = g.data(id);
            terms.extend(data.params().iter().map(|(_, t)| t));
            terms.extend(data.indices().iter().map(|(_, t)| t));
            for ctor in data.ctors() {
                terms.extend(ctor.fields.iter().map(|(_, t)| t));
                terms.extend(ctor.result.iter());
            }
            terms.extend(data.validators().iter().map(|v| &v.decision));
        }
    }
    for term in terms {
        for (sub, _) in term.subterms() {
            match sub {
                Term::Def(id) => each(Decl::Def(*id)),
                Term::Data(id, _)
                | Term::Ctor(id, _, _)
                | Term::Case(_, id, _)
                | Term::Proj(id, ..) => each(Decl::Data(*id)),
                // Literals refer to their data types implicitly, as the
                // hasher counts them (`Char`'s fields include its validity
                // proof).
                Term::Nat(_) | Term::NumCase(..) => {
                    builtins.nat.into_iter().for_each(|d| each(Decl::Data(d)))
                }
                Term::Chars(_) => {
                    if let Some(text) = &builtins.text {
                        each(Decl::Data(text.list));
                        each(Decl::Data(text.char));
                    }
                }
                _ => {}
            }
        }
    }
}
