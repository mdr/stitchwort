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

use crate::collections::HashSet;
use crate::ev::Ev;
use crate::term::{DataId, DefId, Term};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    Def(DefId),
    Data(DataId),
}

/// The assumptions `roots` rely on, together: every assumption reachable
/// from their checked types and bodies (a root that is itself one
/// included). Empty means none is used. Declarations that aren't final are
/// walked as far as they have terms.
pub fn relied_on(g: &Ev, roots: &[DefId]) -> BTreeSet<DefId> {
    let mut found = BTreeSet::new();
    let mut seen: HashSet<Node> = HashSet::default();
    let mut pending: Vec<Node> = roots.iter().map(|id| Node::Def(*id)).collect();
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        let mut terms: Vec<&Term> = Vec::new();
        match node {
            Node::Def(id) => {
                let def = g.def(id);
                if def.assumption.is_some() {
                    found.insert(id);
                }
                terms.push(&def.ty);
                terms.extend(def.body.as_deref());
                terms.extend(def.run_body.as_deref());
                terms.extend(def.validators.iter().map(|v| &v.decision));
                pending.extend(def.unfolding.iter().map(|d| Node::Def(*d)));
            }
            Node::Data(id) => {
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
                    Term::Def(id) => pending.push(Node::Def(*id)),
                    Term::Data(id, _)
                    | Term::Ctor(id, _, _)
                    | Term::Case(_, id, _)
                    | Term::Proj(id, ..) => pending.push(Node::Data(*id)),
                    _ => {}
                }
            }
        }
    }
    found
}
