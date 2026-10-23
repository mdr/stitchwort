//! The axiom report (docs/proposals/map-equality.md §10, D864 and D925):
//! which axioms a declaration depends on, transitively.
//!
//! Today there is one, `Quot.sound`. It's a term former, not a declaration,
//! so following named references isn't enough: the walk scans the checked
//! terms (type and body) of every definition it reaches, and of the data
//! types it reaches (their parameters, indices and constructor fields), at
//! every position, and reports each `Term::Quot(Sound)` node it finds. It
//! doesn't use the runtime's `reachable`, which skips the bodies of erased
//! definitions: a proof is exactly where `Quot.sound` shows up.

use std::collections::{BTreeSet, HashSet};

use stitchwort_core::globals::Globals;
use stitchwort_core::{DataId, DefId, QuotForm, Term};

/// The names of the axioms `root` depends on, sorted.
pub fn axioms(globals: &Globals, root: DefId) -> BTreeSet<&'static str> {
    let mut found = BTreeSet::new();
    let mut seen_defs = HashSet::new();
    let mut seen_datas = HashSet::new();
    let mut pending = vec![Node::Def(root)];
    while let Some(node) = pending.pop() {
        let mut terms: Vec<&Term> = Vec::new();
        match node {
            Node::Def(id) => {
                if !seen_defs.insert(id) {
                    continue;
                }
                let def = globals.def(id);
                terms.push(&def.ty);
                terms.extend(def.body().map(|b| &**b));
            }
            Node::Data(id) => {
                if !seen_datas.insert(id) {
                    continue;
                }
                let data = globals.data(id);
                terms.extend(data.params.iter().map(|(_, t)| t));
                terms.extend(data.indices.iter().map(|(_, t)| t));
                for ctor in &data.ctors {
                    terms.extend(ctor.fields.iter().map(|(_, t)| t));
                    terms.extend(ctor.result.iter());
                }
            }
        }
        for term in terms {
            for (sub, _) in term.subterms() {
                match sub {
                    Term::Quot(QuotForm::Sound, _, _) => {
                        found.insert("Quot.sound");
                    }
                    Term::Def(id) => pending.push(Node::Def(*id)),
                    Term::Data(id, _) | Term::Ctor(id, _, _) | Term::Case(_, id, _) => {
                        pending.push(Node::Data(*id));
                    }
                    _ => {}
                }
            }
        }
    }
    found
}

enum Node {
    Def(DefId),
    Data(DataId),
}
