//! `stitchwort uses`: which declarations of a project refer to a given one,
//! read off the checked terms (statement, body, run body, validators), not
//! off the text, so two namespaces defining the same short name are told
//! apart.

use std::collections::BTreeSet;

use serde::Serialize;
use stitchwort_core::DefId;
use stitchwort_core::assumption::Decl;

use crate::audit::Generated;
use crate::driver::Session;

/// A declaration that refers to the one asked about.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct User {
    /// The namespace the user is in: its full name without the last part.
    pub namespace: String,
    /// The user's full name.
    pub declaration: String,
    pub file: String,
    pub line: usize,
}

/// Whether the definition is a user-written one or a lifted helper of one
/// (`f.%match1`), which is credited to `f`.
fn owner(path: &str) -> &str {
    path.split_once(".%").map_or(path, |(head, _)| head)
}

impl Session {
    /// The definitions of `namespaces` (project namespaces as loaded) whose
    /// full name is `name` or ends in `.name`, written in source.
    pub fn defs_named(&self, namespaces: &[String], name: &str) -> Vec<DefId> {
        let made = Generated::new(&self.elab.ev());
        let g = self.elab.ev();
        let mut found = BTreeSet::new();
        for ns in namespaces {
            for i in self.elab.namespace_def_range(ns) {
                let path = g.def(DefId(i)).path();
                let matches = **path == *name
                    || path
                        .strip_suffix(name)
                        .is_some_and(|head| head.ends_with('.'));
                if matches && !path.contains('%') && !made.contains(&g, DefId(i)) {
                    found.insert(i);
                }
            }
        }
        found.into_iter().map(DefId).collect()
    }

    /// The declarations in `namespaces` whose checked terms mention
    /// `target`, sorted by namespace and place.
    pub fn users_of(&self, namespaces: &[String], target: DefId) -> Vec<User> {
        let g = self.elab.ev();
        let made = Generated::new(&g);
        let mut seen = BTreeSet::new();
        let mut users = BTreeSet::new();
        for ns in namespaces {
            for i in self.elab.namespace_def_range(ns) {
                if !seen.insert(i) || i == target.0 {
                    continue;
                }
                let id = DefId(i);
                let def = g.def(id);
                let path = def.path().to_string();
                let helper = path.contains(".%");
                if !helper && made.contains(&g, id) {
                    continue;
                }
                let mut hit = false;
                stitchwort_core::assumption::mentions(&g, Decl::Def(id), &mut |d| {
                    hit |= d == Decl::Def(target)
                });
                if !hit {
                    continue;
                }
                let name = owner(&path).to_string();
                if *name == **g.def(target).path() {
                    continue;
                }
                users.insert(self.user_at(&g, id, name));
            }
        }
        users.into_iter().collect()
    }

    /// The written definitions in the namespaces `scope` (and under them)
    /// that no declaration of `namespaces`, the whole project, refers to
    /// besides itself. Tests, and theorems named `…Example`, are left out:
    /// nothing is meant to use them.
    pub fn unused_in(&self, namespaces: &[String], scope: &[String]) -> Vec<User> {
        let g = self.elab.ev();
        let made = Generated::new(&g);
        let mut seen = BTreeSet::new();
        let mut mentioned = BTreeSet::new();
        let mut candidates = Vec::new();
        let tests: BTreeSet<DefId> = self.elab.tests().iter().map(|t| t.def).collect();
        for ns in namespaces {
            for i in self.elab.namespace_def_range(ns) {
                if !seen.insert(i) {
                    continue;
                }
                let id = DefId(i);
                stitchwort_core::assumption::mentions(&g, Decl::Def(id), &mut |d| {
                    if let Decl::Def(used) = d
                        && used != id
                    {
                        mentioned.insert(used);
                    }
                });
                let path = g.def(id).path().to_string();
                let in_scope = scope.iter().any(|s| {
                    path.strip_prefix(s.as_str())
                        .is_some_and(|rest| rest.starts_with('.'))
                });
                if in_scope
                    && !path.contains('%')
                    && !path.ends_with("Example")
                    && !tests.contains(&id)
                    && !made.contains(&g, id)
                {
                    candidates.push(id);
                }
            }
        }
        let mut users: Vec<User> = candidates
            .into_iter()
            .filter(|id| !mentioned.contains(id))
            .map(|id| self.user_at(&g, id, g.def(id).path().to_string()))
            .collect();
        users.sort();
        users
    }

    fn user_at(&self, g: &stitchwort_core::Ev, id: DefId, name: String) -> User {
        let span = g.def(id).span();
        let file = self.sources.get(span.file);
        let before = &file.text[..(span.start as usize).min(file.text.len())];
        User {
            namespace: name
                .rsplit_once('.')
                .map_or(String::new(), |(ns, _)| ns.to_string()),
            declaration: name,
            file: file.name.clone(),
            line: before.matches('\n').count() + 1,
        }
    }
}
