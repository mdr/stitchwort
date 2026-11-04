//! Which declaration has each path, for the check cache: an entry names
//! the declarations it depends on by path, and a path may be used only if
//! exactly one declaration has it.
//!
//! It is derived from the environment, so a rewind only cuts it to the
//! declarations that remain, as [`super::owners::Owners`] cuts its tags.
//! Like them it is filled in lazily ([`DeclPaths::sync`]) from the
//! declarations made since it last looked, so nothing that makes one has to
//! tell it. It replaces a map over the whole environment built for each
//! entry, which grew with the square of the project.

use stitchwort_core::collections::HashMap;
use stitchwort_core::env::Env;
use stitchwort_core::term::Name;

use super::table::Ids;

/// The ids with one path: the first, and any others (rare).
#[derive(Default)]
struct Holders {
    first: usize,
    more: Vec<usize>,
}

#[derive(Default)]
struct Kind {
    by_path: HashMap<Name, Holders>,
    /// The path of each declaration indexed, to take it out again.
    paths: Vec<Name>,
}

impl Kind {
    fn extend(&mut self, new: impl Iterator<Item = Name>) {
        for path in new {
            let id = self.paths.len();
            match self.by_path.get_mut(&path) {
                Some(h) => h.more.push(id),
                None => {
                    self.by_path.insert(
                        path.clone(),
                        Holders {
                            first: id,
                            more: Vec::new(),
                        },
                    );
                }
            }
            self.paths.push(path);
        }
    }

    fn truncate(&mut self, len: usize) {
        while self.paths.len() > len {
            let path = self.paths.pop().expect("longer than len");
            let id = self.paths.len();
            let h = self.by_path.get_mut(&path).expect("indexed");
            if h.more.pop().is_none() {
                debug_assert_eq!(h.first, id);
                self.by_path.remove(&path);
            }
        }
    }

    fn unique(&self, path: &str) -> Option<usize> {
        self.by_path
            .get(path)
            .filter(|h| h.more.is_empty())
            .map(|h| h.first)
    }
}

#[derive(Default)]
pub(crate) struct DeclPaths {
    defs: Kind,
    datas: Kind,
}

/// Where [`DeclPaths`] are, for a rewind.
pub(crate) struct Mark {
    ids: Ids,
}

impl DeclPaths {
    /// Indexes the declarations made since the last call.
    pub(crate) fn sync(&mut self, env: &Env) {
        let (defs, datas) = (env.defs(), env.datas());
        debug_assert!(
            self.defs.paths.len() <= defs.len()
                && self
                    .defs
                    .paths
                    .last()
                    .is_none_or(|p| *p == *defs[self.defs.paths.len() - 1].path()),
            "the path index missed a cut"
        );
        debug_assert!(
            self.datas.paths.len() <= datas.len()
                && self
                    .datas
                    .paths
                    .last()
                    .is_none_or(|p| *p == *datas[self.datas.paths.len() - 1].path()),
            "the path index missed a cut"
        );
        let n = self.defs.paths.len();
        self.defs.extend(defs[n..].iter().map(|d| d.path().clone()));
        let n = self.datas.paths.len();
        self.datas
            .extend(datas[n..].iter().map(|d| d.path().clone()));
    }

    /// The definition with `path`, if exactly one has it.
    pub(crate) fn unique_def(&self, path: &str) -> Option<usize> {
        self.defs.unique(path)
    }

    pub(crate) fn unique_data(&self, path: &str) -> Option<usize> {
        self.datas.unique(path)
    }

    /// Forgets the declarations from `ids` on, which have been removed.
    pub(crate) fn truncate(&mut self, ids: Ids) {
        self.defs.truncate(ids.defs);
        self.datas.truncate(ids.datas);
    }

    pub(crate) fn mark(&self) -> Mark {
        Mark {
            ids: Ids {
                defs: self.defs.paths.len(),
                datas: self.datas.paths.len(),
            },
        }
    }

    /// Back to `m`: what was indexed after it is removed (the declarations
    /// it covers are still there, as a rewind goes in stack order).
    pub(crate) fn rewind(&mut self, m: &Mark) {
        self.truncate(m.ids);
    }
}
