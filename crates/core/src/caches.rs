//! What the evaluator derives from the environment and can work out again:
//! nothing here is a fact, so a rewind only cuts it by id
//! (docs/proposals/globals-split.md §2).

use std::cell::RefCell;
use std::rc::Rc;

use crate::collections::HashMap;
use crate::erase::DefErasure;
use crate::globals::HashKey;
use crate::hash::ContentHash;

#[derive(Default)]
pub struct EvalCaches {
    /// Content hashes computed so far. Declarations never change once
    /// checked, so these never go stale.
    pub hashes: RefCell<HashMap<HashKey, ContentHash>>,
    /// What each definition erases, worked out on first use from its type,
    /// which never changes once it's final (`erase.rs`).
    pub(crate) erasure_defs: RefCell<Vec<Option<Rc<DefErasure>>>>,
}

impl EvalCaches {
    /// Forgets what was derived for the definitions from `defs` on and the
    /// data types from `datas` on, when they are removed again.
    pub fn forget_from(&self, defs: usize, datas: usize) {
        self.hashes.borrow_mut().retain(|k, _| match k {
            HashKey::Def(id) => id.0 < defs,
            HashKey::Data(d) => d.0 < datas,
        });
        self.erasure_defs.borrow_mut().truncate(defs);
    }
}
