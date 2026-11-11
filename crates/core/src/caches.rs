//! What the evaluator derives from the environment and can work out again:
//! nothing here is a fact, so a rewind only cuts it by id
//! (docs/proposals/globals-split.md §2).

use std::cell::RefCell;
use std::rc::Rc;

use crate::assumption::Decl;
use crate::collections::HashMap;
use crate::erase::{DefErasure, ProofPositions};
use crate::globals::HashKey;
use crate::hash::ContentHash;
use crate::term::DefId;

#[derive(Default)]
pub struct EvalCaches {
    /// Content hashes computed so far. Declarations never change once
    /// checked, so these never go stale.
    pub hashes: RefCell<HashMap<HashKey, ContentHash>>,
    /// What each definition erases, worked out on first use from its type,
    /// which never changes once it's final (`erase.rs`).
    pub(crate) erasure_defs: RefCell<Vec<Option<Rc<DefErasure>>>>,
    /// Content hashes without proofs (`hash::proofless_hash`), computed so
    /// far.
    pub(crate) proofless: RefCell<HashMap<HashKey, ContentHash>>,
    /// Which parts of each definition are proofs (`erase::proof_positions`).
    pub(crate) proof_positions: RefCell<Vec<Option<Rc<ProofPositions>>>>,
    /// For final declarations: an open goal's assumption each relies on, or
    /// `None` if it relies on none (`assumption::relies_on`). A final
    /// declaration's terms never change, nor do those of what it mentions,
    /// which are final too.
    pub(crate) reliance: RefCell<HashMap<Decl, Option<DefId>>>,
}

impl EvalCaches {
    /// Forgets what was derived for the definitions from `defs` on and the
    /// data types from `datas` on, when they are removed again.
    pub fn forget_from(&self, defs: usize, datas: usize) {
        self.hashes.borrow_mut().retain(|k, _| match k {
            HashKey::Def(id) => id.0 < defs,
            HashKey::Data(d) => d.0 < datas,
        });
        self.proofless.borrow_mut().retain(|k, _| match k {
            HashKey::Def(id) => id.0 < defs,
            HashKey::Data(d) => d.0 < datas,
        });
        self.erasure_defs.borrow_mut().truncate(defs);
        self.proof_positions.borrow_mut().truncate(defs);
        let kept = |d: &Decl| match d {
            Decl::Def(id) => id.0 < defs,
            Decl::Data(d) => d.0 < datas,
        };
        self.reliance
            .borrow_mut()
            .retain(|d, a| kept(d) && a.is_none_or(|a| a.0 < defs));
    }
}
