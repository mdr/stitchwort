//! What the effects pre-pass ([`crate::effects::may_perform_at`]) found for
//! each expression it walked in a declaration, so that asking again about a
//! part of an expression already walked is a lookup: checking `f (f (… 0))`
//! asks about every argument at every level, which made the pre-pass's work
//! the square of the depth (docs/proposals/effects-prepass-cost.md,
//! option B).
//!
//! An answer depends on the expression, the context ([`Ctx::identity`]),
//! the abilities declared so far, whether a description's recursion is in
//! scope, `bare_rows_pure`, and what the metavariables are solved to; for a
//! list, tuple or record literal, also on the type expected, so a literal
//! asked about against a type is neither looked up nor recorded. The first
//! five are the key. The solutions are covered by a stamp: an answer is
//! reused only while nothing has been taken back (the store's
//! `meta_epoch`: the memo is emptied when it moves) and every solution made
//! since the answer's walk began is of a metavariable made since, which the
//! walk can't have read. Nothing else the walk reads changes within a
//! declaration: the names, the definitions' types, the dot-call tables.
//!
//! Expressions are named by their address, which another expression can
//! take once one is freed: the elaborator builds syntax, walks it and drops
//! it within a declaration. So an answer is recorded only for an expression
//! known to stay allocated as long as the entry: the expression of the
//! innermost open [`Scope`] (`check`, `infer` and computation mode open one
//! around the expression they're given, which they borrow throughout), the
//! parts a walk reaches from it, and the parts a later walk reaches from
//! one of those (`Memo::alive`). What a scope recorded is dropped when it
//! closes, while what it was reached from is still borrowed. Looking
//! up needs no such care: while an entry's expression is allocated, no
//! other expression can be at its address.
//!
//! With `STITCHWORT_SHADOW_MEMO=1`, every answer found here is worked out
//! again without the memo, and a difference panics.

use stitchwort_core::collections::{HashMap, HashSet};

use stitchwort_syntax::ast::Expr;

use crate::Elaborator;
use crate::check::Ctx;

/// The expression's address, the context's identity, and the number of
/// abilities declared with whether a description's recursion is in scope
/// and `bare_rows_pure` in its low two bits. (The memo holds an entry per
/// expression walked, so the key and entry are kept small.)
type Key = (usize, u64, u32);

/// The answers of one declaration (see the module doc).
#[derive(Default)]
pub(crate) struct Memo {
    entries: HashMap<Key, Entry>,
    /// The addresses of the expressions that stay allocated until the
    /// innermost scope that recorded them closes: those the walks reached
    /// from a scope's own expression, through their parts.
    alive: HashSet<usize>,
    /// The keys recorded, oldest first, so that a closing scope drops its
    /// own, entries and addresses: those from its length at the scope's
    /// opening on.
    log: Vec<Key>,
    /// The open scopes, innermost last: the address of each one's
    /// expression and the log's length when it opened.
    scopes: Vec<(usize, usize)>,
    /// The store's `meta_epoch` that the entries and `minima` belong to.
    epoch: u64,
    /// How much of the store's solution trail `minima` has taken in.
    seen: usize,
    /// For the trail since the epoch began, the solutions whose
    /// metavariable's number is smaller than that of every solution after
    /// it: their positions and numbers, both ascending. The smallest number
    /// solved since position `t` is that of the first at or after `t`.
    minima: Vec<(usize, usize)>,
    /// Set while the shadow mode works an answer out again: nothing is
    /// looked up or recorded.
    bypass: bool,
}

#[derive(Clone, Copy)]
struct Entry {
    performs: bool,
    /// How many metavariables there were, and how long the trail was, when
    /// the walk that found it began.
    metas: u32,
    trail: u32,
}

impl Memo {
    /// Whether nothing is recorded and no scope is open: so between
    /// declarations.
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty() && self.scopes.is_empty()
    }

    /// Takes in the solutions made since last asked, first emptying the
    /// memo if any were taken back.
    fn catch_up(&mut self, cx: &Ctx) {
        let store = cx.metas();
        let trail = store.meta_trail.borrow();
        if store.meta_epoch.get() != self.epoch {
            self.epoch = store.meta_epoch.get();
            self.entries.clear();
            self.minima.clear();
            self.seen = trail.len();
        }
        for (position, &(meta, _)) in trail.iter().enumerate().skip(self.seen) {
            while self.minima.last().is_some_and(|&(_, m)| m >= meta) {
                self.minima.pop();
            }
            self.minima.push((position, meta));
        }
        self.seen = trail.len();
    }

    /// Whether `entry` still holds: no solution since its walk began is of
    /// a metavariable that existed then.
    fn holds(&self, entry: &Entry) -> bool {
        let first = self
            .minima
            .partition_point(|&(at, _)| at < entry.trail as usize);
        self.minima
            .get(first)
            .is_none_or(|&(_, m)| m >= entry.metas as usize)
    }
}

/// A walk's use of the memo: the keys of the expressions it went through
/// in its loop (each has the walk's answer), whether it may record them,
/// and its stamp.
pub(crate) struct Walk {
    pub(crate) live: bool,
    keys: Vec<Key>,
    epoch: u64,
    metas: usize,
    trail: usize,
}

fn key(cx: &Ctx, expr: &Expr) -> Key {
    // A declaration can't have 2^30 abilities: each is a table entry.
    let abilities = u32::try_from(cx.e.tables.abilities.len()).unwrap_or(u32::MAX >> 2);
    (
        std::ptr::from_ref(expr) as usize,
        cx.identity(),
        abilities << 2
            | u32::from(cx.e.decl.recursion.is_some()) << 1
            | u32::from(cx.e.decl.bare_rows_pure.get()),
    )
}

/// Whether the answer for `expr` may depend on `expected` (see
/// `effects::performs_by_expected`, which `literal` is), so that it isn't
/// one of the memo's.
fn depends_on_expected(expr: &Expr, expected: bool, literal: bool) -> bool {
    expected && (literal || matches!(expr, Expr::Interpolated(..)))
}

impl Walk {
    /// The start of a walk of `expr`; `live` if `expr` is a part of an
    /// expression whose answers may be recorded.
    pub(crate) fn start(cx: &Ctx, expr: &Expr, live: bool) -> Walk {
        let mut memo = cx.e.decl.performs_memo.borrow_mut();
        let address = std::ptr::from_ref(expr) as usize;
        let live = !memo.bypass
            && (live
                || memo.scopes.last().is_some_and(|s| s.0 == address)
                || memo.alive.contains(&address));
        // So that `minima` covers the trail from the walk's start on.
        memo.catch_up(cx);
        let store = cx.metas();
        Walk {
            live,
            keys: Vec::new(),
            epoch: store.meta_epoch.get(),
            metas: store.metas.borrow().len(),
            trail: store.meta_trail.borrow().len(),
        }
    }

    /// The remembered answer for `expr`, reached by the walk's loop (asked
    /// against `expected` if `expected`); `literal` is whether it's a
    /// literal whose answer depends on the type expected. With no answer,
    /// `expr` is noted to be given the walk's.
    pub(crate) fn known(
        &mut self,
        cx: &Ctx,
        expr: &Expr,
        expected: bool,
        literal: bool,
    ) -> Option<bool> {
        if depends_on_expected(expr, expected, literal) {
            return None;
        }
        let mut memo = cx.e.decl.performs_memo.borrow_mut();
        if memo.bypass {
            return None;
        }
        let key = key(cx, expr);
        memo.catch_up(cx);
        if let Some(entry) = memo.entries.get(&key).copied() {
            if memo.holds(&entry) {
                return Some(entry.performs);
            }
            memo.entries.remove(&key);
        }
        if self.live {
            self.keys.push(key);
        }
        None
    }

    /// Records `performs` as the answer for the expressions the walk went
    /// through, if it may.
    pub(crate) fn record(self, cx: &Ctx, performs: bool) {
        if self.keys.is_empty() {
            return;
        }
        let mut memo = cx.e.decl.performs_memo.borrow_mut();
        for key in &self.keys {
            memo.alive.insert(key.0);
            memo.log.push(*key);
        }
        // Solutions taken back during the walk: the answer may have read
        // them.
        if cx.metas().meta_epoch.get() != self.epoch {
            return;
        }
        memo.catch_up(cx);
        // Counts too large to hold are not recorded.
        let (Ok(metas), Ok(trail)) = (u32::try_from(self.metas), u32::try_from(self.trail)) else {
            return;
        };
        let entry = Entry {
            performs,
            metas,
            trail,
        };
        // Or a solution of an older metavariable made during the walk, which
        // may have read it unsolved first.
        if !memo.holds(&entry) {
            return;
        }
        for key in self.keys {
            memo.entries.insert(key, entry);
        }
    }
}

/// Whether the shadow mode is on (`STITCHWORT_SHADOW_MEMO=1`).
pub(crate) fn shadow() -> bool {
    static SHADOW: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SHADOW.get_or_init(|| std::env::var_os("STITCHWORT_SHADOW_MEMO").is_some_and(|v| v == "1"))
}

/// `f`, with the memo neither consulted nor written: the shadow mode's
/// answer worked out afresh.
pub(crate) fn without<T>(cx: &Ctx, f: impl FnOnce() -> T) -> T {
    let before = std::mem::replace(&mut cx.e.decl.performs_memo.borrow_mut().bypass, true);
    let result = f();
    cx.e.decl.performs_memo.borrow_mut().bypass = before;
    result
}

/// An open scope of the memo (see the module doc): answers recorded while
/// it's the innermost are dropped when it closes.
pub(crate) struct Scope<'e> {
    e: &'e Elaborator,
    depth: usize,
}

/// Opens a scope around `expr`, which the caller borrows for as long as the
/// scope is open.
pub(crate) fn scope<'e>(e: &'e Elaborator, expr: &Expr) -> Scope<'e> {
    let mut memo = e.decl.performs_memo.borrow_mut();
    let depth = memo.scopes.len();
    let logged = memo.log.len();
    memo.scopes
        .push((std::ptr::from_ref(expr) as usize, logged));
    Scope { e, depth }
}

impl Drop for Scope<'_> {
    fn drop(&mut self) {
        let mut memo = self.e.decl.performs_memo.borrow_mut();
        let Some(&(_, logged)) = memo.scopes.get(self.depth) else {
            return;
        };
        memo.scopes.truncate(self.depth);
        let Memo {
            entries,
            alive,
            log,
            ..
        } = &mut *memo;
        for key in log.drain(logged.min(log.len())..) {
            entries.remove(&key);
            alive.remove(&key.0);
        }
    }
}
