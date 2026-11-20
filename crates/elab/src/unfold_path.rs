//! The middle step of the searches of `match`, `cases`, `rewrite` and the
//! transport along a `match`'s equation (docs/proposals/partial-unfold.md):
//! the target as written, with only the calls on the path to an occurrence
//! hidden inside them unfolded.
//!
//! The search as written ([`crate::matching`]'s and [`crate::rewrite`]'s
//! `as_written`) finds nothing where the term is only inside a call kept
//! folded, and the search after it reads the whole target back unfolded, so
//! the arms (or the next goal) have every definition unfolded: a
//! `Parse.Follows` around two parsers becomes the runs of both, already
//! applied to a state. [`opened`] reads the target back folded and walks it,
//! arguments before bodies:
//!
//! 1. A subterm the site's own test accepts ([`Oracle`]) is an occurrence,
//!    and is kept as it is.
//! 2. A call `f a₁ … aₙ` has its arguments walked first. If none of them,
//!    outside the occurrences found in them, mentions a variable the term
//!    looked for mentions, its unfolding can't hold a further occurrence
//!    (definitions are closed), and it is kept. Otherwise it is unfolded one
//!    step ([`unfold_once`]), read back folded and walked; if that finds an
//!    occurrence, the call is on the path and the unfolding replaces it,
//!    and otherwise the call is kept, its unfolding thrown away.
//! 3. Anything else is walked part by part.
//!
//! So `Follows (() => rowStart … lower second) …`, looking for `lower &&
//! isSome Colon second`, opens `rowStart` (its arguments mention `lower`),
//! finds the scrutinee as its `if`'s condition, and keeps `Follows` folded:
//! its arguments then mention `lower` only inside the occurrence.
//!
//! The result is a term convertible with the target, which the caller hands
//! to the search as written in place of the target read back folded: every
//! check that search makes (agreement with the usual search, no copy left
//! hidden, today's instance, the motive's type) is made on it unchanged, and
//! any failure falls back to the usual search. A call already being opened
//! further out is not opened again inside itself, so a recursive definition
//! is opened once on each path, and at most [`MAX_TRIES`] calls are opened
//! in all.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use stitchwort_core::value::{eval, quote_folded, unfold_once};
use stitchwort_core::{DefId, Icit, Term, Value};
use stitchwort_syntax::Diagnostic;

use crate::check::{Ctx, Result};
use crate::lift::{replace_with, replace_with_under};
use crate::rewrite::{Key, key, mentions_bound};

/// Whether a candidate, under the given number of binders of the target, is
/// an occurrence: the site's own comparison, which leaves the context as it
/// found it.
pub(crate) type Oracle<'o> = dyn Fn(&mut Ctx, &Term, usize) -> Result<bool> + 'o;

/// The calls one walk may unfold, whether or not they turn out to be on the
/// path: each costs an unfolding, a read-back and a walk of it.
const MAX_TRIES: usize = 64;

/// The type of the annotation that marks an occurrence during the walk:
/// never a real unknown, and stripped before the term is returned.
const OCCURRENCE: usize = usize::MAX - 1;

/// `target` (read back folded, in `cx`'s context) with the calls on the path
/// to an occurrence unfolded, as the module describes; `None` if there are
/// none, so that the result would be `target` itself. `keys` are the heads
/// worth asking `oracle` about, and `relevant` the levels of the variables
/// that the terms looked for mention.
pub(crate) fn opened(
    cx: &mut Ctx,
    target: &Term,
    keys: &[Key],
    relevant: &[usize],
    oracle: &Oracle,
) -> Result<Option<Term>> {
    let level = cx.level();
    let mut is_relevant = vec![false; level];
    for &l in relevant {
        if l < level {
            is_relevant[l] = true;
        }
    }
    if !is_relevant.iter().any(|&r| r) {
        return Ok(None);
    }
    let g = cx.g();
    let walk = Walk {
        cx: RefCell::new(cx),
        keys,
        relevant: is_relevant,
        oracle,
        level,
        opening: RefCell::new(Vec::new()),
        opened: Cell::new(0),
        tries: Cell::new(0),
        error: RefCell::new(None),
    };
    let walked = walk.walk(target, 0)?;
    if walk.opened.get() == 0 {
        return Ok(None);
    }
    let stripped = replace_with(
        &g,
        &walked,
        level,
        &|l| Ok(Term::Var(level - 1 - l)),
        &|t, _| marked(t).map(|e| e.clone()),
    )?;
    Ok(Some(stripped))
}

struct Walk<'c, 'e, 'k, 'o> {
    cx: RefCell<&'c mut Ctx<'e>>,
    keys: &'k [Key],
    /// By level, below `level`.
    relevant: Vec<bool>,
    oracle: &'o Oracle<'o>,
    level: usize,
    /// The definitions whose calls are being opened, outermost first.
    opening: RefCell<Vec<DefId>>,
    /// Calls opened and kept open: on the path.
    opened: Cell<usize>,
    tries: Cell<usize>,
    error: RefCell<Option<Diagnostic>>,
}

impl Walk<'_, '_, '_, '_> {
    /// `term`, under `under` binders of the target, walked: its occurrences
    /// marked ([`OCCURRENCE`]), the calls on the path to one unfolded.
    fn walk(&self, term: &Term, under: usize) -> Result<Term> {
        let g = self.cx.borrow().g();
        let level = self.level;
        let walked = replace_with_under(
            &g,
            term,
            level,
            under,
            &|l| Ok(Term::Var(level - 1 - l)),
            &|t, under| self.visit(t, under),
        );
        if let Some(e) = self.error.take() {
            return Err(e);
        }
        walked
    }

    fn visit(&self, t: &Term, under: usize) -> Option<Term> {
        if self.error.borrow().is_some() {
            return Some(t.clone());
        }
        let found = (|| -> Result<Option<Term>> {
            if let Some(k) = key(t, under)
                && self.keys.contains(&k)
                && !mentions_bound(t, under)
            {
                let mut cx = self.cx.borrow_mut();
                if (self.oracle)(&mut cx, t, under)? {
                    return Ok(Some(mark(t)));
                }
            }
            if let (Term::Def(id), _) = t.spine()
                && matches!(t.strip_loc(), Term::App(..))
            {
                return self.call(*id, t, under).map(Some);
            }
            Ok(None)
        })();
        match found {
            Ok(found) => found,
            Err(e) => {
                *self.error.borrow_mut() = Some(e);
                Some(t.clone())
            }
        }
    }

    /// The call `t` of `id`, under `under` binders: its arguments walked,
    /// then opened if it is on the path.
    fn call(&self, id: DefId, t: &Term, under: usize) -> Result<Term> {
        let mut args: Vec<(&Term, Icit)> = Vec::new();
        let mut node = t.strip_loc();
        while let Term::App(f, a, i) = node {
            args.push((a, *i));
            node = f.strip_loc();
        }
        args.reverse();
        let mut walked = Vec::with_capacity(args.len());
        for (a, i) in args {
            walked.push((self.walk(a, under)?, i));
        }
        let mentions = walked.iter().any(|(a, _)| self.mentions(a, under));
        let mut call = Term::Def(id);
        for (a, i) in walked {
            call = Term::App(Rc::new(call), Rc::new(a), i);
        }
        if !mentions || self.tries.get() >= MAX_TRIES || self.opening.borrow().contains(&id) {
            return Ok(call);
        }
        self.tries.set(self.tries.get() + 1);
        let body = {
            let cx = self.cx.borrow();
            let g = cx.g();
            let mut env = cx.env.clone();
            env.extend((0..under).map(|k| Value::var(self.level + k)));
            let Value::Call(id, spine, _) = eval(&g, &env, &call)? else {
                return Ok(call);
            };
            let step = unfold_once(&g, id, spine)?;
            quote_folded(&g, self.level + under, &step)?
        };
        self.opening.borrow_mut().push(id);
        let inside = self.walk(&body, under);
        self.opening.borrow_mut().pop();
        let inside = inside?;
        if !inside.subterms().any(|(t, _)| marked(t).is_some()) {
            return Ok(call);
        }
        self.opened.set(self.opened.get() + 1);
        Ok(inside)
    }

    /// Whether `t`, under `under` binders of the target, mentions a relevant
    /// variable outside the occurrences marked in it.
    fn mentions(&self, t: &Term, under: usize) -> bool {
        // A work list: a term read back can nest too deeply to recurse.
        let mut pending = vec![(t, under)];
        while let Some((t, under)) = pending.pop() {
            if marked(t).is_some() {
                continue;
            }
            if let Term::Var(ix) | Term::Case(ix, ..) | Term::NumCase(ix, ..) = t
                && *ix >= under
                && *ix - under < self.level
                && self.relevant[self.level - 1 - (ix - under)]
            {
                return true;
            }
            t.for_each_child(|child, binders| pending.push((child, under + binders)));
        }
        false
    }
}

fn mark(t: &Term) -> Term {
    Term::Ann(Rc::new(t.clone()), Rc::new(Term::Meta(OCCURRENCE)))
}

/// The occurrence `t` marks, if it is a mark.
fn marked(t: &Term) -> Option<&Term> {
    match t {
        Term::Ann(e, ty) if matches!(**ty, Term::Meta(OCCURRENCE)) => Some(e),
        _ => None,
    }
}
