//! Values, evaluation, quotation and conversion (normalisation by evaluation).
//!
//! Variables in values are de Bruijn *levels*: `Var(0)` is the outermost binder.
//!
//! Reduction policy: a definition stays folded (a neutral `Def` head) until it
//! has all its parameters *and* its case tree can take a step. This keeps
//! comparison from unfolding recursive definitions forever. See `docs/core.md`.

use crate::collections::{HashMap, HashSet, QuickHasher};
use crate::ev::Ev;
use std::rc::Rc;

use num_bigint::BigUint;

use crate::budget::{ResourceError, Result};
use crate::chars::{self, Chars};
use crate::erase::{self, erased};
use crate::nat_add::Unread;
use crate::native;
use crate::proof_counts;
use crate::registry::Builtin;
use crate::term::{Branch, DataId, DefId, Icit, Name, ProofMark, QuotForm, Sort, Term};

#[derive(Clone, Debug)]
pub enum Value {
    Sort(Sort),
    /// The mark, the term's, says whether the bound variable is a proof.
    /// (Not in the closure, which would make a value, and so the machine's
    /// frames, a word larger.)
    Pi(Name, Icit, Shared, Closure, ProofMark),
    Lam(Name, Icit, Closure, ProofMark),
    Data(DataId, DataArgs),
    /// Fields are shared, so copying a value (a list, say) is cheap.
    Ctor(DataId, usize, Values),
    /// A number, standing for `Succ (Succ … Zero)`. See [`native`].
    Nat(Rc<BigUint>),
    /// `k + x` for a number `k ≥ 1` and an `x` not built from numbers:
    /// `Succ` applied `k` times to `x`. See [`native::view`]. The exception
    /// is `compare_lazily`, which can build `k + call` for a folded call.
    NatAdd(Rc<BigUint>, Shared),
    /// A `List Char`, standing for `Cons (MkChar c byComputing) … Nil`. Never empty
    /// when made by evaluation (that's `Nil`). See [`chars`].
    Chars(Chars),
    Eq(Shared, Shared, Shared),
    Refl,
    /// A computation stuck on a variable or an unsolved metavariable, or a
    /// folded definition.
    Neutral(Head, Spine),
    /// A definition applied to all its parameters, kept as the call while
    /// gluing ([`Machine::glue`](crate::machine::Machine::glue), docs/proposals/folded-calls.md). It means
    /// its unfolding, which [`force`] computes the first time something
    /// looks inside and every copy of the call then shares. The spine has
    /// an application for each parameter, then perhaps projections: a
    /// field of the call's record ([`project_call`]), which means that
    /// field of the unfolding.
    Call(DefId, Spine, Rc<Unfolding>),
    /// Only while running a partial computation (`step.rs`): the rest of a
    /// handled computation, captured where an operation reached its handler
    /// (docs/proposals/partial-handlers.md §5.1). It only ever appears as
    /// the argument of a partly applied `foldD`, the resumption `k` a
    /// handler's clause gets, and never reaches the checker.
    Resumption(Rc<crate::step::Capture>),
}

/// A value owned through a shared pointer: a function type's domain, the
/// number a `NatAdd` adds to, the parts of an equality type.
///
/// A chain of these a million deep (`Eq (Eq (Eq …))`) would overflow the
/// stack in the default drop (SW-2482), so freeing the last reference drops
/// the value the default way only down to [`NESTING_LIMIT`] levels, then
/// frees the rest iteratively, as [`Values`] and [`Spine`] do.
#[derive(Clone, Debug)]
pub struct Shared(Rc<Value>);

impl Shared {
    pub fn new(value: Value) -> Shared {
        Shared(Rc::new(value))
    }

    /// The pointer itself, for comparing by address and for keeping alive.
    pub fn rc(&self) -> &Rc<Value> {
        &self.0
    }

    pub fn ptr_eq(a: &Shared, b: &Shared) -> bool {
        Rc::ptr_eq(&a.0, &b.0)
    }

    /// The value, if this was the only reference to it; otherwise just drops
    /// the reference.
    pub fn into_unique(mut self) -> Option<Value> {
        if Rc::strong_count(&self.0) != 1 {
            return None;
        }
        let hole = HOLE.try_with(Rc::clone).ok()?;
        Rc::try_unwrap(std::mem::replace(&mut self.0, hole)).ok()
    }
}

impl From<Rc<Value>> for Shared {
    fn from(rc: Rc<Value>) -> Shared {
        Shared(rc)
    }
}

impl From<Value> for Shared {
    fn from(value: Value) -> Shared {
        Shared::new(value)
    }
}

impl std::ops::Deref for Shared {
    type Target = Value;
    fn deref(&self) -> &Value {
        &self.0
    }
}

impl Drop for Shared {
    #[inline]
    fn drop(&mut self) {
        if Rc::strong_count(&self.0) == 1 && !self.0.is_atom() {
            self.free_nested();
        }
    }
}

impl Shared {
    /// Drops the value the default way, counting the nesting.
    #[inline(never)]
    fn free_nested(&mut self) {
        if let Some(value) = Rc::get_mut(&mut self.0) {
            drop_nested(std::mem::replace(value, Value::Refl), |value, pending| {
                pending.push(value)
            });
        }
    }
}

/// The arguments of a [`Value::Data`]. Like [`Values`] and [`Shared`], freeing
/// them is bounded the same way as a [`Shared`] (SW-2482): `List (List (List
/// …))` a million deep is a chain of these.
#[derive(Clone, Debug, Default)]
pub struct DataArgs(Vec<Value>);

impl DataArgs {
    /// The arguments, leaving none behind.
    pub fn take(&mut self) -> Vec<Value> {
        std::mem::take(&mut self.0)
    }

    pub fn into_vec(mut self) -> Vec<Value> {
        self.take()
    }
}

impl std::ops::Deref for DataArgs {
    type Target = Vec<Value>;
    fn deref(&self) -> &Vec<Value> {
        &self.0
    }
}

impl std::ops::DerefMut for DataArgs {
    fn deref_mut(&mut self) -> &mut Vec<Value> {
        &mut self.0
    }
}

impl From<Vec<Value>> for DataArgs {
    fn from(args: Vec<Value>) -> DataArgs {
        DataArgs(args)
    }
}

impl FromIterator<Value> for DataArgs {
    fn from_iter<I: IntoIterator<Item = Value>>(args: I) -> DataArgs {
        DataArgs(args.into_iter().collect())
    }
}

impl IntoIterator for DataArgs {
    type Item = Value;
    type IntoIter = std::vec::IntoIter<Value>;
    fn into_iter(mut self) -> Self::IntoIter {
        self.take().into_iter()
    }
}

impl<'a> IntoIterator for &'a DataArgs {
    type Item = &'a Value;
    type IntoIter = std::slice::Iter<'a, Value>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl Drop for DataArgs {
    #[inline]
    fn drop(&mut self) {
        if self.0.iter().any(|arg| !arg.is_atom()) {
            drop_nested(self.take(), |args, pending| pending.extend(args));
        }
    }
}

/// How many [`Shared`], [`DataArgs`], [`Values`] and [`Spine`] drops are
/// running inside one another on this thread. A level takes between 256 and
/// 512 bytes of stack natively and about ten times its wasm stack in a
/// browser's first tier (SW-4863: 120 levels were the peak of one proof), so
/// the recursion is kept to a few levels: shallow values, nearly all of
/// them, still drop the cheap default way, and anything deeper is freed by
/// the loop in constant stack.
const NESTING_LIMIT: usize = 8;

thread_local! {
    static NESTING: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Drops `owned` the default (recursive) way, which is the cheapest for the
/// shallow values nearly all of them are, until the drops are
/// [`NESTING_LIMIT`] deep; then `to_pending` moves it onto the work list
/// instead, and [`free_iteratively`] frees it and all it holds without
/// recursing. Each level here costs a few small stack frames, so the limit
/// bounds the stack a drop uses however deep the value is (SW-2482).
fn drop_nested<T>(owned: T, to_pending: impl FnOnce(T, &mut Vec<Value>)) {
    let depth = NESTING.try_with(|n| n.get()).unwrap_or(NESTING_LIMIT);
    if depth >= NESTING_LIMIT {
        free_iteratively(|pending| to_pending(owned, pending));
    } else {
        NESTING.with(|n| n.set(depth + 1));
        drop(owned);
        NESTING.with(|n| n.set(depth));
    }
}

impl Value {
    /// Whether dropping this can't start a drop chain: it owns no value
    /// through a [`Shared`] or [`DataArgs`]. (Constructor fields, closure
    /// environments, spines and unfoldings bound their own drops.)
    #[inline]
    fn is_atom(&self) -> bool {
        match self {
            Value::Data(_, args) => args.is_empty(),
            Value::Eq(..) | Value::Pi(..) | Value::NatAdd(..) => false,
            _ => true,
        }
    }
}

/// The unfolding of a [`Value::Call`] once computed: the value the call
/// unfolds to, forced (no `Call` or solved metavariable at its top), with
/// the [`Metas::epoch`](crate::ev::Metas::epoch) and the [`Modes`] it was
/// computed in. A reader uses it only if it could have computed it itself
/// ([`Kept::fits`]); otherwise it computes the unfolding again and keeps
/// that instead. So what a call unfolds to never depends on who forced it
/// first (SW-1782, D2570).
///
/// For a call whose spine ends in a projection, `base` is the unfolding of
/// the call without it, so the fields of one call share its unfolding. Each
/// keeps its own [`Kept`], checked on its own: the field's may be served
/// while the base's is recomputed, or the reverse.
///
/// Record eta's `no_eta` mark isn't one of the [`Modes`]: rule 2 reads a
/// type's `eta` flag, which is fixed when the type becomes final and
/// `no_eta` can be set only while it's pending, so no unfolding is computed
/// under one value of it and read under another. What rule 2 does depend on
/// that can change, whether a program is running, is in the modes already.
#[derive(Debug, Default)]
pub struct Unfolding {
    kept: std::cell::RefCell<Option<Kept>>,
    base: Option<Rc<Unfolding>>,
}

#[derive(Debug)]
struct Kept {
    epoch: u64,
    modes: Modes,
    value: Value,
}

/// The machine's modes that change what a call unfolds to
/// ([`crate::machine::Machine`]).
#[derive(Debug)]
struct Modes {
    /// Gluing: unfolded with it off, the value has no calls left in it, so a
    /// folded read-back of it writes all of it out.
    glue: bool,
    /// Erasure: proofs and types erased.
    erasing: bool,
    /// A program running: every opaque definition's body is visible.
    program: bool,
    /// The kernel checking ([`Machine::kernel`](crate::machine::Machine)):
    /// [`eta_fields`] builds a stuck field of a folded call differently
    /// for the kernel and the elaborator, and a kept type's calls
    /// (`Def::ty_value`) are forced by both, so an unfolding the kernel
    /// made while checking a body must not serve the elaborator, or what a
    /// goal shows would depend on whether that body was checked or
    /// replayed from the cache.
    kernel: bool,
    /// The opaque definitions whose bodies were visible.
    transparent: Rc<[DefId]>,
}

impl Modes {
    fn now(g: &Ev) -> Modes {
        Modes {
            glue: g.machine.glue.get(),
            erasing: g.machine.erasure.active(),
            program: g.machine.erasure.program_running(),
            kernel: g.machine.kernel.get(),
            transparent: g.machine.transparent.0.borrow().clone(),
        }
    }
}

impl Kept {
    /// Whether a reader now may use this unfolding: from epoch 0 (made with
    /// no metavariables, by the kernel) or the current one (one from
    /// another epoch may have used a metavariable solution that's since
    /// been taken back), and made in the reader's modes, except that one
    /// made glued serves a reader with gluing off: such a reader forces the
    /// calls in it as it meets them, and sees what it would have computed.
    /// Not the reverse: the folded read-back writes a call as the call, and
    /// one unfolded unglued has none left.
    ///
    /// Most unfoldings die with the check that made them; those of the
    /// calls in a kept type (`Def::ty_value`, evaluated glued, D3680) live
    /// as long as the definition and are forced by the kernel and the
    /// elaborator alike. The kernel's `Ev` is at epoch 0, so it never uses
    /// one the elaborator made (its epochs start at 1) and recomputes it;
    /// and since whether the kernel made it is one of the modes, the
    /// elaborator never uses one the kernel made either.
    fn fits(&self, g: &Ev) -> bool {
        let m = &self.modes;
        (self.epoch == 0 || self.epoch == g.metas.epoch())
            && (m.glue || !g.machine.glue.get())
            && m.erasing == g.machine.erasure.active()
            && m.program == g.machine.erasure.program_running()
            && m.kernel == g.machine.kernel.get()
            && {
                let now = g.machine.transparent.0.borrow();
                Rc::ptr_eq(&m.transparent, &now) || *m.transparent == **now
            }
    }
}

impl Unfolding {
    fn get(&self, g: &Ev) -> Option<Value> {
        match &*self.kept.borrow() {
            Some(kept) if kept.fits(g) => Some(kept.value.clone()),
            _ => None,
        }
    }

    fn set(&self, g: &Ev, value: Value) {
        *self.kept.borrow_mut() = Some(Kept {
            epoch: g.metas.epoch(),
            modes: Modes::now(g),
            value,
        });
    }
}

/// Freeing an unfolding frees the value it kept without recursing. A call's
/// unfolding can hold a call whose unfolding holds a call, and so on
/// millions deep (`n + 2^128` unfolded `Succ` by `Succ` up to the size
/// limit, SW-2452); the default drop would overflow the stack there. The
/// value goes through [`Values`]' iterative free, as the fields of a
/// constructor do.
///
/// The base it shares is a chain too (one unfolding per projection of a long
/// run of them), so that is walked, not recursed into.
impl Drop for Unfolding {
    fn drop(&mut self) {
        if let Some(Kept { value, .. }) = self.kept.get_mut().take() {
            // Through the same bounded free as a `Values`, without making
            // one: a one-element `Values` here is a heap allocation, and how
            // many unfoldings still keep a value when they are dropped
            // depends on the order they are dropped in, so that allocation
            // made the benchmark's count differ between runs.
            drop_nested(value, |value, pending| pending.push(value));
        }
        let mut base = self.base.take();
        while let Some(rc) = base {
            // Dropping `unfolding` at the end of the iteration frees its kept
            // value as above, and has no base left to recurse into.
            let Ok(mut unfolding) = Rc::try_unwrap(rc) else {
                break;
            };
            base = unfolding.base.take();
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Head {
    /// A variable, by level, with the numbers it's known not to be: in a
    /// number case's default arm, the matched variable is none of the arms'
    /// numbers ([`Apart`]). That's a fact about the variable, not part of
    /// it: two `Var`s of the same level are the same variable, so they're
    /// equal and hash alike whatever each knows. The mark, copied from the
    /// binder, says whether the variable is a proof; it too is a fact about
    /// the variable, which equality and hashing ignore.
    Var(usize, Apart, ProofMark),
    Def(DefId),
    Meta(usize),
    /// A quotient form (docs/proposals/map-equality.md §7), its arguments
    /// the first [`QuotForm::arity`] applications of the spine (the implicit
    /// ones marked so), any further ones applying its result. `Quot A R` and
    /// `Quot.mk a` are values; `Quot.ind` and `Quot.sound` never compute;
    /// `Quot.lift` here is stuck, its quotient argument not a `Quot.mk`.
    /// `Quot.mk` is never a constructor (`Value::Ctor`), so nothing that
    /// takes constructors apart (a `case`, index unification) sees inside it.
    /// The mark is the term's: whether the result is a proof. Equality and
    /// hashing ignore it, since it's determined by the form and arguments.
    Quot(QuotForm, ProofMark),
}

impl PartialEq for Head {
    fn eq(&self, other: &Head) -> bool {
        match (self, other) {
            (Head::Var(a, ..), Head::Var(b, ..)) => a == b,
            (Head::Def(a), Head::Def(b)) => a == b,
            (Head::Meta(a), Head::Meta(b)) => a == b,
            (Head::Quot(a, _), Head::Quot(b, _)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Head {}

impl std::hash::Hash for Head {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Head::Var(l, ..) => l.hash(state),
            Head::Def(d) => d.hash(state),
            Head::Meta(m) => m.hash(state),
            Head::Quot(q, _) => q.hash(state),
        }
    }
}

/// The numbers a variable is known not to be (docs/proposals/
/// literal-match-facts.md): nothing, or a set in [`Machine::apart_sets`](crate::machine::Machine::apart_sets).
///
/// A number case's default arm is taken only for a number none of its arms
/// has, so there the matched variable is checked as a `Var` apart from them.
/// A number case on such a variable (or on `k` plus one) whose numbers it is
/// known not to be takes its default: a proof that matches a character
/// against `'k'`, `'j'` and `_` has the program's own match on `'k'`, `'j'`
/// and `_` reach its `_` arm in the proof's `_` arm.
///
/// Each set has one name ([`crate::machine::ApartSets`]), so two `Apart`s
/// are equal exactly when they stand for the same numbers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Apart(u32);

impl Apart {
    /// Nothing known.
    pub const NONE: Apart = Apart(0);

    /// The set `numbers` (sorted, without duplicates), named in `g`.
    pub fn new(g: &Ev, numbers: Rc<[BigUint]>) -> Apart {
        Apart(g.machine.apart_sets.borrow_mut().name(numbers))
    }

    /// The numbers, sorted; empty for [`Apart::NONE`].
    pub fn numbers(self, g: &Ev) -> Rc<[BigUint]> {
        match self.0 {
            0 => Rc::from([]),
            i => g.machine.apart_sets.borrow().get(i),
        }
    }

    /// Whether a number case on `k + x`, for `x` known not to be these
    /// numbers, can take none of `arms` (sorted): each is below `k`, or `k`
    /// plus one of these.
    pub fn excludes(self, g: &Ev, k: &BigUint, arms: &[crate::term::NumArm]) -> bool {
        if self == Apart::NONE {
            return false;
        }
        let numbers = self.numbers(g);
        arms.iter()
            .all(|arm| *arm.value < *k || numbers.binary_search(&(&*arm.value - k)).is_ok())
    }
}

/// The representative of a `Quot.mk` value, if `value` is one.
pub fn quot_mk_rep(value: &Value) -> Option<&Value> {
    match value {
        Value::Neutral(Head::Quot(QuotForm::Mk, _), spine)
            if spine.len() == QuotForm::Mk.arity() =>
        {
            match &spine[2] {
                Elim::App(a, _) => Some(a),
                Elim::J { .. } | Elim::Proj(..) => None,
            }
        }
        _ => None,
    }
}

/// A quotient form applied to the values `args`.
pub fn quot_value(form: QuotForm, args: Vec<Value>, mark: ProofMark) -> Value {
    let spine = args
        .into_iter()
        .enumerate()
        .map(|(i, v)| {
            let icit = if i < form.implicit() {
                Icit::Implicit
            } else {
                Icit::Explicit
            };
            Elim::App(v, icit)
        })
        .collect();
    Value::Neutral(Head::Quot(form, mark), spine)
}

#[derive(Clone, Debug)]
pub enum Elim {
    App(Value, Icit),
    /// Boxed, so the common case, an application, sets the size.
    J {
        motive: Box<Value>,
        base: Box<Value>,
        /// The term's: whether the result is a proof.
        result: ProofMark,
        /// A cast into data whose term carries its ends ([`Term::j_ends`]):
        /// them, which didn't meet when it was evaluated (rule K).
        ends: Option<Box<Ends>>,
    },
    /// Field `i` of a value of data type `DataId`, which has eta
    /// ([`Term::Proj`]): stuck because the value is unknown.
    Proj(DataId, usize),
}

/// The two ends of a cast into data, `x` and `y` of its proof's `x = y`,
/// and their type (docs/core.md, "The equality rule", rule K). A cast whose
/// ends are equal is its base, whatever its proof; one whose ends differ is
/// stuck, and two stuck casts are compared by these, the motive and the
/// base, never by their proofs (docs/proposals/full-proof-irrelevance-audit.md,
/// finding B).
#[derive(Clone, Debug)]
pub struct Ends {
    pub ty: Value,
    pub x: Value,
    pub y: Value,
}

/// The lowest level comparisons started by evaluation (rule K's test,
/// [`ends_meet`]; rule S's) make their fresh variables at. No context
/// reaches it (a context that deep can't exist in memory), so a fresh
/// variable there never names a free variable of the values compared
/// (docs/proposals/full-proof-irrelevance-audit.md, finding A: with `v5`
/// free, comparing `z => z` with `z => v5` at level 5 would answer
/// "equal"). 2^31 on a 32-bit target (the web build).
pub const RESERVED_LEVELS: usize = if usize::BITS >= 64 { 1 << 40 } else { 1 << 31 };

/// One above the highest level a comparison may make a fresh variable at:
/// below the levels kept for markers ([`DUMMY_LEVEL`], `erase::ERASED`,
/// [`unused`]), which a fresh variable must never be taken for.
pub const LEVEL_CAP: usize = usize::MAX - 3;

/// The level after `k` fresh variables made from `level` (`level` to
/// `level + k - 1`), or `None` past [`LEVEL_CAP`].
pub fn next_level(level: usize, k: usize) -> Option<usize> {
    level.checked_add(k).filter(|&next| next <= LEVEL_CAP)
}

/// The level after `k` fresh variables made from `level` by a comparison
/// going under binders (or into a `case` branch's fields), raising
/// [`Machine::reached`](crate::machine::Machine::reached) to it. Every
/// fresh variable a comparison makes goes through here, before it's used:
/// applying a closure to it can already evaluate a cast with it in its
/// ends, whose test must start above it. Past [`LEVEL_CAP`] there's no
/// answer (`E-RESOURCE`).
fn fresh_past(g: &Ev, level: usize, k: usize) -> Result<usize> {
    let Some(next) = next_level(level, k) else {
        return Err(g.machine.budget.too_deep("comparison"));
    };
    if next > g.machine.reached.get() {
        g.machine.reached.set(next);
    }
    Ok(next)
}

/// Puts [`Machine::reached`](crate::machine::Machine::reached) back as it
/// was when dropped, on any return or error.
struct RestoreReached<'a>(&'a crate::machine::Machine, usize);

impl Drop for RestoreReached<'_> {
    fn drop(&mut self) {
        self.0.reached.set(self.1);
    }
}

/// Whether the ends of a cast into data are equal, so the cast is its base
/// (rule K). Read-only: a comparison ([`conv`]), never the unifier, so it
/// solves nothing and leaves nothing to undo (the audit's condition G). An
/// unsolved unknown in either end is compared as itself, so a cast waiting
/// on one stays stuck until something inspects it again after it's solved.
pub fn ends_meet(g: &Ev, ends: &Ends) -> Result<bool> {
    let same = meet_in_evaluation(g, &ends.x, &ends.y)?;
    if same {
        proof_counts::record(g, proof_counts::Kind::CastFired, 1);
    }
    Ok(same)
}

/// Whether `x` and `y`, of one type, are equal, compared where evaluation
/// has no count of the variables in scope (rules K and S): read-only, with
/// fresh variables from the larger of [`RESERVED_LEVELS`] and
/// [`Machine::reached`](crate::machine::Machine::reached), so above every
/// variable either value can hold: one of the context's, or one a
/// comparison in progress made. The test gives its levels back when it
/// returns: its variables live on only in caches that match values without
/// evaluating them. Running out of levels is an error, never "not equal".
///
/// Answers are remembered for the rest of the outermost test (the one not
/// inside another), by the two values' shapes ([`ShapeMemo`]), so a test
/// met again inside it is answered at once: when a cast's two ends each
/// hold the same recursive call, comparing them evaluates that call twice,
/// and each evaluation tests the call's own cast; without this the second
/// test repeats the first, and the work doubles at each level. An answer
/// depends only on the two values, the metavariable solutions and the
/// machine's modes; none of these change inside a test (a comparison
/// solves nothing), and each test's fresh variables are above every one
/// either value can hold, so an answer found at one level holds at any.
fn meet_in_evaluation(g: &Ev, x: &Value, y: &Value) -> Result<bool> {
    struct ClearAnswers<'a>(&'a crate::machine::Machine, bool);
    impl Drop for ClearAnswers<'_> {
        fn drop(&mut self) {
            if self.1 {
                *self.0.cast_answers.borrow_mut() = None;
            }
        }
    }
    let level = RESERVED_LEVELS.max(g.machine.reached.get());
    #[cfg(feature = "test-bypass")]
    check_levels::below(level, x, y);
    let outermost = g.machine.cast_answers.borrow().is_none();
    let _clear = ClearAnswers(g.machine, outermost);
    let filed = {
        let mut answers = g.machine.cast_answers.borrow_mut();
        let memo = answers.get_or_insert_with(ShapeMemo::default);
        for answer in [true, false] {
            let at = memo.file(g, answer, x, y)?;
            if memo.contains(g, &at, x, y)? {
                return Ok(answer);
            }
        }
        memo.file(g, true, x, y)?
    };
    let same = conv_with(g, level, x, y, &mut CallMemo::default())?;
    if let Some(memo) = g.machine.cast_answers.borrow_mut().as_mut() {
        memo.insert((same, filed.1, filed.2), x, y);
    }
    Ok(same)
}

/// The test-only check of [`meet_in_evaluation`]'s invariant: every
/// variable in the two values is below the test's first level. Off unless
/// [`check_levels::set`] or `STITCHWORT_CHECK_TEST_LEVELS=1` turns it on
/// (the soundness examples do), since it walks both values whole.
#[cfg(feature = "test-bypass")]
pub mod check_levels {
    use super::{Closure, Elim, Head, Shared, Value};
    use crate::collections::HashSet;
    use std::rc::Rc;
    use std::sync::atomic::{AtomicBool, Ordering};

    static ON: AtomicBool = AtomicBool::new(false);

    /// Turns the check on or off for every thread.
    pub fn set(on: bool) {
        ON.store(on, Ordering::Relaxed);
    }

    fn on() -> bool {
        static ENV: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        ON.load(Ordering::Relaxed)
            || *ENV.get_or_init(|| crate::env_flag::env_flag("STITCHWORT_CHECK_TEST_LEVELS"))
    }

    /// Panics if `x` or `y` holds a variable at `start` or above (the
    /// marker levels apart), walking closures' environments, stuck casts'
    /// ends and a resumption's captured frames but forcing nothing. Each
    /// shared part (a closure's environment, a constructor's fields, a
    /// spine, a shared value) is walked once, by address, so the walk is
    /// the value's size in memory however much of it is shared.
    pub(super) fn below(start: usize, x: &Value, y: &Value) {
        if !on() {
            return;
        }
        let mut seen: HashSet<usize> = HashSet::default();
        let mut work = vec![x.clone(), y.clone()];
        let closure = |c: &Closure, work: &mut Vec<Value>, seen: &mut HashSet<usize>| {
            if seen.insert(c.env.as_ptr() as usize) {
                work.extend(c.env.iter().cloned());
            }
        };
        let shared = |s: &Shared, work: &mut Vec<Value>, seen: &mut HashSet<usize>| {
            if seen.insert(Rc::as_ptr(s.rc()) as usize) {
                work.push((**s).clone());
            }
        };
        while let Some(value) = work.pop() {
            match &value {
                Value::Sort(_) | Value::Nat(_) | Value::Chars(_) | Value::Refl => {}
                Value::Resumption(capture) => {
                    if seen.insert(Rc::as_ptr(capture) as usize) {
                        capture.values(&mut work);
                    }
                }
                Value::Pi(_, _, a, b, _) => {
                    shared(a, &mut work, &mut seen);
                    closure(b, &mut work, &mut seen);
                }
                Value::Lam(_, _, b, _) => closure(b, &mut work, &mut seen),
                Value::Data(_, args) => work.extend(args.iter().cloned()),
                Value::Ctor(_, _, fields) => {
                    if seen.insert(fields.as_ptr() as usize) {
                        work.extend(fields.iter().cloned());
                    }
                }
                Value::NatAdd(_, x) => shared(x, &mut work, &mut seen),
                Value::Eq(a, x, y) => {
                    for part in [a, x, y] {
                        shared(part, &mut work, &mut seen);
                    }
                }
                Value::Neutral(_, spine) | Value::Call(_, spine, _) => {
                    if let Value::Neutral(Head::Var(l, ..), _) = &value {
                        assert!(
                            *l < start || *l >= super::LEVEL_CAP,
                            "internal error: a test starting at level {start} compares a value holding the variable at level {l}"
                        );
                    }
                    if spine.addr() != 0 && !seen.insert(spine.addr()) {
                        continue;
                    }
                    for elim in spine.iter() {
                        match elim {
                            Elim::App(v, _) => work.push(v.clone()),
                            Elim::Proj(..) => {}
                            Elim::J {
                                motive, base, ends, ..
                            } => {
                                work.extend([(**motive).clone(), (**base).clone()]);
                                if let Some(ends) = ends {
                                    work.extend([ends.ty.clone(), ends.x.clone(), ends.y.clone()]);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// The eliminations applied to a neutral value's head, in order: shared, so
/// copying a value is cheap however large the stuck computation in it.
/// Adding an elimination copies the list only if it's shared (copying each
/// elimination is then cheap too). Empty spines (variables, folded
/// definitions with no arguments yet) allocate nothing.
#[derive(Clone, Debug, Default)]
pub struct Spine(Option<Rc<Elims>>);

/// A spine's eliminations: the first two in the same allocation as the
/// shared count, so a short spine is one allocation, as a `Vec` was. (An
/// `Rc<Vec>` took two, which made running programs, which build a short spine
/// for every partly applied definition, about 7% slower; four inline was no
/// faster than two, and needed more memory.)
type Elims = smallvec::SmallVec<[Elim; SPINE_INLINE]>;
const SPINE_INLINE: usize = 2;

impl Spine {
    pub fn new() -> Spine {
        Spine(None)
    }

    /// Adds `elim` at the end.
    pub fn push(&mut self, elim: Elim) {
        match &mut self.0 {
            Some(elims) => Rc::make_mut(elims).push(elim),
            None => self.0 = Some(Rc::new(smallvec::smallvec![elim])),
        }
    }

    /// The eliminations, copied only if they're shared.
    pub fn into_vec(mut self) -> Vec<Elim> {
        match self.0.take() {
            Some(elims) => Rc::try_unwrap(elims)
                .unwrap_or_else(|elims| (*elims).clone())
                .into_vec(),
            None => Vec::new(),
        }
    }

    /// The address of the eliminations, if another value holds them too.
    pub fn shared_key(&self) -> Option<*const ()> {
        let elims = self.0.as_ref()?;
        (Rc::strong_count(elims) > 1).then(|| Rc::as_ptr(elims).cast())
    }

    /// The address of the eliminations (0 for none): an identity for as
    /// long as the spine is held.
    pub(crate) fn addr(&self) -> usize {
        self.0
            .as_ref()
            .map_or(0, |elims| Rc::as_ptr(elims) as usize)
    }

    /// Whether `self` and `other` are the same shared list (so equal).
    pub fn ptr_eq(&self, other: &Spine) -> bool {
        match (&self.0, &other.0) {
            (Some(a), Some(b)) => Rc::ptr_eq(a, b),
            (None, None) => true,
            _ => false,
        }
    }
}

impl std::ops::Deref for Spine {
    type Target = [Elim];
    fn deref(&self) -> &[Elim] {
        match &self.0 {
            Some(elims) => elims,
            None => &[],
        }
    }
}

impl From<Vec<Elim>> for Spine {
    fn from(elims: Vec<Elim>) -> Spine {
        if elims.is_empty() {
            Spine(None)
        } else {
            Spine(Some(Rc::new(Elims::from_vec(elims))))
        }
    }
}

impl FromIterator<Elim> for Spine {
    fn from_iter<I: IntoIterator<Item = Elim>>(elims: I) -> Spine {
        elims.into_iter().collect::<Vec<_>>().into()
    }
}

impl<'s> IntoIterator for &'s Spine {
    type Item = &'s Elim;
    type IntoIter = std::slice::Iter<'s, Elim>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[derive(Clone, Debug)]
pub struct Closure {
    /// Shared, not copied: values captured by nested closures would
    /// otherwise be copied again at every level.
    pub env: Values,
    pub body: Rc<Term>,
}

/// A shared sequence of values: constructor fields and closure environments.
///
/// Freeing one is bounded like freeing a [`Shared`]: the default recursive
/// drop down to [`NESTING_LIMIT`] levels, then, however deeply the values
/// nest (a list of a million elements is a million nested `Ctor`s), the
/// values of a uniquely owned sequence are moved onto a work list and taken
/// apart one at a time. Rust frees nested data recursively by default, which
/// would overflow the stack. (Always taking them apart made a check of
/// tools/fmt retire about 8% more instructions: nearly every sequence freed
/// is shallow, SW-4641.)
#[derive(Clone, Debug)]
pub struct Values(Rc<[Value]>);

impl std::ops::Deref for Values {
    type Target = [Value];
    fn deref(&self) -> &[Value] {
        &self.0
    }
}

impl Values {
    /// Whether another value holds these same values.
    pub fn is_shared(&self) -> bool {
        Rc::strong_count(&self.0) > 1
    }
}

impl From<Vec<Value>> for Values {
    fn from(values: Vec<Value>) -> Values {
        Values(values.into())
    }
}

impl From<&[Value]> for Values {
    fn from(values: &[Value]) -> Values {
        Values(values.into())
    }
}

impl FromIterator<Value> for Values {
    fn from_iter<I: IntoIterator<Item = Value>>(values: I) -> Values {
        Values(values.into_iter().collect())
    }
}

impl<const N: usize> From<[Value; N]> for Values {
    fn from(values: [Value; N]) -> Values {
        Values(Rc::new(values))
    }
}

thread_local! {
    /// What a taken-apart sequence is left holding, so taking it apart
    /// doesn't allocate.
    static EMPTY: Rc<[Value]> = Rc::new([]);
    /// What a taken-apart [`Shared`] is left pointing at.
    static HOLE: Rc<Value> = Rc::new(Value::Refl);
    /// The work list for freeing, kept between uses so that freeing doesn't
    /// allocate either.
    static PENDING: std::cell::RefCell<Vec<Value>> = const { std::cell::RefCell::new(Vec::new()) };
}

impl Drop for Values {
    fn drop(&mut self) {
        if Rc::strong_count(&self.0) != 1 || self.0.is_empty() {
            return;
        }
        let Ok(empty) = EMPTY.try_with(Rc::clone) else {
            return; // the thread is ending
        };
        let values = std::mem::replace(&mut self.0, empty);
        drop_nested(values, take_apart);
    }
}

/// A spine can hold values that hold spines, millions deep (a stuck
/// computation applied to a stuck computation, and so on), so freeing one is
/// bounded as for [`Values`] rather than recursing through `Elim`, `Value`
/// and `Spine` in turn without limit (SW-2468).
impl Drop for Spine {
    fn drop(&mut self) {
        if let Some(elims) = self.0.take_if(|elims| Rc::strong_count(elims) == 1) {
            drop_nested(elims, take_elims);
        }
    }
}

/// Frees what `seed` puts on the work list, and everything those values
/// hold, one value at a time. Freeing never starts another free that needs
/// the shared work list (everything it frees has been taken apart), but if
/// it ever did, a local one would do.
fn free_iteratively(seed: impl FnOnce(&mut Vec<Value>)) {
    let Ok(empty) = EMPTY.try_with(Rc::clone) else {
        return; // the thread is ending
    };
    let mut seed = Some(seed);
    let mut free = |pending: &mut Vec<Value>| {
        if let Some(seed) = seed.take() {
            seed(pending);
        }
        while let Some(value) = pending.pop() {
            detach(value, &empty, pending);
        }
    };
    let shared = PENDING.try_with(|p| match p.try_borrow_mut() {
        Ok(mut p) => {
            free(&mut p);
            true
        }
        Err(_) => false,
    });
    if shared != Ok(true) {
        free(&mut Vec::new());
    }
}

/// Moves the values in `elims` onto `pending`, if this is the last reference
/// to them; otherwise just drops the reference.
fn take_elims(elims: Rc<Elims>, pending: &mut Vec<Value>) {
    let Ok(elims) = Rc::try_unwrap(elims) else {
        return;
    };
    for elim in elims {
        match elim {
            Elim::App(v, _) => pending.push(v),
            Elim::J {
                motive, base, ends, ..
            } => {
                pending.push(*motive);
                pending.push(*base);
                if let Some(ends) = ends {
                    let Ends { ty, x, y } = *ends;
                    pending.extend([ty, x, y]);
                }
            }
            Elim::Proj(..) => {}
        }
    }
}

/// Moves the values of `values` onto `pending`, if this is the last
/// reference to them; otherwise just drops the reference.
fn take_apart(mut values: Rc<[Value]>, pending: &mut Vec<Value>) {
    if let Some(slots) = Rc::get_mut(&mut values) {
        for slot in slots.iter_mut() {
            pending.push(std::mem::replace(slot, Value::Refl));
        }
    }
}

/// Moves whatever `value` holds onto `pending` (when it's the only owner),
/// so that dropping `value` itself doesn't recurse.
fn detach(value: Value, empty: &Rc<[Value]>, pending: &mut Vec<Value>) {
    let mut unwrap = |v: Shared| {
        if let Some(v) = v.into_unique() {
            pending.push(v);
        }
    };
    match value {
        Value::Ctor(_, _, mut fields) => {
            take_apart(std::mem::replace(&mut fields.0, empty.clone()), pending);
        }
        Value::Lam(_, _, mut closure, _) => {
            take_apart(
                std::mem::replace(&mut closure.env.0, empty.clone()),
                pending,
            );
        }
        Value::Pi(_, _, dom, mut closure, _) => {
            unwrap(dom);
            take_apart(
                std::mem::replace(&mut closure.env.0, empty.clone()),
                pending,
            );
        }
        Value::Data(_, args) => pending.extend(args),
        Value::NatAdd(_, base) => unwrap(base),
        Value::Eq(ty, a, b) => {
            unwrap(ty);
            unwrap(a);
            unwrap(b);
        }
        Value::Call(_, spine, unfolding) => {
            if let Ok(mut unfolding) = Rc::try_unwrap(unfolding)
                && let Some(Kept { value, .. }) = unfolding.kept.get_mut().take()
            {
                pending.push(value);
            }
            pending.push(Value::Neutral(
                Head::Var(0, Apart::NONE, ProofMark::Unknown),
                spine,
            ));
        }
        Value::Neutral(_, mut spine) => {
            if let Some(elims) = spine.0.take() {
                take_elims(elims, pending);
            }
        }
        Value::Sort(_) | Value::Nat(_) | Value::Chars(_) | Value::Refl | Value::Resumption(_) => {}
    }
}

impl Closure {
    pub fn apply(&self, g: &Ev, arg: Value) -> Result<Value> {
        run(g, enter(self, arg))
    }

    /// Like `apply`, but only computes the argument if the body uses it. For
    /// the result type of an application: `f a : B a` needs the value of `a`
    /// only when `B` depends on it, and computing it may be expensive.
    pub fn apply_lazy(&self, g: &Ev, arg: impl FnOnce() -> Result<Value>) -> Result<Value> {
        let arg = if self.body.mentions(0) {
            arg()?
        } else {
            unused()
        };
        self.apply(g, arg)
    }
}

/// A placeholder for a value that's never looked at: an environment entry the
/// body doesn't mention.
pub fn unused() -> Value {
    Value::Neutral(
        Head::Var(usize::MAX, Apart::NONE, ProofMark::Unknown),
        Spine::new(),
    )
}

/// A level no binder in scope has, for walking a `Pi` type's codomain without
/// instantiating it. That is safe while only the codomain's shape is read: no
/// context lookup can find this level. If a value under it is ever read back as
/// a term, `quote`'s debug assertion fires (the level is at or above the
/// context) and in release the variable index would wrap. `usize::MAX` is
/// [`unused`] and `usize::MAX - 1` is the erased placeholder.
pub const DUMMY_LEVEL: usize = usize::MAX - 2;

impl Value {
    /// The variable at `level`, not known to be a proof or not.
    pub fn var(level: usize) -> Value {
        Value::var_marked(level, ProofMark::Unknown)
    }

    /// The fake binder [`DUMMY_LEVEL`], for the same use.
    pub fn dummy_var() -> Value {
        Value::var(DUMMY_LEVEL)
    }

    /// The variable at `level`, with its binder's mark.
    pub fn var_marked(level: usize, mark: ProofMark) -> Value {
        Value::Neutral(Head::Var(level, Apart::NONE, mark), Spine::new())
    }
}

/// Whether `v` is a proof (docs/core.md, "Proof marks";
/// docs/proposals/full-proof-irrelevance.md §4.3), read off the marks in
/// constant time, forcing nothing: a stuck computation by its last
/// elimination that isn't an application (a field's sort, a `J`'s result
/// mark), else by its head (a variable's binder, a definition's type, a
/// quotient form's result); a constructor by its type's sort. By
/// impredicativity, applying a proof gives a proof, so applications don't
/// change the answer.
///
/// [`ProofMark::Unknown`] for a lambda (a comparison goes under it and
/// asks about the bodies), an unknown (the elaborator's `is_proof` asks its
/// type), and anything whose mark wasn't set: a value made from a term the
/// kernel hasn't checked. Nothing that changes what's accepted uses it yet.
pub fn is_proof(g: &Ev, v: &Value) -> ProofMark {
    let spine_mark = |spine: &Spine| {
        spine.iter().rev().find_map(|elim| match elim {
            Elim::App(..) => None,
            Elim::J { result, .. } => Some(*result),
            Elim::Proj(d, i) => Some(field_mark(g, *d, *i)),
        })
    };
    match v {
        Value::Neutral(head, spine) => spine_mark(spine).unwrap_or(match head {
            Head::Var(_, _, mark) => *mark,
            Head::Def(id) => ProofMark::from_bool(g.def(*id).proof),
            Head::Meta(_) => ProofMark::Unknown,
            Head::Quot(_, mark) => *mark,
        }),
        Value::Call(id, spine, _) => {
            spine_mark(spine).unwrap_or(ProofMark::from_bool(g.def(*id).proof))
        }
        Value::Ctor(d, ..) => ProofMark::of_sort(g.data(*d).sort),
        Value::Refl => ProofMark::Proof,
        Value::Nat(_) | Value::NatAdd(..) | Value::Chars(_) => ProofMark::NotProof,
        Value::Sort(_) | Value::Pi(..) | Value::Data(..) | Value::Eq(..) => ProofMark::NotProof,
        Value::Lam(..) | Value::Resumption(_) => ProofMark::Unknown,
    }
}

/// Whether values of type `ty` are proofs, read off `ty` without a
/// checker: an equation, a data type's sort, a function type's codomain
/// (under a variable at `fresh` and above), or a stuck type's head type
/// applied to its arguments until it is a sort. A call is read from its
/// definition's declared type without unfolding it; when that doesn't
/// decide, the call is unfolded as before. `types` gives a context
/// variable's type, when known. [`ProofMark::Unknown`] for anything else
/// (an unknown, a projection or cast in the type, a type's sort still to
/// be solved): the elaborator marks its variables with this, and an
/// unknown mark only makes comparison look inside, as before rule I.
pub fn mark_of_type(
    g: &Ev,
    ty: &Value,
    types: &dyn Fn(usize) -> Option<Value>,
    fresh: usize,
) -> Result<ProofMark> {
    let mut ty = ty.clone();
    for depth in 0..32 {
        // Read a call's result sort off its definition's type, without
        // forcing the call: forcing a type such as `cost < 5` would compute
        // `cost`, which nothing here needs (SW-4864).
        if let Value::Neutral(Head::Def(id), spine) | Value::Call(id, spine, _) = &ty
            && let Ok(mark @ (ProofMark::Proof | ProofMark::NotProof)) =
                mark_of_head(g, g.def(*id).ty_value.clone(), spine)
        {
            return Ok(mark);
        }
        let (head_ty, spine) = match force(g, ty)? {
            Value::Eq(..) => return Ok(ProofMark::Proof),
            Value::Data(d, _) => return Ok(ProofMark::of_sort(g.data(d).sort)),
            Value::Sort(_) => return Ok(ProofMark::NotProof),
            Value::Pi(_, _, _, cod, mark) => {
                ty = cod.apply(g, Value::var_marked(fresh + depth, mark))?;
                continue;
            }
            Value::Neutral(Head::Var(l, ..), spine) => match types(l) {
                Some(t) => (t, spine),
                None => return Ok(ProofMark::Unknown),
            },
            Value::Neutral(Head::Def(id), spine) | Value::Call(id, spine, _) => {
                (g.def(id).ty_value.clone(), spine)
            }
            _ => return Ok(ProofMark::Unknown),
        };
        return mark_of_head(g, head_ty, &spine);
    }
    Ok(ProofMark::Unknown)
}

/// The mark of a value of type `head_ty` applied to `spine` (the arguments of
/// a call or a variable's type).
fn mark_of_head(g: &Ev, head_ty: Value, spine: &Spine) -> Result<ProofMark> {
    let mut t = head_ty;
    for elim in spine.iter() {
        let Elim::App(arg, _) = elim else {
            return Ok(ProofMark::Unknown);
        };
        t = match force(g, t)? {
            Value::Pi(_, _, _, cod, _) => cod.apply(g, arg.clone())?,
            _ => return Ok(ProofMark::Unknown),
        };
    }
    Ok(match force(g, t)? {
        Value::Sort(s) => ProofMark::of_sort(s),
        _ => ProofMark::Unknown,
    })
}

/// Whether field `i` of the one constructor of `d` (a type with eta) is a
/// proof.
fn field_mark(g: &Ev, d: DataId, i: usize) -> ProofMark {
    match g.data(d).ctors.first().and_then(|c| c.field_sorts.get(i)) {
        Some(sort) => ProofMark::of_sort(*sort),
        None => ProofMark::Unknown,
    }
}

pub fn eval(g: &Ev, env: &[Value], term: &Term) -> Result<Value> {
    run(g, Control::Eval(Rc::new(term.clone()), env.into()))
}

pub fn apply(g: &Ev, f: Value, arg: Value) -> Result<Value> {
    apply_icit(g, f, arg, Icit::Explicit)
}

pub fn apply_icit(g: &Ev, f: Value, arg: Value, icit: Icit) -> Result<Value> {
    run(g, Control::Apply(Box::new((f, arg, icit))))
}

/// What looking inside `value` sees (its weak head, as far as the
/// elaborator's additions go): a solved metavariable at its head is
/// replaced by its solution, and a call ([`Value::Call`]) by its unfolding,
/// until neither is at the top. Everything that takes a value apart by its
/// shape calls this first. Without metavariables and gluing (the kernel),
/// it returns `value` as it is.
#[inline]
pub fn force(g: &Ev, value: Value) -> Result<Value> {
    if needs_forcing(g, &value) {
        force_now(g, value)
    } else {
        Ok(value)
    }
}

/// [`force`] for a value it changes: a call's kept unfolding if there is
/// one, or else the machine.
#[inline(never)]
fn force_now(g: &Ev, value: Value) -> Result<Value> {
    if let Value::Call(_, _, unfolding) = &value
        && let Some(unfolded) = unfolding.get(g)
        && !needs_forcing(g, &unfolded)
    {
        return Ok(unfolded);
    }
    run(g, Control::Force(value))
}

/// [`force`] on a borrowed value, copying it only if forcing changes it.
pub fn force_ref<'v>(g: &Ev, value: &'v Value) -> Result<std::borrow::Cow<'v, Value>> {
    Ok(if needs_forcing(g, value) {
        std::borrow::Cow::Owned(force(g, value.clone())?)
    } else {
        std::borrow::Cow::Borrowed(value)
    })
}

/// [`force`], but stopping at a glued call ([`Value::Call`]): a solved
/// metavariable at the head is replaced by its solution, applied to the
/// spine, until none is; a call that gives is returned as the call. For
/// reading back folded ([`quote_folded`]). Without gluing, it's [`force`]
/// except on a call itself.
pub fn force_solved(g: &Ev, value: Value) -> Result<Value> {
    if !g.machine.glue.get() {
        // Nothing is glued now, so `force` as usual (taking the same steps);
        // but a call kept from while gluing (a goal's context, printed
        // afterwards) is still written as the call.
        return match value {
            Value::Call(..) => Ok(value),
            other => force(g, other),
        };
    }
    let mut value = value;
    loop {
        let Value::Neutral(Head::Meta(m), spine) = &value else {
            return Ok(value);
        };
        let Some(solution) = g.meta_solution(*m) else {
            return Ok(value);
        };
        if spine
            .iter()
            .any(|e| matches!(e, Elim::J { .. } | Elim::Proj(..)))
        {
            return force(g, value);
        }
        let args: Vec<(Value, Icit)> = (spine.iter())
            .map(|elim| match elim {
                Elim::App(arg, icit) => (arg.clone(), *icit),
                _ => unreachable!("checked above"),
            })
            .collect();
        value = apply_all(g, solution, &args)?;
    }
}

/// `f` applied to `args` in turn, a closure's run of lambdas taking its
/// arguments at once ([`enter_run`]).
fn apply_all(g: &Ev, mut f: Value, args: &[(Value, Icit)]) -> Result<Value> {
    let mut next = 0;
    while next < args.len() {
        if let Value::Lam(_, _, closure, _) = &f {
            let (body, env, taken) = enter_run(closure, args[next..].iter().map(|(a, _)| a));
            f = run(g, Control::Eval(body, env))?;
            next += taken;
        } else {
            let (arg, icit) = &args[next];
            f = apply_icit(g, f, arg.clone(), *icit)?;
            next += 1;
        }
    }
    Ok(f)
}

/// Applying `closure` to the first of `args` and then, while its body is
/// another lambda, the result to the next, without making the closures in
/// between: the body reached, its environment, and how many arguments it
/// took (at least one). A metavariable's solution is a function of every
/// variable in scope where it was made, and is applied to all of them each
/// time it is forced; entering each lambda on its own copies the
/// environment to add one, quadratic in the variables (SW-3726).
fn enter_run<'a>(
    closure: &Closure,
    args: impl Iterator<Item = &'a Value>,
) -> (Rc<Term>, Env, usize) {
    let mut args = args.peekable();
    let mut env: Vec<Value> = closure.env.to_vec();
    env.extend(args.next().cloned());
    let mut body = &closure.body;
    loop {
        match &**body {
            Term::Loc(_, inner) => body = inner,
            Term::Lam(_, _, inner, _) if args.peek().is_some() => {
                env.extend(args.next().cloned());
                body = inner;
            }
            _ => break,
        }
    }
    let taken = env.len() - closure.env.len();
    (body.clone(), env.into(), taken)
}

/// Glued call `id spine` unfolded one step: its case tree run, the calls in
/// what it returns kept as calls rather than forced.
pub fn unfold_once(g: &Ev, id: DefId, spine: Spine) -> Result<Value> {
    // A field of a call: that field of the call's step.
    if let Some(&Elim::Proj(d, i)) = spine.last() {
        let base = unfold_once(g, id, spine[..spine.len() - 1].iter().cloned().collect())?;
        return match base {
            call @ Value::Call(..) => Ok(project_call(d, i, call)),
            other => Ok(project(d, i, force(g, other)?)),
        };
    }
    let mut stack = Stack::default();
    let start = unfold_now(g, &mut stack, id, spine, false)?;
    run_on(g, start, stack)
}

/// Whether glued call spine `spine` is a field of a call ([`project_call`]):
/// it ends in a projection. Code that reads a call as its definition
/// applied to arguments ([`call_args`]) must not take such a call for one.
pub fn is_call_field(spine: &[Elim]) -> bool {
    matches!(spine.last(), Some(Elim::Proj(..)))
}

/// Whether glued call `id spine` takes a step at once by matching: its case
/// tree starts with a case on an argument that is already a constructor or
/// a number, or a call that does this itself (`List.length (List.append
/// (Cons x xs) ys)`); not any other call that might compute to one, which
/// isn't forced to find out. Read back folded, such a call is written as
/// its unfolding:
/// `if True then a else b` is `a`, and `List.length (Cons x xs)` is
/// `Succ (List.length xs)`, while `invalid r` or `List.length (f xs)` stay
/// calls (docs/proposals/folded-calls.md, stage 3).
pub fn matches_at_once(g: &Ev, id: DefId, spine: &Spine) -> Result<bool> {
    // A field of a call ([`project_call`]) steps when the call does.
    if is_call_field(spine) {
        let call = spine
            .iter()
            .take_while(|e| matches!(e, Elim::App(..)))
            .count();
        return matches_at_once(g, id, &spine[..call].iter().cloned().collect());
    }
    let def = g.def(id);
    let Some(body) = body_seen(g, id) else {
        return Ok(false);
    };
    let tree = Term::peel_lams_rc(body, def.arity);
    let (Term::Case(ix, ..) | Term::NumCase(ix, ..)) = &*tree else {
        return Ok(false);
    };
    let Some(Elim::App(arg, _)) = spine.len().checked_sub(1 + ix).and_then(|i| spine.get(i)) else {
        return Ok(false);
    };
    let arg = match force_solved(g, arg.clone())? {
        // A call that itself matches at once is looked through.
        Value::Call(i, s, u) if matches_at_once(g, i, &s)? => force(g, Value::Call(i, s, u))?,
        other => other,
    };
    Ok(matches!(
        arg,
        Value::Ctor(..) | Value::Nat(_) | Value::NatAdd(..) | Value::Chars(_) | Value::Refl
    ))
}

/// A glued call's arguments, in order, with how each is passed. Not for a
/// field of a call ([`is_call_field`]), which isn't its definition applied.
pub fn call_args(spine: &Spine) -> Vec<(Value, Icit)> {
    spine
        .iter()
        .map(|elim| match elim {
            Elim::App(v, i) => (v.clone(), *i),
            Elim::J { .. } | Elim::Proj(..) => {
                unreachable!("a call's spine has only applications")
            }
        })
        .collect()
}

/// A short description of a value for internal errors, which mustn't print
/// a value that may be arbitrarily deep.
fn describe(value: &Value) -> &'static str {
    match value {
        Value::Sort(_) => "a sort",
        Value::Pi(..) => "a function type",
        Value::Lam(..) => "a function",
        Value::Data(..) => "a data type",
        Value::Ctor(..) => "a constructor",
        Value::Nat(_) | Value::NatAdd(..) => "a number",
        Value::Chars(_) => "a list of characters",
        Value::Eq(..) => "an equation",
        Value::Refl => "byComputing",
        Value::Neutral(..) => "a stuck term",
        Value::Call(..) => "a call",
        Value::Resumption(_) => "a handler's resumption",
    }
}

// The evaluator: an abstract machine (docs/proposals/stack-safe-evaluation.md).
//
// It was derived from a recursive evaluator (kept as `reference.rs`, for
// tests) by turning each place that waited for a recursive call into a
// `Frame` on an explicit stack. So evaluation never recurses on the Rust
// stack: a program recursing a million deep has a million frames on the
// heap, counted against the operation's limits. A call in tail position
// (applying a closure, a case tree's leaf) adds no frame.
//
// Inside the machine nothing calls `eval`, `apply` or `force`, which would
// start another machine; it moves to the matching control state instead. The
// one exception is natives forcing their arguments (`native::view`). A
// native's arguments that are glued calls are forced by the machine first
// ([`Control::NativeArg`]), and so is a glued call it comes to inside a
// number, after which it runs again ([`run_native`], and [`run_float`] for
// the float natives), so the native's own `force` finds each one's kept
// unfolding: what is left for it is a solved metavariable, during
// elaboration, or a call whose kept unfolding needs forcing again. Rule E's
// reading of a `case`'s scrutinee forces and unfolds on this machine too
// ([`reread_on`]).

type Env = Values;

/// The definition whose case tree is being walked, applied to its spine:
/// what's left folded if the tree can't take a step (`None` for a case
/// outside a definition). The flag says whether a `Quot.lift` leaf whose
/// quotient isn't a `Quot.mk` leaves it folded too, as a `case` that can't
/// step does (docs/proposals/map-equality.md §7.2, the unfolding policy):
/// when unfolding it normally, but not when taking a folded call apart
/// ([`unfold_for`], [`unfold_folded`]), which must see its body.
type Stuck = Option<(DefId, Spine, bool)>;

/// What the machine does next.
enum Control {
    /// Evaluate a term.
    Eval(Rc<Term>, Env),
    /// Apply a value to an argument. (Boxed: it's the largest state, and most
    /// applications happen directly, through [`apply_step`].)
    Apply(Box<(Value, Value, Icit)>),
    /// A definition with these arguments: run its native implementation or
    /// its case tree, or leave it folded.
    Unfold(DefId, Spine),
    /// [`Control::Unfold`], with the result to be that many more `Succ`s
    /// ([`native::Outcome::Succs`]). (Boxed through its `Rc`: rare.)
    UnfoldAfterSuccs(Rc<BigUint>, DefId, Spine),
    /// Force argument `index` of native definition `id` applied to the
    /// spine, then run the native ([`unforced_number_arg`]).
    NativeArg(DefId, Spine, usize),
    /// Walk a case tree. If it's stuck, the result is the definition left
    /// folded (or, for a case outside a definition, an internal error).
    Tree(Rc<Term>, Vec<Value>, Stuck),
    /// Replace a solved metavariable at the head of a value.
    Force(Value),
    /// Give a value to the frame on top of the stack.
    Return(Value),
}

// Deep evaluation holds many frames at once, so their size shows in its peak
// memory (64 to 104 bytes cost the text benchmarks 10%, docs/testing.md):
// box the large, rare ones.
#[cfg(target_pointer_width = "64")]
const _: () = assert!(std::mem::size_of::<Frame>() <= 64);

/// Work waiting for a value.
enum Frame {
    /// The function of `f a` (the argument is next).
    AppArg(Rc<Term>, Env, Icit),
    /// The argument of `f a`.
    AppFun(Value, Icit),
    /// The function of `f a`, whose argument is erased (`erase.rs`).
    AppErased(Icit),
    /// A number this many more than the value it waits for
    /// ([`native::Outcome::Succs`]).
    AddNat(Rc<BigUint>),
    /// The next argument of a data type or constructor (`term`).
    Args {
        term: Rc<Term>,
        env: Env,
        done: Vec<Value>,
    },
    /// The value of `let` `term` (its body is next, with the value added).
    LetBody { term: Rc<Term>, env: Env },
    /// The domain of a function type (`term`).
    PiDomain { term: Rc<Term>, env: Env },
    /// The next part of an equation `term`: its type, then the sides.
    EqParts {
        term: Rc<Term>,
        env: Env,
        done: Vec<Value>,
    },
    /// The proof of `J` (`term`), which is forced next.
    JProof { term: Rc<Term>, env: Env },
    /// The proof of a cast into data (`term`) whose ends, evaluated, were
    /// found to differ: it is evaluated, not forced, as a stuck cast needs
    /// its head and nothing reads more of it. (Boxed: it's rare.)
    JCast(Box<(Rc<Term>, Env, Ends)>),
    /// The forced proof of `J`.
    JForced { term: Rc<Term>, env: Env },
    /// The forced proof of `J`, already unfolded if it was a folded call.
    JReady { term: Rc<Term>, env: Env },
    /// The value a projection `Term::Proj(d, i, _)` takes field `i` of,
    /// which is forced next.
    ProjOf(DataId, usize),
    /// The forced value a projection takes a field of.
    ProjForced(DataId, usize),
    /// The forced value a projection takes a field of, already unfolded if
    /// it was a folded call.
    ProjReady(DataId, usize),
    /// What folded call `f x` computed to (to the end, `Frame::Unfolding`),
    /// for its field `(f x).i`, kept as that stuck form if what it computed
    /// to is stuck ([`names_folded_fields`]). (Boxed: it's rare.)
    FoldedField(Box<(DataId, usize, Value)>),
    /// The motive of a stuck `J` (the base is next).
    JMotive {
        term: Rc<Term>,
        env: Env,
        head: Head,
        spine: Spine,
        ends: Option<Box<Ends>>,
    },
    /// The base of a stuck `J`: its head, spine, motive and ends. (Boxed:
    /// it's the largest frame, and rare.)
    JBase(Box<StuckJ>),
    /// The quotient argument of the `Quot.lift` `term` (forced next). With
    /// `stuck`, the lift is a leaf of that definition's case tree.
    LiftQuotient {
        term: Rc<Term>,
        env: Env,
        stuck: Stuck,
    },
    /// The forced quotient argument of a `Quot.lift`.
    LiftForced {
        term: Rc<Term>,
        env: Env,
        stuck: Stuck,
    },
    /// The forced quotient argument of a `Quot.lift`, already unfolded if it
    /// was a folded call.
    LiftReady {
        term: Rc<Term>,
        env: Env,
        stuck: Stuck,
    },
    /// The next argument of a quotient form `term` (after `done`; `last`,
    /// if there, is its final argument, already computed). (`last` is boxed:
    /// unboxed, it made this the largest frame, and every frame pays for it.)
    QuotArgs {
        term: Rc<Term>,
        env: Env,
        done: Vec<Value>,
        last: Option<Box<Value>>,
    },
    /// The forced scrutinee of the case node `tree`.
    Scrutinee {
        tree: Rc<Term>,
        env: Vec<Value>,
        stuck: Stuck,
    },
    /// The scrutinee of the case node `tree`, already unfolded if it was a
    /// folded call.
    ScrutineeReady {
        tree: Rc<Term>,
        env: Vec<Value>,
        stuck: Stuck,
    },
    /// A number case waiting for a glued call inside its scrutinee to be
    /// forced before [`branch_asked`] reads it again. (Boxed: it's large,
    /// and rare.)
    NumberScrutinee(Box<NumberScrutinee>),
    /// The unfolding of a folded call ([`folded_call`])
    /// that the frame `next` takes apart: unfolded again if it's another
    /// folded call, directly or once a glued call it ends in is forced, and
    /// given to `next` as it is if it's this call, stuck. So `next` gets
    /// what unglued evaluation would: never a folded call that can still
    /// compute.
    /// (Boxed: it's large, and rare.)
    Unfolding(Box<(DefId, Spine, Frame)>),
    /// A metavariable's solution, or the result of applying it so far:
    /// apply the eliminations of `spine` from `next` on, then force again.
    Replay { spine: Spine, next: usize },
    /// The forced value a `J` elimination or a projection at `spine[next]`
    /// applies to.
    ReplayElim { spine: Spine, next: usize },
    /// The forced function of an application of a call to `arg`.
    AppTo(Value, Icit),
    /// The unfolding of a call, to force and then keep.
    Unfolded(Rc<Unfolding>, DefId),
    /// Argument `next - 1` of native definition `id` applied to `spine`,
    /// forced and kept in its call ([`Control::NativeArg`]): the arguments
    /// from `next` on are looked at next, then the native runs.
    NativeArg {
        id: DefId,
        spine: Spine,
        next: usize,
    },
    /// Native definition `id` applied to `spine`, waiting for a glued call
    /// inside one of its numbers to be forced before it runs again
    /// ([`run_native`]), the last of `asked` times.
    NativeAgain {
        id: DefId,
        spine: Spine,
        asked: usize,
    },
    /// Float operation `id` applied to `spine`, unfolded gluing if `glue`,
    /// waiting as a [`Frame::NativeAgain`] does ([`run_float`]).
    FloatAgain {
        id: DefId,
        spine: Spine,
        glue: bool,
        asked: usize,
    },
    /// The forced value of the call that field call `id spine` (spine
    /// ending in projection `d`, `i`; [`project_call`]) takes field `i`
    /// of ([`CallField`]). (Boxed: it's large, and rare.)
    CallField(Box<CallField>),
    /// What the call of a stuck field of a call computed to, for an
    /// elimination of the field ([`unfold_field_for`]). (Boxed: it's large,
    /// and rare.)
    FieldOf(Box<FieldOf>),
    /// Part of a number being read ([`read_number`]), forced: the second
    /// argument of a stuck `add m n`, for R3 and R4, or what a
    /// [`Frame::AddNat`] got. (Boxed: it's large, and rare.)
    ReadNumber(Box<ReadNumber>),
    /// Rule E's walk from a `case`, waiting for a case tree run or a value
    /// forced for the unfolding of a call folded by name ([`reread_on`]).
    Reread(Box<Reread>),
}

/// What a [`Frame::NumberScrutinee`] waits with: the case node `tree`, its
/// environment, and its forced scrutinee, which has had this machine force
/// a glued call inside it `asked` times.
struct NumberScrutinee {
    tree: Rc<Term>,
    env: Vec<Value>,
    stuck: Stuck,
    scrutinee: Value,
    asked: usize,
}

/// A number being read as `k + base` ([`read_number`]), and what to make
/// of it: `k` is the `Succ`s found so far, and `outer` more go around the
/// result.
struct ReadNumber {
    of: NumberOf,
    outer: BigUint,
    k: BigUint,
}

/// What a number [`read_number`] reads is for.
enum NumberOf {
    /// The second argument of this stuck sum, for R3 and R4.
    Sum(StuckSum),
    /// The rest of a number a native took `outer` `Succ`s off
    /// ([`Frame::AddNat`]).
    Rest,
    /// A number rule E's walk asked for ([`reread_on`]; `outer` is zero).
    Reread(Box<Reread>),
}

/// Rule E's walk from a `case` whose scrutinee is a stuck sum
/// ([`reread_on`]): the walk, the unfolding it is waiting for if any, and
/// the `case` that goes on with what it reads.
struct Reread {
    walk: crate::nat_add::Walk,
    folded: Option<Folded>,
    then: AfterReread,
}

/// The `case` waiting for rule E's walk ([`reread_on`]): the case node
/// `tree` with its environment, and the stuck sum `value` it reads. For a
/// number case, `succs` is the `Succ`s its scrutinee has around the sum.
struct AfterReread {
    tree: Rc<Term>,
    env: Vec<Value>,
    stuck: Stuck,
    succs: Option<BigUint>,
    value: Value,
}

/// What a [`Folded`] needs from its evaluator before it can go on.
enum FoldNeed {
    /// The case tree run as [`Control::Tree`] would, for [`Folded::answer`].
    Run(Rc<Term>, Vec<Value>, Stuck),
    /// The value forced, for [`Folded::answer`].
    Force(Value),
    /// What [`unfold_folded`] gives.
    Done(Option<Value>),
}

/// [`unfold_folded`], a step at a time: each step ends where it needs a
/// case tree run or a value forced ([`FoldNeed`]). `unfold_folded` does
/// those with [`run`] and [`force`]; rule E's walk on the machine
/// ([`reread_on`]) does them on the machine's own stack. Its levels are
/// `unfold_folded`'s recursion, for the field of a call (`(f x).i`) whose
/// value is another folded call, innermost last.
struct Folded {
    levels: Vec<FoldLevel>,
}

/// One [`unfold_folded`] of [`Folded`]: of `value`, unfolded to `current`
/// so far, waiting `at`.
struct FoldLevel {
    value: Value,
    current: Option<Value>,
    at: FoldAt,
}

/// What a [`FoldLevel`] is waiting for.
enum FoldAt {
    /// Nothing: about to look at `current`.
    Idle,
    /// The case tree of `id` applied to `call` to run, for a call of which
    /// `fields` are then taken.
    Ran {
        id: DefId,
        call: Spine,
        fields: Vec<(DataId, usize)>,
    },
    /// `next`, what the case tree ran to, to be forced.
    Forced(Value),
    /// The value field `fields[i]` is taken of, to be forced.
    FieldBase {
        fields: Vec<(DataId, usize)>,
        i: usize,
    },
    /// The level above to unfold `base`, the forced value field
    /// `fields[i]` is taken of.
    FieldInner {
        fields: Vec<(DataId, usize)>,
        i: usize,
        base: Value,
    },
    /// What the level above unfolded `fields[i]`'s value to, to be forced.
    FieldUnfolded {
        fields: Vec<(DataId, usize)>,
        i: usize,
    },
}

/// A stuck `add m n` whose `n` R3 and R4 are reading: `stuck` is the
/// result if they find neither a number nor anything under `k > 0` `Succ`s.
struct StuckSum {
    id: DefId,
    m: Value,
    stuck: Value,
}

impl ReadNumber {
    /// Goes on with the number read to `k` `Succ`s around `base` (`None`:
    /// around nothing). For a sum, what R3 and R4 make of it, as
    /// [`crate::nat_add::stuck`] does: `m + k` is `k + m`, `m + (k + n')`
    /// with `k > 0` is `k + add m n'`, and otherwise the sum stays stuck.
    /// For the rest of a number, `outer + k + base`, as `Frame::AddNat`
    /// made it with [`native::view_with`]. For rule E's walk, the walk
    /// goes on.
    fn done(self, g: &Ev, stack: &mut Stack, base: Option<Value>) -> Result<Control> {
        let ReadNumber { of, outer, k } = self;
        let sum = match of {
            NumberOf::Sum(sum) => sum,
            NumberOf::Rest => return Ok(Control::Return(native::from_view(outer + k, base))),
            NumberOf::Reread(mut reread) => {
                let need = reread.walk.viewed(g, k, base)?;
                return reread_go(g, stack, reread, RereadStep::Walk(need));
            }
        };
        Ok(Control::Return(match base {
            None => native::from_view(outer + k, Some(sum.m)),
            Some(_) if num_traits::Zero::is_zero(&k) => sum.stuck,
            Some(base) => {
                native::from_view(outer + k, Some(crate::nat_add::call(sum.id, sum.m, base)))
            }
        }))
    }
}

/// What a [`Frame::CallField`] waits for: field call `id spine`, whose spine
/// ends in projection `data`, `index`.
pub struct CallField {
    data: DataId,
    index: usize,
    id: DefId,
    spine: Spine,
    /// Whether the call has been unfolded already, if it was a folded call.
    unfolded: bool,
}

/// What a [`Frame::FieldOf`] waits for: the call `id call` of stuck field
/// call `id spine` (`call` then the projections), whose field `then` takes
/// apart.
struct FieldOf {
    id: DefId,
    spine: Spine,
    call: Spine,
    then: FieldUse,
}

/// A stuck `J` waiting for its base: the head and spine of its proof, its
/// motive, its result's mark and its ends.
type StuckJ = (Head, Spine, Value, ProofMark, Option<Box<Ends>>);

/// An elimination of a stuck field of a call that computes the field first.
enum FieldUse {
    /// Applying it to an argument.
    App(Value, Icit),
    /// `J` on it, as the proof (the `J` term, and its environment).
    J { term: Rc<Term>, env: Env },
}

#[cfg(any(test, feature = "reference"))]
thread_local! {
    static RUNS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// How many times the machine has been started on this thread. For tests
/// checking that a deep evaluation runs inside one machine, not nested ones.
#[cfg(any(test, feature = "reference"))]
pub fn machine_runs() -> usize {
    RUNS.with(|r| r.get())
}

/// Applying `f` to `arg`: the next state.
fn apply_step(f: Value, arg: Value, icit: Icit) -> Control {
    if erase::is_erased(&f) {
        // An erased function's result is erased too.
        return Control::Return(f);
    }
    match f {
        Value::Lam(_, _, closure, _) => enter(&closure, arg),
        // A stuck field of a call names a projection, not a call short of
        // arguments: `run` computes it first ([`apply_field`]).
        f @ Value::Neutral(Head::Def(_), _) if ends_in_field(&f) => apply_later(f, arg, icit),
        Value::Neutral(Head::Def(id), mut spine) => {
            spine.push(Elim::App(arg, icit));
            Control::Unfold(id, spine)
        }
        Value::Neutral(head, mut spine) => {
            spine.push(Elim::App(arg, icit));
            Control::Return(Value::Neutral(head, spine))
        }
        // Its unfolding is a function: `run` forces it first.
        f @ Value::Call(..) => apply_later(f, arg, icit),
        other => panic!("internal error: applying {}", describe(&other)),
    }
}

// The machine's steps for calls (`Value::Call`), out of line: they only
// happen while gluing, and the evaluator's hot path stays as it was.

/// Whether neutral `f` ends in a projection, as a stuck field of a call
/// does ([`is_call_field`]).
#[inline(always)]
fn ends_in_field(f: &Value) -> bool {
    matches!(f, Value::Neutral(_, spine) if is_call_field(spine))
}

/// Applying call `f` to `arg`, or a stuck field of a call
/// ([`apply_field`]): `run` forces `f` first ([`apply_call`]).
#[cold]
#[inline(never)]
fn apply_later(f: Value, arg: Value, icit: Icit) -> Control {
    Control::Apply(Box::new((f, arg, icit)))
}

/// Applying call `f` to `arg`: its unfolding, once forced, is applied.
#[cold]
#[inline(never)]
fn apply_call(g: &Ev, stack: &mut Stack, f: Value, arg: Value, icit: Icit) -> Result<Control> {
    push(g, stack, Frame::AppTo(arg, icit))?;
    Ok(Control::Force(f))
}

/// Applying `f`, a neutral definition whose spine ends in a projection, to
/// `arg`. A stuck field of a call ([`is_folded`]), `(f x).i a`, is the
/// field of the call's unfolding applied, as a call applied beyond its
/// arguments is ([`apply_call`]): left as `f x .i a`, it would be a stuck
/// term headed by `f` that names nothing, which neither conversion nor the
/// unfolded read-back looks inside, so the unknown the call is stuck on
/// would be hidden from `match` and `byComputing` (docs/proposals/match-call-field.md
/// §2.1). Anything else (an opaque call's field) stays stuck, as it was.
/// Only while gluing ([`computes_field`]).
#[cold]
#[inline(never)]
fn apply_field(g: &Ev, stack: &mut Stack, f: Value, arg: Value, icit: Icit) -> Result<Control> {
    if computes_field(g, &f) {
        return unfold_field_for(g, stack, f, FieldUse::App(arg, icit));
    }
    let Value::Neutral(Head::Def(id), mut spine) = f else {
        unreachable!("checked by the caller")
    };
    spine.push(Elim::App(arg, icit));
    Ok(Control::Unfold(id, spine))
}

/// Forcing a call: its kept unfolding, or else unfolding it now, to be
/// kept (`Frame::Unfolded`).
#[cold]
#[inline(never)]
fn force_call(
    g: &Ev,
    stack: &mut Stack,
    id: DefId,
    spine: Spine,
    unfolding: Rc<Unfolding>,
) -> Result<Control> {
    Ok(match unfolding.get(g) {
        Some(unfolded) => Control::Force(unfolded),
        None => match spine.last() {
            // A field of a call: the call without it, forced, then the field.
            Some(&Elim::Proj(d, i)) => {
                let base = Value::Call(
                    id,
                    spine[..spine.len() - 1].iter().cloned().collect(),
                    unfolding.base.clone().unwrap_or_default(),
                );
                push(g, stack, Frame::Unfolded(unfolding, id))?;
                push(
                    g,
                    stack,
                    Frame::CallField(Box::new(CallField {
                        data: d,
                        index: i,
                        id,
                        spine,
                        unfolded: false,
                    })),
                )?;
                Control::Force(base)
            }
            _ => {
                push(g, stack, Frame::Unfolded(unfolding, id))?;
                unfold_now(g, stack, id, spine, false)?
            }
        },
    })
}

/// Applying a closure: evaluating its body with the argument added.
fn enter(closure: &Closure, arg: Value) -> Control {
    Control::Eval(closure.body.clone(), extend(&closure.env, arg))
}

/// `env` with `value` added as the innermost variable.
fn extend(env: &Env, value: Value) -> Env {
    if crate::env_metrics::on() {
        crate::env_metrics::record(env.len(), !env.is_shared());
    }
    // Built in place, in one allocation.
    let env: Rc<[Value]> = env.iter().cloned().chain(std::iter::once(value)).collect();
    Values(env)
}

fn run(g: &Ev, control: Control) -> Result<Value> {
    run_on(g, control, Stack::default())
}

/// [`run`], with `stack`'s frames waiting for the result.
fn run_on(g: &Ev, mut control: Control, mut stack: Stack) -> Result<Value> {
    #[cfg(any(test, feature = "reference"))]
    RUNS.with(|r| r.set(r.get() + 1));
    loop {
        g.machine.budget.step()?;
        control = match control {
            Control::Eval(term, env) => eval_step(g, term, env, &mut stack)?,
            Control::Apply(application) => {
                let (f, arg, icit) = *application;
                match f {
                    Value::Call(..) => apply_call(g, &mut stack, f, arg, icit)?,
                    Value::Neutral(Head::Def(_), _) if ends_in_field(&f) => {
                        apply_field(g, &mut stack, f, arg, icit)?
                    }
                    f => apply_step(f, arg, icit),
                }
            }
            Control::Unfold(id, spine) => unfold(g, &mut stack, id, spine)?,
            Control::NativeArg(id, spine, index) => native_arg(g, &mut stack, id, spine, index)?,
            Control::UnfoldAfterSuccs(k, id, spine) => {
                push(g, &mut stack, Frame::AddNat(k))?;
                unfold(g, &mut stack, id, spine)?
            }
            Control::Tree(node, env, stuck) => {
                if let Some((id, ..)) = &stuck {
                    g.machine.budget.enter_definition(id.0, g.env.def(*id).std);
                }
                let node = Term::strip_loc_rc(&node);
                match &*node {
                    Term::Case(ix, ..) | Term::NumCase(ix, ..) => {
                        let scrutinee = env[env.len() - 1 - ix].clone();
                        if needs_forcing(g, &scrutinee) || folded_call(g, &scrutinee) {
                            push(
                                g,
                                &mut stack,
                                Frame::Scrutinee {
                                    tree: node.clone(),
                                    env,
                                    stuck,
                                },
                            )?;
                            Control::Force(scrutinee)
                        } else {
                            branch(g, &mut stack, node, env, stuck, scrutinee)?
                        }
                    }
                    // A `Quot.lift` leaf counts as a case on its quotient
                    // (the unfolding policy, `Stuck`): its definition stays
                    // folded unless the quotient is a `Quot.mk`. Only a
                    // definition marked for it (`Def::lift_leaf`), so every
                    // call left folded here is one `is_folded` unfolds again
                    // for a comparison.
                    Term::Quot(QuotForm::Lift, args, _, _)
                        if args.len() == QuotForm::Lift.arity()
                            && matches!(&stuck, Some((id, _, true)) if folds_on_lift(g, *id)) =>
                    {
                        let q = args[5].clone();
                        let env: Env = env.into();
                        push(
                            g,
                            &mut stack,
                            Frame::LiftQuotient {
                                term: node.clone(),
                                env: env.clone(),
                                stuck,
                            },
                        )?;
                        Control::Eval(q, env)
                    }
                    _ => Control::Eval(node, env.into()),
                }
            }
            Control::Force(value) => match value {
                Value::Neutral(Head::Meta(m), spine) => match g.meta_solution(m) {
                    Some(solution) => {
                        push(g, &mut stack, Frame::Replay { spine, next: 0 })?;
                        Control::Return(solution)
                    }
                    None => Control::Return(Value::Neutral(Head::Meta(m), spine)),
                },
                Value::Call(id, spine, unfolding) => {
                    force_call(g, &mut stack, id, spine, unfolding)?
                }
                other => Control::Return(other),
            },
            Control::Return(value) => match stack.pop() {
                None => return Ok(value),
                Some(frame) => resume(g, frame, value, &mut stack)?,
            },
        };
    }
}

/// A cast's ends, evaluated with gluing on whatever the machine's mode, so
/// a call in them stays a call until the test needs it: with gluing off,
/// a cast whose ends mention a recursive call would evaluate that call in
/// full, whose own cast's ends hold the next one, and so on to the bottom.
/// A reader with gluing off forces the calls as it meets them, and sees
/// what it would have computed (see `Kept::fits`).
fn eval_ends(g: &Ev, env: &Env, ty: &Term, x: &Term, y: &Term) -> Result<Ends> {
    let was = g.machine.glue.replace(true);
    let ends = (|| {
        Ok(Ends {
            ty: eval(g, env, ty)?,
            x: eval(g, env, x)?,
            y: eval(g, env, y)?,
        })
    })();
    g.machine.glue.set(was);
    ends
}

/// The machine's pending work: its frames, and where each frame that
/// starts a segment ([`push_segment`]) is.
///
/// A segment is a forcing that was a machine of its own, started by
/// [`force`] (or [`run`]) on the Rust stack, before this machine did it
/// with its own stack (SW-4865, SW-4878, SW-4881): forcing a part of a
/// number that R3 and R4, a native, a number `case` or [`Frame::AddNat`]
/// read, and the forcing and case tree runs of rule E's reading for a
/// `case` ([`reread_on`]). The frame limit counts the frames of the
/// topmost segment, those above the frame that waits for it, so each
/// forcing has the allowance of frames its own machine had, and a run is
/// refused for depth exactly where it was then. The frames that start
/// segments are counted against the same limit, in place of the Rust stack
/// those nested machines took, so a chain of them that never ends still
/// stops (at a depth no configured stack reached before: each nested
/// machine took over a kilobyte of it).
#[derive(Default)]
struct Stack {
    frames: Vec<Frame>,
    /// The positions in `frames` of the frames that start segments.
    segments: Vec<usize>,
}

impl Stack {
    /// The frames the limit counts: those of the topmost segment.
    fn counted(&self) -> &[Frame] {
        let base = self.segments.last().map_or(0, |&i| i + 1);
        &self.frames[base..]
    }

    fn pop(&mut self) -> Option<Frame> {
        let frame = self.frames.pop()?;
        if self.segments.last() == Some(&self.frames.len()) {
            self.segments.pop();
        }
        Some(frame)
    }
}

/// The most segments ([`Stack`]) a run keeps pending. A chain of 2,000,000
/// stuck sums held 2.6 GB (about 1.3 KB a link), enough to exhaust a
/// browser's wasm memory before the frame limit refused it; no configured
/// stack reached 200,000 nested machines before these forcings shared this
/// stack (SW-4879).
const MAX_PENDING_SEGMENTS: usize = 200_000;

fn push(g: &Ev, stack: &mut Stack, frame: Frame) -> Result<()> {
    frames_for(g, stack, stack.counted().len() + 1)?;
    stack.frames.push(frame);
    Ok(())
}

/// [`push`] for `frame` waiting for a forcing that was a machine of its own
/// ([`Stack`]): the frames above it are a new segment.
fn push_segment(g: &Ev, stack: &mut Stack, frame: Frame) -> Result<()> {
    if stack.segments.len() >= MAX_PENDING_SEGMENTS {
        let e = g.machine.budget.too_much_pending();
        if e == ResourceError::Depth {
            note_deepest(g, stack.counted());
        }
        return Err(e);
    }
    frames_for(g, stack, stack.segments.len() + 1)?;
    stack.segments.push(stack.frames.len());
    stack.frames.push(frame);
    Ok(())
}

/// Whether the frame limit allows `pending` frames, noting the deepest
/// calls if not.
fn frames_for(g: &Ev, stack: &Stack, pending: usize) -> Result<()> {
    if let Err(e) = g.machine.budget.frames(pending) {
        if e == ResourceError::Depth {
            note_deepest(g, stack.counted());
        }
        return Err(e);
    }
    Ok(())
}

/// Tells the budget which definitions the pending frames are calls of: the
/// three with the most, for the message about recursing too deeply.
#[cold]
fn note_deepest(g: &Ev, stack: &[Frame]) {
    let mut counts: crate::collections::HashMap<usize, usize> = Default::default();
    for frame in stack {
        match frame {
            Frame::Unfolded(_, id) => *counts.entry(id.0).or_insert(0) += 1,
            // A case of a definition's body waiting for its scrutinee.
            Frame::Scrutinee {
                stuck: Some((id, ..)),
                ..
            }
            | Frame::ScrutineeReady {
                stuck: Some((id, ..)),
                ..
            } => *counts.entry(id.0).or_insert(0) += 1,
            _ => {}
        }
    }
    let mut counts: Vec<(usize, usize)> = counts.into_iter().collect();
    counts.sort_by_key(|&(id, count)| (std::cmp::Reverse(count), id));
    counts.truncate(3);
    // Calls that are pending as frames name themselves; otherwise the
    // definition running when the limit was hit is the best guess.
    if counts.is_empty()
        && let Some(id) = g.machine.budget.last_entered()
    {
        counts.push((id, stack.len()));
    }
    g.machine.budget.set_deepest(counts);
}

/// The value of `term` if it takes no evaluation steps (a variable, a
/// number, a function, a folded definition, a constructor with no fields), so
/// common terms like `f x` need no frames.
fn quick(g: &Ev, term: &Rc<Term>, env: &Env) -> Option<Value> {
    match &**term {
        Term::Var(ix) => Some(env[env.len() - 1 - ix].clone()),
        Term::Nat(n) => Some(Value::Nat(n.clone())),
        Term::Chars(c) => Some(chars_value(g, c)),
        Term::Sort(s) => Some(Value::Sort(*s)),
        Term::Refl => Some(Value::Refl),
        Term::Lam(x, i, b, pm) => Some(Value::Lam(
            x.clone(),
            *i,
            Closure {
                env: env.clone(),
                body: b.clone(),
            },
            *pm,
        )),
        Term::Def(id) => {
            let def = g.def(*id);
            match body_seen(g, *id) {
                _ if erases_proof(g, *id) => Some(erased()),
                Some(_) if def.arity == 0 && !folds(g, *id) => None,
                None if def.assumption.is_some() && erases_result(g, *id) => Some(erased()),
                None if def.assumption.is_some() && g.machine.erasure.program_running() => None,
                _ => Some(Value::Neutral(Head::Def(*id), Spine::new())),
            }
        }
        Term::Ctor(d, c, args) if args.is_empty() => Some(native::ctor(g, *d, *c, Vec::new())),
        Term::Loc(_, t) => quick(g, t, env),
        _ => None,
    }
}

/// The first step of evaluating `term`.
fn eval_step(g: &Ev, term: Rc<Term>, env: Env, stack: &mut Stack) -> Result<Control> {
    Ok(match &*term {
        Term::Var(ix) => Control::Return(env[env.len() - 1 - ix].clone()),
        Term::Def(id) => {
            let def = g.def(*id);
            match body_seen(g, *id) {
                _ if erases_proof(g, *id) => Control::Return(erased()),
                Some(_) if def.arity == 0 && erases_result(g, *id) => Control::Return(erased()),
                // An open goal's assumption that is a proof (or a type) is
                // erased like a theorem; one that is data stays neutral.
                None if def.assumption.is_some() && erases_result(g, *id) => {
                    Control::Return(erased())
                }
                // A running program can't compute with data it doesn't have.
                None if def.assumption.is_some() && g.machine.erasure.program_running() => {
                    g.machine.erasure.note_reached(Some(*id));
                    return Err(ResourceError::Unreachable);
                }
                // While gluing, a constant written in the source, or a
                // parameter default's helper, is kept as a call with no
                // arguments: read back by name, unfolded when forced. Other
                // ones the compiler made (a `%` in their name) aren't.
                Some(_)
                    if def.arity == 0
                        && !folds(g, *id)
                        && g.machine.glue.get()
                        && glues(g, *id)
                        && (def.param_default || !def.name.contains('%')) =>
                {
                    Control::Return(Value::Call(*id, Spine::new(), Rc::default()))
                }
                Some(body) if def.arity == 0 && !folds(g, *id) => {
                    Control::Eval(body.clone(), Values::from([]))
                }
                _ => Control::Return(Value::Neutral(Head::Def(*id), Spine::new())),
            }
        }
        Term::Meta(m) => Control::Return(match g.meta_solution(*m) {
            Some(value) => value,
            None => Value::Neutral(Head::Meta(*m), Spine::new()),
        }),
        Term::Data(d, args) if args.is_empty() => {
            Control::Return(Value::Data(*d, DataArgs::default()))
        }
        Term::Ctor(d, c, args) if args.is_empty() => {
            Control::Return(native::ctor(g, *d, *c, Vec::new()))
        }
        Term::Data(_, args) | Term::Ctor(_, _, args) => {
            let done = Vec::with_capacity(args.len());
            fields(g, term.clone(), env, done, stack)?
        }
        Term::Nat(n) => Control::Return(Value::Nat(n.clone())),
        Term::Chars(c) => Control::Return(chars_value(g, c)),
        Term::Sort(s) => Control::Return(Value::Sort(*s)),
        Term::Pi(_, _, a, _, _) => {
            let a = a.clone();
            push(
                g,
                stack,
                Frame::PiDomain {
                    term: term.clone(),
                    env: env.clone(),
                },
            )?;
            Control::Eval(a, env)
        }
        Term::Lam(x, i, b, pm) => Control::Return(Value::Lam(
            x.clone(),
            *i,
            Closure {
                env,
                body: b.clone(),
            },
            *pm,
        )),
        Term::App(f, a, i)
            if g.machine.erasure.active() && quick(g, a, &env).is_none() && erased_arg(g, f) =>
        {
            match quick(g, f, &env) {
                Some(f) => apply_step(f, erased(), *i),
                None => {
                    push(g, stack, Frame::AppErased(*i))?;
                    Control::Eval(f.clone(), env)
                }
            }
        }
        Term::App(f, a, i) => match quick(g, f, &env) {
            Some(f) => match quick(g, a, &env) {
                Some(a) => apply_step(f, a, *i),
                None => {
                    push(g, stack, Frame::AppFun(f, *i))?;
                    Control::Eval(a.clone(), env)
                }
            },
            None => {
                push(g, stack, Frame::AppArg(a.clone(), env.clone(), *i))?;
                Control::Eval(f.clone(), env)
            }
        },
        Term::Ann(e, _) => Control::Eval(e.clone(), env),
        // Strict and shared: the value is computed once, before the body,
        // which sees it in its environment (docs/proposals/let.md §A.2).
        // While running, a skipped `let` (a proof, a type, or unused; see
        // `Term::Let`) isn't computed: the placeholder takes its slot.
        Term::Let(_, _, _, body, true, _) if g.machine.erasure.active() => {
            Control::Eval(body.clone(), extend(&env, erased()))
        }
        Term::Let(_, _, value, body, _, _) => match quick(g, value, &env) {
            Some(value) => Control::Eval(body.clone(), extend(&env, value)),
            None => {
                let value = value.clone();
                push(
                    g,
                    stack,
                    Frame::LetBody {
                        term: term.clone(),
                        env: env.clone(),
                    },
                )?;
                Control::Eval(value, env)
            }
        },
        Term::Loc(_, t) => Control::Eval(t.clone(), env),
        Term::Case(..) | Term::NumCase(..) => Control::Tree(term.clone(), env.to_vec(), None),
        Term::Eq(ty, _, _) => {
            let ty = ty
                .clone()
                .expect("internal error: evaluating an unchecked equation");
            push(
                g,
                stack,
                Frame::EqParts {
                    term: term.clone(),
                    env: env.clone(),
                    done: Vec::with_capacity(3),
                },
            )?;
            Control::Eval(ty, env)
        }
        Term::Refl => Control::Return(Value::Refl),
        // While running (docs/proposals/map-equality.md §7.4.1, D862,
        // D921): `Quot.ind` and `Quot.sound` are proofs, and a lift whose
        // result is erased (a proof, a proposition or a type; the checker's
        // flag) is too, so each is the placeholder, which `J` takes its
        // base on (rule 4). A `Quot.mk` whose representative is erased
        // (its carrier's elements are types) has the placeholder for it.
        Term::Quot(QuotForm::Lift, _, true, _)
        | Term::Quot(QuotForm::Ind | QuotForm::Sound, ..)
            if g.machine.erasure.active() =>
        {
            Control::Return(erased())
        }
        Term::Quot(QuotForm::Mk, args, true, _)
            if g.machine.erasure.active() && args.len() == QuotForm::Mk.arity() =>
        {
            quot_args(g, term.clone(), env, Vec::new(), Some(erased()), stack)?
        }
        // The one computation rule (docs/proposals/map-equality.md §7.2):
        // `Quot.lift f h (Quot.mk a)` is `f a`. The quotient first, then.
        Term::Quot(QuotForm::Lift, args, _, _) if args.len() == QuotForm::Lift.arity() => {
            let q = args[5].clone();
            push(
                g,
                stack,
                Frame::LiftQuotient {
                    term: term.clone(),
                    env: env.clone(),
                    stuck: None,
                },
            )?;
            Control::Eval(q, env)
        }
        Term::Quot(..) => quot_args(g, term.clone(), env, Vec::new(), None, stack)?,
        // Rule K before the proof is evaluated: a cast into data whose ends
        // are equal is its base, and its proof is never computed (rule F).
        Term::J(_, base, proof, result)
            if *result != ProofMark::Proof && Term::j_ends(proof).is_some() =>
        {
            let (ty, x, y) = Term::j_ends(proof).expect("checked by the guard");
            let ends = eval_ends(g, &env, ty, x, y)?;
            if ends_meet(g, &ends)? {
                return Ok(Control::Eval(base.clone(), env));
            }
            let proof = proof.clone();
            push(
                g,
                stack,
                Frame::JCast(Box::new((term.clone(), env.clone(), ends))),
            )?;
            Control::Eval(proof, env)
        }
        Term::J(_, _, proof, _) => {
            let proof = proof.clone();
            push(
                g,
                stack,
                Frame::JProof {
                    term: term.clone(),
                    env: env.clone(),
                },
            )?;
            Control::Eval(proof, env)
        }
        Term::Proj(d, i, t) => {
            push(g, stack, Frame::ProjOf(*d, *i))?;
            Control::Eval(t.clone(), env)
        }
    })
}

/// Evaluates the arguments of a data type or constructor `term` after the
/// ones `done`: as many as are quick, then a frame for the next.
fn fields(
    g: &Ev,
    term: Rc<Term>,
    env: Env,
    mut done: Vec<Value>,
    stack: &mut Stack,
) -> Result<Control> {
    let (Term::Data(_, args) | Term::Ctor(_, _, args)) = &*term else {
        unreachable!("fields of a data type or constructor")
    };
    let field_erased = match &*term {
        Term::Ctor(d, c, _) if g.machine.erasure.active() => {
            Some(&g.data(*d).ctors[*c].field_erased)
        }
        _ => None,
    };
    while let Some(arg) = args.get(done.len()) {
        if field_erased.is_some_and(|e| e[done.len()]) {
            done.push(erased());
            continue;
        }
        match quick(g, arg, &env) {
            Some(v) => done.push(v),
            None => {
                let arg = arg.clone();
                push(
                    g,
                    stack,
                    Frame::Args {
                        term: term.clone(),
                        env: env.clone(),
                        done,
                    },
                )?;
                return Ok(Control::Eval(arg, env));
            }
        }
    }
    Ok(Control::Return(match &*term {
        Term::Data(d, _) => Value::Data(*d, done.into()),
        Term::Ctor(d, c, _) => native::ctor(g, *d, *c, done),
        _ => unreachable!(),
    }))
}

/// Evaluates the arguments of the quotient form `term` after the ones
/// `done` (and before `last`, its final argument if already computed): as
/// many as are quick, then a frame for the next. With all of them, the form
/// applied to them.
fn quot_args(
    g: &Ev,
    term: Rc<Term>,
    env: Env,
    mut done: Vec<Value>,
    last: Option<Value>,
    stack: &mut Stack,
) -> Result<Control> {
    let Term::Quot(form, args, _, mark) = &*term else {
        unreachable!("arguments of a quotient form")
    };
    let n = args.len() - usize::from(last.is_some());
    while let Some(arg) = args[..n].get(done.len()) {
        match quick(g, arg, &env) {
            Some(v) => done.push(v),
            None => {
                let arg = arg.clone();
                push(
                    g,
                    stack,
                    Frame::QuotArgs {
                        term: term.clone(),
                        env: env.clone(),
                        done,
                        last: last.map(Box::new),
                    },
                )?;
                return Ok(Control::Eval(arg, env));
            }
        }
    }
    done.extend(last);
    Ok(Control::Return(quot_value(*form, done, *mark)))
}

/// Continues `frame` with the value it was waiting for.
fn resume(g: &Ev, frame: Frame, value: Value, stack: &mut Stack) -> Result<Control> {
    Ok(match frame {
        Frame::AppArg(arg, env, icit) => {
            push(g, stack, Frame::AppFun(value, icit))?;
            Control::Eval(arg, env)
        }
        Frame::AppFun(f, icit) => apply_step(f, value, icit),
        Frame::AppErased(icit) => apply_step(value, erased(), icit),
        Frame::NativeArg { id, spine, next } => {
            // Forcing an argument whose head is no number, `native::run`
            // stops there and forces no more (`run_partial` may).
            if native::number_head(g, &value) {
                from_native(g, stack, id, spine, next)?
            } else {
                run_native(g, stack, id, spine, 0)?
            }
        }
        Frame::ReadNumber(read) => read_number(g, stack, *read, value, true)?,
        // `k` more than `value`, read as `native::view_with` would.
        Frame::AddNat(k) => {
            let read = ReadNumber {
                of: NumberOf::Rest,
                outer: Rc::unwrap_or_clone(k),
                k: BigUint::default(),
            };
            read_number(g, stack, read, value, false)?
        }
        Frame::Args {
            term,
            env,
            mut done,
        } => {
            done.push(value);
            fields(g, term, env, done, stack)?
        }
        Frame::QuotArgs {
            term,
            env,
            mut done,
            last,
        } => {
            done.push(value);
            quot_args(g, term, env, done, last.map(|last| *last), stack)?
        }
        Frame::LiftQuotient { term, env, stuck } => {
            push(g, stack, Frame::LiftForced { term, env, stuck })?;
            Control::Force(value)
        }
        // A folded call is taken apart: it unfolds.
        Frame::LiftForced { term, env, stuck } if folded_call(g, &value) => {
            unfold_for(g, stack, value, Frame::LiftReady { term, env, stuck })?
        }
        Frame::LiftForced { term, env, stuck } | Frame::LiftReady { term, env, stuck } => {
            let Term::Quot(_, args, _, _) = &*term else {
                unreachable!("a `LiftForced` frame is for `Quot.lift`")
            };
            match quot_mk_rep(&value) {
                // `f a`, as an application with `f` computed now.
                Some(a) => {
                    push(g, stack, Frame::AppTo(a.clone(), Icit::Explicit))?;
                    Control::Eval(args[3].clone(), env)
                }
                // Stuck: a leaf of a case tree leaves its definition folded;
                // otherwise it's the lift applied to its arguments.
                None if matches!(stuck, Some((_, _, true))) => stuck_tree(g, stack, stuck)?,
                None => quot_args(g, term, env, Vec::new(), Some(value), stack)?,
            }
        }
        Frame::LetBody { term, env } => {
            let Term::Let(_, _, _, body, _, _) = &*term else {
                unreachable!("a `LetBody` frame is for a `let`")
            };
            Control::Eval(body.clone(), extend(&env, value))
        }
        Frame::PiDomain { term, env } => {
            let Term::Pi(x, i, _, b, pm) = &*term else {
                unreachable!("a `PiDomain` frame is for a function type")
            };
            Control::Return(Value::Pi(
                x.clone(),
                *i,
                Shared::new(value),
                Closure {
                    env,
                    body: b.clone(),
                },
                *pm,
            ))
        }
        // A field of a glued call waits for the call, as rule 2's do.
        Frame::ProjOf(d, i) if matches!(value, Value::Call(..)) => {
            Control::Return(project_call(d, i, value))
        }
        Frame::ProjOf(d, i) => {
            push(g, stack, Frame::ProjForced(d, i))?;
            Control::Force(value)
        }
        Frame::ProjForced(d, i) if folded_call(g, &value) => {
            let next = if names_folded_fields(g) && is_eta_type(g, d) {
                Frame::FoldedField(Box::new((d, i, project(d, i, value.clone()))))
            } else {
                Frame::ProjReady(d, i)
            };
            unfold_for(g, stack, value, next)?
        }
        Frame::FoldedField(field) => {
            let (d, i, named) = *field;
            Control::Return(match value {
                Value::Neutral(head, _) if !matches!(head, Head::Meta(_)) => named,
                other => project(d, i, other),
            })
        }
        Frame::ProjForced(d, i) | Frame::ProjReady(d, i) => Control::Return(project(d, i, value)),
        // A folded call is taken apart: it unfolds.
        Frame::Scrutinee { tree, env, stuck } if folded_call(g, &value) => {
            unfold_for(g, stack, value, Frame::ScrutineeReady { tree, env, stuck })?
        }
        Frame::Scrutinee { tree, env, stuck } | Frame::ScrutineeReady { tree, env, stuck } => {
            branch(g, stack, tree, env, stuck, value)?
        }
        Frame::AppTo(arg, icit) => apply_step(value, arg, icit),
        Frame::Unfolded(unfolding, id) => {
            if needs_forcing(g, &value) {
                push(g, stack, Frame::Unfolded(unfolding, id))?;
                Control::Force(value)
            } else {
                unfolding.set(g, value.clone());
                Control::Return(value)
            }
        }
        // Off the hot path, so that their temporaries don't widen every
        // frame of this function, which is on the Rust stack once a machine.
        frame => resume_rare(g, frame, value, stack)?,
    })
}

/// [`resume`] for the frames that are rare, or whose work needs large
/// temporaries: equations, `J`, fields of calls, replaying a solved
/// metavariable's spine and unfolding folded calls.
#[inline(never)]
fn resume_rare(g: &Ev, frame: Frame, value: Value, stack: &mut Stack) -> Result<Control> {
    Ok(match frame {
        Frame::EqParts {
            term,
            env,
            mut done,
        } => {
            done.push(value);
            let Term::Eq(_, a, b) = &*term else {
                unreachable!("an `EqParts` frame is for an equation")
            };
            match done.len() {
                1 | 2 => {
                    let next = if done.len() == 1 {
                        a.clone()
                    } else {
                        b.clone()
                    };
                    push(
                        g,
                        stack,
                        Frame::EqParts {
                            term: term.clone(),
                            env: env.clone(),
                            done,
                        },
                    )?;
                    Control::Eval(next, env)
                }
                _ => {
                    let mut parts = done.into_iter().map(Shared::new);
                    let (ty, a, b) = (
                        parts.next().expect("three parts"),
                        parts.next().expect("three parts"),
                        parts.next().expect("three parts"),
                    );
                    Control::Return(Value::Eq(ty, a, b))
                }
            }
        }
        Frame::JProof { term, env } => {
            push(g, stack, Frame::JForced { term, env })?;
            Control::Force(value)
        }
        Frame::JCast(cast) => {
            let (term, env, ends) = *cast;
            let Term::J(motive, base, _, result) = &*term else {
                unreachable!("a `JCast` frame is for `J`")
            };
            match value {
                Value::Refl => Control::Eval(base.clone(), env),
                v if erase::is_erased(&v) => {
                    g.machine.erasure.note_transport();
                    Control::Eval(base.clone(), env)
                }
                Value::Neutral(head, spine) => {
                    if *result == ProofMark::NotProof {
                        proof_counts::record(g, proof_counts::Kind::StuckCastIntoData, 1);
                    }
                    let motive = motive.clone();
                    push(
                        g,
                        stack,
                        Frame::JMotive {
                            term: term.clone(),
                            env: env.clone(),
                            head,
                            spine,
                            ends: Some(Box::new(ends)),
                        },
                    )?;
                    Control::Eval(motive, env)
                }
                // A glued call (only an elaborator's term whose mark isn't
                // known can have one here): forced, as any proof of `J` is.
                other => {
                    push(g, stack, Frame::JForced { term, env })?;
                    Control::Force(other)
                }
            }
        }
        // A folded call is taken apart: it unfolds (in this machine, so a
        // proof made of many folded steps needs no Rust stack).
        Frame::JForced { term, env } if folded_call(g, &value) => {
            unfold_for(g, stack, value, Frame::JReady { term, env })?
        }
        // So is a stuck field of a call, as when it's applied ([`apply_field`]).
        Frame::JForced { term, env } if computes_field(g, &value) => {
            unfold_field_for(g, stack, value, FieldUse::J { term, env })?
        }
        Frame::JForced { term, env } | Frame::JReady { term, env } => {
            let Term::J(motive, base, proof, result) = &*term else {
                unreachable!("a `JForced` frame is for `J`")
            };
            match value {
                Value::Refl => Control::Eval(base.clone(), env),
                // Every closed proof of an equation is `refl` (`erase.rs`).
                v if erase::is_erased(&v) => {
                    g.machine.erasure.note_transport();
                    Control::Eval(base.clone(), env)
                }
                Value::Neutral(head, spine) => {
                    // Rule K: a cast into data whose ends are equal is its
                    // base, whatever its proof (which is never looked at).
                    let ends = match Term::j_ends(proof) {
                        // Only the kernel puts ends on a `J`, and only on
                        // one into data; the elaborator's copies of it may
                        // not know the mark.
                        Some((ty, x, y)) if *result != ProofMark::Proof => {
                            let ends = eval_ends(g, &env, ty, x, y)?;
                            if ends_meet(g, &ends)? {
                                return Ok(Control::Eval(base.clone(), env));
                            }
                            Some(Box::new(ends))
                        }
                        _ => None,
                    };
                    if *result == ProofMark::NotProof {
                        proof_counts::record(g, proof_counts::Kind::StuckCastIntoData, 1);
                    }
                    let motive = motive.clone();
                    push(
                        g,
                        stack,
                        Frame::JMotive {
                            term: term.clone(),
                            env: env.clone(),
                            head,
                            spine,
                            ends,
                        },
                    )?;
                    Control::Eval(motive, env)
                }
                other => panic!("internal error: J applied to {}", describe(&other)),
            }
        }
        Frame::CallField(field) if !field.unfolded && folded_call(g, &value) => {
            let CallField {
                data: d,
                index: i,
                id,
                spine,
                ..
            } = *field;
            unfold_for(
                g,
                stack,
                value,
                Frame::CallField(Box::new(CallField {
                    data: d,
                    index: i,
                    id,
                    spine,
                    unfolded: true,
                })),
            )?
        }
        Frame::CallField(field) => {
            let CallField {
                data: d,
                index: i,
                id,
                spine,
                ..
            } = *field;
            // A call that steps at once is named by its step, as it's read
            // back (`(if True then x else y).i` is `x.i`).
            if matches!(value, Value::Neutral(ref head, _) if !matches!(head, Head::Meta(_)))
                && matches_at_once(g, id, &spine)?
            {
                return Ok(Control::Force(unfold_once(g, id, spine)?));
            }
            Control::Return(match value {
                // Stuck, the field is the field call itself, as a folded call
                // ([`is_folded`]): `(f x).i` stays in goals as that, as
                // `f x` does, rather than as the projection of what `f x`
                // computed to. It's a name for that projection, which is
                // stuck too: the machine takes it apart as stuck, and a
                // comparison that finds it different from something
                // unfolds it to the projection first (`conv`, the
                // unifier), so it's equal to exactly what that is. An
                // unknown's field stays one, which the unifier can solve.
                Value::Neutral(head, _) if !matches!(head, Head::Meta(_)) => {
                    Value::Neutral(Head::Def(id), spine)
                }
                other => project(d, i, other),
            })
        }
        Frame::JMotive {
            term,
            env,
            head,
            spine,
            ends,
        } => {
            let Term::J(_, base, _, result) = &*term else {
                unreachable!("a `JMotive` frame is for `J`")
            };
            push(
                g,
                stack,
                Frame::JBase(Box::new((head, spine, value, *result, ends))),
            )?;
            Control::Eval(base.clone(), env)
        }
        Frame::JBase(stuck) => {
            let (head, mut spine, motive, result, ends) = *stuck;
            spine.push(Elim::J {
                motive: Box::new(motive),
                base: Box::new(value),
                result,
                ends,
            });
            Control::Return(Value::Neutral(head, spine))
        }
        Frame::Unfolding(unfolding) => {
            let (id, spine, next) = *unfolding;
            match &value {
                // Stuck: `next` gets the call as it is.
                Value::Neutral(Head::Def(i2), s2) if *i2 == id && s2.ptr_eq(&spine) => {
                    resume(g, next, value, stack)?
                }
                _ if folded_call(g, &value) => unfold_for(g, stack, value, next)?,
                // A glued call (a `decreasing` definition's fuelled helper)
                // or a solved metavariable is forced, and what it computes
                // to looked at again: it may
                // be another folded call (the helper's leaf `g y`), which
                // unglued evaluation, where the helper isn't glued, reaches
                // here as it is and unfolds. Handed to `next` still folded, a
                // `case` on it, or on a field of it, would stay stuck glued
                // where unglued evaluation computes (SW-2126, D3030).
                _ if needs_forcing(g, &value) => {
                    push(g, stack, Frame::Unfolding(Box::new((id, spine, next))))?;
                    Control::Force(value)
                }
                _ => {
                    push(g, stack, next)?;
                    Control::Return(value)
                }
            }
        }
        // The forced part has its unfolding kept, where reading the
        // scrutinee again finds it.
        Frame::NumberScrutinee(waiting) => {
            let NumberScrutinee {
                tree,
                env,
                stuck,
                scrutinee,
                asked,
            } = *waiting;
            branch_asked(g, stack, tree, env, stuck, scrutinee, asked)?
        }
        Frame::NativeAgain { id, spine, asked } => run_native(g, stack, id, spine, asked)?,
        Frame::FloatAgain {
            id,
            spine,
            glue,
            asked,
        } => run_float(g, stack, id, spine, glue, asked)?,
        Frame::Reread(mut reread) => {
            let folded = reread.folded.as_mut().expect("an unfolding is waiting");
            let need = folded.answer(g, value);
            reread_go(g, stack, reread, RereadStep::Fold(need))?
        }
        Frame::FieldOf(field) => {
            let FieldOf {
                id,
                spine,
                call,
                then,
            } = *field;
            // Stuck in its own case tree, the call has no unfolding to take a
            // field of: the field is eliminated as it is, stuck.
            if matches!(&value, Value::Neutral(Head::Def(i2), s2) if *i2 == id && s2.ptr_eq(&call))
            {
                return Ok(match then {
                    FieldUse::App(arg, icit) => {
                        let mut spine = spine;
                        spine.push(Elim::App(arg, icit));
                        Control::Unfold(id, spine)
                    }
                    FieldUse::J { term, env } => {
                        push(g, stack, Frame::JReady { term, env })?;
                        Control::Return(Value::Neutral(Head::Def(id), spine))
                    }
                });
            }
            push(
                g,
                stack,
                match then {
                    FieldUse::App(arg, icit) => Frame::AppTo(arg, icit),
                    // The field isn't forced yet: it may be a call.
                    FieldUse::J { term, env } => Frame::JProof { term, env },
                },
            )?;
            let arity = g.def(id).arity;
            for elim in spine[arity..].iter().rev() {
                let &Elim::Proj(d, i) = elim else {
                    unreachable!("checked by is_folded")
                };
                push(g, stack, Frame::ProjOf(d, i))?;
            }
            Control::Return(value)
        }
        Frame::Replay { spine, next } => match spine.get(next) {
            None => Control::Force(value),
            Some(Elim::App(..)) if matches!(value, Value::Lam(..)) => {
                let Value::Lam(_, _, closure, _) = &value else {
                    unreachable!("matched above")
                };
                let args = spine[next..].iter().map_while(|e| match e {
                    Elim::App(arg, _) => Some(arg),
                    _ => None,
                });
                let (body, env, taken) = enter_run(closure, args);
                push(
                    g,
                    stack,
                    Frame::Replay {
                        spine,
                        next: next + taken,
                    },
                )?;
                Control::Eval(body, env)
            }
            Some(Elim::App(arg, icit)) => {
                let (arg, icit) = (arg.clone(), *icit);
                push(
                    g,
                    stack,
                    Frame::Replay {
                        spine,
                        next: next + 1,
                    },
                )?;
                apply_step(value, arg, icit)
            }
            // A field of a glued call waits for the call, as with `ProjOf`.
            Some(&Elim::Proj(d, i)) if matches!(value, Value::Call(..)) => {
                push(
                    g,
                    stack,
                    Frame::Replay {
                        spine,
                        next: next + 1,
                    },
                )?;
                Control::Return(project_call(d, i, value))
            }
            Some(Elim::J { .. } | Elim::Proj(..)) => {
                push(g, stack, Frame::ReplayElim { spine, next })?;
                Control::Force(value)
            }
        },
        Frame::ReplayElim { spine, next } => {
            let elim = spine[next].clone();
            // A metavariable's solution while elaborating, or the rest of a
            // spine after a folded call that conversion unfolded
            // ([`unfold_folded_head`], the kernel too): either way the
            // machine this starts for a folded value is bounded by the
            // program.
            // What it unfolds to may be a glued call (a `decreasing`
            // definition's fuelled helper), which a projection can't take
            // apart unforced.
            let unfolded = match unfold_folded(g, &value)? {
                Some(unfolded) => Some(force(g, unfolded)?),
                None => None,
            };
            let result = match &elim {
                // A field of a folded call whose unfolding is stuck is kept
                // as the call's, as `Frame::FoldedField` keeps it.
                Elim::Proj(d, i)
                    if names_folded_fields(g)
                        && is_eta_type(g, *d)
                        && folded_call(g, &value)
                        && matches!(&unfolded, Some(Value::Neutral(head, _)) if !matches!(head, Head::Meta(_))) =>
                {
                    project(*d, *i, value)
                }
                Elim::Proj(d, i) => project(*d, *i, unfolded.unwrap_or(value)),
                Elim::J { base, ends, .. } => match unfolded.unwrap_or(value) {
                    Value::Refl => (**base).clone(),
                    // Rule K, again: an unknown in the ends may have been
                    // solved since.
                    Value::Neutral(..)
                        if ends.as_deref().map(|e| ends_meet(g, e)).transpose()? == Some(true) =>
                    {
                        (**base).clone()
                    }
                    Value::Neutral(head, mut s) => {
                        s.push(elim.clone());
                        Value::Neutral(head, s)
                    }
                    other => panic!("internal error: J applied to {}", describe(&other)),
                },
                Elim::App(..) => unreachable!("a `ReplayElim` frame is for a `J` or a projection"),
            };
            push(
                g,
                stack,
                Frame::Replay {
                    spine,
                    next: next + 1,
                },
            )?;
            Control::Return(result)
        }
        Frame::AppArg(..)
        | Frame::AppFun(..)
        | Frame::AppErased(..)
        | Frame::NativeArg { .. }
        | Frame::ReadNumber(..)
        | Frame::AddNat(..)
        | Frame::Args { .. }
        | Frame::QuotArgs { .. }
        | Frame::LiftQuotient { .. }
        | Frame::LiftForced { .. }
        | Frame::LiftReady { .. }
        | Frame::LetBody { .. }
        | Frame::PiDomain { .. }
        | Frame::ProjOf(..)
        | Frame::ProjForced(..)
        | Frame::ProjReady(..)
        | Frame::FoldedField(..)
        | Frame::Scrutinee { .. }
        | Frame::ScrutineeReady { .. }
        | Frame::AppTo(..)
        | Frame::Unfolded(..) => unreachable!("`resume` takes these frames"),
    })
}

/// The value of a compact list. Only checked terms, and the elaborator's
/// (which makes them only once the representation is registered), are
/// evaluated, and the kernel refuses `Term::Chars` without it.
fn chars_value(g: &Ev, c: &Chars) -> Value {
    let text = g
        .env
        .builtins()
        .text
        .as_ref()
        .expect("internal error: compact text without `List` and `Char`");
    chars::value(text, c.clone())
}

/// One step of the expansion of a compact list `value`, as matching sees it
/// (see [`chars::step`]); anything else as it is.
pub fn expand_step(g: &Ev, value: Value) -> Value {
    match (&value, &g.env.builtins().text) {
        (Value::Chars(c), Some(text)) => chars::step(text, c),
        _ => value,
    }
}

/// Whether [`force`] would change `value`: it's headed by a solved
/// metavariable, or it's a call.
#[inline]
fn needs_forcing(g: &Ev, value: &Value) -> bool {
    match value {
        Value::Neutral(Head::Meta(m), _) => g.meta_solution(*m).is_some(),
        Value::Call(..) => true,
        _ => false,
    }
}

/// Counts a `case` on `value` stuck in a definition whose result is data,
/// if `value` is a proof of a proposition `d` with one constructor (what
/// rule S would compute; `proof_counts`).
#[cold]
fn count_stuck_one_shape(g: &Ev, d: DataId, stuck: &Stuck, value: &Value) {
    let data = g.data(d);
    let into_data = matches!(stuck, Some((id, ..)) if !g.def(*id).proof);
    if data.sort == Sort::Prop
        && data.ctors.len() == 1
        && into_data
        && !matches!(value, Value::Ctor(..))
    {
        proof_counts::record(g, proof_counts::Kind::StuckOneShapeIntoData, 1);
    }
}

/// The branch of the case node `tree` for the (forced) scrutinee `value`.
#[inline]
fn branch(
    g: &Ev,
    stack: &mut Stack,
    tree: Rc<Term>,
    env: Vec<Value>,
    stuck: Stuck,
    value: Value,
) -> Result<Control> {
    branch_asked(g, stack, tree, env, stuck, value, 0)
}

/// [`branch`], for a number case that has had this machine force a glued
/// call inside `value` `asked` times ([`Frame::NumberScrutinee`]).
fn branch_asked(
    g: &Ev,
    stack: &mut Stack,
    tree: Rc<Term>,
    mut env: Vec<Value>,
    stuck: Stuck,
    value: Value,
    asked: usize,
) -> Result<Control> {
    // A folded call was unfolded before this (`Frame::Scrutinee`).
    let (d, branches, scrutinee) = match &*tree {
        Term::Case(ix, d, branches) => (d, branches, &env[env.len() - 1 - ix]),
        Term::NumCase(_, arms, default) => {
            // A glued call inside the number is forced by this machine, and
            // then the number is read again, as a native's are
            // ([`run_native`]).
            start_read();
            let viewed = native::view_with(g, &value, forcing_for(asked));
            if let Some(part) = ASKED.take() {
                let waiting = Box::new(NumberScrutinee {
                    tree: tree.clone(),
                    env: env.clone(),
                    stuck,
                    scrutinee: value,
                    asked: asked + 1,
                });
                push_segment(g, stack, Frame::NumberScrutinee(waiting))?;
                return Ok(Control::Force(part));
            }
            let next = match viewed? {
                // A number: its arm, or the default.
                (k, None) => match arms.binary_search_by(|a| (*a.value).cmp(&k)) {
                    Ok(i) => arms[i].body.clone(),
                    Err(_) => default.clone(),
                },
                // `k + x` is at least `k`, so if every arm's number is below
                // `k`, it can't be any of them. Otherwise it depends on `x`
                // (failing to show `x` is some number never means it isn't).
                // Likewise if `x` is a variable known not to be the number
                // each arm's is `k` short of (`Apart`).
                (k, Some(base)) => match arms.last() {
                    Some(last) if *last.value < k => default.clone(),
                    _ if apart_of(&base).excludes(g, &k, arms) => default.clone(),
                    _ => {
                        let then = AfterReread {
                            tree: tree.clone(),
                            env,
                            stuck,
                            succs: Some(k),
                            value: base,
                        };
                        return reread_on(g, stack, then);
                    }
                },
            };
            return Ok(Control::Tree(next, env, stuck));
        }
        _ => unreachable!("a case node"),
    };
    let (c, fields) = match value {
        Value::Ctor(d2, c, fields) if d2 == *d => (c, fields.to_vec()),
        // A constructor of another type: only an ill-typed term gets here,
        // which the kernel never runs, but the elaborator may, before the
        // kernel sees it: unification's first-order rule can solve an
        // unknown whose type it doesn't know with a value of another type
        // (`unify::first_order`, SW-919, SW-2961). It doesn't compute, as a
        // neutral wouldn't; taking the constructor's index as this type's
        // would pick a wrong branch, or one past the end. A program run with
        // one is a compiler bug, and fails loudly.
        Value::Ctor(..) => {
            if g.machine.erasure.program_running() {
                panic!("internal error: a case on one type was given another type's constructor");
            }
            return stuck_tree(g, stack, stuck);
        }
        other @ (Value::Nat(_) | Value::NatAdd(..)) if Some(*d) == g.env.builtins().nat => {
            match native::split_value(&other) {
                Some(split) => split,
                None => return stuck_tree(g, stack, stuck),
            }
        }
        // A compact list: what matching its expansion would find.
        Value::Chars(chars) => match &g.env.builtins().text {
            Some(text) if text.list == *d => chars::split(text, &chars),
            _ => return stuck_tree(g, stack, stuck),
        },
        // An erased proof: matching it into data is allowed only for one
        // constructor with only proof fields (`E-PROP-ELIM`, `erase.rs`).
        v if erase::is_erased(&v) && g.data(*d).sort == Sort::Prop && !branches.is_empty() => {
            (0, vec![erased(); g.data(*d).ctors[0].fields.len()])
        }
        // A proof of a proposition with no constructors (`Void`, `False =
        // True`): a running program has one only through a false goal's
        // erased proof, and stops, as at an impossible branch.
        v if erase::is_erased(&v) && branches.is_empty() && g.machine.erasure.program_running() => {
            g.machine.erasure.note_reached(None);
            return Err(ResourceError::Unreachable);
        }
        // Record eta, rule 2 (docs/proposals/record-eta.md §6.4): a `case`
        // on an unknown value of a type with eta takes its only branch, its
        // fields bound to the value's projections. Sound because every value
        // of such a type is its constructor applied to its fields (the
        // conditions are at `check::qualifies_for_eta`), so whatever `n` turns out to
        // be, this is the branch it takes, with these fields; and it ends,
        // since it removes a `case` and adds none. An unsolved metavariable
        // counts as unknown too: the kernel never sees one, and to the
        // elaborator `?r.row` is as stuck as `match ?r` was, but now it has
        // the shape the other side of a comparison computes to
        // (`Bag.has ?b x` against `Bag.has b x` meet at `?b.items` and
        // `b.items`, which the unifier compares by their records). Not while
        // a program runs (its values are closed; an open goal's data-typed
        // assumption is closed but neutral, and a `case` on it stays stuck).
        //
        // The fields are projections of the scrutinee as it was (§6.4): a
        // glued call stays a call in them ([`project_call`]), so a goal
        // keeps `(Set.map s f).items` rather than the inside of `Set.map`'s
        // unfolding. Both mean the same.
        n @ Value::Neutral(..)
            if eta_case(g, *d) && !matches!(&stuck, Some((id, ..)) if eta_held(g, *id)) =>
        {
            let k = g.data(*d).ctors[0].fields.len();
            (0, eta_fields(g, *d, k, scrutinee, n)?)
        }
        // Rule S (docs/core.md, "The equality rule"): a `case` producing
        // data on a proof of a proposition with one constructor takes its
        // branch whatever the proof, each field (a proof too) bound to that
        // field of the proof. `E-PROP-ELIM` allowed the match, so the
        // constructor has only proof fields and doesn't mention its type.
        n @ Value::Neutral(..) if one_shape(g, *d, &stuck, &env, &tree, &n)? => {
            proof_counts::record(g, proof_counts::Kind::OneShapeFired, 1);
            let k = g.data(*d).ctors[0].fields.len();
            (0, (0..k).map(|i| project(*d, i, n.clone())).collect())
        }
        other => {
            let then = AfterReread {
                tree: tree.clone(),
                env,
                stuck,
                succs: None,
                value: other,
            };
            return reread_on(g, stack, then);
        }
    };
    let Some(body) = branches[c].body.clone() else {
        // An impossible branch is never reached by a well-typed value
        // (docs/proposals/indexed-families.md §6.8) whose proofs are all
        // checked. A run reaches one only through an open goal's erased
        // proof whose goal is false, and stops; checking leaves the
        // definition folded.
        if g.machine.erasure.program_running() {
            g.machine.erasure.note_reached(None);
            return Err(ResourceError::Unreachable);
        }
        return stuck_tree(g, stack, stuck);
    };
    env.extend(fields);
    Ok(Control::Tree(body, env, stuck))
}

/// Whether a `case` on a proof of `d`, the case node `tree` with its
/// environment `env`, in the case tree of the definition `stuck` names,
/// takes its only branch by rule S (docs/core.md, "The equality rule"): `d`
/// is a proposition with one constructor whose fields are all proofs, and
/// the definition's result is data (a proof is never computed, and needs no
/// branch taken).
///
/// For a proposition with indices (D3724, as Lean's `to_cnstr_when_K`;
/// D3727 for fields), the constructor's result indices, for the
/// scrutinee's parameters and its fields read as the scrutinee's
/// projections, must equal the scrutinee's indices: then the constructor
/// applied to those projections is a proof of the scrutinee's own type, so
/// rule I makes the scrutinee that constructor, and the branch's
/// refinement already holds. The scrutinee's type is read off the
/// definition's type for a parameter, and for a field an enclosing `case`
/// bound, off that field's declared type ([`slot_type`]).
fn one_shape(
    g: &Ev,
    d: DataId,
    stuck: &Stuck,
    env: &[Value],
    tree: &Term,
    scrutinee: &Value,
) -> Result<bool> {
    let data = g.data(d);
    let Some((id, ..)) = stuck else {
        return Ok(false);
    };
    let ctor = match &data.ctors[..] {
        [ctor] => ctor,
        _ => return Ok(false),
    };
    if data.sort != Sort::Prop
        || ctor.field_sorts.iter().any(|s| *s != Sort::Prop)
        || g.def(*id).proof
    {
        return Ok(false);
    }
    if data.indices.is_empty() {
        return Ok(true);
    }
    let Term::Case(ix, ..) = tree else {
        unreachable!("a case node")
    };
    let level = env.len() - 1 - ix;
    let Some(ty) = slot_type(g, *id, tree, env, level)? else {
        return Ok(false);
    };
    let params = data.params.len();
    let Value::Data(d2, args) = ty else {
        return Ok(false);
    };
    if d2 != d || args.len() != params + ctor.result.len() {
        return Ok(false);
    }
    let mut ctor_env = args[..params].to_vec();
    ctor_env.extend((0..ctor.fields.len()).map(|i| project(d, i, scrutinee.clone())));
    for (k, index) in ctor.result.iter().enumerate() {
        let from_ctor = eval(g, &ctor_env, index)?;
        if !meet_in_evaluation(g, &from_ctor, &args[params + k])? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Where a variable of a case tree's environment past its definition's
/// parameters was bound: field `field` of constructor `ctor` of `d`, by the
/// `case` on the variable at level `scrutinee`, whose fields start at level
/// `first`.
#[derive(Clone, Copy)]
struct BoundField {
    d: DataId,
    scrutinee: usize,
    ctor: usize,
    field: usize,
    first: usize,
}

/// The type of the variable at `level` of `env`, the environment of the
/// case node `tree` in definition `id`'s case tree, forced: a parameter's
/// as the definition's type gives it, over the parameters before it; a
/// field's as its constructor declares it, over the type of the enclosing
/// scrutinee's parameters and the fields before it (as `check::infer_proj`
/// types a projection). That holds whichever way the enclosing `case` took
/// its branch: iota, rule S, record eta or a number's split each bind the
/// constructor's fields of a value of the scrutinee's type. `None` if it
/// can't be read: a type that doesn't compute to a function type that far, or a
/// node found other than exactly once in the tree (so that the path to it,
/// and with it what each variable is, is the one evaluation took).
fn slot_type(g: &Ev, id: DefId, tree: &Term, env: &[Value], level: usize) -> Result<Option<Value>> {
    let def = g.def(id);
    if level < def.arity {
        return field_type(g, id, &[], env, level);
    }
    let Some(body) = &def.body else {
        return Ok(None);
    };
    let root = Term::peel_lams_rc(body, def.arity);
    let mut found = None;
    let mut times = 0;
    bound_fields(
        &root,
        tree,
        def.arity,
        &mut Vec::new(),
        &mut found,
        &mut times,
    );
    match found {
        Some(fields) if times == 1 && fields.len() + def.arity == env.len() => {
            field_type(g, id, &fields, env, level)
        }
        _ => Ok(None),
    }
}

/// [`slot_type`] for `level`, given what binds each variable past the
/// parameters.
fn field_type(
    g: &Ev,
    id: DefId,
    fields: &[BoundField],
    env: &[Value],
    level: usize,
) -> Result<Option<Value>> {
    let def = g.def(id);
    if level < def.arity {
        return parameter_type(g, def.ty(), &env[..level]);
    }
    let f = fields[level - def.arity];
    let Some(Value::Data(d, args)) = field_type(g, id, fields, env, f.scrutinee)? else {
        return Ok(None);
    };
    let data = g.data(f.d);
    let params = data.params.len();
    if d != f.d || args.len() < params {
        return Ok(None);
    }
    let Some((_, field_ty)) = data.ctors.get(f.ctor).and_then(|c| c.fields.get(f.field)) else {
        return Ok(None);
    };
    let mut ctor_env = args[..params].to_vec();
    ctor_env.extend(env[f.first..f.first + f.field].iter().cloned());
    Ok(Some(force(g, eval(g, &ctor_env, field_ty)?)?))
}

/// Finds the case node `target` in the case tree `node`, whose environment
/// so far is `arity` parameters and then `path`: `found` gets what binds
/// each variable past the parameters at `target`, and `times` counts the
/// nodes found.
fn bound_fields(
    node: &Term,
    target: &Term,
    arity: usize,
    path: &mut Vec<BoundField>,
    found: &mut Option<Vec<BoundField>>,
    times: &mut usize,
) {
    let node = node.strip_loc();
    if std::ptr::eq(node, target) {
        *times += 1;
        *found = Some(path.clone());
        return;
    }
    match node {
        Term::Case(ix, d, branches) => {
            let len = arity + path.len();
            let Some(scrutinee) = len.checked_sub(1 + ix) else {
                return;
            };
            for (c, branch) in branches.iter().enumerate() {
                let Some(body) = &branch.body else {
                    continue;
                };
                let k = branch.names.len();
                path.extend((0..k).map(|field| BoundField {
                    d: *d,
                    scrutinee,
                    ctor: c,
                    field,
                    first: len,
                }));
                bound_fields(body, target, arity, path, found, times);
                path.truncate(len - arity);
            }
        }
        Term::NumCase(_, arms, default) => {
            for arm in arms.iter() {
                bound_fields(&arm.body, target, arity, path, found, times);
            }
            bound_fields(default, target, arity, path, found, times);
        }
        _ => {}
    }
}

/// The type of the next parameter of the closed function type `ty`, after
/// `args`, forced: `ty` evaluated, each function type forced (so a type
/// written through a definition, `def f: Reader` for `def Reader: Type :=
/// (x: Nat) → Q2 x → Nat`, is read as what it unfolds to, SW-4796) and its
/// codomain given the next argument. `None` if `ty` doesn't compute to a
/// function type that far, as for one behind an opaque definition this
/// evaluation can't unfold.
fn parameter_type(g: &Ev, ty: &Term, args: &[Value]) -> Result<Option<Value>> {
    let mut ty = eval(g, &[], ty)?;
    for arg in args {
        let Value::Pi(_, _, _, cod, _) = force(g, ty)? else {
            return Ok(None);
        };
        ty = cod.apply(g, arg.clone())?;
    }
    match force(g, ty)? {
        Value::Pi(_, _, domain, _, _) => Ok(Some(force(g, (*domain).clone())?)),
        _ => Ok(None),
    }
}

/// A stuck `m + n` with a call folded by name in `n`, as what R3 and R4
/// make of it once that is unfolded ([`crate::nat_add::reread`]): for a
/// comparison or a `case` that reads the sum (rule E, G2), never for
/// evaluation itself.
fn reread_sum(g: &Ev, value: &Value, unread: &mut Unread) -> Result<Option<Value>> {
    crate::nat_add::reread(g, value, force, |x| unfold_folded(g, x), unread)
}

/// [`reread_sum`] for a `case` whose scrutinee, `then.value`, is a stuck
/// sum, on this machine's stack, then the `case` going on with what it
/// reads ([`AfterReread::finish`]).
///
/// The walk is [`crate::nat_add::Walk`], as `reread_sum`'s is; only where
/// it forces and unfolds differs. `reread_sum` forces with [`force`] and
/// unfolds with [`unfold_folded`], each of which starts another machine on
/// the Rust stack, and what that machine computes can be another `case` on
/// such a sum, read the same way: a chain of `n` of them took `n` nested
/// machines. Here each is done by this machine, with a frame waiting for it
/// that starts a segment ([`Stack`]): the number reads of [`read_number`]
/// ([`NumberOf::Reread`]), and the case tree runs and forcings of
/// [`Folded`] ([`Frame::Reread`]). As for `read_number`, the machine doing
/// one from that state takes the steps, and gives the value, that the
/// nested machine would: it starts from the same [`Control`], and the
/// frames below it are only counted, as that machine counted its own. What
/// `force` does without a machine (nothing, or taking a call's kept
/// unfolding) is done here without one too, taking no step. The walk's own
/// steps (one per sum it goes down to) are its own, as before.
fn reread_on(g: &Ev, stack: &mut Stack, then: AfterReread) -> Result<Control> {
    #[cfg(any(test, feature = "reference"))]
    if NESTED_REREAD.with(|n| n.get()) {
        let read = reread_sum(g, &then.value, &mut Unread::default())?;
        return then.finish(g, stack, read);
    }
    let mut unread = Unread::default();
    match crate::nat_add::Walk::start(g, &then.value, &mut unread) {
        None => then.finish(g, stack, None),
        Some((walk, need)) => {
            let reread = Box::new(Reread {
                walk,
                folded: None,
                then,
            });
            reread_go(g, stack, reread, RereadStep::Walk(need))
        }
    }
}

#[cfg(any(test, feature = "reference"))]
thread_local! {
    static NESTED_REREAD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Makes a `case` on this thread read a stuck sum by rule E with
/// [`reread_sum`], forcing and unfolding with machines of their own, if
/// `nested`; returns what it was. For tests comparing that with
/// [`reread_on`], which must take the same steps.
#[cfg(any(test, feature = "reference"))]
pub fn set_nested_reread(nested: bool) -> bool {
    NESTED_REREAD.with(|n| n.replace(nested))
}

/// Where [`reread_go`] picks up: what the walk needs, or what its
/// unfolding ([`Reread::folded`]) needs.
enum RereadStep {
    Walk(crate::nat_add::Need),
    Fold(FoldNeed),
}

/// [`reread_on`] going on from `step`, until the walk needs this machine
/// or is done.
fn reread_go(
    g: &Ev,
    stack: &mut Stack,
    mut reread: Box<Reread>,
    mut step: RereadStep,
) -> Result<Control> {
    use crate::nat_add::Need;
    loop {
        step = match step {
            RereadStep::Walk(Need::View(n)) => {
                let mut k = BigUint::default();
                match read_on(g, &mut k, n, false) {
                    Ok(base) => RereadStep::Walk(reread.walk.viewed(g, k, base)?),
                    Err(part) => {
                        let read = ReadNumber {
                            of: NumberOf::Reread(reread),
                            outer: BigUint::default(),
                            k,
                        };
                        push_segment(g, stack, Frame::ReadNumber(Box::new(read)))?;
                        return Ok(Control::Force(part));
                    }
                }
            }
            RereadStep::Walk(Need::Unfold(call)) => {
                let (folded, need) = Folded::start(g, call);
                reread.folded = Some(folded);
                RereadStep::Fold(need)
            }
            RereadStep::Walk(Need::Done(read)) => return reread.then.finish(g, stack, read),
            RereadStep::Fold(FoldNeed::Run(tree, env, stuck)) => {
                push_segment(g, stack, Frame::Reread(reread))?;
                return Ok(Control::Tree(tree, env, stuck));
            }
            RereadStep::Fold(FoldNeed::Force(value)) => match forced_free(g, &value) {
                Some(forced) => {
                    let folded = reread.folded.as_mut().expect("an unfolding is going on");
                    RereadStep::Fold(folded.answer(g, forced))
                }
                None => {
                    push_segment(g, stack, Frame::Reread(reread))?;
                    return Ok(Control::Force(value));
                }
            },
            RereadStep::Fold(FoldNeed::Done(next)) => {
                reread.folded = None;
                RereadStep::Walk(reread.walk.unfolded(g, next)?)
            }
        };
    }
}

impl AfterReread {
    /// The `case` going on with what rule E read its scrutinee as (`None`:
    /// nothing, and it is stuck), as [`branch_asked`] did after
    /// [`reread_sum`].
    fn finish(self, g: &Ev, stack: &mut Stack, read: Option<Value>) -> Result<Control> {
        let AfterReread {
            tree,
            env,
            stuck,
            succs,
            value,
        } = self;
        match (read, succs) {
            (Some(read), Some(k)) => {
                let value = native::from_view(k, Some(read));
                branch_asked(g, stack, tree, env, stuck, value, 0)
            }
            (Some(read), None) => branch_asked(g, stack, tree, env, stuck, read, 0),
            (None, succs) => {
                if succs.is_none()
                    && proof_counts::on()
                    && let Term::Case(_, d, _) = &*tree
                {
                    count_stuck_one_shape(g, *d, &stuck, &value);
                }
                stuck_tree(g, stack, stuck)
            }
        }
    }
}

/// What [`force`] gives for `value` without starting a machine, if it
/// can: `value` itself if it needs no forcing, or a call's kept unfolding
/// that needs no more (`force_now`'s shortcut). Neither takes a step.
fn forced_free(g: &Ev, value: &Value) -> Option<Value> {
    if !needs_forcing(g, value) {
        return Some(value.clone());
    }
    match value {
        Value::Call(_, _, unfolding) => unfolding
            .get(g)
            .filter(|unfolded| !needs_forcing(g, unfolded)),
        _ => None,
    }
}

impl Folded {
    /// [`unfold_folded`] of `value`, with what it needs first.
    fn start(g: &Ev, value: Value) -> (Folded, FoldNeed) {
        let mut folded = Folded {
            levels: vec![FoldLevel {
                value,
                current: None,
                at: FoldAt::Idle,
            }],
        };
        let need = folded.go(g, None);
        (folded, need)
    }

    /// Goes on with `value`, what the last [`FoldNeed::Run`] ran to or the
    /// last [`FoldNeed::Force`] forced to.
    fn answer(&mut self, g: &Ev, value: Value) -> FoldNeed {
        self.go(g, Some(value))
    }

    /// `unfold_folded`'s loop, for the innermost level, from `answer` to
    /// what it was waiting for (`None`: from the top of the loop), until
    /// it needs something.
    fn go(&mut self, g: &Ev, mut answer: Option<Value>) -> FoldNeed {
        loop {
            let level = self.levels.last_mut().expect("a level");
            let at = std::mem::replace(&mut level.at, FoldAt::Idle);
            let finished = match (at, answer.take()) {
                (FoldAt::Idle, _) => {
                    let v = level.current.as_ref().unwrap_or(&level.value);
                    if !is_folded(g, v) {
                        level.current.take()
                    } else {
                        let Value::Neutral(Head::Def(id), spine) = v else {
                            unreachable!()
                        };
                        let id = *id;
                        let def = g.def(id);
                        let body = def.body.as_ref().expect("checked by is_folded");
                        let (args, call, fields) = folded_parts(g, id, spine);
                        let tree = Term::peel_lams_rc(body, def.arity);
                        let stuck = Some((id, call.clone(), false));
                        level.at = FoldAt::Ran { id, call, fields };
                        return FoldNeed::Run(tree, args, stuck);
                    }
                }
                (FoldAt::Ran { id, call, fields }, Some(next)) => {
                    if let Value::Neutral(Head::Def(id2), s2) = &next
                        && *id2 == id
                        && s2.ptr_eq(&call)
                    {
                        level.current.take() // stuck
                    } else if fields.is_empty() && needs_forcing(g, &next) {
                        // Another folded call, perhaps (`unfold_folded`).
                        level.at = FoldAt::Forced(next.clone());
                        return FoldNeed::Force(next);
                    } else if fields.is_empty() {
                        level.current = Some(next);
                        continue;
                    } else {
                        level.at = FoldAt::FieldBase { fields, i: 0 };
                        return FoldNeed::Force(next);
                    }
                }
                (FoldAt::Forced(next), Some(forced)) => {
                    level.current = Some(if folded_call(g, &forced) {
                        forced
                    } else {
                        next
                    });
                    continue;
                }
                (FoldAt::FieldBase { fields, i }, Some(base)) => {
                    level.at = FoldAt::FieldInner {
                        fields,
                        i,
                        base: base.clone(),
                    };
                    self.levels.push(FoldLevel {
                        value: base,
                        current: None,
                        at: FoldAt::Idle,
                    });
                    continue;
                }
                (FoldAt::FieldUnfolded { fields, i }, Some(base)) => {
                    if let Some(need) = Self::field(level, fields, i, base) {
                        return need;
                    }
                    continue;
                }
                (FoldAt::FieldInner { .. }, _) | (_, None) => {
                    unreachable!("an answer for what the level waits for")
                }
            };
            // The innermost level is done: `unfold_folded` returns
            // `finished`, to the level below if there is one.
            self.levels.pop();
            let Some(level) = self.levels.last_mut() else {
                return FoldNeed::Done(finished);
            };
            let FoldAt::FieldInner { fields, i, base } =
                std::mem::replace(&mut level.at, FoldAt::Idle)
            else {
                unreachable!("a level below waits for the one above")
            };
            match finished {
                Some(unfolded) => {
                    level.at = FoldAt::FieldUnfolded { fields, i };
                    return FoldNeed::Force(unfolded);
                }
                None => {
                    if let Some(need) = Self::field(level, fields, i, base) {
                        return need;
                    }
                }
            }
        }
    }

    /// `level` takes field `fields[i]` of `base`, the forced value of the
    /// call or of what it unfolds to, then the next field, if any, of that.
    fn field(
        level: &mut FoldLevel,
        fields: Vec<(DataId, usize)>,
        i: usize,
        base: Value,
    ) -> Option<FoldNeed> {
        let (d, field) = fields[i];
        let next = project(d, field, base);
        if i + 1 == fields.len() {
            level.current = Some(next);
            return None;
        }
        level.at = FoldAt::FieldBase { fields, i: i + 1 };
        Some(FoldNeed::Force(next))
    }
}

/// Field `i` of `value`, a forced value of data type `d`, which has eta
/// ([`Term::Proj`]): the constructor's field, or the projection left stuck
/// on an unknown. A constructor of another type (the Lean projection bug,
/// docs/proposals/records.md §7.6) is never taken apart: the kernel's typing
/// refuses such a projection, so only an ill-typed term could reach it.
pub fn project(d: DataId, i: usize, value: Value) -> Value {
    match value {
        Value::Ctor(d2, 0, fields) if d2 == d && i < fields.len() => fields[i].clone(),
        Value::Neutral(head, mut spine) => {
            spine.push(Elim::Proj(d, i));
            Value::Neutral(head, spine)
        }
        // While running, an erased value's parts are erased too.
        v if erase::is_erased(&v) => v,
        other => panic!(
            "internal error: projecting field {i} of {}",
            describe(&other)
        ),
    }
}

/// Field `i` of glued call `call`, of eta type `d`, still a call: `(f x).i`.
/// Rule 2 binds a branch's fields to these when its scrutinee was a call
/// that computed to a neutral (record-eta.md §6.4): projections of what it
/// computed to would lose the call from goals, where `rewrite` and `match`
/// look for it. It means `project(d, i, force(call))`, which forcing it
/// computes ([`force_call`]), sharing the call's unfolding; so it's equal
/// to that by definition, and two of them with the same definition,
/// arguments and fields are equal (`same_spines`, which pairs the
/// projections), as fields of equal values are.
pub fn project_call(d: DataId, i: usize, call: Value) -> Value {
    let Value::Call(id, mut spine, unfolding) = call else {
        unreachable!("project_call takes a call")
    };
    spine.push(Elim::Proj(d, i));
    let unfolding = Rc::new(Unfolding {
        kept: Default::default(),
        base: Some(unfolding),
    });
    Value::Call(id, spine, unfolding)
}

/// Whether a field of a folded call ([`folded_call`]) whose unfolding is
/// stuck is kept as the stuck form `(f x).i` ([`eta_fields`], and
/// `Frame::FoldedField` for a projection): while the elaborator glues, not
/// in the kernel, which turns gluing on to check a body
/// ([`Machine::kernel`](crate::machine::Machine::kernel)).
fn names_folded_fields(g: &Ev) -> bool {
    g.machine.glue.get() && !g.machine.kernel.get()
}

/// Whether data type `d` has record eta. A type the environment doesn't hold
/// (only unit tests build such values) has none.
pub fn is_eta_type(g: &Ev, d: DataId) -> bool {
    g.env.datas().get(d.0).is_some_and(|data| data.eta)
}

/// Whether a `case` on type `d` takes its only branch on a neutral by
/// record eta (rule 2, [`branch`]): `d` has eta and no program is running.
fn eta_case(g: &Ev, d: DataId) -> bool {
    is_eta_type(g, d) && !g.machine.erasure.program_running()
}

/// Whether rule 2 is off in the case tree of definition `id`: it has a
/// native implementation (D2551). Such a definition models a machine
/// operation, and its record patterns are there to leave it stuck until its
/// arguments are known (`Float.add`'s `| { bits = a, … }, { bits = b, … }`,
/// so `x + y` stays as written on unknowns). Opening them on unknowns gives
/// its model's arithmetic on unknown bits: all stuck, far larger than the
/// call, and saying nothing more. Conversion then decides fewer equalities,
/// never more, so this is sound; the reference evaluator holds the same
/// definitions (`reference::eval_tree`). Today `Float.add`, `mul`, `div`,
/// `rem`, `floor`, `ceil`, `trunc` and `round` have both a native and a
/// record pattern.
pub fn eta_held(g: &Ev, id: DefId) -> bool {
    g.env.builtins().has_native(id)
}

/// Rule 2's `k` fields for a `case` on type `d` whose scrutinee was
/// `unforced` and is the neutral `forced`: fields of the call if it was a
/// glued call, else projections of the neutral.
///
/// A field of a call comes with its unfolding kept when `forced` already
/// says what forcing it would give (`Frame::CallField`): with `forced` not
/// an unknown and the call not stepping at once, the field call itself,
/// stuck. Forcing it would otherwise force the call again and unfold what
/// that computed to, which `forced` is: for a call whose unfolding is
/// itself a folded call taking apart the same kind of record (`Map.raw
/// (blinkCounts m)`, with `blinkCounts` a `Map.foldLeft` of `m.raw`), each
/// level did the one below twice, exponential in the depth (SW-1829).
///
/// A folded call ([`folded_call`]: a `decreasing` definition or a
/// dictionary; a call with a `Quot.lift` leaf is glued, and folded only in a
/// value made unglued) is never glued, but its fields are kept as
/// fields of the call too, the stuck form `(f x).i`, for the same reason:
/// the projections of its unfolding would put its internals (a `decreasing`
/// definition's fuelled helper) in goals, where a `match` on something its
/// body tests would rewrite inside the call (docs/proposals/match-call-field.md
/// §2.2, D2991). Only when `forced` is stuck and not an unknown: then every
/// field is stuck either way, so this names it without changing what it
/// computes to; conversion unfolds the stuck form ([`unfold_folded`]).
/// `forced` is the call unfolded to the end ([`Frame::Unfolding`]), so it
/// isn't a folded call that can still compute; at most one stuck in its own
/// case tree. A solved metavariable standing for the call is seen through,
/// as `Frame::ReplayElim` does for a projection of one. Only in the
/// elaborator, where goals are shown and searched: the kernel's
/// evaluation is left as it was, gluing or not ([`Machine::kernel`]).
///
/// [`Machine::kernel`]: crate::machine::Machine::kernel
fn eta_fields(g: &Ev, d: DataId, k: usize, unforced: &Value, forced: Value) -> Result<Vec<Value>> {
    let Value::Call(id, spine, _) = unforced else {
        let named = names_folded_fields(g)
            && matches!(&forced, Value::Neutral(head, _) if !matches!(head, Head::Meta(_)));
        // A folded call reached through solved metavariables is named too,
        // as it would be reached directly.
        let base = match unforced {
            Value::Neutral(Head::Meta(_), _) if named => force_solved(g, unforced.clone())?,
            _ => unforced.clone(),
        };
        let base = if named && folded_call(g, &base) {
            base
        } else {
            forced
        };
        return Ok((0..k).map(|i| project(d, i, base.clone())).collect());
    };
    let named = matches!(&forced, Value::Neutral(head, _) if !matches!(head, Head::Meta(_)))
        && !matches_at_once(g, *id, spine)?;
    Ok((0..k)
        .map(|i| {
            let field = project_call(d, i, unforced.clone());
            if named && let Value::Call(id, spine, unfolding) = &field {
                unfolding.set(g, Value::Neutral(Head::Def(*id), spine.clone()));
            }
            field
        })
        .collect())
}

/// What `value` is known not to be: something only for a variable on its
/// own ([`Apart`]).
pub fn apart_of(value: &Value) -> Apart {
    match value {
        Value::Neutral(Head::Var(_, apart, _), spine) if spine.is_empty() => *apart,
        _ => Apart::NONE,
    }
}

/// A case tree that can't take a step: its definition stays folded, unless
/// it's `Nat.add` and R3 or R4 applies (`nat_add.rs`, [`read_number`]).
fn stuck_tree(g: &Ev, stack: &mut Stack, stuck: Stuck) -> Result<Control> {
    match stuck {
        Some((id, spine, _)) => {
            if g.env.builtins().nat_add_rule == Some(id)
                && let [Elim::App(m, _), Elim::App(n, _)] = &spine[..]
            {
                let (m, n) = (m.clone(), n.clone());
                let read = ReadNumber {
                    of: NumberOf::Sum(StuckSum {
                        id,
                        m,
                        stuck: Value::Neutral(Head::Def(id), spine),
                    }),
                    outer: BigUint::default(),
                    k: BigUint::default(),
                };
                return read_number(g, stack, read, n, false);
            }
            Ok(Control::Return(Value::Neutral(Head::Def(id), spine)))
        }
        None => panic!("internal error: a case outside a definition's case tree got stuck"),
    }
}

/// Reading `next`, the rest of the number `read` describes, as
/// [`native::view_with`] reads it (for R3 and R4, in
/// [`crate::nat_add::stuck`]): each part is forced as [`force`] would, then
/// `Succ`s and numbers are counted until something else is found.
///
/// The one difference is where a part is forced: `force` starts another
/// machine on the Rust stack, and a part is often a glued call whose
/// unfolding is another stuck sum, read the same way, so a chain of `n`
/// such sums (2021 day 11's proofs: one a step of the puzzle) took `n`
/// nested machines. Here a part that needs the machine is forced by this
/// one, with a frame waiting for it ([`Frame::ReadNumber`]), so the chain
/// is frames on the heap. The machine forcing it from this state takes the
/// steps, and gives the value, that `force`'s own machine would: it starts
/// from the same [`Control::Force`], and the frames below it are never
/// looked at until it returns, except to count them for the depth limit
/// and its message ([`Stack`], which counts as that machine did). `forced`
/// says `next` is a value forcing gave, which isn't forced again (as
/// `view_with` doesn't).
#[inline(never)]
fn read_number(
    g: &Ev,
    stack: &mut Stack,
    mut read: ReadNumber,
    next: Value,
    forced: bool,
) -> Result<Control> {
    match read_on(g, &mut read.k, next, forced) {
        Ok(base) => read.done(g, stack, base),
        Err(part) => {
            push_segment(g, stack, Frame::ReadNumber(Box::new(read)))?;
            Ok(Control::Force(part))
        }
    }
}

/// [`read_number`]'s reading, adding the `Succ`s it finds to `k`: `Ok`
/// with the base once read (`None`: a number), or `Err` with a part that
/// needs this machine to force it, before reading goes on from there.
fn read_on(
    g: &Ev,
    k: &mut BigUint,
    mut next: Value,
    mut forced: bool,
) -> std::result::Result<Option<Value>, Value> {
    let nat = g.env.builtins().nat;
    loop {
        if !forced {
            match forced_free(g, &next) {
                Some(free) => next = free,
                None => return Err(next),
            }
        }
        forced = false;
        next = match next {
            Value::Nat(n) => {
                *k += &*n;
                return Ok(None);
            }
            Value::NatAdd(n, base) => {
                *k += &*n;
                (*base).clone()
            }
            Value::Ctor(d, 0, _) if Some(d) == nat => return Ok(None),
            Value::Ctor(d, 1, fields) if Some(d) == nat && fields.len() == 1 => {
                *k += 1u32;
                fields[0].clone()
            }
            other => return Ok(Some(other)),
        };
    }
}

/// A definition applied to `spine`: its native implementation, or its case
/// tree if it has all its arguments (kept as the call instead while gluing,
/// [`glues`]), or else it stays folded.
fn unfold(g: &Ev, stack: &mut Stack, id: DefId, spine: Spine) -> Result<Control> {
    unfold_now(g, stack, id, spine, true)
}

/// Whether definition `id`, about to run its case tree, is kept as a call
/// ([`Value::Call`]) instead: gluing is on ([`Machine::glue`](crate::machine::Machine::glue)), no program
/// is running, and it isn't a native (which computes at once on numbers).
/// Dictionaries, folded by name already, never get this far.
#[cold]
#[inline(never)]
fn glues(g: &Ev, id: DefId) -> bool {
    !g.machine.erasure.program_running() && g.env.builtins().native(id).is_none()
}

/// [`unfold`], gluing only if `glue`: a call being forced unfolds now.
#[inline(always)]
fn unfold_now(g: &Ev, stack: &mut Stack, id: DefId, spine: Spine, glue: bool) -> Result<Control> {
    if (g.def(id).opaque && hidden(g, id)) || frozen(g, id) {
        return Ok(Control::Return(Value::Neutral(Head::Def(id), spine)));
    }
    if erases_proof(g, id) || (spine.len() == g.def(id).arity && erases_result(g, id)) {
        return Ok(Control::Return(erased()));
    }
    if g.env
        .builtins()
        .float_def(id, g.machine.erasure.program_running())
        .is_some()
    {
        return run_float(g, stack, id, spine, glue, 0);
    }
    unfold_unless_float(g, stack, id, spine, glue)
}

/// [`unfold_now`] for a definition that isn't a float operation, or whose
/// float native gave nothing.
#[inline(always)]
fn unfold_unless_float(
    g: &Ev,
    stack: &mut Stack,
    id: DefId,
    spine: Spine,
    glue: bool,
) -> Result<Control> {
    if let Some(op) = g.env.builtins().native(id)
        && op.arity() == spine.len()
    {
        return from_native(g, stack, id, spine, 0);
    }
    case_tree(g, id, spine, glue)
}

/// Native definition `id` applied to all its arguments, `spine`, once its
/// number arguments before `from` have been looked at: the next argument
/// [`native::run`] would force that is a call not yet unfolded is forced
/// by this machine first ([`Control::NativeArg`]); with none left, the
/// native runs.
///
/// A native forces its arguments by calling [`force`], which starts another
/// machine, on the Rust stack. A number computed by glued calls nested
/// `n` deep (`Nat.iterate 2000 nextSecret seed` in 2024 day 22's proof)
/// would recurse `n` deep there, through each call's natives; forced here,
/// each nesting is frames on this machine's stack, and the native's own
/// `force` finds every argument's kept unfolding at once.
#[inline(always)]
fn from_native(g: &Ev, stack: &mut Stack, id: DefId, spine: Spine, from: usize) -> Result<Control> {
    let op = g.env.builtins().native(id).expect("a native");
    match unforced_number_arg(g, op, &spine, from) {
        Some(index) => Ok(Control::NativeArg(id, spine, index)),
        None => run_native(g, stack, id, spine, 0),
    }
}

/// Float operation `id` applied to `spine`: its float native, or else
/// what [`unfold_now`] does with any other definition. It has had this
/// machine force a glued call inside one of its arguments `asked` times.
/// The native reads its arguments as [`run_native`]'s do, with
/// [`force_or_ask`], and runs again from the start once the call is forced
/// ([`Frame::FloatAgain`]); it charges nothing, so a rerun repeats only
/// forcings that take no step.
#[inline(never)]
fn run_float(
    g: &Ev,
    stack: &mut Stack,
    id: DefId,
    spine: Spine,
    glue: bool,
    asked: usize,
) -> Result<Control> {
    start_read();
    let outcome = crate::float::run(g, id, &spine, forcing_for(asked));
    if let Some(part) = ASKED.take() {
        let asked = asked + 1;
        let waiting = Frame::FloatAgain {
            id,
            spine,
            glue,
            asked,
        };
        push_segment(g, stack, waiting)?;
        return Ok(Control::Force(part));
    }
    match outcome? {
        Some(value) => Ok(Control::Return(value)),
        None => unfold_unless_float(g, stack, id, spine, glue),
    }
}

/// Native definition `id` applied to all its arguments, `spine`: its
/// native implementation, or else its case tree. It has had this machine
/// force a glued call inside one of its numbers `asked` times.
///
/// The native forces with [`force_or_ask`]: where it comes to a glued call
/// not yet unfolded (inside a number, as `Succ (f x)` or `k + f x`, where
/// [`from_native`] doesn't look), this machine forces the call, with a
/// frame waiting for it that runs the native again from the start
/// ([`Frame::NativeAgain`], as the start of a segment, [`Stack`]). The
/// call then has its unfolding kept, so the native's `force` finds it at
/// once, taking no step, and goes on to where it stopped, forcing the same
/// parts in the same order as with [`force`]; nothing a native does before
/// its last forcing (it charges for big numbers after) is done twice. So a
/// chain of such calls (`Succ (f k x) + 1` with `f (k + 1) x` the same
/// again) is frames on the heap, where `force` would start a machine per
/// link on the Rust stack. Past [`ASKS`] times, or once the run has forced
/// something that took steps ([`FORCED`]), the native forces with `force`
/// ([`forcing_for`], [`force_or_ask`]).
fn run_native(g: &Ev, stack: &mut Stack, id: DefId, spine: Spine, asked: usize) -> Result<Control> {
    let op = g.env.builtins().native(id).expect("a native");
    start_read();
    let outcome = native::run(g, id, op, &spine, forcing_for(asked));
    if let Some(part) = ASKED.take() {
        let asked = asked + 1;
        push_segment(g, stack, Frame::NativeAgain { id, spine, asked })?;
        return Ok(Control::Force(part));
    }
    match outcome? {
        Some(native::Outcome::Done(value)) => return Ok(Control::Return(value)),
        Some(native::Outcome::Again(spine)) => return Ok(Control::Unfold(id, spine.into())),
        Some(native::Outcome::Succs(k, spine)) => {
            return Ok(Control::UnfoldAfterSuccs(Rc::new(k), id, spine.into()));
        }
        Some(native::Outcome::AddStuck { k, m, n }) => {
            let stuck = native::from_view(
                k.clone(),
                Some(crate::nat_add::call(id, m.clone(), n.clone())),
            );
            if g.env.builtins().nat_add_rule != Some(id) {
                return Ok(Control::Return(stuck));
            }
            let read = ReadNumber {
                of: NumberOf::Sum(StuckSum { id, m, stuck }),
                outer: k,
                k: BigUint::default(),
            };
            return read_number(g, stack, read, n, false);
        }
        None => {}
    }
    // A native is never glued ([`glues`]), so this is the same as `glue` on.
    case_tree(g, id, spine, false)
}

thread_local! {
    /// The call [`force_or_ask`] handed back, for the machine to force. Set
    /// only between `force_or_ask` returning and the read it was called
    /// from (`native::run` in [`run_native`], `float::run` in
    /// [`run_float`], `native::view_with` in [`branch_asked`]) returning to
    /// its caller, which takes it.
    static ASKED: std::cell::Cell<Option<Value>> = const { std::cell::Cell::new(None) };
    /// Whether the read in progress has forced something that took steps
    /// (a solved metavariable replayed, a call's kept unfolding forced
    /// again): [`force_or_ask`] then asks no more, as a rerun would take
    /// those steps again, and build fresh values whose glued calls keep no
    /// unfolding, so it would ask again too.
    static FORCED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Starts a read with [`force_or_ask`]: nothing asked or forced yet. (A
/// panic between an ask and its take leaves nothing for the next read.)
fn start_read() {
    ASKED.set(None);
    FORCED.set(false);
}

/// Whether [`force`] takes no step on `value`: it leaves it as it is, or
/// takes a call's kept unfolding (`force_now`'s shortcut).
fn forces_free(g: &Ev, value: &Value) -> bool {
    match value {
        Value::Call(_, _, unfolding) => unfolding
            .get(g)
            .is_some_and(|unfolded| !needs_forcing(g, &unfolded)),
        other => !needs_forcing(g, other),
    }
}

/// How many times a native's run ([`run_native`], [`run_float`]), or a number case's read
/// of its scrutinee ([`branch_asked`]), has this machine force a glued call
/// and starts again, before it forces with [`force`] instead. Each time
/// reads the numbers again up to where the last stopped, so a number with
/// `n` such calls in it one inside the other (`Succ (f k)` with `f k`
/// unfolding to `Succ (f (k - 1))`) would be read `n` times; `force`
/// reads it once, starting a machine for each call that is done before
/// the next starts, so Rust's stack only grows where a call's forcing
/// comes to such a call in turn. Which of the two forces a call changes
/// no value, step or limit, only Rust stack and time.
const ASKS: usize = 8;

/// The forcing for a native run, or a number case's read, that has had
/// this machine force a glued call `asked` times ([`ASKS`]).
fn forcing_for(asked: usize) -> native::Force {
    #[cfg(any(test, feature = "reference"))]
    if NEVER_ASK.with(|n| n.get()) {
        return force;
    }
    if asked < ASKS { force_or_ask } else { force }
}

#[cfg(any(test, feature = "reference"))]
thread_local! {
    static NEVER_ASK: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Makes natives and number cases on this thread force with [`force`]
/// alone, never asking the machine ([`force_or_ask`]), if `never`; returns
/// what it was. For tests comparing the two, which must take the same
/// steps.
#[cfg(any(test, feature = "reference"))]
pub fn set_never_ask(never: bool) -> bool {
    NEVER_ASK.with(|n| n.replace(never))
}

/// [`force`] for a native that [`run_native`] runs, or a number case's
/// read of its scrutinee ([`branch_asked`]): a glued call with no kept
/// unfolding, for which `force` would start another machine, is handed
/// back to the machine instead ([`ASKED`]), with an error that stops the
/// read there (`native.rs`'s reads pass every error on, and never look at
/// one). Anything else is forced as `force` does it. Once the read has
/// forced anything that took steps ([`FORCED`]), it asks no more, so the
/// runs before a rerun forced only what takes no step, and a rerun takes
/// exactly the steps `force` would have.
fn force_or_ask(g: &Ev, value: Value) -> Result<Value> {
    if !FORCED.get()
        && let Value::Call(_, _, unfolding) = &value
        && unfolding.get(g).is_none()
    {
        ASKED.set(Some(value));
        return Err(ResourceError::Cancelled);
    }
    let free = forces_free(g, &value);
    let forced = force(g, value);
    // After `force`: a read nested in it starts its own, clearing the flag.
    if !free {
        FORCED.set(true);
    }
    forced
}

/// The index of the first number argument of native `op`, from `from` on,
/// that [`native::run`] would force and that is a glued call without a kept
/// unfolding, if there is one. It looks at the arguments as `native::run`
/// does, in order, and stops where it stops (an argument whose head is no
/// number, or a spine that isn't all explicit arguments), so the machine
/// forces only what the native would have. A solved metavariable it leaves
/// to the native: it keeps no unfolding to find.
fn unforced_number_arg(g: &Ev, op: native::Native, spine: &Spine, from: usize) -> Option<usize> {
    if !spine
        .iter()
        .all(|e| matches!(e, Elim::App(_, Icit::Explicit)))
    {
        return None;
    }
    for (index, elim) in spine.iter().enumerate().take(op.arity()).skip(from) {
        let Elim::App(arg, _) = elim else {
            unreachable!("checked above")
        };
        let kept;
        let head = match arg {
            Value::Call(_, _, unfolding) => match unfolding.get(g) {
                Some(value) => {
                    kept = value;
                    &kept
                }
                None => return Some(index),
            },
            other => other,
        };
        if needs_forcing(g, head) || !native::number_head(g, head) {
            return None;
        }
    }
    None
}

/// [`unfold_now`] once natives and floats are ruled out: the case tree of
/// definition `id`, if it has all its arguments (kept as the call instead
/// while gluing, if `glue`), or else it stays folded.
#[inline(always)]
fn case_tree(g: &Ev, id: DefId, spine: Spine, glue: bool) -> Result<Control> {
    let def = g.def(id);
    if let Some(body) = &def.body
        && def.arity == spine.len()
        && !folds(g, id)
        && !native::folds_mul(g, id, &spine)
    {
        let args: Option<Vec<Value>> = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => Some(v.clone()),
                Elim::J { .. } | Elim::Proj(..) => None,
            })
            .collect();
        if let Some(args) = args {
            if glue && g.machine.glue.get() && glues(g, id) {
                return Ok(Control::Return(Value::Call(id, spine, Rc::default())));
            }
            let tree = Term::peel_lams_rc(body, def.arity);
            return Ok(Control::Tree(tree, args, Some((id, spine, true))));
        }
    }
    Ok(Control::Return(Value::Neutral(Head::Def(id), spine)))
}

/// Forcing argument `index` of native `id` applied to `spine`
/// ([`Control::NativeArg`]), with the native to run once it is forced.
#[cold]
#[inline(never)]
fn native_arg(g: &Ev, stack: &mut Stack, id: DefId, spine: Spine, index: usize) -> Result<Control> {
    let Some(Elim::App(arg, _)) = spine.get(index) else {
        unreachable!("an explicit argument, by unforced_number_arg")
    };
    let arg = arg.clone();
    push(
        g,
        stack,
        Frame::NativeArg {
            id,
            spine,
            next: index + 1,
        },
    )?;
    Ok(Control::Force(arg))
}

/// Whether definition `id` stays folded when it has all its arguments, except
/// while a program runs: a dictionary ([`crate::globals::Def::fold`]). A
/// `case`, `J`, projection or comparison that takes it apart unfolds it
/// first, so what's equal doesn't change, only when it's computed. (A
/// theorem needs no folding: outside a program it is sealed, [`hidden`].)
fn folds(g: &Ev, id: DefId) -> bool {
    g.def(id).fold && !g.machine.erasure.program_running()
}

/// Whether definition `id` is opaque and its body can't be used now
/// (docs/proposals/opaque-definitions.md §6.4): no program is running, and
/// it isn't in the current transparency set ([`Machine::transparent`](crate::machine::Machine::transparent)). Then
/// a call of it is neutral, like a variable applied to arguments: it never
/// unfolds (not even by a native implementation), and no shortcut of
/// conversion or matching looks at its body ([`body_seen`]).
pub fn hidden(g: &Ev, id: DefId) -> bool {
    g.def(id).opaque && !g.machine.erasure.program_running() && !g.machine.transparent.contains(id)
}

/// Whether definition `id`'s type is a proposition, so that a call of it is
/// a proof and is never computed while checking (rule F, docs/core.md
/// "Proof irrelevance"): rules I, K and S never read a proof, so nothing
/// needs its unfolding, and freezing it keeps every computation the
/// checker makes inside data (the Abel-Coquand loop is all proofs). A
/// running program still unfolds it, though erasure has removed it first.
#[inline(always)]
pub fn frozen(g: &Ev, id: DefId) -> bool {
    g.def(id).proof && !g.machine.erasure.program_running()
}

/// Whether a call of definition `id` can't unfold here but may elsewhere
/// or later: it's [`hidden`] or [`frozen`], or it has no body (a member of
/// the group being checked, an axiom, or an open goal's assumption, whose
/// `?` may later be filled). Its arguments are compared as any call's are,
/// which agrees with unfolding (see `same_spines`), so the call's
/// unfolding, wherever it happens, can only add equalities.
pub fn sealed(g: &Ev, id: DefId) -> bool {
    body_seen(g, id).is_none()
}

/// Definition `id`'s body, if it has one and it isn't [`hidden`] or
/// [`frozen`]: what every path that unfolds a definition, or looks at its
/// case tree, reads.
#[inline(always)]
pub fn body_seen<'a>(g: &Ev<'a>, id: DefId) -> Option<&'a Rc<Term>> {
    let def = g.def(id);
    def.body
        .as_ref()
        .filter(|_| (!def.opaque || !hidden(g, id)) && !frozen(g, id))
}

/// Folded call `value` ([`is_folded`]) is taken apart by the frame `next`:
/// its case tree runs in this machine, and `next` gets the result
/// ([`Frame::Unfolding`]).
fn unfold_for(g: &Ev, stack: &mut Stack, value: Value, next: Frame) -> Result<Control> {
    let Value::Neutral(Head::Def(id), spine) = value else {
        unreachable!("checked by is_folded")
    };
    let def = g.def(id);
    let body = def.body.as_ref().expect("checked by is_folded");
    let (args, call, _) = folded_parts(g, id, &spine);
    let tree = Term::peel_lams_rc(body, def.arity);
    push(
        g,
        stack,
        Frame::Unfolding(Box::new((id, call.clone(), next))),
    )?;
    Ok(Control::Tree(tree, args, Some((id, call, false))))
}

/// Whether `value` is a stuck field of a call ([`is_folded`]) that an
/// application or `J` computes first ([`unfold_field_for`]): only while
/// gluing, where `Frame::CallField` and rule 2 name fields of calls stuck
/// anywhere inside. Without gluing, such a value is a field of a call stuck
/// in its own case tree, which computes to itself.
///
/// The kernel reaches this too: it checks every body and signature glued
/// (`check.rs`, `admit_group` and `declare_def`). That's sound: it unfolds
/// only a body [`body_seen`] allows (a hidden opaque definition, or a member
/// of the group being checked, which has no body yet, stays neutral); it
/// runs the case tree in the same machine and budget; and it takes the
/// field and applies it by the ordinary rules, so `(f x).i a` is the field
/// of `f x`'s unfolding applied, by delta. That is what unglued evaluation
/// gives already, since there `f x` unfolds when it's built, or, for a
/// folded call, when a field of it is taken (through a `Quot.lift` leaf
/// too, [`unfold_field_for`]). So it adds nothing to trust, and glued and
/// unglued evaluation agree on what's equal (D3030).
fn computes_field(g: &Ev, value: &Value) -> bool {
    g.machine.glue.get() && ends_in_field(value) && is_folded(g, value)
}

/// Stuck field of a call `value` ([`is_folded`]), `(f x).i`, eliminated by
/// `then`: the call's case tree runs in this machine (as in
/// [`unfold_folded`], which conversion uses), and `then` takes apart that
/// field of what it computes to ([`Frame::FieldOf`]).
fn unfold_field_for(g: &Ev, stack: &mut Stack, value: Value, then: FieldUse) -> Result<Control> {
    let Value::Neutral(Head::Def(id), spine) = value else {
        unreachable!("checked by is_folded")
    };
    let def = g.def(id);
    let body = def.body.as_ref().expect("checked by is_folded");
    let (args, call, _) = folded_parts(g, id, &spine);
    let tree = Term::peel_lams_rc(body, def.arity);
    let next = Frame::FieldOf(Box::new(FieldOf {
        id,
        spine,
        call: call.clone(),
        then,
    }));
    push(
        g,
        stack,
        Frame::Unfolding(Box::new((id, call.clone(), next))),
    )?;
    // A `Quot.lift` leaf is computed through, not left folded: unglued
    // evaluation and the reference take a field of such a call through its
    // lift too (`Frame::ProjForced`, `unfold_for`), and `(f x).i a` left
    // folded would be a rigid term no conversion opens, unequal to theirs.
    Ok(Control::Tree(tree, args, Some((id, call, false))))
}

/// Whether `value` is a dictionary left folded by name ([`folds`]) that
/// [`unfold_folded`] would unfold; or a definition with a `Quot.lift` leaf
/// ([`folds_on_lift`]), which may be folded because of it: taking it apart,
/// or comparing it with something that isn't the same call with the same
/// arguments, looks at its body (docs/proposals/map-equality.md §7.2: the
/// policy changes what's shown and when things are computed, never what's
/// equal). Or a stuck field of a call, `(f x).i` (`Frame::CallField`): any
/// definition applied to all its parameters, then projected, which is
/// compared as what it unfolds to; the machine takes it apart as it is,
/// stuck (as it does any stuck call, [`folded_call`]).
pub fn is_folded(g: &Ev, value: &Value) -> bool {
    match value {
        Value::Neutral(Head::Def(id), spine) if is_call_field(spine) => {
            let arity = g.def(*id).arity;
            spine.len() > arity
                && spine[..arity].iter().all(|e| matches!(e, Elim::App(..)))
                && spine[arity..].iter().all(|e| matches!(e, Elim::Proj(..)))
                && body_seen(g, *id).is_some()
        }
        _ => folded_call(g, value),
    }
}

/// Whether `value` is a folded call that the machine unfolds to take it
/// apart: [`is_folded`] without the fields of calls (`(f x).i`), which the
/// machine takes apart as they are.
fn folded_call(g: &Ev, value: &Value) -> bool {
    matches!(value, Value::Neutral(Head::Def(id), spine)
        if (folds(g, *id) || folds_on_lift(g, *id) || native::folds_mul(g, *id, spine))
            && spine.len() == g.def(*id).arity
            && body_seen(g, *id).is_some())
}

/// Folded call `id spine` ([`is_folded`]) as the call, of which it may be
/// fields: its arguments, the spine of the call, and the projections taken
/// of that, first first.
fn folded_parts(g: &Ev, id: DefId, spine: &Spine) -> (Vec<Value>, Spine, Vec<(DataId, usize)>) {
    let arity = g.def(id).arity;
    let call: Spine = if spine.len() == arity {
        spine.clone()
    } else {
        spine[..arity].iter().cloned().collect()
    };
    let args = call
        .iter()
        .map(|e| match e {
            Elim::App(v, _) => v.clone(),
            Elim::J { .. } | Elim::Proj(..) => unreachable!("checked by is_folded"),
        })
        .collect();
    let fields = spine[arity..]
        .iter()
        .map(|e| match e {
            Elim::Proj(d, i) => (*d, *i),
            Elim::App(..) | Elim::J { .. } => unreachable!("checked by is_folded"),
        })
        .collect();
    (args, call, fields)
}

/// Whether definition `id`, applied to all its parameters, stays folded when
/// its case tree reaches a `Quot.lift` whose quotient isn't a `Quot.mk`, as
/// when it reaches a `case` that can't step: so a goal shows `Map.get k m`,
/// not the lift it unfolds to. Except while a program runs.
fn folds_on_lift(g: &Ev, id: DefId) -> bool {
    g.def(id).lift_leaf && !g.machine.erasure.program_running()
}

/// Whether case tree `tree` (a definition's body under its parameters) has a
/// `Quot.lift` leaf: what [`folds_on_lift`] looks for, and what the machine's
/// tree walk treats as a case.
pub(crate) fn has_lift_leaf(tree: &Term) -> bool {
    let mut pending = vec![tree];
    while let Some(t) = pending.pop() {
        match t.strip_loc() {
            Term::Case(_, _, branches) => {
                pending.extend(branches.iter().filter_map(|b| b.body.as_deref()));
            }
            Term::NumCase(_, arms, default) => {
                pending.extend(arms.iter().map(|a| &*a.body));
                pending.push(default);
            }
            Term::Quot(QuotForm::Lift, args, _, _) if args.len() == QuotForm::Lift.arity() => {
                return true;
            }
            _ => {}
        }
    }
    false
}

/// A dictionary left folded by name, unfolded until it isn't one (its body
/// may be a call of another, `Ord.fromCompare …`): what taking it apart, or
/// comparing it with something that isn't the same call, sees. `None` if
/// `value` isn't one, or its case tree is stuck.
///
/// Its steps are [`Folded`]'s, with each case tree run by another machine
/// ([`run`]) and each value forced with [`force`]. The body of a call is
/// run from its case tree, as [`Control::Tree`], leaving the call stuck as
/// it was if the tree is stuck; what that gives is forced, if it is a glued
/// call or a solved metavariable, and kept if that is another folded call
/// (a `decreasing` definition's fuelled helper computing to its leaf `g y`,
/// which unglued evaluation, where the helper isn't glued, gets here as it
/// is and unfolds too, SW-2126); otherwise the call is kept, unfolding
/// shared, for conversion to compare lazily. For a field of a call
/// (`(f x).i`), the field is taken of the call's value, forced, and
/// unfolded and forced again if that is another folded call.
pub fn unfold_folded(g: &Ev, value: &Value) -> Result<Option<Value>> {
    let (mut folded, mut need) = Folded::start(g, value.clone());
    loop {
        need = match need {
            FoldNeed::Run(tree, env, stuck) => {
                let next = run(g, Control::Tree(tree, env, stuck))?;
                folded.answer(g, next)
            }
            FoldNeed::Force(value) => {
                let forced = force(g, value)?;
                folded.answer(g, forced)
            }
            FoldNeed::Done(unfolded) => return Ok(unfolded),
        }
    }
}

/// A folded call applied to all its arguments, then eliminated further by a
/// `J` or an application (`bumpBy q 3`, with `bumpBy q` a `Quot.lift`
/// returning a function): the call unfolded ([`unfold_folded`]) and the rest
/// of the spine applied to what it computes to. `None` if `value` isn't one,
/// or the call is stuck in its own case tree. Conversion and the unifier
/// compare such a value with anything that isn't the same call this way, in
/// every mode, the kernel's included: a definition's arity is its body's
/// leading lambdas (docs/core.md), so a definition with a `Quot.lift` leaf
/// returning a function, applied to all its arguments and more, is such a
/// value there too, compared by delta and then the eliminations after it,
/// as docs/core.md's equality rule asks
/// (`examples/accept/lift-call-over-applied.sw`).
pub fn unfold_folded_head(g: &Ev, value: &Value) -> Result<Option<Value>> {
    if !unfolds_head(g, value) {
        return Ok(None);
    }
    let Value::Neutral(Head::Def(id), spine) = value else {
        unreachable!("checked by unfolds_head")
    };
    let arity = g.def(*id).arity;
    let call = Value::Neutral(Head::Def(*id), spine[..arity].iter().cloned().collect());
    if !folded_call(g, &call) {
        return Ok(None);
    }
    let Some(unfolded) = unfold_folded(g, &call)? else {
        return Ok(None);
    };
    let rest: Spine = spine[arity..].iter().cloned().collect();
    run_on(
        g,
        Control::Return(unfolded),
        Stack {
            frames: vec![Frame::Replay {
                spine: rest,
                next: 0,
            }],
            segments: Vec::new(),
        },
    )
    .map(Some)
}

/// Whether [`unfold_folded_head`] may unfold `value`: a folded call applied to
/// all its arguments, then a `J` or an application.
pub fn unfolds_head(g: &Ev, value: &Value) -> bool {
    matches!(value, Value::Neutral(Head::Def(id), spine)
        if spine.len() > g.def(*id).arity
            && spine[g.def(*id).arity..].iter().any(|e| matches!(e, Elim::J { .. } | Elim::App(..)))
            && spine[..g.def(*id).arity].iter().all(|e| matches!(e, Elim::App(..)))
            && (folds(g, *id) || folds_on_lift(g, *id))
            && body_seen(g, *id).is_some())
}

/// Whether, while erasing, definition `id` (with a body, an open goal's
/// assumption or a stated theorem) applied to all its parameters is erased
/// rather than run (`erase.rs`).
fn erases_result(g: &Ev, id: DefId) -> bool {
    g.machine.erasure.active()
        && (g.def(id).defined() || g.def(id).assumption.is_some())
        && erase::of_def(g, id).is_some_and(|e| e.result)
}

/// Whether, while erasing, a call of definition `id` is erased whatever it
/// is applied to: its type is a proposition ([`crate::globals::Def::proof`]), so the call
/// is a proof at any number of arguments, partial or not, and with or
/// without a body here (a stated theorem has none). Its arity, which for a
/// theorem is the shape of its proof, isn't read.
#[inline(always)]
fn erases_proof(g: &Ev, id: DefId) -> bool {
    g.def(id).proof && g.machine.erasure.active()
}

/// Whether, while erasing, the argument applied to `f` is erased: `f` is a
/// definition applied to some arguments, and the parameter it's for is.
fn erased_arg(g: &Ev, f: &Term) -> bool {
    let mut n = 0;
    let mut f = f;
    loop {
        match f {
            Term::App(h, _, _) => {
                n += 1;
                f = h;
            }
            Term::Loc(_, t) | Term::Ann(t, _) => f = t,
            Term::Def(id) => {
                return erase::of_def(g, *id).is_some_and(|e| e.params.get(n) == Some(&true));
            }
            _ => return false,
        }
    }
}

/// Converts a value back into a term, with `level` variables in scope.
/// Solved metavariables are replaced by their solutions, and a glued call
/// ([`Value::Call`]) by its unfolding: the normal form.
pub fn quote(g: &Ev, level: usize, value: &Value) -> Result<Term> {
    Ok(quote_as(g, level, value, Readback::Unfolded, None, None)?.expect("no cap"))
}

/// [`quote`], or `None` if the term would have more than `cap` nodes: for
/// callers that only inspect the normal form and can do without it when it's
/// large.
pub fn quote_at_most(g: &Ev, level: usize, value: &Value, cap: u64) -> Result<Option<Term>> {
    quote_as(g, level, value, Readback::Unfolded, Some(cap), None)
}

/// [`quote`], but a glued call ([`Value::Call`]) is written as the call,
/// its arguments read back the same way, rather than as its unfolding
/// (docs/proposals/folded-calls.md, stage 3): `List.length xs`, not what it
/// computes to. The two terms are convertible. Without gluing (the kernel)
/// there are no calls, and this is [`quote`].
pub fn quote_folded(g: &Ev, level: usize, value: &Value) -> Result<Term> {
    if g.machine.glue.get() && force_unglued_first() {
        force_unglued(g, level, value);
    }
    Ok(quote_as(g, level, value, Readback::Folded, None, None)?.expect("no cap"))
}

/// [`quote_folded`], or `None` if the term would have more than `cap` nodes.
pub fn quote_folded_at_most(g: &Ev, level: usize, value: &Value, cap: u64) -> Result<Option<Term>> {
    if g.machine.glue.get() && force_unglued_first() {
        force_unglued(g, level, value);
    }
    quote_as(g, level, value, Readback::Folded, Some(cap), None)
}

/// [`quote_folded`], but every glued call is written as the call, one that
/// steps at once too: nothing is computed but what applying a solution to
/// its arguments takes. For substituting solutions into a term
/// (`countDown 100000 []` stays that, where [`quote_folded`] computes the
/// list) and stating a goal as written.
pub fn quote_as_written(g: &Ev, level: usize, value: &Value) -> Result<Term> {
    Ok(quote_as(g, level, value, Readback::AsWritten, None, None)?.expect("no cap"))
}

/// [`quote_as_written`] for display: a sum stuck on an unknown is written
/// `x + k` ([`native::nat_add_shown`], SW-895). For printing only.
pub fn quote_as_written_shown(g: &Ev, level: usize, value: &Value) -> Result<Term> {
    Ok(quote_as(g, level, value, Readback::AsWrittenShown, None, None)?.expect("no cap"))
}

/// A hook [`quote_unfolded_keeping`] asks at each glued call, with the
/// number of variables in scope there: the call's read-back to use in
/// place of its unfolding, or `None` to unfold it as [`quote`] does.
pub type Keep<'a> = &'a mut dyn FnMut(usize, &Value) -> Result<Option<Term>>;

/// [`quote`], but at each glued call ([`Value::Call`]) met, `keep` may give
/// the term to put there instead of the call's unfolding (SW-4637: a
/// `match`'s occurrence test keeps calls folded where its scrutinee can't be
/// hidden). Equal to [`quote`] where `keep` always says `None`.
pub fn quote_unfolded_keeping(g: &Ev, level: usize, value: &Value, keep: Keep<'_>) -> Result<Term> {
    match quote_as_until(
        g,
        level,
        value,
        Readback::Unfolded,
        None,
        None,
        None,
        Some(keep),
    )? {
        Quoted::Term(term) => Ok(term.expect("no cap")),
        Quoted::Met(_) => unreachable!("nothing stops a read-back without `stop`"),
    }
}

/// Instrumentation (SW-1782): with `STITCHWORT_DEBUG_FORCE_UNGLUED` set,
/// every folded read-back is preceded by an unfolded one with gluing off,
/// which fills the cells of every call it reaches. Its result, steps and
/// errors are thrown away.
fn force_unglued_first() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| crate::env_flag::env_flag("STITCHWORT_DEBUG_FORCE_UNGLUED"))
}

#[cold]
fn force_unglued(g: &Ev, level: usize, value: &Value) {
    let saved = g.machine.budget.start_attempt(crate::budget::Limits {
        work: 2_000_000,
        stack: usize::MAX,
        size: 1_000_000,
        frames: 100_000,
        native_frames: 100_000,
    });
    let glue = g.machine.glue.replace(false);
    let _ = quote(g, level, value);
    g.machine.glue.set(glue);
    g.machine.budget.restore(saved);
}

/// [`quote_folded`] for display: a call that steps at once is written as
/// its one step rather than forced through, so the calls that step returns
/// stay calls (`if True then concatenate a b else 0` is `concatenate a b`).
/// For printing only; elaborated terms are read back with [`quote_folded`].
/// A sum stuck on an unknown is written `x + k`
/// ([`native::nat_add_shown`], SW-895).
pub fn quote_shown(g: &Ev, level: usize, value: &Value) -> Result<Term> {
    Ok(quote_as(g, level, value, Readback::Shown, None, None)?.expect("no cap"))
}

/// [`quote_shown`], or `None` if reading it back visits more than `cap`
/// nodes: for a note in a message (SW-2600).
pub fn quote_shown_at_most(g: &Ev, level: usize, value: &Value, cap: u64) -> Result<Option<Term>> {
    quote_as(g, level, value, Readback::Shown, Some(cap), None)
}

/// [`quote`] for display: the normal form, but a sum stuck on an unknown is
/// written `x + k` ([`native::nat_add_shown`], SW-895). For printing only.
pub fn quote_unfolded_shown(g: &Ev, level: usize, value: &Value) -> Result<Term> {
    Ok(quote_as(g, level, value, Readback::UnfoldedShown, None, None)?.expect("no cap"))
}

/// [`quote_unfolded_shown`], or `None` if reading it back visits more than
/// `cap` nodes: for a message that cuts the text short anyway, so it needn't
/// unfold a value up to the budget's size limit (SW-2569).
pub fn quote_unfolded_shown_at_most(
    g: &Ev,
    level: usize,
    value: &Value,
    cap: u64,
) -> Result<Option<Term>> {
    quote_as(g, level, value, Readback::UnfoldedShown, Some(cap), None)
}

/// [`quote_unfolded_shown_at_most`], but a part more than `max_depth` levels
/// below the root is not read back: it is [`ELIDED`], which prints as `…`.
/// A message shows only the top of a value, so this never unfolds the rest
/// (SW-2598). Still `None` past `cap` nodes, for a value that is wide
/// rather than deep.
pub fn quote_unfolded_shown_to_depth(
    g: &Ev,
    level: usize,
    value: &Value,
    cap: u64,
    max_depth: usize,
) -> Result<Option<Term>> {
    quote_as(
        g,
        level,
        value,
        Readback::UnfoldedShown,
        Some(cap),
        Some(max_depth),
    )
}

/// The metavariable number of the placeholder for a part a depth-limited
/// readback left out ([`quote_unfolded_shown_to_depth`]): never a real one.
pub const ELIDED: usize = usize::MAX;

/// Whether reading `value` back takes no work: a leaf, shown whatever the depth.
fn is_atomic_value(value: &Value) -> bool {
    match value {
        Value::Sort(_) | Value::Nat(_) | Value::Refl | Value::Chars(_) => true,
        Value::Neutral(_, spine) => spine.is_empty(),
        _ => false,
    }
}

/// How [`quote_as`] reads back glued calls.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Readback {
    /// As their unfoldings ([`quote`]).
    Unfolded,
    /// As calls, except one that steps at once, forced ([`quote_folded`]).
    Folded,
    /// As calls, one that steps at once by that step ([`quote_shown`]).
    Shown,
    /// As calls, every one ([`quote_as_written`]).
    AsWritten,
    /// As [`Readback::Unfolded`], for display ([`quote_unfolded_shown`]).
    UnfoldedShown,
    /// As [`Readback::AsWritten`], for display ([`quote_as_written_shown`]).
    AsWrittenShown,
}

impl Readback {
    /// Whether glued calls are read back as their unfoldings.
    fn unfolds(self) -> bool {
        matches!(self, Readback::Unfolded | Readback::UnfoldedShown)
    }

    /// Whether the term is only printed, so a stuck sum `k + x` is written
    /// `x + k` ([`native::nat_add_shown`]).
    fn for_display(self) -> bool {
        matches!(
            self,
            Readback::Shown | Readback::UnfoldedShown | Readback::AsWrittenShown
        )
    }

    /// Whether every glued call is read back as the call, even one that
    /// steps at once.
    fn keeps_every_call(self) -> bool {
        matches!(self, Readback::AsWritten | Readback::AsWrittenShown)
    }
}

/// The readback; `None` if it grows past `cap` nodes (when given and below
/// the budget's size limit, which is otherwise an error).
fn quote_as(
    g: &Ev,
    level: usize,
    value: &Value,
    mode: Readback,
    cap: Option<u64>,
    max_depth: Option<usize>,
) -> Result<Option<Term>> {
    match quote_as_until(g, level, value, mode, cap, max_depth, None, None)? {
        Quoted::Term(term) => Ok(term),
        Quoted::Met(_) => unreachable!("nothing stops a read-back without `stop`"),
    }
}

/// What [`quote_as_until`] finds.
enum Quoted {
    /// The read-back, or `None` past its cap.
    Term(Option<Term>),
    /// An unknown `stop` accepted, met before the read-back was finished.
    Met(usize),
}

/// The normal form of `value`, as [`quote_at_most`] reads it back, holds an
/// unknown `stop` accepts: `Some(Some(m))` with one, `Some(None)` with none,
/// `None` if it has more than `cap` nodes. The read-back stops at the first
/// unknown it meets, rather than finishing the term to scan it, which can
/// cost as much as computing every call the value mentions: whether a
/// continuation's goal still holds an unknown, asked of a relation about a
/// parser, was a quarter of a walk's steps (SW-4512). `m` is the first met
/// in the read-back's order, which needn't be the first in the finished
/// term's.
pub fn normal_form_meets(
    g: &Ev,
    level: usize,
    value: &Value,
    cap: u64,
    stop: &dyn Fn(usize) -> bool,
) -> Result<Option<Option<usize>>> {
    let scan = |term: &Term| {
        term.subterms().find_map(|(t, _)| match t {
            Term::Meta(m) if stop(*m) => Some(*m),
            _ => None,
        })
    };
    Ok(
        match quote_as_until(
            g,
            level,
            value,
            Readback::Unfolded,
            Some(cap),
            None,
            Some(stop),
            None,
        )? {
            Quoted::Met(m) => Some(Some(m)),
            Quoted::Term(Some(term)) => Some(scan(&term)),
            Quoted::Term(None) => None,
        },
    )
}

/// [`quote_as`], stopping at an unknown `stop` accepts where it meets one
/// as a value to read back: an unknown no solution replaced, or the erased
/// placeholder. One it doesn't meet that way (a value that only forces to
/// one) is in the finished term.
#[allow(clippy::too_many_arguments)]
fn quote_as_until(
    g: &Ev,
    level: usize,
    value: &Value,
    mode: Readback,
    cap: Option<u64>,
    max_depth: Option<usize>,
    stop: Option<&dyn Fn(usize) -> bool>,
    mut keep: Option<Keep<'_>>,
) -> Result<Quoted> {
    let _phase = g.machine.budget.phase(crate::budget::Phase::Readback);
    // A work list rather than recursion: `tasks` are values still to visit
    // and terms still to assemble, and `done` holds finished terms, which
    // each assembly takes its parts from.
    let mut tasks = vec![QuoteTask::Visit(level, value.clone(), 0)];
    let mut done: Vec<Term> = Vec::new();
    let mut size = 0u64;
    // If it gets too large: which definition's call the whole value was.
    let root_def = match value {
        Value::Neutral(Head::Def(id), _) | Value::Call(id, ..) => Some(id.0),
        _ => None,
    };
    let limit = g.machine.budget.size_limit();
    let cap = cap.filter(|&cap| cap <= limit);
    let rc = |t: Term| Rc::new(t);
    while let Some(task) = tasks.pop() {
        match task {
            QuoteTask::Visit(level, value, depth) => {
                g.machine.budget.step()?;
                if max_depth.is_some_and(|m| depth > m) && !is_atomic_value(&value) {
                    done.push(Term::Meta(ELIDED));
                    continue;
                }
                size += 1;
                if cap.is_some_and(|cap| size > cap) {
                    g.machine.budget.note_readback(size);
                    return Ok(Quoted::Term(None));
                }
                if size > limit {
                    g.machine.budget.note_readback(size);
                    g.machine.budget.set_too_large(root_def);
                    g.machine.budget.note_ran_out();
                    return Err(ResourceError::Size(limit));
                }
                if let Some(stop) = stop {
                    let met = match &value {
                        Value::Neutral(Head::Meta(m), _) if g.meta_solution(*m).is_none() => {
                            Some(*m)
                        }
                        Value::Neutral(Head::Var(l, _, _), _) if *l == erase::ERASED => {
                            Some(ELIDED)
                        }
                        _ => None,
                    };
                    if let Some(m) = met.filter(|&m| stop(m)) {
                        g.machine.budget.note_readback(size);
                        return Ok(Quoted::Met(m));
                    }
                }
                if let (Some(keep), Value::Call(..)) = (keep.as_mut(), &value)
                    && let Some(term) = keep(level, &value)?
                {
                    done.push(term);
                    continue;
                }
                visit(g, level, value, depth, mode, &mut tasks, &mut done)?;
            }
            QuoteTask::Pi(x, i, pm) => {
                let (a, b) = pop2(&mut done);
                done.push(Term::Pi(x, i, rc(a), rc(b), pm));
            }
            QuoteTask::Lam(x, i, pm) => {
                let b = done.pop().expect("a body");
                done.push(Term::Lam(x, i, rc(b), pm));
            }
            QuoteTask::Data(d, n) => {
                let args = done.split_off(done.len() - n);
                done.push(Term::data(d, args));
            }
            QuoteTask::Ctor(d, c, n) => {
                let args = done.split_off(done.len() - n);
                done.push(Term::ctor(d, c, args));
            }
            QuoteTask::NatAdd(k) => {
                let base = done.pop().expect("a base");
                done.push(if mode.for_display() {
                    native::nat_add_shown(g, &k, base)
                } else {
                    native::nat_add_term(g, &k, base)
                });
            }
            QuoteTask::Eq => {
                let b = done.pop().expect("three parts");
                let (ty, a) = pop2(&mut done);
                done.push(Term::Eq(Some(rc(ty)), rc(a), rc(b)));
            }
            QuoteTask::Spine(head, shape) => {
                let n = shape.iter().map(|s| s.parts()).sum::<usize>()
                    + usize::from(matches!(head, SpineHead::Part));
                let mut parts = done.split_off(done.len() - n).into_iter();
                let (mut term, shape) = match head {
                    SpineHead::Term(term) => (term, &shape[..]),
                    SpineHead::Part => (parts.next().expect("a head"), &shape[..]),
                    // The form's own arguments, then what applies its result.
                    SpineHead::Quot(form, k, pm) => {
                        let args = parts.by_ref().take(k).map(Rc::new).collect();
                        (Term::Quot(form, args, false, pm), &shape[k..])
                    }
                };
                for &elim in shape {
                    term = match elim {
                        SpineShape::App(icit) => {
                            Term::app_icit(term, parts.next().expect("an argument"), icit)
                        }
                        SpineShape::J(pm, ends) => {
                            let motive = parts.next().expect("a motive");
                            let base = parts.next().expect("a base");
                            // A cast's ends go back on its proof, as the
                            // kernel puts them there.
                            let proof = if ends {
                                let ty = parts.next().expect("a type");
                                let x = parts.next().expect("an end");
                                let y = parts.next().expect("an end");
                                Term::Ann(rc(term), rc(Term::Eq(Some(rc(ty)), rc(x), rc(y))))
                            } else {
                                term
                            };
                            Term::J(rc(motive), rc(base), rc(proof), pm)
                        }
                        SpineShape::Proj(d, i) => Term::Proj(d, i, rc(term)),
                    };
                }
                done.push(term);
            }
        }
    }
    g.machine.budget.note_readback(size);
    Ok(Quoted::Term(Some(done.pop().expect("one term"))))
}

/// Quotation still to do.
enum QuoteTask {
    /// Quote a value, with this many variables in scope, `depth` levels below
    /// the root.
    Visit(usize, Value, usize),
    /// Assemble from the finished terms on top of the stack:
    Pi(Name, Icit, ProofMark),
    Lam(Name, Icit, ProofMark),
    Data(DataId, usize),
    Ctor(DataId, usize, usize),
    NatAdd(Rc<BigUint>),
    Eq,
    /// A head and its eliminations.
    Spine(SpineHead, Vec<SpineShape>),
}

/// One elimination of a [`QuoteTask::Spine`].
#[derive(Clone, Copy)]
enum SpineShape {
    /// An application: one part.
    App(Icit),
    /// A `J`: two parts, its motive and base, then, for a cast that carries
    /// them, three more: its ends' type and its ends.
    J(ProofMark, bool),
    /// A projection: no part.
    Proj(DataId, usize),
}

impl SpineShape {
    fn parts(self) -> usize {
        match self {
            SpineShape::App(_) => 1,
            SpineShape::J(_, ends) => 2 + 3 * usize::from(ends),
            SpineShape::Proj(..) => 0,
        }
    }
}

/// The head of a neutral value being quoted.
pub(crate) enum SpineHead {
    Term(Term),
    /// The first part, quoted before the eliminations' parts.
    Part,
    /// A quotient form, whose arguments are the first this many
    /// eliminations.
    Quot(QuotForm, usize, ProofMark),
}

/// How many of `spine`'s first eliminations are arguments of quotient form
/// `form`: its arity, unless the spine is malformed.
pub(crate) fn quot_args_in(form: QuotForm, spine: &[Elim]) -> usize {
    spine
        .iter()
        .take(form.arity())
        .take_while(|e| matches!(e, Elim::App(..)))
        .count()
}

fn pop2(done: &mut Vec<Term>) -> (Term, Term) {
    let b = done.pop().expect("two parts");
    let a = done.pop().expect("two parts");
    (a, b)
}

/// Push `id`'s call, with its arguments, to be read back as the call itself
/// rather than as its unfolding.
fn keep_call(level: usize, depth: usize, id: DefId, spine: &Spine, tasks: &mut Vec<QuoteTask>) {
    let shapes = spine
        .iter()
        .map(|elim| match elim {
            Elim::App(_, i) => SpineShape::App(*i),
            Elim::Proj(d, i) => SpineShape::Proj(*d, *i),
            Elim::J { .. } => unreachable!("a call's spine has no `J`"),
        })
        .collect();
    tasks.push(QuoteTask::Spine(SpineHead::Term(Term::Def(id)), shapes));
    for elim in spine.iter().rev() {
        if let Elim::App(v, _) = elim {
            tasks.push(QuoteTask::Visit(level, v.clone(), depth + 1));
        }
    }
}

/// Quotes the outermost layer of `value`: finished at once, or an assembly
/// task with its parts to visit first.
fn visit(
    g: &Ev,
    level: usize,
    value: Value,
    depth: usize,
    mode: Readback,
    tasks: &mut Vec<QuoteTask>,
    done: &mut Vec<Term>,
) -> Result<()> {
    // Parts are pushed last-first, so they're finished first-first.
    let visit_all = |tasks: &mut Vec<QuoteTask>, values: &[Value]| {
        for v in values.iter().rev() {
            tasks.push(QuoteTask::Visit(level, v.clone(), depth + 1));
        }
    };
    let value = if !mode.unfolds() {
        match force_solved(g, value)? {
            Value::Call(id, spine, _)
                if mode.keeps_every_call() || !matches_at_once(g, id, &spine)? =>
            {
                keep_call(level, depth, id, &spine, tasks);
                return Ok(());
            }
            // Shown, a call that steps at once is read back as that one step,
            // in which the calls it returns stay folded.
            Value::Call(id, spine, _) if mode == Readback::Shown => {
                tasks.push(QuoteTask::Visit(level, unfold_once(g, id, spine)?, depth));
                return Ok(());
            }
            other => force(g, other)?,
        }
    } else {
        // A `Float` order comparison says more as itself than as the two
        // order keys it computes to (SW-3426): keep it a call in a message,
        // never in the read-back the elaborator uses (`Readback::Unfolded`).
        if mode.for_display()
            && let Value::Call(id, spine, _) = &value
            && (g.env.registry().is_def(Builtin::FloatLeq, *id)
                || g.env.registry().is_def(Builtin::FloatLess, *id))
        {
            keep_call(level, depth, *id, spine, tasks);
            return Ok(());
        }
        let value = force(g, value)?;
        // A stuck field of a call (`Frame::CallField`), `(f x).i`: the field
        // of the call read back unfolded, as a field of anything else is.
        if let Value::Neutral(Head::Def(id), spine) = &value
            && is_call_field(spine)
            && is_folded(g, &value)
        {
            let (_, call, fields) = folded_parts(g, *id, spine);
            let shapes = fields
                .iter()
                .map(|&(d, i)| SpineShape::Proj(d, i))
                .collect();
            tasks.push(QuoteTask::Spine(SpineHead::Part, shapes));
            tasks.push(QuoteTask::Visit(
                level,
                Value::Call(*id, call, Rc::default()),
                depth,
            ));
            return Ok(());
        }
        value
    };
    match value {
        Value::Sort(s) => done.push(Term::Sort(s)),
        Value::Nat(n) => done.push(Term::Nat(n)),
        // The range, as a term; it means what its expansion would.
        Value::Chars(c) => done.push(match &g.env.builtins().text {
            Some(text) => chars::term(text, &c),
            None => unreachable!("a compact list without `List` and `Char`"),
        }),
        Value::Refl => done.push(Term::Refl),
        Value::Pi(x, i, a, b, pm) => {
            tasks.push(QuoteTask::Pi(x, i, pm));
            tasks.push(QuoteTask::Visit(
                level + 1,
                b.apply(g, Value::var_marked(level, pm))?,
                depth + 1,
            ));
            tasks.push(QuoteTask::Visit(level, (*a).clone(), depth + 1));
        }
        Value::Lam(x, i, b, pm) => {
            tasks.push(QuoteTask::Lam(x, i, pm));
            tasks.push(QuoteTask::Visit(
                level + 1,
                b.apply(g, Value::var_marked(level, pm))?,
                depth + 1,
            ));
        }
        Value::Data(d, args) => {
            tasks.push(QuoteTask::Data(d, args.len()));
            visit_all(tasks, &args);
        }
        // Read back folded, `Succ` of a call stays that: the call is what
        // was written.
        Value::Ctor(d, 1, args)
            if mode.unfolds() && Some(d) == g.env.builtins().nat && has_call_base(g, &args) =>
        {
            visit(
                g,
                level,
                succ_unglued(g, &args[0])?,
                depth,
                mode,
                tasks,
                done,
            )?;
        }
        Value::Ctor(d, c, args) => {
            tasks.push(QuoteTask::Ctor(d, c, args.len()));
            visit_all(tasks, &args);
        }
        Value::NatAdd(k, base) => {
            tasks.push(QuoteTask::NatAdd(k));
            tasks.push(QuoteTask::Visit(level, (*base).clone(), depth + 1));
        }
        Value::Eq(ty, a, b) => {
            tasks.push(QuoteTask::Eq);
            visit_all(tasks, &[(*ty).clone(), (*a).clone(), (*b).clone()]);
        }
        // The erased placeholder ([`erase::erased`]), applied or not, stands
        // for a proof or a type no binder has: it reads back as the elision
        // `…`, which no checked term contains, rather than as a variable
        // outside the context (whose index would wrap). Values computed with
        // erasure on hold it in their erased fields, and an error message's
        // counterexample puts it for a hypothesis's proof.
        Value::Neutral(Head::Var(l, _, _), _) if l == erase::ERASED => {
            done.push(Term::Meta(ELIDED));
        }
        Value::Neutral(head, spine) => {
            let head = match head {
                // Checked in release builds too: past it, the index wraps
                // to one no context has, which a printer shows as some
                // other name rather than failing.
                Head::Var(l, _, _) => {
                    assert!(
                        l < level,
                        "internal error: variable at level {l} read back with {level} in scope: \
                         the caller is quoting outside the context the value was made in"
                    );
                    SpineHead::Term(Term::Var(level - 1 - l))
                }
                Head::Def(id) => SpineHead::Term(Term::Def(id)),
                Head::Meta(m) => SpineHead::Term(Term::Meta(m)),
                Head::Quot(form, pm) => SpineHead::Quot(form, quot_args_in(form, &spine), pm),
            };
            let mut shape = Vec::with_capacity(spine.len());
            let mut parts = Vec::new();
            for elim in &spine {
                match elim {
                    Elim::App(v, i) => {
                        shape.push(SpineShape::App(*i));
                        parts.push(v.clone());
                    }
                    Elim::J {
                        motive,
                        base,
                        result,
                        ends,
                    } => {
                        shape.push(SpineShape::J(*result, ends.is_some()));
                        parts.push((**motive).clone());
                        parts.push((**base).clone());
                        if let Some(ends) = ends {
                            parts.extend([ends.ty.clone(), ends.x.clone(), ends.y.clone()]);
                        }
                    }
                    Elim::Proj(d, i) => shape.push(SpineShape::Proj(*d, *i)),
                }
            }
            tasks.push(QuoteTask::Spine(head, shape));
            visit_all(tasks, &parts);
        }
        // Read back unfolded: `force` gave the unfolding.
        Value::Call(..) => unreachable!("a forced value is never a call"),
        Value::Resumption(_) => {
            panic!("internal error: a handler's resumption reached the checker")
        }
    }
    Ok(())
}

/// Whether `Succ` of `args` (a `Succ` value's field) is `Succ` applied,
/// perhaps several times, to a glued call ([`Value::Call`]). Without
/// gluing, `Succ` of a number is a number ([`native::ctor`]); a call is
/// a number only once unfolded, so the `Succ` around it stayed a
/// constructor. Never true without gluing (the kernel).
#[inline]
fn has_call_base(g: &Ev, args: &[Value]) -> bool {
    let mut field = &args[0];
    loop {
        match field {
            Value::Call(..) => return true,
            Value::Ctor(d, 1, inner) if Some(*d) == g.env.builtins().nat => field = &inner[0],
            _ => return false,
        }
    }
}

/// `Succ field`, built as without gluing: each call under the `Succ`s
/// unfolded and the `Succ`s put back with [`native::ctor`], which keeps
/// numbers compact. So read-back gives `2`, not `Succ 1`, for the
/// unfolding of `List.length [x, y]`, as it does without gluing
/// (docs/proposals/folded-calls.md, stage 2).
#[cold]
#[inline(never)]
fn succ_unglued(g: &Ev, field: &Value) -> Result<Value> {
    let nat = g.env.builtins().nat.expect("a `Succ` value needs `Nat`");
    let mut succs = 1usize;
    let mut base = field.clone();
    loop {
        base = match base {
            call @ Value::Call(..) => force(g, call)?,
            Value::Ctor(d, 1, inner) if d == nat => {
                succs += 1;
                inner[0].clone()
            }
            _ => break,
        };
    }
    for _ in 0..succs {
        base = native::ctor(g, nat, 1, vec![base]);
    }
    Ok(base)
}

/// Definitional equality, with `level` variables in scope. Used by the kernel,
/// which never sees metavariables (the elaborator unifies instead).
/// `Ok(false)` means the values were compared and differ; an error means
/// there's no answer.
///
/// It doesn't recurse on the Rust stack: the pairs still to compare are kept
/// on a work list, depth first and left to right, so the first difference
/// found stops it, as a recursive version would.
///
/// **Precondition: homogeneous values.** `a` and `b` have the same type.
/// Two proofs are equal without being looked at (rule I, docs/core.md
/// "Proof irrelevance"), which is true only because they prove the same
/// proposition, and the values don't say what that is: a caller handing
/// over two proofs of different statements gets "equal". Breaking this is
/// a soundness bug, not just a wrong `false`: a caller that has two values
/// of possibly different types compares the types first
/// (docs/proposals/full-proof-irrelevance-audit.md). Inside, parts are
/// taken left to right, so earlier parts (which later parts' types depend
/// on) are compared first, and each pair formed has one type.
///
/// **Precondition: the level.** `level` is above every free variable of
/// `a` and `b`: fresh variables are made from it, so one too low can name
/// a free variable and make two different functions equal.
///
/// The elaborator's calls that may hand over values of different types
/// (`data_auto.rs`, `check.rs`'s environments for a `?`, `walk/two.rs`,
/// `cases.rs`'s known values, the head-keyed searches) rely on the kernel
/// checking whatever they conclude.
#[track_caller]
pub fn conv(g: &Ev, level: usize, a: &Value, b: &Value) -> Result<bool> {
    let same = conv_with(g, level, a, b, &mut CallMemo::default())?;
    if proof_counts::on() && both_proofs(g, a, b) {
        proof_counts::record_caller(g, "conv", std::panic::Location::caller(), !same);
    }
    Ok(same)
}

/// Whether `a` and `b` are both marked proofs ([`is_proof`]).
pub fn both_proofs(g: &Ev, a: &Value, b: &Value) -> bool {
    is_proof(g, a).is_proof() && is_proof(g, b).is_proof()
}

/// Rule I (docs/core.md, "Proof irrelevance"): two proofs are equal, and
/// nothing inside them is looked at. `Some(true)` when both are marked
/// proofs; `Some(false)` when one is and the other is visibly not one (a
/// value of a data type in `Type`, a number, a type), which breaks
/// [`conv`]'s precondition: in the kernel's own checking that is an internal
/// error under the `reference` feature (the audit's tripwire, condition C),
/// and "different" otherwise. An unmarked side (an elaborator's unknown, a
/// lambda) is neither: `None`, and the comparison goes on by shape, which
/// can only miss an equality.
pub fn by_rule_i(g: &Ev, a: &Value, b: &Value) -> Option<bool> {
    let (ma, mb) = (is_proof(g, a), is_proof(g, b));
    if ma.is_proof() && mb.is_proof() {
        proof_counts::record(g, proof_counts::Kind::RuleI, 1);
        return Some(true);
    }
    if (ma.is_proof() && visibly_data(g, b)) || (mb.is_proof() && visibly_data(g, a)) {
        #[cfg(feature = "reference")]
        if g.machine.kernel.get() {
            panic!(
                "internal error: the kernel compared a proof with a value that isn't one: {} against {}",
                describe(a),
                describe(b)
            );
        }
        return Some(false);
    }
    None
}

/// Whether `value` is visibly not a proof, whatever its marks: a type, a
/// number, or a constructor of a data type in `Type`. A variable, a call or
/// a stuck computation marked "not a proof" isn't counted: the mark may be
/// one the elaborator left unknown, and the tripwire must not fire on that.
fn visibly_data(g: &Ev, value: &Value) -> bool {
    match value {
        Value::Sort(_) | Value::Pi(..) | Value::Data(..) | Value::Eq(..) => true,
        Value::Nat(_) | Value::NatAdd(..) | Value::Chars(_) => true,
        Value::Ctor(d, ..) => g.data(*d).sort != Sort::Prop,
        Value::Refl
        | Value::Lam(..)
        | Value::Neutral(..)
        | Value::Call(..)
        | Value::Resumption(_) => false,
    }
}

/// [`conv`], inside an outermost one whose record of glued calls
/// compared so far is `memo`.
///
/// This is the frame that recurs once per level of nesting where `conv`
/// recurses (in [`recurse`]), so it holds only the work list and the pair
/// in hand: comparing a pair's outer layer ([`conv_step`]) and comparing
/// codomains have frames of their own, which are gone before the recursion
/// starts.
fn conv_with(g: &Ev, level: usize, a: &Value, b: &Value, memo: &mut CallMemo) -> Result<bool> {
    // Every level below `level` may be free in `a` and `b` (the caller's
    // promise), so a test met while comparing them starts at or above it.
    let reached = g.machine.reached.get();
    let _restore = RestoreReached(g.machine, reached);
    if level > reached {
        g.machine.reached.set(level);
    }
    let mut work = vec![ConvTask::Values(level, a.clone(), b.clone())];
    while let Some(mut task) = work.pop() {
        g.machine.budget.step()?;
        let same = match task {
            // The pair is compared where it lies in `task`, not moved out.
            ConvTask::Values(level, ref mut a, ref mut b) => {
                // `conv_step` stops where the comparison recurses, and is
                // called again, from where it stopped, if the recursion
                // doesn't settle it.
                let mut from = Stage::Calls;
                let same = loop {
                    let kind = match conv_step(g, level, a, b, from, &mut work, memo)? {
                        Step::Answer(same) => break same,
                        Step::Recurse(kind) => kind,
                    };
                    match recurse(g, level, a, b, kind, &mut work, memo)? {
                        Resume::Answer(same) => break same,
                        Resume::From(stage) => from = stage,
                    }
                };
                if !same && proof_counts::on() && both_proofs(g, a, b) {
                    proof_counts::record(g, proof_counts::Kind::DifferentProofs, 1);
                }
                same
            }
            ConvTask::Codomains(level, b1, b2, mark) => {
                codomains(g, level, b1, b2, mark, &mut work)?
            }
        };
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Function types' codomains, compared once their domains are: pushes the
/// two applied to a fresh variable, unless they are the same function,
/// which gives the same codomain (see `same_closure`).
#[inline(never)]
fn codomains(
    g: &Ev,
    level: usize,
    b1: Closure,
    b2: Closure,
    mark: ProofMark,
    work: &mut Vec<ConvTask>,
) -> Result<bool> {
    if same_closure(g, &b1, &b2)? {
        return Ok(true);
    }
    let next = fresh_past(g, level, 1)?;
    let fresh = Value::var_marked(level, mark);
    work.push(ConvTask::Values(
        next,
        b1.apply(g, fresh.clone())?,
        b2.apply(g, fresh)?,
    ));
    Ok(true)
}

/// Comparison still to do.
enum ConvTask {
    Values(usize, Value, Value),
    /// With the binder's mark, for the fresh variable.
    Codomains(usize, Closure, Closure, ProofMark),
}

// Two glued calls of the same definition (D483, docs/proposals/
// folded-calls.md §7 stage 4).
//
// The kernel checks a definition's body with gluing on (`check.rs`
// `admit_group`), so `f a` stays the call until something looks inside. Two
// calls of the same definition are compared by their arguments first: if
// those are equal, so are the calls (congruence: the same function applied
// to equal arguments). If not, they're compared by their unfoldings, as
// before, since `f a` and `f b` can be equal with `a` and `b` different. So
// the rule only ever answers "equal" where unfolding would too, given the
// time; it can't make the kernel accept anything it wouldn't.
//
// Trying the arguments first and then the unfoldings could repeat work when
// they differ: the unfoldings usually contain the same arguments (`f n =
// Succ n`), so `f (f (f x))` against `f (f (f y))` would compare the inner
// pairs again at every level, twice as much per level. So each outermost
// `conv` keeps a record of the pairs of calls it has met, by the addresses
// of their unfolding cells (shared by every copy of a call), at the same
// level: a pair whose arguments were found different isn't tried by its
// arguments again, and a pair found different outright (an argument pair
// compared on its own) is answered "different" at once.
//
// A pair found equal by its arguments is answered "equal" at once too
// (SW-4647). Values share their parts, but a comparison walks them as
// trees: the lexer's items each hold parser states built by
// `State.advance` from the one before, so comparing a source's items
// against the same items computed again met the same pairs of calls
// millions of times (`readsBackHungListExample`, 147M steps). Every
// remembered answer is the one comparing the pair again would give, since
// whether two values are convertible depends only on them and the level
// (the kernel has no metavariables; rule I reads only the marks, which are
// part of the values: the cells are the same, so the values are), so the
// record only saves
// work: an "equal" is recorded once the arguments' comparisons have all
// finished, never while the pair is still open. The record holds the
// values, so an address can't be reused for another call while it lives;
// it's dropped when the outermost `conv` ends. Lookups don't depend on the
// order of the map, so the resource counters stay deterministic.

/// What one outermost [`conv`] has found about pairs of glued calls of the
/// same definition, by level and the addresses of their unfolding cells.
/// Also the stuck sums found to have
/// nothing for rule E to read ([`crate::nat_add::Unread`]).
#[derive(Default)]
struct CallMemo {
    calls: HashMap<CallKey, (Found, Value, Value)>,
    sums: crate::nat_add::Unread,
}

/// A pair of calls in a [`CallMemo`]: level and the two unfolding
/// cells' addresses.
type CallKey = (usize, usize, usize);

/// What a [`CallMemo`] knows about a pair of calls.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Found {
    /// Equal by their arguments.
    Equal,
    /// Their arguments differ: compare them by their unfoldings.
    ArgumentsDiffer,
    /// Different outright.
    Different,
}

impl CallMemo {
    fn key(level: usize, a: &Value, b: &Value) -> Option<CallKey> {
        match (a, b) {
            (Value::Call(i1, _, u1), Value::Call(i2, _, u2)) if i1 == i2 => {
                Some((level, Rc::as_ptr(u1) as usize, Rc::as_ptr(u2) as usize))
            }
            _ => None,
        }
    }

    fn get(&self, level: usize, a: &Value, b: &Value) -> Option<Found> {
        let key = Self::key(level, a, b)?;
        self.calls.get(&key).map(|entry| entry.0)
    }

    fn record(&mut self, level: usize, a: &Value, b: &Value, found: Found) {
        if let Some(key) = Self::key(level, a, b) {
            self.calls.insert(key, (found, a.clone(), b.clone()));
        }
    }
}

/// Whether two spines of the same definition are equal argument by argument
/// (and `J` by `J`), each pair compared by a [`conv`] of its own: this is
/// what every comparison of calls by their arguments uses. Proofs among the
/// arguments are equal by rule I, and unfolding never reads a proof (rules
/// K, S and F), so arguments equal here give equal unfoldings. This is
/// where `conv` recurses on the Rust stack: once per level of calls nested
/// in arguments, ended by the stack guard (`budget.rs`, E-RESOURCE) if
/// that's too deep. A pair of glued calls found different is recorded as
/// such ([`CallMemo`]).
fn same_spines(
    g: &Ev,
    level: usize,
    s1: &[Elim],
    s2: &[Elim],
    memo: &mut CallMemo,
) -> Result<bool> {
    if s1.len() != s2.len() {
        return Ok(false);
    }
    let Some(pairs) = spine_pairs(s1, s2, level) else {
        return Ok(false);
    };
    for pair in pairs {
        let ConvTask::Values(l, x, y) = pair else {
            unreachable!()
        };
        if !conv_with(g, l, &x, &y, memo)? {
            memo.record(l, &x, &y, Found::Different);
            return Ok(false);
        }
    }
    Ok(true)
}

/// Where [`conv_step`] starts comparing a pair, or takes it up again after
/// [`recurse`] has compared parts of it without settling it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Stage {
    /// From the start: two glued calls of one definition.
    Calls,
    /// Dictionaries left folded by name, compared by their arguments.
    Folded,
    /// The same, unfolded: the arguments differ, or the heads do.
    Unfold,
}

/// Where [`conv_step`] stopped: the answer for the pair, or the point where
/// comparing it recurses.
enum Step {
    Answer(bool),
    Recurse(Recursion),
}

/// Moves a value out of a pair [`conv_step`] is comparing, which isn't
/// looked at again.
fn take(value: &mut Value) -> Value {
    std::mem::replace(value, Value::Refl)
}

/// The comparisons of a pair that call [`conv_with`] for parts of it, each
/// done by [`recurse`] once [`conv_step`] has found it applies.
#[derive(Clone, Copy)]
enum Recursion {
    /// Two glued calls of one definition, by their arguments.
    Calls,
    /// Two folded dictionaries of one definition, by their arguments.
    Folded,
    /// Two hidden opaque calls of one definition, by their arguments.
    Sealed,
    /// Two calls of one definition stuck on a `case`.
    StuckSame,
    /// Two partially applied calls of one definition: arguments, or eta.
    Underapplied,
    /// Calls of two different definitions, each stuck on a `case`.
    StuckDifferent,
}

/// What [`recurse`] found: the answer for the pair, or the stage of
/// [`conv_step`] to go on from.
enum Resume {
    Answer(bool),
    From(Stage),
}

/// Compares the outermost layer of `a` and `b`, starting at stage `from`:
/// `false` if they differ there; otherwise pushes the pairs of parts still
/// to compare. Where comparing them would call [`conv_with`] for parts of
/// them, it stops instead and hands the pair back, for [`recurse`] to do
/// that from a smaller frame: the stack a level of nesting takes is then
/// `conv_with`'s and `recurse`'s, not this function's, which has room for
/// every rule. The rules are tried in the same order either way.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn conv_step(
    g: &Ev,
    level: usize,
    a: &mut Value,
    b: &mut Value,
    mut from: Stage,
    work: &mut Vec<ConvTask>,
    memo: &mut CallMemo,
) -> Result<Step> {
    if from == Stage::Calls
        && let Some(answer) = by_rule_i(g, a, b)
    {
        return Ok(Step::Answer(answer));
    }
    // Two glued calls of the same definition: their arguments first, then
    // (below) their unfoldings. See `CallMemo`.
    if from == Stage::Calls
        && let (Value::Call(i1, ..), Value::Call(i2, ..)) = (&*a, &*b)
        && i1 == i2
        && !shortcuts_disabled()
    {
        match memo.get(level, a, b) {
            Some(Found::Equal) => return Ok(Step::Answer(true)),
            Some(Found::Different) => return Ok(Step::Answer(false)),
            Some(Found::ArgumentsDiffer) => {}
            None => return Ok(Step::Recurse(Recursion::Calls)),
        }
    }
    // Dictionaries left folded by name: the same one applied to equal
    // arguments is equal; otherwise they're compared unfolded. (Like a
    // partially applied definition below, this recurses once per level of
    // nested dictionaries, which is bounded by the program.) Before numbers
    // and text: a folded definition with `decreasing` can be a number
    // (`f n` against `1 + …`), and is compared as one once unfolded.
    let unfolds = |v: &Value| is_folded(g, v) || unfolds_head(g, v);
    if from != Stage::Unfold && (unfolds(a) || unfolds(b)) {
        if let (Value::Neutral(Head::Def(i1), _), Value::Neutral(Head::Def(i2), _)) = (&*a, &*b)
            && i1 == i2
        {
            return Ok(Step::Recurse(Recursion::Folded));
        }
        from = Stage::Unfold;
    }
    if from == Stage::Unfold {
        let unfold = |v: &Value| match unfold_folded(g, v)? {
            Some(u) => Ok(Some(u)),
            None => unfold_folded_head(g, v),
        };
        let a2 = unfold(a)?;
        let b2 = unfold(b)?;
        if a2.is_some() || b2.is_some() {
            work.push(ConvTask::Values(
                level,
                a2.unwrap_or(take(a)),
                b2.unwrap_or(take(b)),
            ));
            return Ok(Step::Answer(true));
        }
    }
    // A sum stuck on its first argument, with a folded call in its second:
    // compared as what R3 and R4 make of it once that is unfolded (G2).
    let mut reread = |v: &Value| reread_sum(g, v, &mut memo.sums);
    if let Some(a2) = reread(a)? {
        work.push(ConvTask::Values(level, a2, take(b)));
        return Ok(Step::Answer(true));
    }
    if let Some(b2) = reread(b)? {
        work.push(ConvTask::Values(level, take(a), b2));
        return Ok(Step::Answer(true));
    }
    // Numbers, `k + x`, `Zero` and `Succ` all compare by their `k + x` forms:
    // `3` and `Succ x` are equal when `x` is `2`. Glued calls in them are
    // unfolded only as far as that needs (`compare_lazily`, SW-1153). A
    // base left against a different count of `Succ`s is unequal unless it's
    // a folded call, which is unfolded and compared again (`Succ (f 0)`
    // against `2`, SW-2157), as the rule above does at the top, or a sum
    // that R3 and R4 read further (G2).
    if native::nat_like(g, a) || native::nat_like(g, b) {
        let mut unfolded = None;
        let same = |x: &Value, y: &Value| {
            work.push(ConvTask::Values(level, x.clone(), y.clone()));
            Ok(true)
        };
        let assign = |x: &Value, rest: &Value| {
            let x = match unfold_folded(g, x)? {
                Some(x) => Some(x),
                None => match unfold_folded_head(g, x)? {
                    Some(x) => Some(x),
                    None => reread(x)?,
                },
            };
            Ok(match x {
                Some(x) => {
                    unfolded = Some((x, rest.clone()));
                    true
                }
                None => false,
            })
        };
        let equal = if shortcuts_disabled() {
            native::compare(g, a, b, same, assign)
        } else {
            native::compare_lazily(g, a, b, same, assign)
        }?;
        if let Some((x, rest)) = unfolded {
            work.push(ConvTask::Values(level, x, rest));
        }
        return Ok(Step::Answer(equal));
    }
    // Compact lists: two ranges are equal when their characters are (their
    // expansions are then the same), and a range against anything else is
    // expanded one cell, which is then compared as a constructor. So a
    // compact `"a"` and `Cons (MkChar 97 h) Nil` are equal: `h` and `byComputing`
    // are in `MkChar`'s proof field.
    match (&*a, &*b) {
        (Value::Chars(x), Value::Chars(y)) => {
            return Ok(Step::Answer(x.as_slice() == y.as_slice()));
        }
        (Value::Chars(_), _) => {
            work.push(ConvTask::Values(level, expand_step(g, take(a)), take(b)));
            return Ok(Step::Answer(true));
        }
        (_, Value::Chars(_)) => {
            work.push(ConvTask::Values(level, take(a), expand_step(g, take(b))));
            return Ok(Step::Answer(true));
        }
        _ => {}
    }
    // Parts are pushed last-first, so they're compared first-first.
    let push_all = |work: &mut Vec<ConvTask>, xs: &[Value], ys: &[Value]| {
        for (x, y) in xs.iter().zip(ys).rev() {
            work.push(ConvTask::Values(level, x.clone(), y.clone()));
        }
    };
    let same = match (&*a, &*b) {
        (Value::Sort(s), Value::Sort(t)) => s == t,
        (Value::Pi(_, i1, a1, b1, m1), Value::Pi(_, i2, a2, b2, m2)) => {
            if i1 != i2 {
                return Ok(Step::Answer(false));
            }
            work.push(ConvTask::Codomains(
                level,
                b1.clone(),
                b2.clone(),
                m1.or(*m2),
            ));
            work.push(ConvTask::Values(level, (**a1).clone(), (**a2).clone()));
            true
        }
        // The same function, recognised without running it: comparing its
        // body applied to a fresh variable would find the same value twice.
        (Value::Lam(_, _, b1, _), Value::Lam(_, _, b2, _)) if same_closure(g, b1, b2)? => true,
        (Value::Lam(_, _, b1, m1), Value::Lam(_, _, b2, m2)) => {
            let next = fresh_past(g, level, 1)?;
            let fresh = Value::var_marked(level, m1.or(*m2));
            work.push(ConvTask::Values(
                next,
                b1.apply(g, fresh.clone())?,
                b2.apply(g, fresh)?,
            ));
            true
        }
        // Eta: `f` and `x => f x` are equal.
        (Value::Lam(_, i, b, mark), other) | (other, Value::Lam(_, i, b, mark)) => {
            let next = fresh_past(g, level, 1)?;
            let fresh = Value::var_marked(level, *mark);
            work.push(ConvTask::Values(
                next,
                b.apply(g, fresh.clone())?,
                apply_icit(g, other.clone(), fresh, *i)?,
            ));
            true
        }
        // Proofs are skipped by position too: a data type's parameters
        // whose type is a proposition (not its indices), and a
        // constructor's proof fields. Rule I would find them equal anyway
        // in a term the kernel checked; this also covers the elaborator's
        // values, whose marks may be unknown. Sound only because both sides
        // have the same type (see `conv`), so the skipped parts prove the
        // same proposition.
        (Value::Data(d1, a1), Value::Data(d2, a2)) => {
            if d1 != d2 || a1.len() != a2.len() {
                return Ok(Step::Answer(false));
            }
            for (k, (x, y)) in a1.iter().zip(a2.iter()).enumerate().rev() {
                if !proof_param(g, *d1, k) {
                    work.push(ConvTask::Values(level, x.clone(), y.clone()));
                }
            }
            true
        }
        (Value::Ctor(d1, c1, a1), Value::Ctor(d2, c2, a2)) => {
            if d1 != d2 || c1 != c2 || a1.len() != a2.len() {
                return Ok(Step::Answer(false));
            }
            for (k, (x, y)) in a1.iter().zip(a2.iter()).enumerate().rev() {
                if !proof_field(g, *d1, *c1, k) {
                    work.push(ConvTask::Values(level, x.clone(), y.clone()));
                }
            }
            true
        }
        (Value::Eq(t1, x1, y1), Value::Eq(t2, x2, y2)) => {
            push_all(
                work,
                &[(**t1).clone(), (**x1).clone(), (**y1).clone()],
                &[(**t2).clone(), (**x2).clone(), (**y2).clone()],
            );
            true
        }
        (Value::Refl, Value::Refl) => true,
        // Two stuck casts: by their ends' type, their ends, the motive and
        // the base, then what is applied to them; never by their proofs
        // (docs/proposals/full-proof-irrelevance-audit.md, finding B). Each
        // pair then has one type: the ends' types are compared first.
        (Value::Neutral(_, s1), Value::Neutral(_, s2))
            if cast_at(s1).is_some() && cast_at(s2).is_some() =>
        {
            let (i, j) = (cast_at(s1).unwrap(), cast_at(s2).unwrap());
            let (
                Elim::J {
                    motive: m1,
                    base: b1,
                    ends: Some(e1),
                    ..
                },
                Elim::J {
                    motive: m2,
                    base: b2,
                    ends: Some(e2),
                    ..
                },
            ) = (&s1[i], &s2[j])
            else {
                unreachable!("found by cast_at")
            };
            let Some(rest) = (s1.len() - i == s2.len() - j)
                .then(|| spine_pairs(&s1[i + 1..], &s2[j + 1..], level))
                .flatten()
            else {
                return Ok(Step::Answer(false));
            };
            work.extend(rest.into_iter().rev());
            push_all(
                work,
                &[
                    e1.ty.clone(),
                    e1.x.clone(),
                    e1.y.clone(),
                    (**m1).clone(),
                    (**b1).clone(),
                ],
                &[
                    e2.ty.clone(),
                    e2.x.clone(),
                    e2.y.clone(),
                    (**m2).clone(),
                    (**b2).clone(),
                ],
            );
            true
        }
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) if h1 == h2 && s1.len() == s2.len() => {
            let kind = if def_head(h1).is_some_and(|f| sealed(g, f)) {
                // A hidden opaque call never unfolds here, but does where
                // `f` is transparent, and a pending group member's does once
                // the group is admitted: compared by its arguments, which
                // agrees with unfolding (see `same_spines`), so the body
                // being seen only ever adds equalities.
                Recursion::Sealed
            } else if opens_by_tree(g, a) && opens_by_tree(g, b) {
                // Two calls of one definition stuck on a `case`: see
                // `recurse`.
                Recursion::StuckSame
            } else if underapplied(g, a).is_none() && underapplied(g, b).is_none() {
                // Eta for definitions doesn't apply, so the spines must match.
                return Ok(Step::Answer(match spine_pairs(s1, s2, level) {
                    Some(pairs) => {
                        work.extend(pairs.into_iter().rev());
                        true
                    }
                    None => false,
                }));
            } else if def_head(h1).is_some() {
                // A function: equal if the spines match, or else by eta.
                Recursion::Underapplied
            } else {
                return Ok(Step::Answer(push_eta(g, level, a, b, work)?));
            };
            return Ok(Step::Recurse(kind));
        }
        // Two different definitions, each stuck on a `case`: compared by
        // their case trees (`same_stuck_trees`, in `recurse`), as are two
        // calls of one definition whose arguments differ (above).
        (Value::Neutral(Head::Def(i1), _), Value::Neutral(Head::Def(i2), _))
            if i1 != i2 && opens_by_tree(g, a) && opens_by_tree(g, b) =>
        {
            return Ok(Step::Recurse(Recursion::StuckDifferent));
        }
        // Calls are compared by their unfoldings: two calls of the same
        // definition whose arguments differ (tried at the top), or a call
        // and anything else. The cases above that a call can reach
        // (numbers, compact lists, dictionaries, eta) look inside it
        // themselves.
        (Value::Call(..), _) | (_, Value::Call(..)) => {
            work.push(ConvTask::Values(
                level,
                force(g, take(a))?,
                force(g, take(b))?,
            ));
            true
        }
        // Record eta, rule 1 (docs/proposals/record-eta.md §6.3): a
        // constructor of a type with eta against an unknown `n` is equal when
        // each field is equal to `n`'s projection. True because every value
        // of such a type is its constructor applied to its fields (the
        // conditions are at `check::qualifies_for_eta`). Nothing checks that `n` is a
        // value of that type: both sides have one type (the precondition of
        // `conv`), the constructor's. Fields go left to right, so each pair
        // has one type once the earlier ones are equal (or skipped as
        // proofs, exactly as for two constructors). It ends: each pair
        // is a strictly smaller part of the constructor against a
        // projection, and only finitely many projections of `n` can be
        // taken, the type not being recursive. Only after glued calls are
        // forced (above), so it never sees a call.
        (Value::Ctor(d, 0, fs), n @ Value::Neutral(..))
        | (n @ Value::Neutral(..), Value::Ctor(d, 0, fs))
            if is_eta_type(g, *d) =>
        {
            for (k, x) in fs.iter().enumerate().rev() {
                if !proof_field(g, *d, 0, k) {
                    work.push(ConvTask::Values(
                        level,
                        x.clone(),
                        project(*d, k, n.clone()),
                    ));
                }
            }
            true
        }
        _ => push_eta(g, level, a, b, work)?,
    };
    Ok(Step::Answer(same))
}

/// The comparisons [`conv_step`] stops at, which call [`conv_with`] for
/// parts of `a` and `b`: this is where `conv` recurses on the Rust stack, so
/// it is kept out of `conv_step`'s frame, and the rarer kinds are in frames
/// of their own.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn recurse(
    g: &Ev,
    level: usize,
    a: &Value,
    b: &Value,
    kind: Recursion,
    work: &mut Vec<ConvTask>,
    memo: &mut CallMemo,
) -> Result<Resume> {
    match kind {
        Recursion::Calls => {
            let (Value::Call(_, s1, _), Value::Call(_, s2, _)) = (a, b) else {
                unreachable!("two calls, from conv_step")
            };
            if same_spines(g, level, s1, s2, memo)? {
                memo.record(level, a, b, Found::Equal);
                return Ok(Resume::Answer(true));
            }
            memo.record(level, a, b, Found::ArgumentsDiffer);
            Ok(Resume::From(Stage::Folded))
        }
        Recursion::Folded => {
            let (_, s1, s2) = def_spines(a, b);
            Ok(if same_spines(g, level, s1, s2, memo)? {
                Resume::Answer(true)
            } else {
                Resume::From(Stage::Unfold)
            })
        }
        Recursion::Sealed => {
            let (_, s1, s2) = def_spines(a, b);
            Ok(Resume::Answer(same_spines(g, level, s1, s2, memo)?))
        }
        Recursion::Underapplied => {
            // This recurses once per level of nested partially applied
            // definitions, which is bounded by the program, not by the size
            // of the data.
            let (_, s1, s2) = def_spines(a, b);
            let same = same_spines(g, level, s1, s2, memo)?;
            Ok(Resume::Answer(same || push_eta(g, level, a, b, work)?))
        }
        Recursion::StuckSame => stuck_same(g, level, a, b, memo).map(Resume::Answer),
        Recursion::StuckDifferent => stuck_different(g, level, a, b, memo).map(Resume::Answer),
    }
}

/// The definition at the head of two neutral values, and their spines.
fn def_spines<'v>(a: &'v Value, b: &'v Value) -> (DefId, &'v [Elim], &'v [Elim]) {
    match (a, b) {
        (Value::Neutral(Head::Def(f), s1), Value::Neutral(_, s2)) => (*f, s1, s2),
        _ => unreachable!("two calls of a definition, from conv_step"),
    }
}

/// Two calls of one definition stuck on a `case`: equal arguments make them
/// equal, but different ones don't make them different (`ignoresFirst 1 x`
/// against `ignoresFirst 2 x`), so then they're compared by their case
/// trees, as two different definitions are ([`stuck_different`]);
/// otherwise conversion isn't transitive (G6, docs/core.md). The arguments
/// are compared here, each by a `conv` of its own, which recurses as the
/// tree comparison does.
#[inline(never)]
fn stuck_same(g: &Ev, level: usize, a: &Value, b: &Value, memo: &mut CallMemo) -> Result<bool> {
    let (_, s1, s2) = def_spines(a, b);
    let arguments = |same: CompareAt<'_>| -> Result<bool> {
        let Some(pairs) = spine_pairs(s1, s2, level) else {
            return Ok(false);
        };
        for pair in pairs {
            let ConvTask::Values(l, x, y) = pair else {
                unreachable!()
            };
            if !same(l, &x, &y)? {
                return Ok(false);
            }
        }
        Ok(true)
    };
    same_stuck_trees(
        g,
        level,
        a,
        b,
        Relation::Conv,
        true,
        arguments,
        &mut |l, x, y| conv_with(g, l, x, y, memo),
    )
}

/// Two different definitions, each stuck on a `case`: compared by their
/// case trees (`same_stuck_trees`), as are two calls of one definition
/// whose arguments differ ([`stuck_same`]). Like a partially applied
/// definition, this recurses: once per level of nested calls of such
/// definitions, in their leaves (bounded by the program, as they aren't
/// recursive) and in the scrutinees and arguments compared (bounded by how
/// deeply the data nests stuck calls). Deep nesting ends in the stack guard
/// (`budget.rs`, E-RESOURCE), not a crash.
#[inline(never)]
fn stuck_different(
    g: &Ev,
    level: usize,
    a: &Value,
    b: &Value,
    memo: &mut CallMemo,
) -> Result<bool> {
    same_stuck_trees(
        g,
        level,
        a,
        b,
        Relation::Conv,
        true,
        |_| Ok(false),
        &mut |l, x, y| conv_with(g, l, x, y, memo),
    )
}

/// A stuck cast in `value` whose ends are equal now (rule K), as its base
/// with the rest of the spine applied; `None` if there is none, or its ends
/// still differ. In the kernel, a cast that didn't fire when it was
/// evaluated never does; in the elaborator, an unknown in its ends may have
/// been solved since, so the unifier asks this before comparing a stuck
/// cast by its parts. What it returns is computed from the solutions as
/// they are now, and isn't kept in `value`: taking a solution back leaves
/// nothing behind (the audit's condition G).
pub fn fire_cast(g: &Ev, value: &Value) -> Result<Option<Value>> {
    let Value::Neutral(_, spine) = value else {
        return Ok(None);
    };
    let Some(i) = cast_at(spine) else {
        return Ok(None);
    };
    let Elim::J {
        base,
        ends: Some(ends),
        ..
    } = &spine[i]
    else {
        unreachable!("found by cast_at")
    };
    if spine[i + 1..].iter().any(|e| matches!(e, Elim::J { .. })) || !ends_meet(g, ends)? {
        return Ok(None);
    }
    let mut value = (**base).clone();
    for elim in &spine[i + 1..] {
        value = match elim {
            Elim::App(arg, icit) => apply_icit(g, value, arg.clone(), *icit)?,
            Elim::Proj(d, k) => match value {
                call @ Value::Call(..) => project_call(*d, *k, call),
                other => project(*d, *k, force(g, other)?),
            },
            Elim::J { .. } => unreachable!("checked above"),
        };
    }
    Ok(Some(value))
}

/// The first elimination in `spine` that is a cast carrying its ends
/// ([`Elim::J`]); what comes before it is its proof.
pub fn cast_at(spine: &[Elim]) -> Option<usize> {
    spine
        .iter()
        .position(|e| matches!(e, Elim::J { ends: Some(_), .. }))
}

/// The pairs of values in two spines of the same length, or `None` if their
/// eliminations don't match. Proof arguments are paired like any others,
/// and rule I answers for them.
#[inline(never)]
fn spine_pairs(s1: &[Elim], s2: &[Elim], level: usize) -> Option<Vec<ConvTask>> {
    let mut pairs = Vec::new();
    for pair in s1.iter().zip(s2) {
        match pair {
            (Elim::App(x, _), Elim::App(y, _)) => {
                pairs.push(ConvTask::Values(level, x.clone(), y.clone()));
            }
            (
                Elim::J {
                    motive: m1,
                    base: b1,
                    ..
                },
                Elim::J {
                    motive: m2,
                    base: b2,
                    ..
                },
            ) => {
                pairs.push(ConvTask::Values(level, (**m1).clone(), (**m2).clone()));
                pairs.push(ConvTask::Values(level, (**b1).clone(), (**b2).clone()));
            }
            (Elim::Proj(d1, i1), Elim::Proj(d2, i2)) if d1 == d2 && i1 == i2 => {}
            _ => return None,
        }
    }
    Some(pairs)
}

/// Whether parameter `k` of data type `d` is a proof. A type the
/// environment doesn't hold (only unit tests build such values) has none.
pub fn proof_param(g: &Ev, d: DataId, k: usize) -> bool {
    g.env
        .datas()
        .get(d.0)
        .is_some_and(|data| data.is_proof_param(k))
}

/// Whether field `k` of constructor `c` of data type `d` is a proof (its
/// type is in `Prop`; not `field_erased`, which types share). A type the
/// environment doesn't hold (only unit tests build such values) has none.
pub fn proof_field(g: &Ev, d: DataId, c: usize, k: usize) -> bool {
    g.env
        .datas()
        .get(d.0)
        .and_then(|data| data.ctors.get(c))
        .is_some_and(|ctor| ctor.field_sorts.get(k) == Some(&Sort::Prop))
}

/// The definition at the head of a neutral value, if it's one.
fn def_head(head: &Head) -> Option<DefId> {
    match head {
        Head::Def(f) => Some(*f),
        _ => None,
    }
}

/// Eta for definitions: a partially applied definition is a function, so it's
/// compared with the other side by applying both to a fresh variable (as for
/// lambdas); `SCRes` defined as `SCRes o = PlusRes … o` then equals
/// `PlusRes …`. Pushes that comparison, or returns `false` if neither side is
/// a partially applied definition.
fn push_eta(g: &Ev, level: usize, a: &Value, b: &Value, work: &mut Vec<ConvTask>) -> Result<bool> {
    let Some((icit, mark)) = next_parameter(g, a).or_else(|| next_parameter(g, b)) else {
        return Ok(false);
    };
    let next = fresh_past(g, level, 1)?;
    let fresh = Value::var_marked(level, mark);
    work.push(ConvTask::Values(
        next,
        apply_icit(g, a.clone(), fresh.clone(), icit)?,
        apply_icit(g, b.clone(), fresh, icit)?,
    ));
    Ok(true)
}

/// If `value` is a definition applied to fewer arguments than it takes (so
/// it's a function that doesn't unfold yet), the implicitness of its next
/// parameter.
pub fn underapplied(g: &Ev, value: &Value) -> Option<Icit> {
    next_parameter(g, value).map(|(icit, _)| icit)
}

/// [`underapplied`], with the next parameter's proof mark, for the fresh
/// variable eta applies both sides to.
///
/// The parameters are read off the body's leading lambdas, so a definition
/// whose body can't be seen ([`body_seen`]: a theorem, by rule F, or a
/// hidden opaque definition) offers none: which of its statement's
/// parameters its proof binds with a lambda is the proof's business, and
/// no other declaration may see it (docs/core.md, opaque definitions, rule
/// 6). Eta is still tried from the other side, and nothing is lost: a call
/// that can't unfold is equal only to a call of the same definition with
/// equal arguments, or, being a proof, to any proof by rule I, and
/// applying both sides to a fresh variable leaves that unchanged.
pub fn next_parameter(g: &Ev, value: &Value) -> Option<(Icit, ProofMark)> {
    let Value::Neutral(Head::Def(id), spine) = value else {
        return None;
    };
    let def = g.def(*id);
    let body = body_seen(g, *id)?;
    if spine.len() >= def.arity {
        return None;
    }
    match body.peel_lams(spine.len()) {
        Term::Lam(_, icit, _, mark) => Some((*icit, *mark)),
        _ => None,
    }
}

// Comparing two different definitions stuck on a `case` (SW-386, D1091).
//
// A definition's body is a case tree, and a call that can't take a step is
// left folded as the definition's name applied to its arguments: there's no
// first-class `case` value to compare. So `f c x` and `g c x`, for two
// definitions with the same tree (two `match`es written alike, each lifted to
// its own helper), used to differ just because `f` and `g` do. They're equal
// by the ordinary rules: unfold both (delta), and compare the two case
// analyses by congruence, the same scrutinee and, for each constructor, the
// same branch with its fields as fresh variables. That's what this does,
// without the scrutinee being known. Every equality it finds holds for every
// value of the scrutinee: whichever constructor it turns out to be, both
// sides take that branch, with the same fields.
//
// Only for definitions that aren't recursive (a recursive one compared this
// way could unfold forever), aren't folded by name (dictionaries, compared
// above) and have no `Quot.lift` leaf. A tree is compared
// node by node: a `case` whose scrutinee's head is a constructor (a folded
// call unfolded, a number or a compact list split, as running it would)
// takes its branch; one stuck on a neutral value is compared with the
// other side's; leaves are compared as values. Any other shape (a `NumCase`,
// one side a leaf and the other a `case`) answers "different", as before.

/// Whether `value` is a definition applied to all its arguments that
/// [`same_stuck_trees`] can compare with another by its case tree.
/// Recursive definitions don't open by tree, and a group of more than one
/// member is recursive, so a test that means to exercise the tree comparison
/// needs each definition in its own group.
pub fn opens_by_tree(g: &Ev, value: &Value) -> bool {
    let Value::Neutral(Head::Def(id), spine) = value else {
        return false;
    };
    let def = g.def(*id);
    body_seen(g, *id).is_some()
        && !def.recursive
        && !def.lift_leaf
        && !folds(g, *id)
        && def.arity > 0
        && spine.len() == def.arity
        && spine.iter().all(|e| matches!(e, Elim::App(..)))
        && g.env.builtins().native(*id).is_none()
        && !g.env.builtins().float_bound(*id)
}

/// The level of the variable that call `value` is stuck on, for a note:
/// `value` forced is a definition applied to all its arguments whose case
/// tree, walked as [`same_stuck_trees`] walks it, stops at a `case` on a
/// neutral value headed by a variable, or on a call that is itself stuck on
/// one (`if beats m m then …` is stuck on `m`). `None` for anything else (a
/// value that computes, a call stuck on an opaque one, a bare variable). Error path only; it runs in the machine's budget.
pub fn stuck_on_variable(g: &Ev, value: &Value) -> Option<usize> {
    let value = force(g, value.clone()).ok()?;
    let Value::Neutral(Head::Def(id), spine) = &value else {
        return None;
    };
    let def = g.def(*id);
    let body = body_seen(g, *id)?;
    if spine.len() != def.arity
        || def.arity == 0
        || folds(g, *id)
        || def.lift_leaf
        || g.env.builtins().native(*id).is_some()
        || g.env.builtins().float_bound(*id)
    {
        return None;
    }
    let mut args = Vec::with_capacity(spine.len());
    for elim in spine.iter() {
        match elim {
            Elim::App(v, _) => args.push(v.clone()),
            Elim::J { .. } | Elim::Proj(..) => return None,
        }
    }
    let tree = Term::peel_lams_rc(body, def.arity);
    match walk_tree(g, tree, args, eta_held(g, *id)).ok()? {
        TreeEnd::Stuck(_, _, Value::Neutral(Head::Var(level, _, _), _)) => Some(level),
        // An `if` or a `match` on a call (`if beats m m then …`) waits for
        // whatever that call waits for.
        TreeEnd::Stuck(_, _, scrutinee @ Value::Neutral(Head::Def(_), _)) => {
            stuck_on_variable(g, &scrutinee)
        }
        _ => None,
    }
}

/// Why call `value` is stuck on a proof, for a note: `value` forced is a
/// definition applied to all its arguments whose case tree stops at a
/// `case` on a proof of a one-constructor proposition that rule S would
/// open (`one_shape`) but for its indices. Returns the proof, the index
/// its type gives and the index the constructor builds, for the first that
/// doesn't agree (`q: Q2 b.n` against `Q2 0`, where `b` is a record that
/// eta took apart, so the variable `b` alone isn't what the call waits for).
/// `None` for anything else. Error path only; it runs in the machine's budget.
pub fn stuck_on_proof_index(g: &Ev, value: &Value) -> Option<(Value, Value, Value)> {
    let value = force(g, value.clone()).ok()?;
    let Value::Neutral(Head::Def(id), spine) = &value else {
        return None;
    };
    let def = g.def(*id);
    let body = body_seen(g, *id)?;
    if spine.len() != def.arity
        || def.arity == 0
        || folds(g, *id)
        || def.lift_leaf
        || def.proof
        || g.env.builtins().native(*id).is_some()
        || g.env.builtins().float_bound(*id)
    {
        return None;
    }
    let mut args = Vec::with_capacity(spine.len());
    for elim in spine.iter() {
        match elim {
            Elim::App(v, _) => args.push(v.clone()),
            Elim::J { .. } | Elim::Proj(..) => return None,
        }
    }
    let tree = Term::peel_lams_rc(body, def.arity);
    let TreeEnd::Stuck(node, env, proof @ Value::Neutral(..)) =
        walk_tree(g, tree, args, eta_held(g, *id)).ok()?
    else {
        return None;
    };
    let Term::Case(ix, d, _) = &*node else {
        return None;
    };
    let data = g.data(*d);
    let [ctor] = &data.ctors[..] else {
        return None;
    };
    if data.sort != Sort::Prop
        || data.indices.is_empty()
        || ctor.field_sorts.iter().any(|s| *s != Sort::Prop)
    {
        return None;
    }
    let level = env.len() - 1 - ix;
    let Value::Data(d2, args) = slot_type(g, *id, &node, &env, level).ok()?? else {
        return None;
    };
    let params = data.params.len();
    if d2 != *d || args.len() != params + ctor.result.len() {
        return None;
    }
    let mut ctor_env = args[..params].to_vec();
    ctor_env.extend((0..ctor.fields.len()).map(|i| project(*d, i, proof.clone())));
    for (k, index) in ctor.result.iter().enumerate() {
        let from_ctor = eval(g, &ctor_env, index).ok()?;
        if !meet_in_evaluation(g, &from_ctor, &args[params + k]).ok()? {
            return Some((proof, args[params + k].clone(), from_ctor));
        }
    }
    None
}

/// Where a case tree, walked with its environment, ends up.
enum TreeEnd {
    /// A `case` stuck on the (forced) neutral scrutinee.
    Stuck(Rc<Term>, Vec<Value>, Value),
    /// A leaf, to evaluate in the environment.
    Leaf(Rc<Term>, Vec<Value>),
    /// Anything else: not compared.
    Other,
}

/// Walks case tree `tree` in `env`, taking every branch a constructor
/// selects, to the first `case` that's stuck or to a leaf. `held` is
/// [`eta_held`] of the tree's definition, as for [`branch`].
fn walk_tree(g: &Ev, mut tree: Rc<Term>, mut env: Vec<Value>, held: bool) -> Result<TreeEnd> {
    loop {
        g.machine.budget.step()?;
        let node = Term::strip_loc_rc(&tree);
        match &*node {
            Term::Case(ix, d, branches) => {
                let unforced = env[env.len() - 1 - ix].clone();
                let scrutinee = tree_scrutinee(g, unforced.clone())?;
                let split = match &scrutinee {
                    // Another type's constructor (ill-typed, as at `branch`)
                    // selects nothing.
                    Value::Ctor(d2, c, fields) if d2 == d => Some((*c, fields.to_vec())),
                    Value::Nat(_) | Value::NatAdd(..) if Some(*d) == g.env.builtins().nat => {
                        native::split_value(&scrutinee)
                    }
                    Value::Chars(chars) => match &g.env.builtins().text {
                        Some(text) if text.list == *d => Some(chars::split(text, chars)),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some((c, fields)) = split {
                    let Some(body) = branches[c].body.clone() else {
                        return Ok(TreeEnd::Other);
                    };
                    env.extend(fields);
                    tree = body;
                    continue;
                }
                match &scrutinee {
                    // Record eta's rule 2, as evaluation takes it (`branch`):
                    // so a tree is compared from where its call is stuck.
                    Value::Neutral(..)
                        if !folded_call(g, &scrutinee) && !held && eta_case(g, *d) =>
                    {
                        let Some(body) = branches[0].body.clone() else {
                            return Ok(TreeEnd::Other);
                        };
                        let k = g.data(*d).ctors[0].fields.len();
                        env.extend(eta_fields(g, *d, k, &unforced, scrutinee.clone())?);
                        tree = body;
                    }
                    Value::Neutral(..) if !folded_call(g, &scrutinee) => {
                        return Ok(TreeEnd::Stuck(node, env, scrutinee));
                    }
                    _ => return Ok(TreeEnd::Other),
                }
            }
            Term::NumCase(..) => return Ok(TreeEnd::Other),
            _ => return Ok(TreeEnd::Leaf(node, env)),
        }
    }
}

/// The head of `value` as a `case` in [`walk_tree`] decides on it (rule E,
/// docs/core.md): forced, and a folded call unfolded (G1), as `branch` sees
/// it after `Frame::Scrutinee`. A folded call that stays stuck is returned
/// as it is. Each unfolding runs in the machine's budget, so this ends.
fn tree_scrutinee(g: &Ev, value: Value) -> Result<Value> {
    let mut value = force(g, value)?;
    while folded_call(g, &value) {
        g.machine.budget.step()?;
        match unfold_folded(g, &value)? {
            Some(next) => value = force(g, next)?,
            None => break,
        }
    }
    Ok(value)
}

/// Whether two calls, each applied to all its arguments and stuck
/// ([`opens_by_tree`] holds for both), are equal: by `arguments` (for two
/// calls of one definition, whether their arguments are equal; `false` for
/// two definitions), or else by their case trees, with `same` comparing
/// values (the scrutinees, then the leaves) by `relation`. A pair already
/// found equal in the same outermost comparison is answered at once, and
/// so is one found different where that answer can't change (see the
/// comment above [`Relation`]). For unification, `settled` says no
/// solution made later can make this pair equal: it mentions no unknown,
/// and the comparison isn't a weakened one. `conv` solves nothing and
/// passes `true`, which counts only when no unification is open around it.
#[allow(clippy::too_many_arguments)]
pub fn same_stuck_trees(
    g: &Ev,
    level: usize,
    a: &Value,
    b: &Value,
    relation: Relation,
    settled: bool,
    arguments: impl FnOnce(CompareAt<'_>) -> Result<bool>,
    same: CompareAt<'_>,
) -> Result<bool> {
    let memo = TreeMemo::enter(g, level, a, b, relation, settled)?;
    if let Some(answer) = memo.known(g)? {
        return Ok(answer);
    }
    // A pair equal by its arguments isn't recorded: a lookup (`known`) walks
    // each recorded pair under its key, so recording every such pair made
    // lookups slow enough to exhaust a small budget where none was needed
    // (SW-2285). Only "different" needs remembering to keep nested calls
    // linear (SW-2269).
    if arguments(same)? {
        return Ok(true);
    }
    let same = same_trees_of_calls(g, level, a, b, same)?;
    memo.record(same);
    Ok(same)
}

/// [`same_trees_of`] for two calls that [`opens_by_tree`]: out of
/// [`same_stuck_trees`]'s frame, which a level of nested calls compared by
/// their arguments goes through.
#[inline(never)]
fn same_trees_of_calls(
    g: &Ev,
    level: usize,
    a: &Value,
    b: &Value,
    same: CompareAt<'_>,
) -> Result<bool> {
    let tree = |value: &Value| -> (Rc<Term>, Vec<Value>, bool) {
        let Value::Neutral(Head::Def(id), spine) = value else {
            unreachable!("checked by opens_by_tree")
        };
        let def = g.def(*id);
        let body = def.body.as_ref().expect("checked by opens_by_tree");
        let args = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => v.clone(),
                Elim::J { .. } | Elim::Proj(..) => unreachable!("checked by opens_by_tree"),
            })
            .collect();
        (Term::peel_lams_rc(body, def.arity), args, eta_held(g, *id))
    };
    same_trees_of(g, level, tree(a), tree(b), same)
}

/// How [`same_stuck_trees`] compares two values at a level.
pub type CompareAt<'a> = &'a mut dyn FnMut(usize, &Value, &Value) -> Result<bool>;

/// [`same_stuck_trees`]'s comparison of the two trees, each with its
/// arguments and [`eta_held`].
fn same_trees_of(
    g: &Ev,
    level: usize,
    (t1, e1, h1): (Rc<Term>, Vec<Value>, bool),
    (t2, e2, h2): (Rc<Term>, Vec<Value>, bool),
    same: &mut dyn FnMut(usize, &Value, &Value) -> Result<bool>,
) -> Result<bool> {
    // The unifier calls this too, outside `conv_with`; the fields'
    // variables are gone when it returns.
    let _restore = RestoreReached(g.machine, g.machine.reached.get());
    // Pairs of subtrees still to compare, each with its level.
    let mut pending = vec![(level, t1, e1, t2, e2)];
    while let Some((level, t1, e1, t2, e2)) = pending.pop() {
        match (walk_tree(g, t1, e1, h1)?, walk_tree(g, t2, e2, h2)?) {
            (TreeEnd::Leaf(t1, e1), TreeEnd::Leaf(t2, e2)) => {
                if !same(level, &eval(g, &e1, &t1)?, &eval(g, &e2, &t2)?)? {
                    return Ok(false);
                }
            }
            (TreeEnd::Stuck(n1, e1, s1), TreeEnd::Stuck(n2, e2, s2)) => {
                let (Term::Case(_, d1, b1), Term::Case(_, d2, b2)) = (&*n1, &*n2) else {
                    unreachable!("a stuck `case`")
                };
                if d1 != d2 || b1.len() != b2.len() {
                    return Ok(false);
                }
                // A `case` with no possible branch on either side never
                // computes, and its scrutinee has an empty type, so the two
                // are equal whatever the scrutinees are (`Void.absurd (p
                // byComputing)` against `myAbsurd (q byComputing)`).
                let impossible = |b: &[Branch]| b.iter().all(|b| b.body.is_none());
                if impossible(b1) && impossible(b2) {
                    continue;
                }
                // The scrutinees of two different definitions needn't have
                // one type: only their data type is known to be the same.
                // For a proposition they are proofs, which rule I would call
                // equal even where they prove different statements (an
                // indexed proposition rule S couldn't fire on, its indices
                // apart), so they aren't handed to the comparison at all:
                // the two `case`s are equal when their branches are, since
                // each call is its one branch whenever its scrutinee exists
                // (docs/proposals/full-proof-irrelevance-audit.md, finding B).
                if g.data(*d1).sort != Sort::Prop && !same(level, &s1, &s2)? {
                    return Ok(false);
                }
                for (c, (x, y)) in b1.iter().zip(b2.iter()).enumerate().rev() {
                    match (&x.body, &y.body) {
                        (None, None) => {}
                        (Some(x), Some(y)) => {
                            let ctor = &g.data(*d1).ctors[c];
                            let k = ctor.fields.len();
                            let next = fresh_past(g, level, k)?;
                            let fresh = (0..k).map(|i| {
                                let mark = ctor
                                    .field_sorts
                                    .get(i)
                                    .map_or(ProofMark::Unknown, |s| ProofMark::of_sort(*s));
                                Value::var_marked(level + i, mark)
                            });
                            let mut e1 = e1.clone();
                            let mut e2 = e2.clone();
                            e1.extend(fresh.clone());
                            e2.extend(fresh);
                            pending.push((next, x.clone(), e1, y.clone(), e2));
                        }
                        _ => return Ok(false),
                    }
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

// Remembering the pairs of calls already found equal (SW-395).
//
// A tree's leaves can call other definitions compared the same way, so one
// comparison can start many more, and they can repeat: when each definition
// calls the next one down in both its branches (`a1 x = match x with | True
// => a0 x | False => a0 x`, and `b1` likewise with `b0`), comparing `a1 x`
// with `b1 x` compares `a0 x` with `b0 x` twice, and a chain of 24 levels on
// each side compared the same 24 pairs 2^24 times (53 s). So, while two trees
// are compared, the pairs of calls found equal are remembered, and a pair
// met again is answered "equal" at once: each pair is compared once, and the
// chain takes a step per level.
//
// Why it can't change an answer: whether two values are equal depends only
// on them, the level and the metavariable solutions, so the same pair at
// the same level gets the same answer while the solutions stand. A pair is
// looked up by exact likeness (`identical`: no evaluation, no unfolding), at
// the same level, by the same relation (`conv`, or the elaborator's
// unification, which share this code but aren't the same relation), and in
// the same `meta_epoch`. Within an epoch solutions are only added, and an
// equality found with fewer solutions still holds with more; taking a
// solution back starts a new epoch, which makes everything remembered before
// it unusable. (The kernel's `conv` solves nothing, and its epoch is 0
// (`NoMetas`).)
//
// Pairs found different are remembered too (SW-2269): a call of one
// definition is compared by its arguments first and then by its tree, whose
// scrutinee is often one of those arguments, so in `pred (pred (… a))`
// against `pred (pred (… b))` each level compared the pair below it twice,
// 2^n comparisons in all. "Different" isn't kept by adding solutions, as
// "equal" is, so it is remembered only where no solution can be made before
// the record is dropped, or none can change the answer: in `conv` when no
// unification is open around it (`conv` solves nothing, and nothing it
// calls unifies), and in unification only for a pair its caller calls
// `settled`, one that mentions no unknown, compared with nothing weakened
// (the unifier's `NO_ETA`). A pair met again is identical, so it mentions
// no unknown either. The record lives as long as the outermost tree
// comparison (the one not inside another) and is dropped when it ends, so
// nothing outlives the query that found it.
//
// Finding a pair costs about its size, not the number of pairs remembered:
// pairs are filed by a hash of their shape (`shape_hash`, which follows the
// same rules as `identical`), and only those with the same hash are compared
// with `identical`. Many calls of the same two definitions with different
// arguments (500 calls of `f0 x [0, …, 0, i]`) made each lookup scan all of
// them before. The hash is only a filing key: a pair is answered "equal" only
// if `identical` says so, so a collision costs a comparison, never a wrong
// answer. A shared part (a list's tail, a call's arguments) is hashed once
// per outermost comparison and then found by its address, so a chain that
// compares `f (f (f … o))` level by level hashes each level once, not the
// whole chain at every level. Hashing takes a budget step per part, so its
// cost is counted like evaluation's.
//
// Considered as well: comparing two definitions with the same content hash
// by their arguments, as for one definition. The kernel keeps no hashes
// (`hash.rs` computes them on demand, by walking the definition); when the
// arguments differed it would still have to fall back on the trees, so as
// not to reject what's accepted now; and it misses chains that are equal in
// value but not in text (`1` at the bottom of one, `0 + 1` of the other),
// which the record handles. So it isn't done.

/// Which comparison a [`same_stuck_trees`] call is part of: remembered
/// equalities are only reused by the same one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Relation {
    /// The kernel's conversion, [`conv`].
    Conv,
    /// The elaborator's unification, which can solve metavariables.
    Unify,
}

/// What [`TreeMemo`] files a pair under: relation, level, metavariable
/// epoch, the two definitions and the [`shape_hash`]es of the two calls.
/// Pairs under one key are told apart by [`identical`], which compares
/// proof marks too: rule I reads them, so two pairs alike but for a
/// variable's mark (a level reused under binders of different types) are
/// not the same pair.
type MemoKey = (Relation, usize, u64, DefId, DefId, u64, u64);

/// This thread's open tree comparisons: how many, how many of them are
/// unification's, the pairs of calls found equal and different since the
/// outermost one started, and the shapes hashed since.
#[derive(Default)]
struct Memo {
    open: usize,
    unifying: usize,
    pairs: HashMap<MemoKey, Vec<(Value, Value)>>,
    different: HashMap<MemoKey, Vec<(Value, Value)>>,
    shapes: ShapeCache,
}

thread_local! {
    /// The [`Memo`] (emptied when the outermost comparison ends).
    static TREE_MEMO: std::cell::RefCell<Memo> = std::cell::RefCell::new(Memo::default());
}

/// One open tree comparison, with the pair it compares and whether a
/// "different" for it may be remembered; dropping it closes the comparison
/// (even on an error).
struct TreeMemo {
    key: MemoKey,
    a: Value,
    b: Value,
    settled: bool,
}

// `enter`, `known`, `record` and `drop` are out of line: they run in
// `same_stuck_trees`, whose frame is one of those a level of nested calls
// compared by their arguments takes.
impl TreeMemo {
    #[inline(never)]
    fn enter(
        g: &Ev,
        level: usize,
        a: &Value,
        b: &Value,
        relation: Relation,
        settled: bool,
    ) -> Result<Box<TreeMemo>> {
        let def = |v: &Value| match v {
            Value::Neutral(Head::Def(id), _) => *id,
            _ => unreachable!("checked by opens_by_tree"),
        };
        let settled = TREE_MEMO.with(|m| {
            let mut m = m.borrow_mut();
            m.open += 1;
            if relation == Relation::Unify {
                m.unifying += 1;
                settled
            } else {
                settled && m.unifying == 0
            }
        });
        // Boxed, so that the frame of `same_stuck_trees`, which holds it
        // while the arguments are compared, stays small.
        let mut memo = Box::new(TreeMemo {
            key: (relation, level, g.metas.epoch(), def(a), def(b), 0, 0),
            a: a.clone(),
            b: b.clone(),
            settled,
        });
        if !shortcuts_disabled() {
            let (ha, hb) = TREE_MEMO.with(|m| -> Result<(u64, u64)> {
                let shapes = &mut m.borrow_mut().shapes;
                Ok((shape_hash(g, shapes, a)?, shape_hash(g, shapes, b)?))
            })?;
            memo.key.5 = ha;
            memo.key.6 = hb;
        }
        Ok(memo)
    }

    /// Whether this pair was already found equal (`Some(true)`) or
    /// different (`Some(false)`). Telling the pairs filed under the key
    /// apart costs a budget step per layer compared ([`identical_charged`]):
    /// a key can collect many pairs, each walked on every lookup.
    #[inline(never)]
    fn known(&self, g: &Ev) -> Result<Option<bool>> {
        if shortcuts_disabled() {
            return Ok(None);
        }
        let among = |pairs: &HashMap<MemoKey, Vec<(Value, Value)>>| -> Result<bool> {
            for (x, y) in pairs.get(&self.key).into_iter().flatten() {
                if identical_charged(g, Same::Values(x, &self.a))?
                    && identical_charged(g, Same::Values(y, &self.b))?
                {
                    return Ok(true);
                }
            }
            Ok(false)
        };
        TREE_MEMO.with(|m| {
            let m = m.borrow();
            Ok(if among(&m.pairs)? {
                Some(true)
            } else if among(&m.different)? {
                Some(false)
            } else {
                None
            })
        })
    }

    /// Remembers that this pair is equal, or different where that can't
    /// change.
    #[inline(never)]
    fn record(&self, equal: bool) {
        if shortcuts_disabled() || !(equal || self.settled) {
            return;
        }
        TREE_MEMO.with(|m| {
            let mut m = m.borrow_mut();
            let pairs = if equal {
                &mut m.pairs
            } else {
                &mut m.different
            };
            pairs
                .entry(self.key)
                .or_default()
                .push((self.a.clone(), self.b.clone()));
        });
    }
}

impl Drop for TreeMemo {
    #[inline(never)]
    fn drop(&mut self) {
        TREE_MEMO.with(|m| {
            let mut m = m.borrow_mut();
            m.open -= 1;
            if self.key.0 == Relation::Unify {
                m.unifying -= 1;
            }
            if m.open == 0 {
                // Moved out first: dropping the values must not find the
                // memo borrowed.
                let old = std::mem::take(&mut *m);
                drop(m);
                drop(old);
            }
        });
    }
}

/// Pairs of values remembered by their shapes, as [`TreeMemo`] remembers
/// them, for a caller of its own: the elaborator's record of pairs of
/// calls found different (`CallMemo` in its `unify.rs`). A pair is filed
/// under the caller's key `K` and the [`shape_hash`]es of its two sides,
/// and is found again only by a pair [`identical`] to it, side by side, so
/// one rebuilt (a call in a closure's body, evaluated again under the same
/// binder) is found where its address would not be. The values are kept,
/// and the shapes hashed, for as long as the memo lives.
pub struct ShapeMemo<K> {
    shapes: ShapeCache,
    pairs: HashMap<ShapeKey<K>, Vec<(Value, Value)>>,
}

/// Where a pair is filed in a [`ShapeMemo`]: the caller's key and the two
/// sides' shape hashes.
pub type ShapeKey<K> = (K, u64, u64);

impl<K> Default for ShapeMemo<K> {
    fn default() -> Self {
        ShapeMemo {
            shapes: ShapeCache::default(),
            pairs: HashMap::default(),
        }
    }
}

impl<K: std::hash::Hash + Eq> ShapeMemo<K> {
    /// Where `a` against `b` is filed under `key`: hashes both, a budget
    /// step per part not hashed before. With the shortcuts off nothing is
    /// hashed, as nothing is filed (see [`ShapeMemo::insert`]).
    pub fn file(&mut self, g: &Ev, key: K, a: &Value, b: &Value) -> Result<ShapeKey<K>> {
        if shortcuts_disabled() {
            return Ok((key, 0, 0));
        }
        let ha = shape_hash(g, &mut self.shapes, a)?;
        let hb = shape_hash(g, &mut self.shapes, b)?;
        Ok((key, ha, hb))
    }

    /// Whether a pair identical to `a` against `b` is filed at `at`: a
    /// budget step per layer compared, as for [`TreeMemo`]'s lookups.
    pub fn contains(&self, g: &Ev, at: &ShapeKey<K>, a: &Value, b: &Value) -> Result<bool> {
        if shortcuts_disabled() {
            return Ok(false);
        }
        for (x, y) in self.pairs.get(at).into_iter().flatten() {
            if identical_charged(g, Same::Values(x, a))?
                && identical_charged(g, Same::Values(y, b))?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Files `a` against `b` at `at`. With the shortcuts off this keeps
    /// nothing, as [`TreeMemo`] keeps nothing: the memo is never consulted
    /// then, and a comparison it would have cut short (about 2ⁿ pairs for
    /// `n` nested calls) would otherwise keep every pair, and every value
    /// hashed, until it ends.
    pub fn insert(&mut self, at: ShapeKey<K>, a: &Value, b: &Value) {
        if shortcuts_disabled() {
            return;
        }
        self.pairs
            .entry(at)
            .or_default()
            .push((a.clone(), b.clone()));
    }
}

/// A part of a value to hash for [`shape_hash`]. The ones that are a shared
/// allocation (all but `Value`) are remembered by address in a
/// [`ShapeCache`].
#[derive(Clone, Copy)]
enum Part<'v> {
    Value(&'v Value),
    Boxed(&'v Shared),
    Fields(&'v Values),
    Spine(&'v Spine),
    Closure(&'v Closure),
    Term(&'v Rc<Term>),
}

/// The hashes of the shared allocations already hashed, by address, for
/// the rest of the outermost tree comparison: a value nested in the next
/// one compared (a chain `f (f (f … o))`, compared level by level) is then
/// hashed once, not once per level.
#[derive(Default)]
struct ShapeCache {
    hashes: HashMap<(usize, usize), u64>,
    /// The allocations hashed, kept alive while their addresses are keys,
    /// so no other can be allocated at one.
    owners: Vec<Owner>,
}

/// A handle on a shared allocation, only held to keep it alive.
#[allow(dead_code)]
enum Owner {
    Boxed(Shared),
    Fields(Values),
    Spine(Spine),
    Closure(Closure),
    Term(Rc<Term>),
}

impl Part<'_> {
    /// The address this part is remembered by, if it's a shared allocation.
    fn address(self) -> Option<(usize, usize)> {
        let at = |p: *const u8| p as usize;
        match self {
            Part::Value(_) => None,
            Part::Boxed(v) => Some((at(Rc::as_ptr(v.rc()).cast()), 0)),
            Part::Fields(f) => Some((at(Rc::as_ptr(&f.0).cast()), 0)),
            Part::Spine(s) => s.0.as_ref().map(|e| (at(Rc::as_ptr(e).cast()), 0)),
            // A closure's hash depends on its body and its environment.
            Part::Closure(c) => Some((
                at(Rc::as_ptr(&c.env.0).cast()),
                at(Rc::as_ptr(&c.body).cast()),
            )),
            Part::Term(t) => Some((at(Rc::as_ptr(t).cast()), 0)),
        }
    }

    /// A handle on the allocation, to keep it alive.
    fn owner(self) -> Owner {
        match self {
            Part::Value(_) => unreachable!("not shared"),
            Part::Boxed(v) => Owner::Boxed(v.clone()),
            Part::Fields(f) => Owner::Fields(f.clone()),
            Part::Spine(s) => Owner::Spine(s.clone()),
            Part::Closure(c) => Owner::Closure(c.clone()),
            Part::Term(t) => Owner::Term(t.clone()),
        }
    }
}

/// A hash of `value`'s shape, for filing it among remembered pairs. It
/// follows [`identical`]'s rules, so identical values hash alike: names and
/// source locations are left out, and a closure hashes as its body and the
/// values of the variables the body uses. A glued call ([`Value::Call`])
/// hashes as its definition and spine, not its unfolding cell: `identical`
/// compares two calls with different cells by definition and spine, and two
/// with the same cell have the same definition and spine too, since a cell
/// is only ever made with its call (a field of a call, [`project_call`], gets
/// a new one). Hashing every call alike would file all pairs that differ only
/// inside glued calls under one key, for every lookup to walk (SW-2308).
/// Built bottom-up, each
/// layer from its own data and its parts' hashes, so a shared allocation is
/// hashed once ([`ShapeCache`]). A work list, as values can nest deeply; a
/// budget step per part hashed.
fn shape_hash(g: &Ev, cache: &mut ShapeCache, value: &Value) -> Result<u64> {
    use std::hash::{Hash, Hasher};
    enum Task<'v> {
        Enter(Part<'v>),
        /// Combine the layer's own hash with its `parts` hashes, the last
        /// ones on the result stack.
        Exit(Part<'v>, u64, usize),
    }
    let mut work = vec![Task::Enter(Part::Value(value))];
    let mut results: Vec<u64> = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Task::Enter(part) => {
                if let Some(hash) = part.address().and_then(|a| cache.hashes.get(&a)) {
                    results.push(*hash);
                    continue;
                }
                g.machine.budget.step()?;
                let mut h = QuickHasher::default();
                let mut parts: Vec<Part> = Vec::new();
                match part {
                    Part::Value(v) => {
                        std::mem::discriminant(v).hash(&mut h);
                        match v {
                            Value::Sort(s) => s.hash(&mut h),
                            Value::Pi(_, i, a, b, _) => {
                                i.hash(&mut h);
                                parts.extend([Part::Boxed(a), Part::Closure(b)]);
                            }
                            Value::Lam(_, i, b, _) => {
                                i.hash(&mut h);
                                parts.push(Part::Closure(b));
                            }
                            Value::Data(d, args) => {
                                (d, args.len()).hash(&mut h);
                                parts.extend(args.iter().map(Part::Value));
                            }
                            Value::Ctor(d, c, fields) => {
                                (d, c).hash(&mut h);
                                parts.push(Part::Fields(fields));
                            }
                            Value::Nat(n) => n.hash(&mut h),
                            Value::NatAdd(k, x) => {
                                k.hash(&mut h);
                                parts.push(Part::Boxed(x));
                            }
                            Value::Chars(chars) => chars.as_slice().hash(&mut h),
                            Value::Eq(t, x, y) => {
                                parts.extend([Part::Boxed(t), Part::Boxed(x), Part::Boxed(y)]);
                            }
                            Value::Refl => {}
                            Value::Call(id, spine, _) => {
                                id.hash(&mut h);
                                parts.push(Part::Spine(spine));
                            }
                            Value::Resumption(r) => Rc::as_ptr(r).hash(&mut h),
                            Value::Neutral(head, spine) => {
                                head.hash(&mut h);
                                parts.push(Part::Spine(spine));
                            }
                        }
                    }
                    Part::Boxed(v) => parts.push(Part::Value(v)),
                    Part::Fields(fields) => {
                        fields.len().hash(&mut h);
                        parts.extend(fields.iter().map(Part::Value));
                    }
                    Part::Spine(spine) => {
                        spine.len().hash(&mut h);
                        for elim in spine.iter() {
                            match elim {
                                Elim::App(x, i) => {
                                    (0u8, i).hash(&mut h);
                                    parts.push(Part::Value(x));
                                }
                                Elim::J { motive, base, .. } => {
                                    1u8.hash(&mut h);
                                    parts.extend([Part::Value(motive), Part::Value(base)]);
                                }
                                Elim::Proj(d, i) => (2u8, d, i).hash(&mut h),
                            }
                        }
                    }
                    Part::Closure(c) => {
                        parts.push(Part::Term(&c.body));
                        for ix in free_variables(&c.body) {
                            if ix == 0 {
                                continue;
                            }
                            ix.hash(&mut h);
                            if ix <= c.env.len() {
                                parts.push(Part::Value(&c.env[c.env.len() - ix]));
                            }
                        }
                    }
                    Part::Term(t) => {
                        let t = t.strip_loc();
                        std::mem::discriminant(t).hash(&mut h);
                        match t {
                            Term::Var(i) => i.hash(&mut h),
                            Term::Def(i) => i.hash(&mut h),
                            Term::Meta(i) => i.hash(&mut h),
                            Term::Sort(s) => s.hash(&mut h),
                            Term::Nat(n) => n.hash(&mut h),
                            Term::Chars(chars) => chars.as_slice().hash(&mut h),
                            Term::Refl => {}
                            Term::Data(d, xs) => {
                                (d, xs.len()).hash(&mut h);
                                parts.extend(xs.iter().map(Part::Term));
                            }
                            Term::Ctor(d, c, xs) => {
                                (d, c, xs.len()).hash(&mut h);
                                parts.extend(xs.iter().map(Part::Term));
                            }
                            Term::Pi(_, i, a, b, _) => {
                                i.hash(&mut h);
                                parts.extend([Part::Term(a), Part::Term(b)]);
                            }
                            Term::Lam(_, i, b, _) => {
                                i.hash(&mut h);
                                parts.push(Part::Term(b));
                            }
                            Term::App(f, a, i) => {
                                i.hash(&mut h);
                                parts.extend([Part::Term(f), Part::Term(a)]);
                            }
                            Term::Ann(e, ty) => parts.extend([Part::Term(e), Part::Term(ty)]),
                            Term::Let(_, ty, v, b, s, _) => {
                                s.hash(&mut h);
                                parts.extend([Part::Term(ty), Part::Term(v), Part::Term(b)]);
                            }
                            Term::Eq(ty, x, y) => {
                                ty.is_some().hash(&mut h);
                                parts.extend(ty.iter().map(Part::Term));
                                parts.extend([Part::Term(x), Part::Term(y)]);
                            }
                            Term::J(m, b, p, _) => {
                                parts.extend([Part::Term(m), Part::Term(b), Part::Term(p)]);
                            }
                            Term::Proj(d, i, t) => {
                                (d, i).hash(&mut h);
                                parts.push(Part::Term(t));
                            }
                            Term::Quot(f, xs, e, _) => {
                                (f, e, xs.len()).hash(&mut h);
                                parts.extend(xs.iter().map(Part::Term));
                            }
                            Term::Case(i, d, branches) => {
                                (i, d, branches.len()).hash(&mut h);
                                for branch in branches.iter() {
                                    (branch.names.len(), branch.body.is_some()).hash(&mut h);
                                    parts.extend(branch.body.iter().map(Part::Term));
                                }
                            }
                            Term::NumCase(i, arms, default) => {
                                (i, arms.len()).hash(&mut h);
                                for arm in arms.iter() {
                                    arm.value.hash(&mut h);
                                    parts.push(Part::Term(&arm.body));
                                }
                                parts.push(Part::Term(default));
                            }
                            // Never identical to anything (`same_term_layer`).
                            _ => {}
                        }
                    }
                }
                work.push(Task::Exit(part, h.finish(), parts.len()));
                work.extend(parts.into_iter().rev().map(Task::Enter));
            }
            Task::Exit(part, own, count) => {
                let mut h = QuickHasher::default();
                own.hash(&mut h);
                for hash in results.drain(results.len() - count..) {
                    hash.hash(&mut h);
                }
                let hash = h.finish();
                if let Some(address) = part.address() {
                    cache.hashes.insert(address, hash);
                    cache.owners.push(part.owner());
                }
                results.push(hash);
            }
        }
    }
    Ok(results.pop().expect("the value's hash"))
}

// Recognising the same function without running it.
//
// Comparing two functions applies both to a fresh variable and compares the
// results, which runs their bodies: for a lambda in a proposition, like
// `n => keepIf (repeated r k n) (plus n)` in a sum over 2 to 10, that can be
// most of the work. When the two closures are *identical* (the same body, and
// the same values for the variables it uses), so are the results, and
// conversion is reflexive, so the comparison can answer "equal" at once.
// That's the whole argument: identity here is exact likeness of
// representation (no evaluation, no unfolding, no `3` against `Succ 2`), so
// whatever running the two bodies could observe, it would observe the same in
// both. When the closures aren't identical, nothing is concluded and the
// comparison runs as before; so this can only skip work that would have
// answered "equal", never change an answer, only whether the comparison
// runs out of resources: the walk costs a budget step per pair of parts it
// compares, each pair of shared parts once (`identical_within`).
//
// The elaborator's unification (`crates/elab/src/unify.rs`) uses it too:
// unifying identical values succeeds without solving any metavariable (a
// metavariable against itself only unifies the identical arguments), so
// answering at once changes nothing there either.
//
// There, a solved metavariable is the value it was solved with: a closure
// whose environment holds `?x`, solved with `seed`, and one holding `seed`
// itself are the same function (SW-920: without this, unification ran both
// bodies, which with `%` on a large number is most of a check). So the
// elaborator's form, [`same_closure_solved`], compares a solved
// metavariable by its solution, where the two sides would otherwise differ.
// That is still no evaluation of either body, and both sides are equal
// under the solutions made, which unification never takes back without
// undoing the comparison too.

#[cfg(any(test, feature = "reference"))]
thread_local! {
    static SHORTCUTS_OFF: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Turns the identical-closure shortcut of [`conv`] (and of the elaborator's
/// unification), and the record of pairs of calls found equal
/// ([`same_stuck_trees`]), and the kernel's comparison of two glued calls
/// by their arguments first ([`CallMemo`]), and the records of a
/// [`ShapeMemo`] (the elaborator's pairs of calls found different), off,
/// or back on, on this thread: for tests comparing the verdicts with and
/// without them.
#[cfg(any(test, feature = "reference"))]
pub fn set_shortcuts_disabled(disabled: bool) {
    SHORTCUTS_OFF.with(|s| s.set(disabled));
}

#[inline]
pub(crate) fn shortcuts_disabled() -> bool {
    #[cfg(any(test, feature = "reference"))]
    {
        SHORTCUTS_OFF.with(|s| s.get())
    }
    #[cfg(not(any(test, feature = "reference")))]
    {
        false
    }
}

/// Whether closures `a` and `b` are identical: the same body term (ignoring
/// names and source locations) and, for each variable it uses from its
/// environment, identical values. Variables the body doesn't use can differ:
/// they're never looked at. A budget step per pair of parts compared
/// ([`identical_within`]); running out is an error, never "different".
pub fn same_closure(g: &Ev, a: &Closure, b: &Closure) -> Result<bool> {
    if shortcuts_disabled() {
        return Ok(false);
    }
    identical_within(Same::Closures(a, b), None, Some(g))
}

/// [`same_closure`], with a solved metavariable alike to its solution: where
/// a value headed by one differs from the value on the other side, it is
/// compared again with the solution applied. For the elaborator.
pub fn same_closure_solved(g: &Ev, a: &Closure, b: &Closure) -> Result<bool> {
    if shortcuts_disabled() {
        return Ok(false);
    }
    identical_within(Same::Closures(a, b), Some(g), Some(g))
}

/// Whether `a` and `b`, which differ as they are, are alike once a solved
/// metavariable heading either is replaced by its solution
/// ([`identical_within`] with `g`), charging `charge` as [`identical_within`] does. `false` if
/// neither is headed by one, or if applying a solution runs out of
/// resources (the caller then takes the long way, which reports that).
#[cold]
#[inline(never)]
fn same_when_solved(g: &Ev, a: &Value, b: &Value, charge: Option<&Ev>) -> Result<bool> {
    let solved =
        |v: &Value| matches!(v, Value::Neutral(Head::Meta(m), _) if g.meta_solution(*m).is_some());
    if !solved(a) && !solved(b) {
        return Ok(false);
    }
    let (Ok(a), Ok(b)) = (force_solved(g, a.clone()), force_solved(g, b.clone())) else {
        return Ok(false);
    };
    identical_within(Same::Values(&a, &b), Some(g), charge)
}

/// Whether two values are exactly alike ([`same_closure`]'s notion), uncharged
/// and without evaluating anything: alike values convert.
pub fn same_value(a: &Value, b: &Value) -> bool {
    !shortcuts_disabled() && identical(Same::Values(a, b))
}

/// Whether two terms are alike apart from names and source locations, as
/// [`same_closure`] compares bodies. The elaborator uses it to find the
/// same recursive call written twice (`crates/elab/src/decreasing.rs`).
pub fn same_term(a: &Term, b: &Term) -> bool {
    identical(Same::Terms(a, b))
}

/// A pair still to compare for [`identical`].
enum Same<'v> {
    Values(&'v Value, &'v Value),
    Closures(&'v Closure, &'v Closure),
    Terms(&'v Term, &'v Term),
}

impl Same<'_> {
    /// What the pair is and where its two sides are, for
    /// [`identical_within`]'s record of pairs compared.
    fn addresses(&self) -> (u8, usize, usize) {
        fn at<T>(x: &T) -> usize {
            std::ptr::from_ref(x) as usize
        }
        match self {
            Same::Values(a, b) => (0, at(*a), at(*b)),
            Same::Closures(a, b) => (1, at(*a), at(*b)),
            Same::Terms(a, b) => (2, at(*a), at(*b)),
        }
    }
}

/// How many pairs [`identical_within`] compares before it starts recording
/// them: most comparisons are smaller, and a record would only slow them.
const IDENTICAL_UNRECORDED: usize = 64;

/// Whether two values, closures or terms are exactly alike (see
/// [`same_closure`]), uncharged: for [`same_term`], whose callers have no
/// budget. No evaluation; the cost is as for [`identical_within`].
fn identical(first: Same) -> bool {
    identical_within(first, None, None).unwrap_or(false)
}

/// [`identical`] at a budget step per pair of layers compared, for the
/// memos' lookups, which may walk many recorded pairs. Solved
/// metavariables aren't looked through, as with `identical`'s `None`.
fn identical_charged(g: &Ev, first: Same) -> Result<bool> {
    identical_within(first, None, Some(g))
}

/// [`identical`], charging a step per pair of layers to `charge`'s budget
/// where given (and so failing only when that runs out).
///
/// Values, closures' environments and terms share parts, so walked as trees
/// they can be exponentially larger than they are in memory: a value built
/// by doubling `n` times is `n` cells but `2ⁿ` paths (SW-2730: one
/// comparison walked millions of pairs). So once a walk is past
/// [`IDENTICAL_UNRECORDED`] pairs, each pair of parts compared is recorded
/// by the two addresses, and a pair met again is skipped: the answer is the
/// conjunction over all pairs, and a pair at the same two addresses is the
/// same two parts, borrowed and so unchanged for the whole walk, with the
/// same answer. Skipping one can't turn "different" into "alike". The cost
/// is then at most the number of distinct pairs of parts reached, which is
/// at most the smaller side's size as a tree, and about its size in memory
/// where both sides share alike.
fn identical_within(first: Same, g: Option<&Ev>, charge: Option<&Ev>) -> Result<bool> {
    let mut work = vec![first];
    let mut walked = 0usize;
    let mut seen: HashSet<(u8, usize, usize)> = HashSet::default();
    while let Some(pair) = work.pop() {
        if let Some(charge) = charge {
            charge.machine.budget.step()?;
        }
        walked += 1;
        if walked > IDENTICAL_UNRECORDED && !seen.insert(pair.addresses()) {
            continue;
        }
        let alike = match pair {
            Same::Values(a, b) => {
                let len = work.len();
                same_layer(a, b, &mut work)
                    || match g {
                        Some(g) => {
                            work.truncate(len);
                            same_when_solved(g, a, b, charge)?
                        }
                        None => false,
                    }
            }
            Same::Closures(a, b) => same_closure_layer(a, b, &mut work),
            Same::Terms(a, b) => same_term_layer(a, b, &mut work),
        };
        if !alike {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Compares two closures for [`identical`]: pushes their bodies and the
/// values of the variables the body uses.
fn same_closure_layer<'v>(a: &'v Closure, b: &'v Closure, work: &mut Vec<Same<'v>>) -> bool {
    let same_body = Rc::ptr_eq(&a.body, &b.body);
    if same_body && Rc::ptr_eq(&a.env.0, &b.env.0) {
        return true;
    }
    if !same_body {
        work.push(Same::Terms(&a.body, &b.body));
    }
    // Variable `ix` of the body is `env[len - ix]`: index 0 is the closure's
    // own parameter, the same fresh variable on both sides. (If the bodies
    // turn out to differ, these pairs are never needed; they're only looked
    // at if everything else matches.)
    let (x, y) = (&a.env, &b.env);
    for ix in free_variables(&a.body) {
        if ix == 0 {
            continue;
        }
        if ix > x.len() || ix > y.len() {
            return false;
        }
        work.push(Same::Values(&x[x.len() - ix], &y[y.len() - ix]));
    }
    true
}

/// The free variables of `term` (de Bruijn indices), each once.
fn free_variables(term: &Term) -> Vec<usize> {
    let mut free: Vec<usize> = term
        .subterms()
        .filter_map(|(t, binders)| match t {
            Term::Var(i) | Term::Case(i, ..) | Term::NumCase(i, ..) if *i >= binders => {
                Some(*i - binders)
            }
            _ => None,
        })
        .collect();
    free.sort_unstable();
    free.dedup();
    free
}

/// Whether two proof marks can belong to one binder: equal, or one not
/// known. [`identical`] compares marks because rule I reads them: within
/// one comparison a level can be a proof under one pair of binders and data
/// under another, and a memo keyed by `identical` must not answer for one
/// with what it found for the other (the SW-4671 review's F4). An unknown
/// mark (the elaborator's) agrees with either: rule I doesn't fire on it,
/// so an answer found with it holds, or only misses an equality, with a
/// known one.
fn marks_agree(a: ProofMark, b: ProofMark) -> bool {
    a == b || a == ProofMark::Unknown || b == ProofMark::Unknown
}

/// [`marks_agree`] for two heads already equal: a variable's mark. A
/// quotient form's mark is a function of the form and its arguments.
fn head_marks_agree(a: &Head, b: &Head) -> bool {
    match (a, b) {
        (Head::Var(_, _, m1), Head::Var(_, _, m2)) => marks_agree(*m1, *m2),
        _ => true,
    }
}

/// Compares the outermost layer of two values for [`identical`], pushing
/// their parts.
fn same_layer<'v>(a: &'v Value, b: &'v Value, work: &mut Vec<Same<'v>>) -> bool {
    let rc_values = |work: &mut Vec<Same<'v>>, x: &'v Shared, y: &'v Shared| {
        if !Shared::ptr_eq(x, y) {
            work.push(Same::Values(x, y));
        }
    };
    let all = |work: &mut Vec<Same<'v>>, xs: &'v [Value], ys: &'v [Value]| {
        work.extend(xs.iter().zip(ys).map(|(x, y)| Same::Values(x, y)));
    };
    match (a, b) {
        (Value::Sort(s), Value::Sort(t)) => s == t,
        (Value::Pi(_, i1, a1, b1, m1), Value::Pi(_, i2, a2, b2, m2)) => {
            rc_values(work, a1, a2);
            work.push(Same::Closures(b1, b2));
            i1 == i2 && marks_agree(*m1, *m2)
        }
        (Value::Lam(_, i1, b1, m1), Value::Lam(_, i2, b2, m2)) => {
            work.push(Same::Closures(b1, b2));
            i1 == i2 && marks_agree(*m1, *m2)
        }
        (Value::Data(d1, a1), Value::Data(d2, a2)) => {
            all(work, a1, a2);
            d1 == d2 && a1.len() == a2.len()
        }
        (Value::Ctor(d1, c1, f1), Value::Ctor(d2, c2, f2)) => {
            if !Rc::ptr_eq(&f1.0, &f2.0) {
                all(work, f1, f2);
            }
            d1 == d2 && c1 == c2 && f1.len() == f2.len()
        }
        (Value::Nat(m), Value::Nat(n)) => m == n,
        (Value::NatAdd(k1, x1), Value::NatAdd(k2, x2)) => {
            rc_values(work, x1, x2);
            k1 == k2
        }
        (Value::Chars(x), Value::Chars(y)) => x.as_slice() == y.as_slice(),
        (Value::Eq(t1, x1, y1), Value::Eq(t2, x2, y2)) => {
            rc_values(work, t1, t2);
            rc_values(work, x1, x2);
            rc_values(work, y1, y2);
            true
        }
        (Value::Refl, Value::Refl) => true,
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) => {
            if h1 != h2 || !head_marks_agree(h1, h2) {
                return false;
            }
            if s1.ptr_eq(s2) {
                return true;
            }
            if s1.len() != s2.len() {
                return false;
            }
            for pair in s1.iter().zip(s2) {
                match pair {
                    (Elim::App(x, i1), Elim::App(y, i2)) if i1 == i2 => {
                        work.push(Same::Values(x, y));
                    }
                    (
                        Elim::J {
                            motive: m1,
                            base: b1,
                            ends: e1,
                            result: r1,
                        },
                        Elim::J {
                            motive: m2,
                            base: b2,
                            ends: e2,
                            result: r2,
                        },
                    ) => {
                        // The ends too: a cast's proof is skipped by rule I,
                        // so two casts alike in all but their ends needn't
                        // be the same cast.
                        match (e1, e2) {
                            (Some(e1), Some(e2)) => {
                                work.push(Same::Values(&e1.ty, &e2.ty));
                                work.push(Same::Values(&e1.x, &e2.x));
                                work.push(Same::Values(&e1.y, &e2.y));
                            }
                            (None, None) => {}
                            _ => return false,
                        }
                        if !marks_agree(*r1, *r2) {
                            return false;
                        }
                        work.push(Same::Values(m1, m2));
                        work.push(Same::Values(b1, b2));
                    }
                    (Elim::Proj(d1, i1), Elim::Proj(d2, i2)) if d1 == d2 && i1 == i2 => {}
                    (Elim::App(..) | Elim::J { .. } | Elim::Proj(..), _) => return false,
                }
            }
            true
        }
        (Value::Call(i1, s1, u1), Value::Call(i2, s2, u2)) => {
            if Rc::ptr_eq(u1, u2) {
                return true;
            }
            if i1 != i2 || s1.len() != s2.len() {
                return false;
            }
            for pair in s1.iter().zip(s2) {
                match pair {
                    (Elim::App(x, i1), Elim::App(y, i2)) if i1 == i2 => {
                        work.push(Same::Values(x, y));
                    }
                    (Elim::Proj(d1, j1), Elim::Proj(d2, j2)) if d1 == d2 && j1 == j2 => {}
                    (Elim::App(..) | Elim::J { .. } | Elim::Proj(..), _) => return false,
                }
            }
            true
        }
        // Every other pair differs; listed by the left side so that a new kind
        // of value is a compile error here.
        (
            Value::Sort(_)
            | Value::Pi(..)
            | Value::Lam(..)
            | Value::Data(..)
            | Value::Ctor(..)
            | Value::Nat(_)
            | Value::NatAdd(..)
            | Value::Chars(_)
            | Value::Eq(..)
            | Value::Refl
            | Value::Neutral(..)
            | Value::Call(..)
            | Value::Resumption(_),
            _,
        ) => false,
    }
}

/// Compares the outermost layer of two terms for [`identical`], pushing
/// their parts. Names and source locations are ignored, as evaluation
/// ignores them; everything else must match.
fn same_term_layer<'v>(a: &'v Term, b: &'v Term, work: &mut Vec<Same<'v>>) -> bool {
    let mut both = |x: &'v Rc<Term>, y: &'v Rc<Term>| {
        if !Rc::ptr_eq(x, y) {
            work.push(Same::Terms(x, y));
        }
    };
    match (a.strip_loc(), b.strip_loc()) {
        (Term::Var(i), Term::Var(j)) => i == j,
        (Term::Def(i), Term::Def(j)) => i == j,
        (Term::Meta(i), Term::Meta(j)) => i == j,
        (Term::Sort(s), Term::Sort(t)) => s == t,
        (Term::Nat(m), Term::Nat(n)) => m == n,
        (Term::Chars(x), Term::Chars(y)) => x.as_slice() == y.as_slice(),
        (Term::Refl, Term::Refl) => true,
        (Term::Data(d1, xs), Term::Data(d2, ys)) => {
            if d1 != d2 || xs.len() != ys.len() {
                return false;
            }
            xs.iter().zip(ys).for_each(|(x, y)| both(x, y));
            true
        }
        (Term::Ctor(d1, c1, xs), Term::Ctor(d2, c2, ys)) => {
            if d1 != d2 || c1 != c2 || xs.len() != ys.len() {
                return false;
            }
            xs.iter().zip(ys).for_each(|(x, y)| both(x, y));
            true
        }
        (Term::Pi(_, i1, a1, b1, m1), Term::Pi(_, i2, a2, b2, m2)) => {
            both(a1, a2);
            both(b1, b2);
            i1 == i2 && marks_agree(*m1, *m2)
        }
        (Term::Lam(_, i1, b1, m1), Term::Lam(_, i2, b2, m2)) => {
            both(b1, b2);
            i1 == i2 && marks_agree(*m1, *m2)
        }
        (Term::App(f1, a1, i1), Term::App(f2, a2, i2)) => {
            both(f1, f2);
            both(a1, a2);
            i1 == i2
        }
        (Term::Ann(e1, t1), Term::Ann(e2, t2)) => {
            both(e1, e2);
            both(t1, t2);
            true
        }
        (Term::Let(_, t1, v1, b1, s1, m1), Term::Let(_, t2, v2, b2, s2, m2)) => {
            both(t1, t2);
            both(v1, v2);
            both(b1, b2);
            s1 == s2 && marks_agree(*m1, *m2)
        }
        (Term::Eq(t1, x1, y1), Term::Eq(t2, x2, y2)) => {
            match (t1, t2) {
                (Some(t1), Some(t2)) => both(t1, t2),
                (None, None) => {}
                _ => return false,
            }
            both(x1, x2);
            both(y1, y2);
            true
        }
        (Term::J(m1, b1, p1, r1), Term::J(m2, b2, p2, r2)) => {
            both(m1, m2);
            both(b1, b2);
            both(p1, p2);
            marks_agree(*r1, *r2)
        }
        (Term::Proj(d1, i1, t1), Term::Proj(d2, i2, t2)) => {
            if d1 != d2 || i1 != i2 {
                return false;
            }
            both(t1, t2);
            true
        }
        (Term::Quot(f1, xs, e1, _), Term::Quot(f2, ys, e2, _)) => {
            if f1 != f2 || e1 != e2 || xs.len() != ys.len() {
                return false;
            }
            xs.iter().zip(ys).for_each(|(x, y)| both(x, y));
            true
        }
        (Term::Case(i1, d1, br1), Term::Case(i2, d2, br2)) => {
            if i1 != i2 || d1 != d2 || br1.len() != br2.len() {
                return false;
            }
            if !Rc::ptr_eq(br1, br2) {
                for (x, y) in br1.iter().zip(br2.iter()) {
                    match (&x.body, &y.body) {
                        _ if x.names.len() != y.names.len() => return false,
                        (Some(a), Some(b)) => both(a, b),
                        (None, None) => {}
                        _ => return false,
                    }
                }
            }
            true
        }
        (Term::NumCase(i1, a1, d1), Term::NumCase(i2, a2, d2)) => {
            if i1 != i2 || a1.len() != a2.len() {
                return false;
            }
            if !Rc::ptr_eq(a1, a2) {
                for (x, y) in a1.iter().zip(a2.iter()) {
                    if x.value != y.value {
                        return false;
                    }
                    both(&x.body, &y.body);
                }
            }
            both(d1, d2);
            true
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Icit;

    fn rc(t: Term) -> Rc<Term> {
        Rc::new(t)
    }

    /// `f x`, with `f` the closure's environment's last value and `x` its
    /// parameter.
    fn call_last() -> Term {
        Term::App(rc(Term::Var(1)), rc(Term::Var(0)), Icit::Explicit)
    }

    /// Fresh variables stop below the marker levels at the top of `usize`.
    #[test]
    fn fresh_levels_stop_below_the_markers() {
        assert_eq!(next_level(LEVEL_CAP - 1, 1), Some(LEVEL_CAP));
        assert_eq!(next_level(LEVEL_CAP, 1), None);
        assert_eq!(next_level(LEVEL_CAP - 2, 3), None);
        assert_eq!(next_level(usize::MAX, 1), None);
        const { assert!(LEVEL_CAP < DUMMY_LEVEL && LEVEL_CAP < crate::erase::ERASED) };
    }

    fn closure(env: Vec<Value>, body: Term) -> Closure {
        Closure {
            env: env.into(),
            body: rc(body),
        }
    }

    fn lam(c: Closure) -> Value {
        Value::Lam("x".into(), Icit::Explicit, c, ProofMark::Unknown)
    }

    /// [`same_closure`] with a kernel's default budget.
    fn same(a: &Closure, b: &Closure) -> bool {
        let g = crate::globals::Kernel::default();
        same_closure(&g.ev(), a, b).unwrap()
    }

    /// A pair of `[x, x]` nested `depth` deep around `leaf`, each level's
    /// two fields one value shared: `depth` cells, `2^depth` paths.
    fn doubled(depth: usize, leaf: Value) -> Value {
        (0..depth).fold(leaf, |x, _| {
            Value::Ctor(DataId(0), 0, Values::from(vec![x.clone(), x]))
        })
    }

    /// `conv` with and without the shortcut, which must agree; and the steps
    /// each took.
    fn conv_both(g: &Ev, a: &Value, b: &Value) -> (bool, u64, u64) {
        let before = g.machine.budget.total_work();
        let with = conv(g, 0, a, b).unwrap();
        let middle = g.machine.budget.total_work();
        set_shortcuts_disabled(true);
        let without = conv(g, 0, a, b);
        set_shortcuts_disabled(false);
        let without = without.unwrap();
        let after = g.machine.budget.total_work();
        assert_eq!(with, without, "the shortcut changed conv's answer");
        (with, middle - before, after - middle)
    }

    /// A kernel with `pair : Type → Type → Type := x y => x → y`, whose
    /// unfolding mentions each argument once more, and its id.
    fn kernel_with_pair() -> (crate::globals::Kernel, DefId) {
        let mut g = crate::globals::Kernel::default();
        let _operation = g.machine.budget.start(crate::budget::Limits::default());
        let ty = Term::Sort(Sort::Type(0));
        let arrow = |dom: Term, cod: Term| {
            Term::Pi(
                "_".into(),
                Icit::Explicit,
                rc(dom),
                rc(cod),
                ProofMark::Unknown,
            )
        };
        let pair_ty = arrow(ty.clone(), arrow(ty.clone(), ty));
        let name: Name = "pair".into();
        let span = stitchwort_syntax::Span::NOWHERE;
        let id =
            crate::check::declare_def(&mut g, &name, &name, &pair_ty, false, false, span).unwrap();
        let body = Term::Lam(
            "x".into(),
            Icit::Explicit,
            rc(Term::Lam(
                "y".into(),
                Icit::Explicit,
                rc(arrow(Term::Var(1), Term::Var(1))),
                ProofMark::Unknown,
            )),
            ProofMark::Unknown,
        );
        crate::check::define_def(&mut g, id, &body).unwrap();
        (g, id)
    }

    /// `depth` glued calls `pair c c` around `leaf`, each level's two
    /// arguments one call (one unfolding cell): `depth` cells, `2^depth`
    /// paths. Each call built makes a fresh cell, so two towers built
    /// separately share none.
    fn pair_tower(id: DefId, depth: usize, leaf: Value) -> Value {
        (0..depth).fold(leaf, |c, _| {
            let arg = |v: Value| Elim::App(v, Icit::Explicit);
            Value::Call(id, Spine::from(vec![arg(c.clone()), arg(c)]), Rc::default())
        })
    }

    /// Two towers of calls built apart compare in a step or so per level
    /// with the shortcut: a pair of calls found equal by its arguments is
    /// answered from `CallMemo` when its second argument meets it again
    /// (SW-4647). Without the shortcut each call is unfolded and the shared
    /// level walked twice, so the steps double per level (without the
    /// record, 511 then 131,071 steps with it on). A pair of towers
    /// differing only at the bottom must still come out different.
    ///
    /// A wrong "equal" in the record (made as a pair opens, or kept when its
    /// comparison fails) can't be shown this way, and isn't reachable: values
    /// are acyclic (a call's arguments exist before its cell), so a pair
    /// never meets itself inside its own arguments; and a pair that comes
    /// out different either ends the outermost `conv` or, compared as an
    /// argument, is recorded as different by
    /// [`same_spines`] at once, over any earlier entry, before anything else
    /// can read it. Recording "equal" for every pair whose arguments differ
    /// still passes this test, for that reason.
    #[test]
    fn calls_found_equal_by_their_arguments_are_compared_once() {
        let (g, id) = kernel_with_pair();
        let ev = g.ev();
        let leaf = || Value::Sort(Sort::Prop);
        let steps = |depth: usize| {
            let (equal, with, without) = conv_both(
                &ev,
                &pair_tower(id, depth, leaf()),
                &pair_tower(id, depth, leaf()),
            );
            assert!(equal, "towers of {depth} levels");
            (with, without)
        };
        let (with8, without8) = steps(8);
        let (with16, without16) = steps(16);
        // Linear with the record: twice the levels, at most about twice the
        // steps. Without it, 256 times the paths.
        assert!(
            with16 <= 2 * with8 + 8,
            "with the record: {with8} then {with16}"
        );
        assert!(
            without16 >= 100 * without8,
            "without it: {without8} then {without16}"
        );
        assert!(with16 * 100 < without16, "{with16} against {without16}");

        let other = Value::Pi(
            "_".into(),
            Icit::Explicit,
            Shared::new(leaf()),
            closure(vec![], Term::Sort(Sort::Prop)),
            ProofMark::Unknown,
        );
        let (equal, with, _) =
            conv_both(&ev, &pair_tower(id, 12, leaf()), &pair_tower(id, 12, other));
        assert!(!equal, "towers differing at the bottom");
        assert!(with < 10_000, "{with} steps to tell them apart");
    }

    fn stuck_call(def: usize) -> Value {
        Value::Neutral(Head::Def(DefId(def)), Spine::from(Vec::new()))
    }

    /// A read-back [`normal_form_meets`] stops early still counts towards
    /// the largest read-back `--timings` reports.
    #[test]
    fn a_read_back_stopped_early_is_counted() {
        let g = crate::globals::Kernel::default();
        let g = g.ev();
        let boxed = Value::Ctor(DataId(0), 0, Values::from(vec![erase::erased()]));
        g.machine.budget.take_peaks();
        let met = normal_form_meets(&g, 0, &boxed, 100, &|m| m == ELIDED).unwrap();
        assert_eq!(met, Some(Some(ELIDED)));
        assert!(g.machine.budget.take_peaks().readback > 0);
    }

    /// Freeing a stuck computation applied to a stuck computation, a million
    /// deep, must not recurse (SW-2468): on a stack far too small for that,
    /// the default drop would overflow it.
    #[test]
    fn freeing_a_deep_spine_does_not_overflow_the_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut value = stuck_call(0);
                for _ in 0..1_000_000 {
                    let mut spine = Spine::new();
                    spine.push(Elim::App(value, Icit::Explicit));
                    value = Value::Neutral(Head::Def(DefId(0)), spine);
                }
                drop(value);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Runs `build` on a stack far too small for recursing through a million
    /// levels, then drops what it returns there. The default drop of such a
    /// chain would overflow the stack and abort the process (SW-2482).
    fn drops_on_a_small_stack(build: fn() -> Value) {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || drop(build()))
            .unwrap()
            .join()
            .unwrap();
    }

    const DEEP: usize = 1_000_000;

    /// A value a thousand levels deep drops on 16 KiB: the recursive part
    /// of a drop is held to a handful of levels (SW-4866).
    #[test]
    fn freeing_a_moderately_deep_value_takes_little_stack() {
        std::thread::Builder::new()
            .stack_size(16 * 1024)
            .spawn(|| {
                let mut value = Value::Data(DataId(0), DataArgs::default());
                for _ in 0..1000 {
                    value = Value::Data(DataId(0), vec![value].into());
                }
                drop(value);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn freeing_deep_data_arguments_does_not_overflow_the_stack() {
        drops_on_a_small_stack(|| {
            let mut value = Value::Data(DataId(0), DataArgs::default());
            for _ in 0..DEEP {
                value = Value::Data(DataId(0), vec![value].into());
            }
            value
        });
    }

    #[test]
    fn freeing_a_deep_function_domain_does_not_overflow_the_stack() {
        drops_on_a_small_stack(|| {
            let closure = || Closure {
                env: Values::from([]),
                body: Rc::new(Term::Sort(Sort::Type(0))),
            };
            let mut value = Value::Sort(Sort::Type(0));
            for _ in 0..DEEP {
                value = Value::Pi(
                    Name::from("x"),
                    Icit::Explicit,
                    value.into(),
                    closure(),
                    ProofMark::Unknown,
                );
            }
            value
        });
    }

    #[test]
    fn freeing_a_deep_equality_type_does_not_overflow_the_stack() {
        drops_on_a_small_stack(|| {
            let mut value = Value::Refl;
            for _ in 0..DEEP {
                value = Value::Eq(Value::Refl.into(), value.into(), Value::Refl.into());
            }
            value
        });
    }

    #[test]
    fn freeing_a_deep_number_sum_does_not_overflow_the_stack() {
        drops_on_a_small_stack(|| {
            let mut value = Value::Refl;
            for _ in 0..DEEP {
                value = Value::NatAdd(Rc::new(BigUint::from(1u32)), value.into());
            }
            value
        });
    }

    #[test]
    fn freeing_a_deep_closure_environment_does_not_overflow_the_stack() {
        drops_on_a_small_stack(|| {
            let mut value = Value::Refl;
            for _ in 0..DEEP {
                value = Value::Lam(
                    Name::from("x"),
                    Icit::Explicit,
                    Closure {
                        env: Values::from([value]),
                        body: Rc::new(Term::Sort(Sort::Type(0))),
                    },
                    ProofMark::Unknown,
                );
            }
            value
        });
    }

    #[test]
    fn freeing_a_deep_unfolding_base_chain_does_not_overflow_the_stack() {
        drops_on_a_small_stack(|| {
            let mut base = None;
            for _ in 0..DEEP {
                base = Some(Rc::new(Unfolding {
                    kept: Default::default(),
                    base,
                }));
            }
            Value::Call(DefId(0), Spine::new(), base.unwrap())
        });
    }

    /// How many pairs the memo holds as different.
    fn remembered_different() -> usize {
        TREE_MEMO.with(|m| m.borrow().different.values().map(Vec::len).sum())
    }

    /// The editor's kept session matches numbers on every request, so naming
    /// a set it has seen must not add one (SW-1819).
    #[test]
    fn naming_the_same_numbers_again_gives_the_same_apart() {
        let g = crate::globals::Kernel::default();
        let ev = g.ev();
        let set = |ns: &[u32]| -> Rc<[BigUint]> { ns.iter().map(|&n| BigUint::from(n)).collect() };
        let a = Apart::new(&ev, set(&[1, 2]));
        let b = Apart::new(&ev, set(&[3]));
        assert_eq!(g.machine.apart_sets.borrow().len(), 2);
        assert_eq!(Apart::new(&ev, set(&[1, 2])), a);
        assert_eq!(Apart::new(&ev, set(&[3])), b);
        assert_ne!(a, b);
        assert_ne!(a, Apart::NONE);
        assert_eq!(g.machine.apart_sets.borrow().len(), 2);
        assert_eq!(*a.numbers(&ev), *set(&[1, 2]));
    }

    #[test]
    fn conv_inside_an_open_unification_remembers_nothing_as_different() {
        let g = crate::globals::Kernel::default();
        let ev = g.ev();
        let (a, b) = (stuck_call(0), stuck_call(1));
        {
            let outer = TreeMemo::enter(&ev, 0, &a, &b, Relation::Unify, true).unwrap();
            let inner = TreeMemo::enter(&ev, 0, &a, &b, Relation::Conv, true).unwrap();
            inner.record(false);
            assert_eq!(remembered_different(), 0, "conv under unification");
            outer.record(false);
            assert_eq!(remembered_different(), 1, "a settled unification pair");
        }
        assert_eq!(remembered_different(), 0, "emptied with the outermost");
        {
            let alone = TreeMemo::enter(&ev, 0, &a, &b, Relation::Conv, true).unwrap();
            alone.record(false);
            assert_eq!(remembered_different(), 1, "conv on its own");
        }
        let unsettled = TreeMemo::enter(&ev, 0, &a, &b, Relation::Unify, false).unwrap();
        unsettled.record(false);
        assert_eq!(remembered_different(), 0, "an unsettled pair");
    }

    #[test]
    fn the_same_body_with_the_same_values_is_the_same_closure() {
        // Separately built bodies, one wrapped in a location and named
        // differently; the unused environment entries differ.
        let a = closure(vec![Value::var(7), Value::var(3)], call_last());
        let b = closure(
            vec![Value::var(9), Value::var(3)],
            Term::Loc(
                {
                    let mut sources = stitchwort_syntax::SourceMap::new();
                    stitchwort_syntax::Span::point(sources.add("test", ""), 0)
                },
                rc(call_last()),
            ),
        );
        assert!(same(&a, &b));
        let g = crate::globals::Kernel::default();
        let (equal, with, without) = conv_both(&g.ev(), &lam(a), &lam(b));
        assert!(equal);
        assert!(with < without, "the shortcut was taken: {with} < {without}");
    }

    #[test]
    fn identical_values_have_the_same_shape_hash() {
        // The same closures as above, inside separately built constructors
        // and calls: identical, so filed under the same hash, each with a
        // cache of its own and with one shared.
        let g = crate::globals::Kernel::default();
        let a = closure(vec![Value::var(7), Value::var(3)], call_last());
        let b = closure(vec![Value::var(9), Value::var(3)], call_last());
        let wrap = |c: Closure| {
            let fields: Values = vec![lam(c), Value::var(1)].into();
            let ctor = Value::Ctor(DataId(0), 1, fields);
            Value::Neutral(
                Head::Def(DefId(0)),
                Spine::from(vec![Elim::App(ctor, Icit::Explicit)]),
            )
        };
        let (x, y) = (wrap(a), wrap(b));
        assert!(identical(Same::Values(&x, &y)));
        let mut shared = ShapeCache::default();
        let hash = shape_hash(&g.ev(), &mut shared, &x).unwrap();
        assert_eq!(hash, shape_hash(&g.ev(), &mut shared, &y).unwrap());
        assert_eq!(
            hash,
            shape_hash(&g.ev(), &mut ShapeCache::default(), &y).unwrap()
        );
        // A used variable's value counts.
        let c = closure(vec![Value::var(7), Value::var(4)], call_last());
        let z = wrap(c);
        assert!(!identical(Same::Values(&x, &z)));
        assert_ne!(hash, shape_hash(&g.ev(), &mut shared, &z).unwrap());
    }

    #[test]
    fn a_different_value_for_a_used_variable_is_not_the_same_closure() {
        let a = closure(vec![Value::var(3)], call_last());
        let b = closure(vec![Value::var(4)], call_last());
        assert!(!same(&a, &b));
        let g = crate::globals::Kernel::default();
        assert!(!conv_both(&g.ev(), &lam(a), &lam(b)).0);
    }

    /// SW-920: for the elaborator, a solved metavariable is its solution.
    #[test]
    fn a_solved_metavariable_is_the_same_as_its_solution_for_the_elaborator() {
        /// One metavariable, `?0`, with the solution the test gives it.
        struct One(std::cell::RefCell<Option<Value>>);
        impl crate::ev::Metas for One {
            fn solution(&self, _m: usize) -> Option<Value> {
                self.0.borrow().clone()
            }
            fn epoch(&self) -> u64 {
                1
            }
        }
        let g = crate::globals::Kernel::default();
        let metas = One(std::cell::RefCell::new(None));
        let ev = Ev {
            metas: &metas,
            ..g.ev()
        };
        let unknown = Value::Neutral(Head::Meta(0), Spine::from(Vec::new()));
        let a = closure(vec![unknown], call_last());
        let b = closure(vec![Value::var(3)], call_last());
        assert!(!same_closure_solved(&ev, &a, &b).unwrap(), "unsolved");
        *metas.0.borrow_mut() = Some(Value::var(3));
        assert!(same_closure_solved(&ev, &a, &b).unwrap());
        assert!(!same(&a, &b), "the kernel's form looks at no solution");
        *metas.0.borrow_mut() = Some(Value::var(4));
        assert!(
            !same_closure_solved(&ev, &a, &b).unwrap(),
            "solved with another value"
        );
    }

    #[test]
    fn a_different_body_is_not_the_same_closure() {
        let a = closure(vec![Value::var(3)], call_last());
        let b = closure(
            vec![Value::var(3)],
            Term::App(rc(Term::Var(1)), rc(Term::Var(1)), Icit::Explicit),
        );
        assert!(!same(&a, &b));
        let implicit = closure(
            vec![Value::var(3)],
            Term::App(rc(Term::Var(1)), rc(Term::Var(0)), Icit::Implicit),
        );
        assert!(!same(&a, &implicit));
        let g = crate::globals::Kernel::default();
        assert!(!conv_both(&g.ev(), &lam(a.clone()), &lam(b)).0);
        // (Conversion ignores how an argument is passed, so this pair is
        // equal the long way; `conv_both` checks the two ways agree.)
        assert!(conv_both(&g.ev(), &lam(a), &lam(implicit)).0);
    }

    #[test]
    fn closures_in_the_environment_are_compared_by_identity_too() {
        let inner = |n| lam(closure(vec![Value::var(n)], call_last()));
        let a = closure(vec![inner(3)], call_last());
        let b = closure(vec![inner(3)], call_last());
        assert!(same(&a, &b));
        let c = closure(vec![inner(4)], call_last());
        assert!(!same(&a, &c));
    }

    /// SW-2730: two closures over separately built but alike values that
    /// share their parts are compared once per pair of parts, not once per
    /// path: as trees these are 2^60 pairs. Conversion takes the shortcut
    /// too, and a difference at the bottom is still found.
    #[test]
    fn shared_parts_are_compared_once() {
        let g = crate::globals::Kernel::default();
        let a = closure(vec![doubled(60, Value::var(3))], call_last());
        let b = closure(vec![doubled(60, Value::var(3))], call_last());
        let before = g.ev().machine.budget.total_work();
        assert!(same(&a, &b));
        assert!(conv(&g.ev(), 0, &lam(a.clone()), &lam(b)).unwrap());
        assert!(g.ev().machine.budget.total_work() - before < 2_000);
        let c = closure(vec![doubled(60, Value::var(4))], call_last());
        assert!(!same(&a, &c));
    }

    /// The shortcut's walk costs budget steps, so a large one runs out of
    /// budget (`E-RESOURCE`) rather than running uncharged.
    #[test]
    fn the_same_closure_walk_is_charged() {
        let g = crate::globals::Kernel::default();
        let long = || {
            (0..5_000).fold(Value::var(3), |x, n| {
                Value::Ctor(DataId(0), 0, Values::from(vec![x, Value::var(n)]))
            })
        };
        let a = closure(vec![long()], call_last());
        let b = closure(vec![long()], call_last());
        let limits = crate::budget::Limits {
            work: 1_000,
            ..crate::budget::Limits::for_stack(1 << 20)
        };
        let ev = g.ev();
        let _operation = ev.machine.budget.operation(limits);
        assert!(same_closure(&ev, &a, &b).is_err());
    }

    #[test]
    fn convertible_but_not_identical_closures_are_still_equal() {
        // `f` against `y => f y`: equal by eta, which only the long way sees.
        let f = Value::var(3);
        let eta = lam(closure(vec![f.clone()], call_last()));
        let a = closure(vec![f], call_last());
        let b = closure(vec![eta], call_last());
        assert!(!same(&a, &b));
        let g = crate::globals::Kernel::default();
        assert!(conv_both(&g.ev(), &lam(a), &lam(b)).0);
    }

    #[test]
    fn function_types_with_the_same_codomain_are_equal() {
        let pi = |env: Vec<Value>| {
            Value::Pi(
                "x".into(),
                Icit::Explicit,
                Rc::new(Value::Sort(Sort::Type(0))).into(),
                closure(env, call_last()),
                ProofMark::Unknown,
            )
        };
        let g = crate::globals::Kernel::default();
        let (equal, with, without) =
            conv_both(&g.ev(), &pi(vec![Value::var(2)]), &pi(vec![Value::var(2)]));
        assert!(equal);
        assert!(with < without);
        assert!(!conv_both(&g.ev(), &pi(vec![Value::var(2)]), &pi(vec![Value::var(5)])).0);
    }
}
