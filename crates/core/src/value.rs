//! Values, evaluation, quotation and conversion (normalisation by evaluation).
//!
//! Variables in values are de Bruijn *levels*: `Var(0)` is the outermost binder.
//!
//! Reduction policy: a definition stays folded (a neutral `Def` head) until it
//! has all its parameters *and* its case tree can take a step. This keeps
//! comparison from unfolding recursive definitions forever. See `docs/core.md`.

use std::collections::HashMap;
use std::rc::Rc;

use num_bigint::BigUint;

use crate::budget::{ResourceError, Result};
use crate::chars::{self, Chars};
use crate::erase::{self, erased};
use crate::globals::Globals;
use crate::native;
use crate::term::{DataId, DefId, Icit, Name, QuotForm, Sort, Term};

#[derive(Clone, Debug)]
pub enum Value {
    Sort(Sort),
    Pi(Name, Icit, Rc<Value>, Closure),
    Lam(Name, Icit, Closure),
    Data(DataId, Vec<Value>),
    /// Fields are shared, so copying a value (a list, say) is cheap.
    Ctor(DataId, usize, Values),
    /// A number, standing for `Succ (Succ … Zero)`. See [`native`].
    Nat(Rc<BigUint>),
    /// `k + x` for a number `k ≥ 1` and an `x` not built from numbers:
    /// `Succ` applied `k` times to `x`. See [`native::view`].
    NatAdd(Rc<BigUint>, Rc<Value>),
    /// A `List Char`, standing for `Cons (MkChar c rfl) … Nil`. Never empty
    /// when made by evaluation (that's `Nil`). See [`chars`].
    Chars(Chars),
    Eq(Rc<Value>, Rc<Value>, Rc<Value>),
    Refl,
    /// A computation stuck on a variable or an unsolved metavariable, or a
    /// folded definition.
    Neutral(Head, Spine),
    /// A definition applied to all its parameters, kept as the call while
    /// gluing ([`Globals::glue`], docs/proposals/folded-calls.md). It means
    /// its unfolding, which [`force`] computes the first time something
    /// looks inside and every copy of the call then shares. The spine has
    /// only applications.
    Call(DefId, Spine, Rc<Unfolding>),
}

/// The unfolding of a [`Value::Call`] once computed: the value the call
/// unfolds to, forced (no `Call` or solved metavariable at its top), with
/// the [`Globals::meta_epoch`] it was computed at. One from an earlier epoch
/// may have used a metavariable solution that's since been taken back, so
/// it's computed again.
#[derive(Debug, Default)]
pub struct Unfolding(std::cell::RefCell<Option<(u64, Value)>>);

impl Unfolding {
    fn get(&self, g: &Globals) -> Option<Value> {
        match &*self.0.borrow() {
            Some((epoch, value)) if *epoch == g.meta_epoch.get() => Some(value.clone()),
            _ => None,
        }
    }

    fn set(&self, g: &Globals, value: Value) {
        *self.0.borrow_mut() = Some((g.meta_epoch.get(), value));
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Head {
    Var(usize),
    Def(DefId),
    Meta(usize),
    /// A quotient form (docs/proposals/map-equality.md §7), its arguments
    /// the first [`QuotForm::arity`] applications of the spine (the implicit
    /// ones marked so), any further ones applying its result. `Quot A R` and
    /// `Quot.mk a` are values; `Quot.ind` and `Quot.sound` never compute;
    /// `Quot.lift` here is stuck, its quotient argument not a `Quot.mk`.
    /// `Quot.mk` is never a constructor (`Value::Ctor`), so nothing that
    /// takes constructors apart (a `case`, index unification) sees inside it.
    Quot(QuotForm),
}

/// The representative of a `Quot.mk` value, if `value` is one.
pub fn quot_mk_rep(value: &Value) -> Option<&Value> {
    match value {
        Value::Neutral(Head::Quot(QuotForm::Mk), spine) if spine.len() == QuotForm::Mk.arity() => {
            match &spine[2] {
                Elim::App(a, _) => Some(a),
                Elim::J { .. } => None,
            }
        }
        _ => None,
    }
}

/// A quotient form applied to the values `args`.
pub fn quot_value(form: QuotForm, args: Vec<Value>) -> Value {
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
    Value::Neutral(Head::Quot(form), spine)
}

#[derive(Clone, Debug)]
pub enum Elim {
    App(Value, Icit),
    /// Boxed, so the common case, an application, sets the size.
    J {
        motive: Box<Value>,
        base: Box<Value>,
    },
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
    pub fn into_vec(self) -> Vec<Elim> {
        match self.0 {
            Some(elims) => Rc::try_unwrap(elims)
                .unwrap_or_else(|elims| (*elims).clone())
                .into_vec(),
            None => Vec::new(),
        }
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
/// Freeing one frees its values without recursing, however deeply they nest
/// (a list of a million elements is a million nested `Ctor`s): the values of
/// a uniquely owned sequence are moved onto a work list and taken apart one
/// at a time. Rust frees nested data recursively by default, which would
/// overflow the stack.
#[derive(Clone, Debug)]
pub struct Values(Rc<[Value]>);

impl std::ops::Deref for Values {
    type Target = [Value];
    fn deref(&self) -> &[Value] {
        &self.0
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
        let mut values = Some(std::mem::replace(&mut self.0, empty.clone()));
        let mut free = |pending: &mut Vec<Value>| {
            if let Some(values) = values.take() {
                take_apart(values, pending);
            }
            while let Some(value) = pending.pop() {
                detach(value, &empty, pending);
            }
        };
        // Freeing never starts another free that needs the shared work list
        // (everything it frees has been taken apart), but if it ever did, a
        // local one would do.
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
    let mut unwrap = |v: Rc<Value>| {
        if let Ok(v) = Rc::try_unwrap(v) {
            pending.push(v);
        }
    };
    match value {
        Value::Ctor(_, _, mut fields) => {
            take_apart(std::mem::replace(&mut fields.0, empty.clone()), pending);
        }
        Value::Lam(_, _, mut closure) => {
            take_apart(
                std::mem::replace(&mut closure.env.0, empty.clone()),
                pending,
            );
        }
        Value::Pi(_, _, dom, mut closure) => {
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
            if let Ok(unfolding) = Rc::try_unwrap(unfolding)
                && let Some((_, value)) = unfolding.0.into_inner()
            {
                pending.push(value);
            }
            pending.push(Value::Neutral(Head::Var(0), spine));
        }
        Value::Neutral(_, spine) => {
            // Only the last owner takes the eliminations apart.
            let elims = match spine.0 {
                Some(elims) => Rc::try_unwrap(elims).unwrap_or_default(),
                None => Elims::new(),
            };
            for elim in elims {
                match elim {
                    Elim::App(v, _) => pending.push(v),
                    Elim::J { motive, base } => {
                        pending.push(*motive);
                        pending.push(*base);
                    }
                }
            }
        }
        Value::Sort(_) | Value::Nat(_) | Value::Chars(_) | Value::Refl => {}
    }
}

impl Closure {
    pub fn apply(&self, g: &Globals, arg: Value) -> Result<Value> {
        run(g, enter(self, arg))
    }

    /// Like `apply`, but only computes the argument if the body uses it. For
    /// the result type of an application: `f a : B a` needs the value of `a`
    /// only when `B` depends on it, and computing it may be expensive.
    pub fn apply_lazy(&self, g: &Globals, arg: impl FnOnce() -> Result<Value>) -> Result<Value> {
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
    Value::Neutral(Head::Var(usize::MAX), Spine::new())
}

impl Value {
    pub fn var(level: usize) -> Value {
        Value::Neutral(Head::Var(level), Spine::new())
    }
}

pub fn eval(g: &Globals, env: &[Value], term: &Term) -> Result<Value> {
    run(g, Control::Eval(Rc::new(term.clone()), env.into()))
}

pub fn apply(g: &Globals, f: Value, arg: Value) -> Result<Value> {
    apply_icit(g, f, arg, Icit::Explicit)
}

pub fn apply_icit(g: &Globals, f: Value, arg: Value, icit: Icit) -> Result<Value> {
    run(g, Control::Apply(Box::new((f, arg, icit))))
}

/// What looking inside `value` sees (its weak head, as far as the
/// elaborator's additions go): a solved metavariable at its head is
/// replaced by its solution, and a call ([`Value::Call`]) by its unfolding,
/// until neither is at the top. Everything that takes a value apart by its
/// shape calls this first. Without metavariables and gluing (the kernel),
/// it returns `value` as it is.
#[inline]
pub fn force(g: &Globals, value: Value) -> Result<Value> {
    if needs_forcing(g, &value) {
        force_now(g, value)
    } else {
        Ok(value)
    }
}

/// [`force`] for a value it changes: a call's kept unfolding if there is
/// one, or else the machine.
#[inline(never)]
fn force_now(g: &Globals, value: Value) -> Result<Value> {
    if let Value::Call(_, _, unfolding) = &value
        && let Some(unfolded) = unfolding.get(g)
        && !needs_forcing(g, &unfolded)
    {
        return Ok(unfolded);
    }
    run(g, Control::Force(value))
}

/// [`force`] on a borrowed value, copying it only if forcing changes it.
pub fn force_ref<'v>(g: &Globals, value: &'v Value) -> Result<std::borrow::Cow<'v, Value>> {
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
pub fn force_solved(g: &Globals, value: Value) -> Result<Value> {
    if !g.glue.get() {
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
        if spine.iter().any(|e| matches!(e, Elim::J { .. })) {
            return force(g, value);
        }
        let mut applied = solution;
        for elim in spine.iter() {
            let Elim::App(arg, icit) = elim else {
                unreachable!("checked above")
            };
            applied = apply_icit(g, applied, arg.clone(), *icit)?;
        }
        value = applied;
    }
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
pub fn matches_at_once(g: &Globals, id: DefId, spine: &Spine) -> Result<bool> {
    let def = g.def(id);
    let Some(body) = &def.body else {
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

/// A glued call's arguments, in order, with how each is passed.
pub fn call_args(spine: &Spine) -> Vec<(Value, Icit)> {
    spine
        .iter()
        .map(|elim| match elim {
            Elim::App(v, i) => (v.clone(), *i),
            Elim::J { .. } => unreachable!("a call's spine has only applications"),
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
        Value::Refl => "rfl",
        Value::Neutral(..) => "a stuck term",
        Value::Call(..) => "a call",
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
// one exception is natives forcing their arguments (`native::view`), which
// only does work on values containing solved metavariables, during
// elaboration.

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
    /// The forced proof of `J`.
    JForced { term: Rc<Term>, env: Env },
    /// The forced proof of `J`, already unfolded if it was a folded call.
    JReady { term: Rc<Term>, env: Env },
    /// The motive of a stuck `J` (the base is next).
    JMotive {
        term: Rc<Term>,
        env: Env,
        head: Head,
        spine: Spine,
    },
    /// The base of a stuck `J`: its head, spine and motive. (Boxed: it's the
    /// largest frame, and rare.)
    JBase(Box<(Head, Spine, Value)>),
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
    /// The unfolding of a folded call (a dictionary or a theorem, [`folds`])
    /// that the frame `next` takes apart: unfolded again if it's another
    /// folded call, and given to `next` as it is if it's this call, stuck.
    /// (Boxed: it's large, and rare.)
    Unfolding(Box<(DefId, Spine, Frame)>),
    /// A metavariable's solution, or the result of applying it so far:
    /// apply the eliminations of `spine` from `next` on, then force again.
    Replay { spine: Spine, next: usize },
    /// The forced value a `J` elimination at `spine[next]` applies to.
    ReplayJ { spine: Spine, next: usize },
    /// The forced function of an application of a call to `arg`.
    AppTo(Value, Icit),
    /// The unfolding of a call, to force and then keep.
    Unfolded(Rc<Unfolding>),
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
        Value::Lam(_, _, closure) => enter(&closure, arg),
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

/// Applying call `f` to `arg`: `run` forces `f` first ([`apply_call`]).
#[cold]
#[inline(never)]
fn apply_later(f: Value, arg: Value, icit: Icit) -> Control {
    Control::Apply(Box::new((f, arg, icit)))
}

/// Applying call `f` to `arg`: its unfolding, once forced, is applied.
#[cold]
#[inline(never)]
fn apply_call(
    g: &Globals,
    stack: &mut Vec<Frame>,
    f: Value,
    arg: Value,
    icit: Icit,
) -> Result<Control> {
    push(g, stack, Frame::AppTo(arg, icit))?;
    Ok(Control::Force(f))
}

/// Forcing a call: its kept unfolding, or else unfolding it now, to be
/// kept (`Frame::Unfolded`).
#[cold]
#[inline(never)]
fn force_call(
    g: &Globals,
    stack: &mut Vec<Frame>,
    id: DefId,
    spine: Spine,
    unfolding: Rc<Unfolding>,
) -> Result<Control> {
    Ok(match unfolding.get(g) {
        Some(unfolded) => Control::Force(unfolded),
        None => {
            push(g, stack, Frame::Unfolded(unfolding))?;
            unfold_now(g, id, spine, false)?
        }
    })
}

/// Applying a closure: evaluating its body with the argument added.
fn enter(closure: &Closure, arg: Value) -> Control {
    Control::Eval(closure.body.clone(), extend(&closure.env, arg))
}

/// `env` with `value` added as the innermost variable.
fn extend(env: &Env, value: Value) -> Env {
    // Built in place, in one allocation.
    let env: Rc<[Value]> = env.iter().cloned().chain(std::iter::once(value)).collect();
    Values(env)
}

fn run(g: &Globals, mut control: Control) -> Result<Value> {
    #[cfg(any(test, feature = "reference"))]
    RUNS.with(|r| r.set(r.get() + 1));
    let mut stack: Vec<Frame> = Vec::new();
    loop {
        g.budget.step()?;
        control = match control {
            Control::Eval(term, env) => eval_step(g, term, env, &mut stack)?,
            Control::Apply(application) => {
                let (f, arg, icit) = *application;
                if let Value::Call(..) = f {
                    apply_call(g, &mut stack, f, arg, icit)?
                } else {
                    apply_step(f, arg, icit)
                }
            }
            Control::Unfold(id, spine) => unfold(g, id, spine)?,
            Control::Tree(node, env, stuck) => {
                let node = Term::strip_loc_rc(&node);
                match &*node {
                    Term::Case(ix, ..) | Term::NumCase(ix, ..) => {
                        let scrutinee = env[env.len() - 1 - ix].clone();
                        if needs_forcing(g, &scrutinee) || is_folded(g, &scrutinee) {
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
                            branch(g, node, env, stuck, scrutinee)?
                        }
                    }
                    // A `Quot.lift` leaf counts as a case on its quotient
                    // (the unfolding policy, `Stuck`): its definition stays
                    // folded unless the quotient is a `Quot.mk`. Only a
                    // definition marked for it (`Def::lift_leaf`), so every
                    // call left folded here is one `is_folded` unfolds again
                    // for a comparison.
                    Term::Quot(QuotForm::Lift, args, _)
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

fn push(g: &Globals, stack: &mut Vec<Frame>, frame: Frame) -> Result<()> {
    g.budget.frames(stack.len() + 1)?;
    stack.push(frame);
    Ok(())
}

/// The value of `term` if it takes no evaluation steps (a variable, a
/// number, a function, a folded definition, a constructor with no fields), so
/// common terms like `f x` need no frames.
fn quick(g: &Globals, term: &Rc<Term>, env: &Env) -> Option<Value> {
    match &**term {
        Term::Var(ix) => Some(env[env.len() - 1 - ix].clone()),
        Term::Nat(n) => Some(Value::Nat(n.clone())),
        Term::Chars(c) => Some(chars_value(g, c)),
        Term::Sort(s) => Some(Value::Sort(*s)),
        Term::Refl => Some(Value::Refl),
        Term::Lam(x, i, b) => Some(Value::Lam(
            x.clone(),
            *i,
            Closure {
                env: env.clone(),
                body: b.clone(),
            },
        )),
        Term::Def(id) => {
            let def = g.def(*id);
            match &def.body {
                Some(_) if def.arity == 0 && !folds(g, *id) => None,
                _ => Some(Value::Neutral(Head::Def(*id), Spine::new())),
            }
        }
        Term::Ctor(d, c, args) if args.is_empty() => Some(native::ctor(g, *d, *c, Vec::new())),
        Term::Loc(_, t) => quick(g, t, env),
        _ => None,
    }
}

/// The first step of evaluating `term`.
fn eval_step(g: &Globals, term: Rc<Term>, env: Env, stack: &mut Vec<Frame>) -> Result<Control> {
    Ok(match &*term {
        Term::Var(ix) => Control::Return(env[env.len() - 1 - ix].clone()),
        Term::Def(id) => {
            let def = g.def(*id);
            match &def.body {
                Some(_) if def.arity == 0 && erases_result(g, *id) => Control::Return(erased()),
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
        Term::Data(d, args) if args.is_empty() => Control::Return(Value::Data(*d, Vec::new())),
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
        Term::Pi(_, _, a, _) => {
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
        Term::Lam(x, i, b) => Control::Return(Value::Lam(
            x.clone(),
            *i,
            Closure {
                env,
                body: b.clone(),
            },
        )),
        Term::App(f, a, i)
            if g.erasure.active() && quick(g, a, &env).is_none() && erased_arg(g, f) =>
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
        Term::Let(_, _, _, body, true) if g.erasure.active() => {
            Control::Eval(body.clone(), extend(&env, erased()))
        }
        Term::Let(_, _, value, body, _) => match quick(g, value, &env) {
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
        Term::Quot(QuotForm::Lift, _, true) | Term::Quot(QuotForm::Ind | QuotForm::Sound, ..)
            if g.erasure.active() =>
        {
            Control::Return(erased())
        }
        Term::Quot(QuotForm::Mk, args, true)
            if g.erasure.active() && args.len() == QuotForm::Mk.arity() =>
        {
            quot_args(g, term.clone(), env, Vec::new(), Some(erased()), stack)?
        }
        // The one computation rule (docs/proposals/map-equality.md §7.2):
        // `Quot.lift f h (Quot.mk a)` is `f a`. The quotient first, then.
        Term::Quot(QuotForm::Lift, args, _) if args.len() == QuotForm::Lift.arity() => {
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
        Term::J(_, _, proof) => {
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
    })
}

/// Evaluates the arguments of a data type or constructor `term` after the
/// ones `done`: as many as are quick, then a frame for the next.
fn fields(
    g: &Globals,
    term: Rc<Term>,
    env: Env,
    mut done: Vec<Value>,
    stack: &mut Vec<Frame>,
) -> Result<Control> {
    let (Term::Data(_, args) | Term::Ctor(_, _, args)) = &*term else {
        unreachable!("fields of a data type or constructor")
    };
    let field_erased = match &*term {
        Term::Ctor(d, c, _) if g.erasure.active() => Some(&g.data(*d).ctors[*c].field_erased),
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
        Term::Data(d, _) => Value::Data(*d, done),
        Term::Ctor(d, c, _) => native::ctor(g, *d, *c, done),
        _ => unreachable!(),
    }))
}

/// Evaluates the arguments of the quotient form `term` after the ones
/// `done` (and before `last`, its final argument if already computed): as
/// many as are quick, then a frame for the next. With all of them, the form
/// applied to them.
fn quot_args(
    g: &Globals,
    term: Rc<Term>,
    env: Env,
    mut done: Vec<Value>,
    last: Option<Value>,
    stack: &mut Vec<Frame>,
) -> Result<Control> {
    let Term::Quot(form, args, _) = &*term else {
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
    Ok(Control::Return(quot_value(*form, done)))
}

/// Continues `frame` with the value it was waiting for.
fn resume(g: &Globals, frame: Frame, value: Value, stack: &mut Vec<Frame>) -> Result<Control> {
    Ok(match frame {
        Frame::AppArg(arg, env, icit) => {
            push(g, stack, Frame::AppFun(value, icit))?;
            Control::Eval(arg, env)
        }
        Frame::AppFun(f, icit) => apply_step(f, value, icit),
        Frame::AppErased(icit) => apply_step(value, erased(), icit),
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
        Frame::LiftForced { term, env, stuck } if is_folded(g, &value) => {
            unfold_for(g, stack, value, Frame::LiftReady { term, env, stuck })?
        }
        Frame::LiftForced { term, env, stuck } | Frame::LiftReady { term, env, stuck } => {
            let Term::Quot(_, args, _) = &*term else {
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
                None if matches!(stuck, Some((_, _, true))) => stuck_tree(stuck),
                None => quot_args(g, term, env, Vec::new(), Some(value), stack)?,
            }
        }
        Frame::LetBody { term, env } => {
            let Term::Let(_, _, _, body, _) = &*term else {
                unreachable!("a `LetBody` frame is for a `let`")
            };
            Control::Eval(body.clone(), extend(&env, value))
        }
        Frame::PiDomain { term, env } => {
            let Term::Pi(x, i, _, b) = &*term else {
                unreachable!("a `PiDomain` frame is for a function type")
            };
            Control::Return(Value::Pi(
                x.clone(),
                *i,
                Rc::new(value),
                Closure {
                    env,
                    body: b.clone(),
                },
            ))
        }
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
                    let mut parts = done.into_iter().map(Rc::new);
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
        // A folded call is taken apart: it unfolds (in this machine, so a
        // proof made of many folded steps needs no Rust stack).
        Frame::JForced { term, env } if is_folded(g, &value) => {
            unfold_for(g, stack, value, Frame::JReady { term, env })?
        }
        Frame::JForced { term, env } | Frame::JReady { term, env } => {
            let Term::J(motive, base, _) = &*term else {
                unreachable!("a `JForced` frame is for `J`")
            };
            match value {
                Value::Refl => Control::Eval(base.clone(), env),
                // Every closed proof of an equation is `refl` (`erase.rs`).
                v if erase::is_erased(&v) => Control::Eval(base.clone(), env),
                Value::Neutral(head, spine) => {
                    let motive = motive.clone();
                    push(
                        g,
                        stack,
                        Frame::JMotive {
                            term: term.clone(),
                            env: env.clone(),
                            head,
                            spine,
                        },
                    )?;
                    Control::Eval(motive, env)
                }
                other => panic!("internal error: J applied to {}", describe(&other)),
            }
        }
        Frame::JMotive {
            term,
            env,
            head,
            spine,
        } => {
            let Term::J(_, base, _) = &*term else {
                unreachable!("a `JMotive` frame is for `J`")
            };
            push(g, stack, Frame::JBase(Box::new((head, spine, value))))?;
            Control::Eval(base.clone(), env)
        }
        Frame::JBase(stuck) => {
            let (head, mut spine, motive) = *stuck;
            spine.push(Elim::J {
                motive: Box::new(motive),
                base: Box::new(value),
            });
            Control::Return(Value::Neutral(head, spine))
        }
        // A folded call is taken apart: it unfolds.
        Frame::Scrutinee { tree, env, stuck } if is_folded(g, &value) => {
            unfold_for(g, stack, value, Frame::ScrutineeReady { tree, env, stuck })?
        }
        Frame::Scrutinee { tree, env, stuck } | Frame::ScrutineeReady { tree, env, stuck } => {
            branch(g, tree, env, stuck, value)?
        }
        Frame::Unfolding(unfolding) => {
            let (id, spine, next) = *unfolding;
            match &value {
                // Stuck: `next` gets the call as it is.
                Value::Neutral(Head::Def(i2), s2) if *i2 == id && s2.ptr_eq(&spine) => {
                    resume(g, next, value, stack)?
                }
                _ if is_folded(g, &value) => unfold_for(g, stack, value, next)?,
                _ => {
                    push(g, stack, next)?;
                    Control::Force(value)
                }
            }
        }
        Frame::Replay { spine, next } => match spine.get(next) {
            None => Control::Force(value),
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
            Some(Elim::J { .. }) => {
                push(g, stack, Frame::ReplayJ { spine, next })?;
                Control::Force(value)
            }
        },
        Frame::ReplayJ { spine, next } => {
            let elim = spine[next].clone();
            let Elim::J { base, .. } = &elim else {
                unreachable!("a `ReplayJ` frame is for a `J` elimination")
            };
            // Only while elaborating (a metavariable's solution), so the
            // machine this starts for a folded proof is bounded by the program.
            let value = unfold_folded(g, &value)?.unwrap_or(value);
            let result = match value {
                Value::Refl => (**base).clone(),
                Value::Neutral(head, mut s) => {
                    s.push(elim.clone());
                    Value::Neutral(head, s)
                }
                other => panic!("internal error: J applied to {}", describe(&other)),
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
        Frame::AppTo(arg, icit) => apply_step(value, arg, icit),
        Frame::Unfolded(unfolding) => {
            if needs_forcing(g, &value) {
                push(g, stack, Frame::Unfolded(unfolding))?;
                Control::Force(value)
            } else {
                unfolding.set(g, value.clone());
                Control::Return(value)
            }
        }
    })
}

/// The value of a compact list. Only checked terms, and the elaborator's
/// (which makes them only once the representation is registered), are
/// evaluated, and the kernel refuses `Term::Chars` without it.
fn chars_value(g: &Globals, c: &Chars) -> Value {
    let text = g
        .builtins
        .text
        .as_ref()
        .expect("internal error: compact text without `List` and `Char`");
    chars::value(text, c.clone())
}

/// One step of the expansion of a compact list `value`, as matching sees it
/// (see [`chars::step`]); anything else as it is.
pub fn expand_step(g: &Globals, value: Value) -> Value {
    match (&value, &g.builtins.text) {
        (Value::Chars(c), Some(text)) => chars::step(text, c),
        _ => value,
    }
}

/// Whether [`force`] would change `value`: it's headed by a solved
/// metavariable, or it's a call.
#[inline]
fn needs_forcing(g: &Globals, value: &Value) -> bool {
    match value {
        Value::Neutral(Head::Meta(m), _) => g.meta_solution(*m).is_some(),
        Value::Call(..) => true,
        _ => false,
    }
}

/// The branch of the case node `tree` for the (forced) scrutinee `value`.
fn branch(
    g: &Globals,
    tree: Rc<Term>,
    mut env: Vec<Value>,
    stuck: Stuck,
    value: Value,
) -> Result<Control> {
    // A folded call was unfolded before this (`Frame::Scrutinee`).
    let (d, branches) = match &*tree {
        Term::Case(_, d, branches) => (d, branches),
        Term::NumCase(_, arms, default) => {
            let next = match native::view(g, &value)? {
                // A number: its arm, or the default.
                (k, None) => match arms.binary_search_by(|a| (*a.value).cmp(&k)) {
                    Ok(i) => arms[i].body.clone(),
                    Err(_) => default.clone(),
                },
                // `k + x` is at least `k`, so if every arm's number is below
                // `k`, it can't be any of them. Otherwise it depends on `x`
                // (failing to show `x` is some number never means it isn't).
                (k, Some(_)) => match arms.last() {
                    Some(last) if *last.value < k => default.clone(),
                    _ => return Ok(stuck_tree(stuck)),
                },
            };
            return Ok(Control::Tree(next, env, stuck));
        }
        _ => unreachable!("a case node"),
    };
    let (c, fields) = match value {
        Value::Ctor(_, c, fields) => (c, fields.to_vec()),
        other @ (Value::Nat(_) | Value::NatAdd(..)) if Some(*d) == g.builtins.nat => {
            match native::split_value(&other) {
                Some(split) => split,
                None => return Ok(stuck_tree(stuck)),
            }
        }
        // A compact list: what matching its expansion would find.
        Value::Chars(chars) => match &g.builtins.text {
            Some(text) if text.list == *d => chars::split(text, &chars),
            _ => return Ok(stuck_tree(stuck)),
        },
        // An erased proof: matching it into data is allowed only for one
        // constructor with only proof fields (`E-PROP-ELIM`, `erase.rs`).
        v if erase::is_erased(&v) && g.data(*d).sort == Sort::Prop && !branches.is_empty() => {
            (0, vec![erased(); g.data(*d).ctors[0].fields.len()])
        }
        _ => return Ok(stuck_tree(stuck)),
    };
    let Some(body) = branches[c].body.clone() else {
        // An impossible branch is never reached by a well-typed value
        // (docs/proposals/indexed-families.md §6.8). A run that reaches one
        // anyway fails loudly; checking leaves the definition folded.
        if g.erasure.program_running() {
            panic!("internal error: unreachable: an impossible branch was reached");
        }
        return Ok(stuck_tree(stuck));
    };
    env.extend(fields);
    Ok(Control::Tree(body, env, stuck))
}

/// A case tree that can't take a step: its definition stays folded.
fn stuck_tree(stuck: Stuck) -> Control {
    match stuck {
        Some((id, spine, _)) => Control::Return(Value::Neutral(Head::Def(id), spine)),
        None => panic!("internal error: a case outside a definition's case tree got stuck"),
    }
}

/// A definition applied to `spine`: its native implementation, or its case
/// tree if it has all its arguments (kept as the call instead while gluing,
/// [`glues`]), or else it stays folded.
fn unfold(g: &Globals, id: DefId, spine: Spine) -> Result<Control> {
    unfold_now(g, id, spine, true)
}

/// Whether definition `id`, about to run its case tree, is kept as a call
/// ([`Value::Call`]) instead: gluing is on ([`Globals::glue`]), no program
/// is running, and it isn't a native (which computes at once on numbers).
/// Dictionaries, folded by name already, never get this far.
#[cold]
#[inline(never)]
fn glues(g: &Globals, id: DefId) -> bool {
    !g.erasure.program_running() && g.builtins.native(id).is_none()
}

/// [`unfold`], gluing only if `glue`: a call being forced unfolds now.
#[inline(always)]
fn unfold_now(g: &Globals, id: DefId, spine: Spine, glue: bool) -> Result<Control> {
    if spine.len() == g.def(id).arity && erases_result(g, id) {
        return Ok(Control::Return(erased()));
    }
    if g.builtins.float_def(id).is_some()
        && let Some(value) = crate::float::run(g, id, &spine, force)?
    {
        return Ok(Control::Return(value));
    }
    if let Some(op) = g.builtins.native(id)
        && op.arity() == spine.len()
    {
        match native::run(g, id, op, &spine, force)? {
            Some(native::Outcome::Done(value)) => return Ok(Control::Return(value)),
            Some(native::Outcome::Again(spine)) => return Ok(Control::Unfold(id, spine.into())),
            None => {}
        }
    }
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
                Elim::J { .. } => None,
            })
            .collect();
        if let Some(args) = args {
            if glue && g.glue.get() && glues(g, id) {
                return Ok(Control::Return(Value::Call(id, spine, Rc::default())));
            }
            let tree = Term::peel_lams_rc(body, def.arity);
            return Ok(Control::Tree(tree, args, Some((id, spine, true))));
        }
    }
    Ok(Control::Return(Value::Neutral(Head::Def(id), spine)))
}

/// Whether definition `id` stays folded when it has all its arguments, except
/// while a program runs: a dictionary ([`crate::globals::Def::fold`]) or a
/// theorem. A theorem's value is a proof, which only a `case` (on a
/// proposition), `J` or a comparison looks inside, and each of those unfolds
/// it first; so a proof that's only passed along is never computed (SW-281:
/// the fuel's proofs in a definition with `decreasing`). What's equal
/// doesn't change, only when it's computed.
fn folds(g: &Globals, id: DefId) -> bool {
    let def = g.def(id);
    (def.fold || def.theorem) && !g.erasure.program_running()
}

/// Folded call `value` ([`is_folded`]) is taken apart by the frame `next`:
/// its case tree runs in this machine, and `next` gets the result
/// ([`Frame::Unfolding`]).
fn unfold_for(g: &Globals, stack: &mut Vec<Frame>, value: Value, next: Frame) -> Result<Control> {
    let Value::Neutral(Head::Def(id), spine) = value else {
        unreachable!("checked by is_folded")
    };
    let def = g.def(id);
    let body = def.body.as_ref().expect("checked by is_folded");
    let args: Option<Vec<Value>> = spine
        .iter()
        .map(|e| match e {
            Elim::App(v, _) => Some(v.clone()),
            Elim::J { .. } => None,
        })
        .collect();
    let Some(args) = args else {
        return resume(g, next, Value::Neutral(Head::Def(id), spine), stack);
    };
    let tree = Term::peel_lams_rc(body, def.arity);
    push(
        g,
        stack,
        Frame::Unfolding(Box::new((id, spine.clone(), next))),
    )?;
    Ok(Control::Tree(tree, args, Some((id, spine, false))))
}

/// Whether `value` is a dictionary left folded by name ([`folds`]) that
/// [`unfold_folded`] would unfold; or a definition with a `Quot.lift` leaf
/// ([`folds_on_lift`]), which may be folded because of it: taking it apart,
/// or comparing it with something that isn't the same call with the same
/// arguments, looks at its body (docs/proposals/map-equality.md §7.2: the
/// policy changes what's shown and when things are computed, never what's
/// equal).
pub fn is_folded(g: &Globals, value: &Value) -> bool {
    matches!(value, Value::Neutral(Head::Def(id), spine)
        if (folds(g, *id) || folds_on_lift(g, *id) || native::folds_mul(g, *id, spine))
            && spine.len() == g.def(*id).arity
            && g.def(*id).body.is_some())
}

/// Whether definition `id`, applied to all its parameters, stays folded when
/// its case tree reaches a `Quot.lift` whose quotient isn't a `Quot.mk`, as
/// when it reaches a `case` that can't step: so a goal shows `Map.get k m`,
/// not the lift it unfolds to. Except while a program runs.
fn folds_on_lift(g: &Globals, id: DefId) -> bool {
    g.def(id).lift_leaf && !g.erasure.program_running()
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
            Term::Quot(QuotForm::Lift, args, _) if args.len() == QuotForm::Lift.arity() => {
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
pub fn unfold_folded(g: &Globals, value: &Value) -> Result<Option<Value>> {
    let mut current: Option<Value> = None;
    loop {
        let v = current.as_ref().unwrap_or(value);
        if !is_folded(g, v) {
            return Ok(current);
        }
        let Value::Neutral(Head::Def(id), spine) = v else {
            unreachable!()
        };
        let (id, spine) = (*id, spine.clone());
        let def = g.def(id);
        let body = def.body.as_ref().expect("checked by is_folded");
        let args: Option<Vec<Value>> = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => Some(v.clone()),
                Elim::J { .. } => None,
            })
            .collect();
        let Some(args) = args else {
            return Ok(current);
        };
        let tree = Term::peel_lams_rc(body, def.arity);
        let next = run(
            g,
            Control::Tree(tree, args, Some((id, spine.clone(), false))),
        )?;
        if let Value::Neutral(Head::Def(id2), s2) = &next
            && *id2 == id
            && s2.ptr_eq(&spine)
        {
            return Ok(current); // stuck
        }
        current = Some(next);
    }
}

/// Whether, while erasing, definition `id` (with a body) applied to all its
/// parameters is erased rather than run (`erase.rs`).
fn erases_result(g: &Globals, id: DefId) -> bool {
    g.erasure.active() && g.def(id).body.is_some() && erase::of_def(g, id).is_some_and(|e| e.result)
}

/// Whether, while erasing, the argument applied to `f` is erased: `f` is a
/// definition applied to some arguments, and the parameter it's for is.
fn erased_arg(g: &Globals, f: &Term) -> bool {
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
pub fn quote(g: &Globals, level: usize, value: &Value) -> Result<Term> {
    quote_as(g, level, value, false)
}

/// [`quote`], but a glued call ([`Value::Call`]) is written as the call,
/// its arguments read back the same way, rather than as its unfolding
/// (docs/proposals/folded-calls.md, stage 3): `List.length xs`, not what it
/// computes to. The two terms are convertible. Without gluing (the kernel)
/// there are no calls, and this is [`quote`].
pub fn quote_folded(g: &Globals, level: usize, value: &Value) -> Result<Term> {
    quote_as(g, level, value, true)
}

fn quote_as(g: &Globals, level: usize, value: &Value, folded: bool) -> Result<Term> {
    // A work list rather than recursion: `tasks` are values still to visit
    // and terms still to assemble, and `done` holds finished terms, which
    // each assembly takes its parts from.
    let mut tasks = vec![QuoteTask::Visit(level, value.clone())];
    let mut done: Vec<Term> = Vec::new();
    let mut size = 0u64;
    let limit = g.budget.size_limit();
    let rc = |t: Term| Rc::new(t);
    while let Some(task) = tasks.pop() {
        match task {
            QuoteTask::Visit(level, value) => {
                g.budget.step()?;
                size += 1;
                if size > limit {
                    return Err(ResourceError::Size);
                }
                visit(g, level, value, folded, &mut tasks, &mut done)?;
            }
            QuoteTask::Pi(x, i) => {
                let (a, b) = pop2(&mut done);
                done.push(Term::Pi(x, i, rc(a), rc(b)));
            }
            QuoteTask::Lam(x, i) => {
                let b = done.pop().expect("a body");
                done.push(Term::Lam(x, i, rc(b)));
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
                done.push(native::nat_add_term(g, &k, base));
            }
            QuoteTask::Eq => {
                let b = done.pop().expect("three parts");
                let (ty, a) = pop2(&mut done);
                done.push(Term::Eq(Some(rc(ty)), rc(a), rc(b)));
            }
            QuoteTask::Spine(head, shape) => {
                let n: usize = shape.iter().map(|s| if s.is_some() { 1 } else { 2 }).sum();
                let mut parts = done.split_off(done.len() - n).into_iter();
                let (mut term, shape) = match head {
                    SpineHead::Term(term) => (term, &shape[..]),
                    // The form's own arguments, then what applies its result.
                    SpineHead::Quot(form, k) => {
                        let args = parts.by_ref().take(k).map(Rc::new).collect();
                        (Term::Quot(form, args, false), &shape[k..])
                    }
                };
                for &icit in shape {
                    term = match icit {
                        Some(icit) => {
                            Term::app_icit(term, parts.next().expect("an argument"), icit)
                        }
                        None => {
                            let motive = parts.next().expect("a motive");
                            let base = parts.next().expect("a base");
                            Term::J(rc(motive), rc(base), rc(term))
                        }
                    };
                }
                done.push(term);
            }
        }
    }
    Ok(done.pop().expect("one term"))
}

/// Quotation still to do.
enum QuoteTask {
    /// Quote a value, with this many variables in scope.
    Visit(usize, Value),
    /// Assemble from the finished terms on top of the stack:
    Pi(Name, Icit),
    Lam(Name, Icit),
    Data(DataId, usize),
    Ctor(DataId, usize, usize),
    NatAdd(Rc<BigUint>),
    Eq,
    /// A head and its eliminations: `Some(icit)` an application, `None` a
    /// `J` (whose motive and base come first).
    Spine(SpineHead, Vec<Option<Icit>>),
}

/// The head of a neutral value being quoted.
pub(crate) enum SpineHead {
    Term(Term),
    /// A quotient form, whose arguments are the first this many
    /// eliminations.
    Quot(QuotForm, usize),
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

/// Quotes the outermost layer of `value`: finished at once, or an assembly
/// task with its parts to visit first.
fn visit(
    g: &Globals,
    level: usize,
    value: Value,
    folded: bool,
    tasks: &mut Vec<QuoteTask>,
    done: &mut Vec<Term>,
) -> Result<()> {
    // Parts are pushed last-first, so they're finished first-first.
    let visit_all = |tasks: &mut Vec<QuoteTask>, values: &[Value]| {
        for v in values.iter().rev() {
            tasks.push(QuoteTask::Visit(level, v.clone()));
        }
    };
    let value = if folded {
        match force_solved(g, value)? {
            Value::Call(id, spine, _) if !matches_at_once(g, id, &spine)? => {
                let args = call_args(&spine);
                tasks.push(QuoteTask::Spine(
                    SpineHead::Term(Term::Def(id)),
                    args.iter().map(|(_, i)| Some(*i)).collect(),
                ));
                for (v, _) in args.into_iter().rev() {
                    tasks.push(QuoteTask::Visit(level, v));
                }
                return Ok(());
            }
            other => force(g, other)?,
        }
    } else {
        force(g, value)?
    };
    match value {
        Value::Sort(s) => done.push(Term::Sort(s)),
        Value::Nat(n) => done.push(Term::Nat(n)),
        // The range, as a term; it means what its expansion would.
        Value::Chars(c) => done.push(match &g.builtins.text {
            Some(text) => chars::term(text, &c),
            None => unreachable!("a compact list without `List` and `Char`"),
        }),
        Value::Refl => done.push(Term::Refl),
        Value::Pi(x, i, a, b) => {
            tasks.push(QuoteTask::Pi(x, i));
            tasks.push(QuoteTask::Visit(level + 1, b.apply(g, Value::var(level))?));
            tasks.push(QuoteTask::Visit(level, (*a).clone()));
        }
        Value::Lam(x, i, b) => {
            tasks.push(QuoteTask::Lam(x, i));
            tasks.push(QuoteTask::Visit(level + 1, b.apply(g, Value::var(level))?));
        }
        Value::Data(d, args) => {
            tasks.push(QuoteTask::Data(d, args.len()));
            visit_all(tasks, &args);
        }
        // Read back folded, `Succ` of a call stays that: the call is what
        // was written.
        Value::Ctor(d, 1, args)
            if !folded && Some(d) == g.builtins.nat && has_call_base(g, &args) =>
        {
            visit(g, level, succ_unglued(g, &args[0])?, folded, tasks, done)?;
        }
        Value::Ctor(d, c, args) => {
            tasks.push(QuoteTask::Ctor(d, c, args.len()));
            visit_all(tasks, &args);
        }
        Value::NatAdd(k, base) => {
            tasks.push(QuoteTask::NatAdd(k));
            tasks.push(QuoteTask::Visit(level, (*base).clone()));
        }
        Value::Eq(ty, a, b) => {
            tasks.push(QuoteTask::Eq);
            visit_all(tasks, &[(*ty).clone(), (*a).clone(), (*b).clone()]);
        }
        Value::Neutral(head, spine) => {
            let head = match head {
                Head::Var(l) => SpineHead::Term(Term::Var(level - 1 - l)),
                Head::Def(id) => SpineHead::Term(Term::Def(id)),
                Head::Meta(m) => SpineHead::Term(Term::Meta(m)),
                Head::Quot(form) => SpineHead::Quot(form, quot_args_in(form, &spine)),
            };
            let mut shape = Vec::with_capacity(spine.len());
            let mut parts = Vec::new();
            for elim in &spine {
                match elim {
                    Elim::App(v, i) => {
                        shape.push(Some(*i));
                        parts.push(v.clone());
                    }
                    Elim::J { motive, base } => {
                        shape.push(None);
                        parts.push((**motive).clone());
                        parts.push((**base).clone());
                    }
                }
            }
            tasks.push(QuoteTask::Spine(head, shape));
            visit_all(tasks, &parts);
        }
        // Read back unfolded: `force` gave the unfolding.
        Value::Call(..) => unreachable!("a forced value is never a call"),
    }
    Ok(())
}

/// Whether `Succ` of `args` (a `Succ` value's field) is `Succ` applied,
/// perhaps several times, to a glued call ([`Value::Call`]). Without
/// gluing, `Succ` of a number is a number ([`native::ctor`]); a call is
/// a number only once unfolded, so the `Succ` around it stayed a
/// constructor. Never true without gluing (the kernel).
#[inline]
fn has_call_base(g: &Globals, args: &[Value]) -> bool {
    let mut field = &args[0];
    loop {
        match field {
            Value::Call(..) => return true,
            Value::Ctor(d, 1, inner) if Some(*d) == g.builtins.nat => field = &inner[0],
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
fn succ_unglued(g: &Globals, field: &Value) -> Result<Value> {
    let nat = g.builtins.nat.expect("a `Succ` value needs `Nat`");
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
pub fn conv(g: &Globals, level: usize, a: &Value, b: &Value) -> Result<bool> {
    let mut work = vec![ConvTask::Values(level, a.clone(), b.clone())];
    while let Some(task) = work.pop() {
        g.budget.step()?;
        let same = match task {
            ConvTask::Values(level, a, b) => conv_step(g, level, a, b, &mut work)?,
            // Function types' codomains, compared once their domains are.
            // The same function gives the same codomain (see `same_closure`).
            ConvTask::Codomains(_, b1, b2) if same_closure(&b1, &b2) => true,
            ConvTask::Codomains(level, b1, b2) => {
                let fresh = Value::var(level);
                work.push(ConvTask::Values(
                    level + 1,
                    b1.apply(g, fresh.clone())?,
                    b2.apply(g, fresh)?,
                ));
                true
            }
        };
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Comparison still to do.
enum ConvTask {
    Values(usize, Value, Value),
    Codomains(usize, Closure, Closure),
}

/// Compares the outermost layer of `a` and `b`: `false` if they differ
/// there; otherwise pushes the pairs of parts still to compare.
fn conv_step(
    g: &Globals,
    level: usize,
    a: Value,
    b: Value,
    work: &mut Vec<ConvTask>,
) -> Result<bool> {
    // Dictionaries left folded by name: the same one applied to equal
    // arguments is equal; otherwise they're compared unfolded. (Like a
    // partially applied definition below, this recurses once per level of
    // nested dictionaries, which is bounded by the program.) Before numbers
    // and text: a folded definition with `decreasing` can be a number
    // (`f n` against `1 + …`), and is compared as one once unfolded.
    if is_folded(g, &a) || is_folded(g, &b) {
        if let (Value::Neutral(Head::Def(i1), s1), Value::Neutral(Head::Def(i2), s2)) = (&a, &b)
            && i1 == i2
            && s1.len() == s2.len()
            && let Some(pairs) = spine_pairs(level, s1, s2)
        {
            let mut same = true;
            for pair in pairs {
                let ConvTask::Values(l, x, y) = pair else {
                    unreachable!()
                };
                if !conv(g, l, &x, &y)? {
                    same = false;
                    break;
                }
            }
            if same {
                return Ok(true);
            }
        }
        let a2 = unfold_folded(g, &a)?;
        let b2 = unfold_folded(g, &b)?;
        if a2.is_some() || b2.is_some() {
            work.push(ConvTask::Values(level, a2.unwrap_or(a), b2.unwrap_or(b)));
            return Ok(true);
        }
    }
    // Numbers, `k + x`, `Zero` and `Succ` all compare by their `k + x` forms:
    // `3` and `Succ x` are equal when `x` is `2`.
    if native::nat_like(g, &a) || native::nat_like(g, &b) {
        return native::compare(
            g,
            &a,
            &b,
            |x, y| {
                work.push(ConvTask::Values(level, x.clone(), y.clone()));
                Ok(true)
            },
            |_, _| Ok(false),
        );
    }
    // Compact lists: two ranges are equal when their characters are (their
    // expansions are then the same), and a range against anything else is
    // expanded one cell, which is then compared as a constructor. So a
    // compact `"a"` and `Cons (MkChar 97 h) Nil` are equal only if `h` and
    // `rfl` are.
    match (&a, &b) {
        (Value::Chars(x), Value::Chars(y)) => return Ok(x.as_slice() == y.as_slice()),
        (Value::Chars(_), _) => {
            work.push(ConvTask::Values(level, expand_step(g, a), b));
            return Ok(true);
        }
        (_, Value::Chars(_)) => {
            work.push(ConvTask::Values(level, a, expand_step(g, b)));
            return Ok(true);
        }
        _ => {}
    }
    let fresh = Value::var(level);
    // Parts are pushed last-first, so they're compared first-first.
    let push_all = |work: &mut Vec<ConvTask>, xs: &[Value], ys: &[Value]| {
        for (x, y) in xs.iter().zip(ys).rev() {
            work.push(ConvTask::Values(level, x.clone(), y.clone()));
        }
    };
    Ok(match (&a, &b) {
        (Value::Sort(s), Value::Sort(t)) => s == t,
        (Value::Pi(_, i1, a1, b1), Value::Pi(_, i2, a2, b2)) => {
            if i1 != i2 {
                return Ok(false);
            }
            work.push(ConvTask::Codomains(level, b1.clone(), b2.clone()));
            work.push(ConvTask::Values(level, (**a1).clone(), (**a2).clone()));
            true
        }
        // The same function, recognised without running it: comparing its
        // body applied to a fresh variable would find the same value twice.
        (Value::Lam(_, _, b1), Value::Lam(_, _, b2)) if same_closure(b1, b2) => true,
        (Value::Lam(_, _, b1), Value::Lam(_, _, b2)) => {
            work.push(ConvTask::Values(
                level + 1,
                b1.apply(g, fresh.clone())?,
                b2.apply(g, fresh)?,
            ));
            true
        }
        // Eta: `f` and `x => f x` are equal.
        (Value::Lam(_, i, b), other) | (other, Value::Lam(_, i, b)) => {
            work.push(ConvTask::Values(
                level + 1,
                b.apply(g, fresh.clone())?,
                apply_icit(g, other.clone(), fresh, *i)?,
            ));
            true
        }
        (Value::Data(d1, a1), Value::Data(d2, a2)) => {
            if d1 != d2 || a1.len() != a2.len() {
                return Ok(false);
            }
            push_all(work, a1, a2);
            true
        }
        (Value::Ctor(d1, c1, a1), Value::Ctor(d2, c2, a2)) => {
            if d1 != d2 || c1 != c2 || a1.len() != a2.len() {
                return Ok(false);
            }
            push_all(work, a1, a2);
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
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) if h1 == h2 && s1.len() == s2.len() => {
            if underapplied(g, &a).is_none() && underapplied(g, &b).is_none() {
                // Eta for definitions doesn't apply, so the spines must match.
                match spine_pairs(level, s1, s2) {
                    Some(pairs) => {
                        work.extend(pairs.into_iter().rev());
                        true
                    }
                    None => false,
                }
            } else {
                // A function: equal if the spines match, or else by eta. This
                // is the one place `conv` recurses, once per level of nested
                // partially applied definitions, which is bounded by the
                // program, not by the size of the data.
                let spines = match spine_pairs(level, s1, s2) {
                    Some(pairs) => {
                        let mut same = true;
                        for pair in pairs {
                            let ConvTask::Values(l, x, y) = pair else {
                                unreachable!()
                            };
                            if !conv(g, l, &x, &y)? {
                                same = false;
                                break;
                            }
                        }
                        same
                    }
                    None => false,
                };
                spines || push_eta(g, level, &a, &b, work)?
            }
        }
        // Two different definitions, each stuck on a `case`: compared by
        // their case trees (`same_stuck_trees`). Like a partially applied
        // definition above, this recurses: once per level of nested calls of
        // such definitions, in their leaves (bounded by the program, as they
        // aren't recursive) and in the scrutinees and arguments compared
        // (bounded by how deeply the data nests stuck calls). Deep nesting
        // ends in the stack guard (`budget.rs`, E-RESOURCE), not a crash.
        (Value::Neutral(Head::Def(i1), _), Value::Neutral(Head::Def(i2), _))
            if i1 != i2 && opens_by_tree(g, &a) && opens_by_tree(g, &b) =>
        {
            same_stuck_trees(g, level, &a, &b, Relation::Conv, &mut |l, x, y| {
                conv(g, l, x, y)
            })?
        }
        // Calls are compared by their unfoldings (D483: the kernel doesn't
        // compare two calls by their arguments first). The cases above
        // that a call can reach (numbers, compact lists, dictionaries, eta)
        // look inside it themselves.
        (Value::Call(..), _) | (_, Value::Call(..)) => {
            work.push(ConvTask::Values(level, force(g, a)?, force(g, b)?));
            true
        }
        _ => push_eta(g, level, &a, &b, work)?,
    })
}

/// The pairs of values in two spines of the same length, or `None` if their
/// eliminations don't match.
fn spine_pairs(level: usize, s1: &[Elim], s2: &[Elim]) -> Option<Vec<ConvTask>> {
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
                },
                Elim::J {
                    motive: m2,
                    base: b2,
                },
            ) => {
                pairs.push(ConvTask::Values(level, (**m1).clone(), (**m2).clone()));
                pairs.push(ConvTask::Values(level, (**b1).clone(), (**b2).clone()));
            }
            _ => return None,
        }
    }
    Some(pairs)
}

/// Eta for definitions: a partially applied definition is a function, so it's
/// compared with the other side by applying both to a fresh variable (as for
/// lambdas); `SCRes` defined as `SCRes o = PlusRes … o` then equals
/// `PlusRes …`. Pushes that comparison, or returns `false` if neither side is
/// a partially applied definition.
fn push_eta(
    g: &Globals,
    level: usize,
    a: &Value,
    b: &Value,
    work: &mut Vec<ConvTask>,
) -> Result<bool> {
    let Some(icit) = underapplied(g, a).or_else(|| underapplied(g, b)) else {
        return Ok(false);
    };
    let fresh = Value::var(level);
    work.push(ConvTask::Values(
        level + 1,
        apply_icit(g, a.clone(), fresh.clone(), icit)?,
        apply_icit(g, b.clone(), fresh, icit)?,
    ));
    Ok(true)
}

/// If `value` is a definition applied to fewer arguments than it takes (so
/// it's a function that doesn't unfold yet), the implicitness of its next
/// parameter.
pub fn underapplied(g: &Globals, value: &Value) -> Option<Icit> {
    let Value::Neutral(Head::Def(id), spine) = value else {
        return None;
    };
    let def = g.def(*id);
    let body = def.body.as_ref()?;
    if spine.len() >= def.arity {
        return None;
    }
    match body.peel_lams(spine.len()) {
        Term::Lam(_, icit, _) => Some(*icit),
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
// way could unfold forever), aren't folded by name (dictionaries and
// theorems, compared above) and have no `Quot.lift` leaf. A tree is compared
// node by node: a `case` whose scrutinee is a constructor takes its branch,
// as running it would; one stuck on a neutral value is compared with the
// other side's; leaves are compared as values. Any other shape (a `NumCase`,
// a number or a list as scrutinee, one side a leaf and the other a `case`)
// answers "different", as before.

/// Whether `value` is a definition applied to all its arguments that
/// [`same_stuck_trees`] can compare with another by its case tree.
pub fn opens_by_tree(g: &Globals, value: &Value) -> bool {
    let Value::Neutral(Head::Def(id), spine) = value else {
        return false;
    };
    let def = g.def(*id);
    def.body.is_some()
        && !def.recursive
        && !def.lift_leaf
        && !folds(g, *id)
        && def.arity > 0
        && spine.len() == def.arity
        && spine.iter().all(|e| matches!(e, Elim::App(..)))
        && g.builtins.native(*id).is_none()
        && g.builtins.float_def(*id).is_none()
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
/// selects, to the first `case` that's stuck or to a leaf.
fn walk_tree(g: &Globals, mut tree: Rc<Term>, mut env: Vec<Value>) -> Result<TreeEnd> {
    loop {
        g.budget.step()?;
        let node = Term::strip_loc_rc(&tree);
        match &*node {
            Term::Case(ix, _, branches) => {
                let scrutinee = force(g, env[env.len() - 1 - ix].clone())?;
                match &scrutinee {
                    Value::Ctor(_, c, fields) => {
                        let Some(body) = branches[*c].body.clone() else {
                            return Ok(TreeEnd::Other);
                        };
                        env.extend(fields.iter().cloned());
                        tree = body;
                    }
                    Value::Neutral(..) if !is_folded(g, &scrutinee) => {
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

/// Whether two different definitions, each applied to all its arguments and
/// stuck ([`opens_by_tree`] holds for both), are equal by their case trees,
/// with `same` comparing values (the scrutinees, then the leaves) by
/// `relation`. A pair already found equal in the same outermost comparison
/// is answered at once (see the comment above [`Relation`]).
pub fn same_stuck_trees(
    g: &Globals,
    level: usize,
    a: &Value,
    b: &Value,
    relation: Relation,
    same: &mut dyn FnMut(usize, &Value, &Value) -> Result<bool>,
) -> Result<bool> {
    let tree = |value: &Value| -> (Rc<Term>, Vec<Value>) {
        let Value::Neutral(Head::Def(id), spine) = value else {
            unreachable!("checked by opens_by_tree")
        };
        let def = g.def(*id);
        let body = def.body.as_ref().expect("checked by opens_by_tree");
        let args = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => v.clone(),
                Elim::J { .. } => unreachable!("checked by opens_by_tree"),
            })
            .collect();
        (Term::peel_lams_rc(body, def.arity), args)
    };
    let memo = TreeMemo::enter(g, level, a, b, relation)?;
    if memo.known_equal() {
        return Ok(true);
    }
    let (t1, e1) = tree(a);
    let (t2, e2) = tree(b);
    // Pairs of subtrees still to compare, each with its level.
    let mut pending = vec![(level, t1, e1, t2, e2)];
    while let Some((level, t1, e1, t2, e2)) = pending.pop() {
        match (walk_tree(g, t1, e1)?, walk_tree(g, t2, e2)?) {
            (TreeEnd::Leaf(t1, e1), TreeEnd::Leaf(t2, e2)) => {
                if !same(level, &eval(g, &e1, &t1)?, &eval(g, &e2, &t2)?)? {
                    return Ok(false);
                }
            }
            (TreeEnd::Stuck(n1, e1, s1), TreeEnd::Stuck(n2, e2, s2)) => {
                let (Term::Case(_, d1, b1), Term::Case(_, d2, b2)) = (&*n1, &*n2) else {
                    unreachable!("a stuck `case`")
                };
                if d1 != d2 || b1.len() != b2.len() || !same(level, &s1, &s2)? {
                    return Ok(false);
                }
                for (c, (x, y)) in b1.iter().zip(b2.iter()).enumerate().rev() {
                    match (&x.body, &y.body) {
                        (None, None) => {}
                        (Some(x), Some(y)) => {
                            let k = g.data(*d1).ctors[c].fields.len();
                            let fresh = (level..level + k).map(Value::var);
                            let mut e1 = e1.clone();
                            let mut e2 = e2.clone();
                            e1.extend(fresh.clone());
                            e2.extend(fresh);
                            pending.push((level + k, x.clone(), e1, y.clone(), e2));
                        }
                        _ => return Ok(false),
                    }
                }
            }
            _ => return Ok(false),
        }
    }
    memo.record_equal();
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
// it unusable. (The kernel's `conv` solves nothing, so its epoch doesn't
// move.) Only "equal" is remembered: a "different" nearly always ends the
// comparison it's part of, and in the elaborator it may be followed by
// solutions being taken back. The record lives as long as the outermost tree
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
/// Pairs under one key are told apart by [`identical`].
type MemoKey = (Relation, usize, u64, DefId, DefId, u64, u64);

/// This thread's open tree comparisons: how many, the pairs of calls found
/// equal since the outermost one started, and the shapes hashed since.
#[derive(Default)]
struct Memo {
    open: usize,
    pairs: HashMap<MemoKey, Vec<(Value, Value)>>,
    shapes: ShapeCache,
}

thread_local! {
    /// The [`Memo`] (emptied when the outermost comparison ends).
    static TREE_MEMO: std::cell::RefCell<Memo> = std::cell::RefCell::new(Memo::default());
}

/// One open tree comparison, with the pair it compares; dropping it closes
/// the comparison (even on an error).
struct TreeMemo {
    key: MemoKey,
    a: Value,
    b: Value,
}

impl TreeMemo {
    fn enter(
        g: &Globals,
        level: usize,
        a: &Value,
        b: &Value,
        relation: Relation,
    ) -> Result<TreeMemo> {
        let def = |v: &Value| match v {
            Value::Neutral(Head::Def(id), _) => *id,
            _ => unreachable!("checked by opens_by_tree"),
        };
        TREE_MEMO.with(|m| m.borrow_mut().open += 1);
        let mut memo = TreeMemo {
            key: (relation, level, g.meta_epoch.get(), def(a), def(b), 0, 0),
            a: a.clone(),
            b: b.clone(),
        };
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

    /// Whether this pair was already found equal.
    fn known_equal(&self) -> bool {
        !shortcuts_disabled()
            && TREE_MEMO.with(|m| {
                m.borrow().pairs.get(&self.key).is_some_and(|pairs| {
                    pairs.iter().any(|(x, y)| {
                        identical(Same::Values(x, &self.a)) && identical(Same::Values(y, &self.b))
                    })
                })
            })
    }

    /// Remembers that this pair is equal.
    fn record_equal(&self) {
        if shortcuts_disabled() {
            return;
        }
        TREE_MEMO.with(|m| {
            m.borrow_mut()
                .pairs
                .entry(self.key)
                .or_default()
                .push((self.a.clone(), self.b.clone()));
        });
    }
}

impl Drop for TreeMemo {
    fn drop(&mut self) {
        TREE_MEMO.with(|m| {
            let mut m = m.borrow_mut();
            m.open -= 1;
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

/// A part of a value to hash for [`shape_hash`]. The ones that are a shared
/// allocation (all but `Value`) are remembered by address in a
/// [`ShapeCache`].
#[derive(Clone, Copy)]
enum Part<'v> {
    Value(&'v Value),
    Boxed(&'v Rc<Value>),
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
    hashes: HashMap<(usize, usize), u64, std::hash::BuildHasherDefault<QuickHasher>>,
    /// The allocations hashed, kept alive while their addresses are keys,
    /// so no other can be allocated at one.
    owners: Vec<Owner>,
}

/// A handle on a shared allocation, only held to keep it alive.
#[allow(dead_code)]
enum Owner {
    Boxed(Rc<Value>),
    Fields(Values),
    Spine(Spine),
    Closure(Closure),
    Term(Rc<Term>),
}

/// A fast, non-cryptographic hasher (the multiply-and-rotate step of the
/// Rust compiler's `FxHasher`), for [`shape_hash`] and its cache. Its
/// hashes only file pairs to compare: a collision costs a comparison, never
/// a wrong answer.
#[derive(Default)]
struct QuickHasher(u64);

impl QuickHasher {
    fn add(&mut self, word: u64) {
        self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
}

impl std::hash::Hasher for QuickHasher {
    fn write(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks(8) {
            let mut word = [0u8; 8];
            word[..chunk.len()].copy_from_slice(chunk);
            self.add(u64::from_le_bytes(word));
        }
    }
    fn write_u8(&mut self, n: u8) {
        self.add(n.into());
    }
    fn write_u32(&mut self, n: u32) {
        self.add(n.into());
    }
    fn write_u64(&mut self, n: u64) {
        self.add(n);
    }
    fn write_usize(&mut self, n: usize) {
        self.add(n as u64);
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

impl Part<'_> {
    /// The address this part is remembered by, if it's a shared allocation.
    fn address(self) -> Option<(usize, usize)> {
        let at = |p: *const u8| p as usize;
        match self {
            Part::Value(_) => None,
            Part::Boxed(v) => Some((at(Rc::as_ptr(v).cast()), 0)),
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
/// hashes as just a call, since `identical` takes two with the same
/// unfolding cell as identical without looking further. Built bottom-up, each
/// layer from its own data and its parts' hashes, so a shared allocation is
/// hashed once ([`ShapeCache`]). A work list, as values can nest deeply; a
/// budget step per part hashed.
fn shape_hash(g: &Globals, cache: &mut ShapeCache, value: &Value) -> Result<u64> {
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
                g.budget.step()?;
                let mut h = QuickHasher::default();
                let mut parts: Vec<Part> = Vec::new();
                match part {
                    Part::Value(v) => {
                        std::mem::discriminant(v).hash(&mut h);
                        match v {
                            Value::Sort(s) => s.hash(&mut h),
                            Value::Pi(_, i, a, b) => {
                                i.hash(&mut h);
                                parts.extend([Part::Boxed(a), Part::Closure(b)]);
                            }
                            Value::Lam(_, i, b) => {
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
                            Value::Refl | Value::Call(..) => {}
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
                                Elim::J { motive, base } => {
                                    1u8.hash(&mut h);
                                    parts.extend([Part::Value(motive), Part::Value(base)]);
                                }
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
                            Term::Pi(_, i, a, b) => {
                                i.hash(&mut h);
                                parts.extend([Part::Term(a), Part::Term(b)]);
                            }
                            Term::Lam(_, i, b) => {
                                i.hash(&mut h);
                                parts.push(Part::Term(b));
                            }
                            Term::App(f, a, i) => {
                                i.hash(&mut h);
                                parts.extend([Part::Term(f), Part::Term(a)]);
                            }
                            Term::Ann(e, ty) => parts.extend([Part::Term(e), Part::Term(ty)]),
                            Term::Let(_, ty, v, b, s) => {
                                s.hash(&mut h);
                                parts.extend([Part::Term(ty), Part::Term(v), Part::Term(b)]);
                            }
                            Term::Eq(ty, x, y) => {
                                ty.is_some().hash(&mut h);
                                parts.extend(ty.iter().map(Part::Term));
                                parts.extend([Part::Term(x), Part::Term(y)]);
                            }
                            Term::J(m, b, p) => {
                                parts.extend([Part::Term(m), Part::Term(b), Part::Term(p)]);
                            }
                            Term::Quot(f, xs, e) => {
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
// answered "equal", never change an answer (apart from not running out of
// resources where the long way would have).
//
// The elaborator's unification (`crates/elab/src/unify.rs`) uses it too:
// unifying identical values succeeds without solving any metavariable (a
// metavariable against itself only unifies the identical arguments), so
// answering at once changes nothing there either.

#[cfg(any(test, feature = "reference"))]
thread_local! {
    static SHORTCUTS_OFF: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Turns the identical-closure shortcut of [`conv`] (and of the elaborator's
/// unification), and the record of pairs of calls found equal
/// ([`same_stuck_trees`]), off, or back on, on this thread: for tests
/// comparing the verdicts with and without them.
#[cfg(any(test, feature = "reference"))]
pub fn set_shortcuts_disabled(disabled: bool) {
    SHORTCUTS_OFF.with(|s| s.set(disabled));
}

#[inline]
fn shortcuts_disabled() -> bool {
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
/// they're never looked at.
pub fn same_closure(a: &Closure, b: &Closure) -> bool {
    !shortcuts_disabled() && identical(Same::Closures(a, b))
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

/// Whether two values, closures or terms are exactly alike (see
/// [`same_closure`]). A work list, not recursion, as values can nest deeply.
/// No evaluation: the cost is at most the size of the smaller side.
fn identical(first: Same) -> bool {
    let mut work = vec![first];
    while let Some(pair) = work.pop() {
        let alike = match pair {
            Same::Values(a, b) => same_layer(a, b, &mut work),
            Same::Closures(a, b) => same_closure_layer(a, b, &mut work),
            Same::Terms(a, b) => same_term_layer(a, b, &mut work),
        };
        if !alike {
            return false;
        }
    }
    true
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

/// Compares the outermost layer of two values for [`identical`], pushing
/// their parts.
fn same_layer<'v>(a: &'v Value, b: &'v Value, work: &mut Vec<Same<'v>>) -> bool {
    let rc_values = |work: &mut Vec<Same<'v>>, x: &'v Rc<Value>, y: &'v Rc<Value>| {
        if !Rc::ptr_eq(x, y) {
            work.push(Same::Values(x, y));
        }
    };
    let all = |work: &mut Vec<Same<'v>>, xs: &'v [Value], ys: &'v [Value]| {
        work.extend(xs.iter().zip(ys).map(|(x, y)| Same::Values(x, y)));
    };
    match (a, b) {
        (Value::Sort(s), Value::Sort(t)) => s == t,
        (Value::Pi(_, i1, a1, b1), Value::Pi(_, i2, a2, b2)) => {
            rc_values(work, a1, a2);
            work.push(Same::Closures(b1, b2));
            i1 == i2
        }
        (Value::Lam(_, i1, b1), Value::Lam(_, i2, b2)) => {
            work.push(Same::Closures(b1, b2));
            i1 == i2
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
            if h1 == h2 && s1.ptr_eq(s2) {
                return true;
            }
            if h1 != h2 || s1.len() != s2.len() {
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
                        },
                        Elim::J {
                            motive: m2,
                            base: b2,
                        },
                    ) => {
                        work.push(Same::Values(m1, m2));
                        work.push(Same::Values(b1, b2));
                    }
                    _ => return false,
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
                    _ => return false,
                }
            }
            true
        }
        _ => false,
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
        (Term::Pi(_, i1, a1, b1), Term::Pi(_, i2, a2, b2)) => {
            both(a1, a2);
            both(b1, b2);
            i1 == i2
        }
        (Term::Lam(_, i1, b1), Term::Lam(_, i2, b2)) => {
            both(b1, b2);
            i1 == i2
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
        (Term::Let(_, t1, v1, b1, s1), Term::Let(_, t2, v2, b2, s2)) => {
            both(t1, t2);
            both(v1, v2);
            both(b1, b2);
            s1 == s2
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
        (Term::J(m1, b1, p1), Term::J(m2, b2, p2)) => {
            both(m1, m2);
            both(b1, b2);
            both(p1, p2);
            true
        }
        (Term::Quot(f1, xs, e1), Term::Quot(f2, ys, e2)) => {
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

    fn closure(env: Vec<Value>, body: Term) -> Closure {
        Closure {
            env: env.into(),
            body: rc(body),
        }
    }

    fn lam(c: Closure) -> Value {
        Value::Lam("x".into(), Icit::Explicit, c)
    }

    /// `conv` with and without the shortcut, which must agree; and the steps
    /// each took.
    fn conv_both(g: &Globals, a: &Value, b: &Value) -> (bool, u64, u64) {
        let before = g.budget.total_work();
        let with = conv(g, 0, a, b).unwrap();
        let middle = g.budget.total_work();
        set_shortcuts_disabled(true);
        let without = conv(g, 0, a, b);
        set_shortcuts_disabled(false);
        let without = without.unwrap();
        let after = g.budget.total_work();
        assert_eq!(with, without, "the shortcut changed conv's answer");
        (with, middle - before, after - middle)
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
        assert!(same_closure(&a, &b));
        let g = Globals::default();
        let (equal, with, without) = conv_both(&g, &lam(a), &lam(b));
        assert!(equal);
        assert!(with < without, "the shortcut was taken: {with} < {without}");
    }

    #[test]
    fn identical_values_have_the_same_shape_hash() {
        // The same closures as above, inside separately built constructors
        // and calls: identical, so filed under the same hash, each with a
        // cache of its own and with one shared.
        let g = Globals::default();
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
        let hash = shape_hash(&g, &mut shared, &x).unwrap();
        assert_eq!(hash, shape_hash(&g, &mut shared, &y).unwrap());
        assert_eq!(
            hash,
            shape_hash(&g, &mut ShapeCache::default(), &y).unwrap()
        );
        // A used variable's value counts.
        let c = closure(vec![Value::var(7), Value::var(4)], call_last());
        let z = wrap(c);
        assert!(!identical(Same::Values(&x, &z)));
        assert_ne!(hash, shape_hash(&g, &mut shared, &z).unwrap());
    }

    #[test]
    fn a_different_value_for_a_used_variable_is_not_the_same_closure() {
        let a = closure(vec![Value::var(3)], call_last());
        let b = closure(vec![Value::var(4)], call_last());
        assert!(!same_closure(&a, &b));
        let g = Globals::default();
        assert!(!conv_both(&g, &lam(a), &lam(b)).0);
    }

    #[test]
    fn a_different_body_is_not_the_same_closure() {
        let a = closure(vec![Value::var(3)], call_last());
        let b = closure(
            vec![Value::var(3)],
            Term::App(rc(Term::Var(1)), rc(Term::Var(1)), Icit::Explicit),
        );
        assert!(!same_closure(&a, &b));
        let implicit = closure(
            vec![Value::var(3)],
            Term::App(rc(Term::Var(1)), rc(Term::Var(0)), Icit::Implicit),
        );
        assert!(!same_closure(&a, &implicit));
        let g = Globals::default();
        assert!(!conv_both(&g, &lam(a.clone()), &lam(b)).0);
        // (Conversion ignores how an argument is passed, so this pair is
        // equal the long way; `conv_both` checks the two ways agree.)
        assert!(conv_both(&g, &lam(a), &lam(implicit)).0);
    }

    #[test]
    fn closures_in_the_environment_are_compared_by_identity_too() {
        let inner = |n| lam(closure(vec![Value::var(n)], call_last()));
        let a = closure(vec![inner(3)], call_last());
        let b = closure(vec![inner(3)], call_last());
        assert!(same_closure(&a, &b));
        let c = closure(vec![inner(4)], call_last());
        assert!(!same_closure(&a, &c));
    }

    #[test]
    fn convertible_but_not_identical_closures_are_still_equal() {
        // `f` against `y => f y`: equal by eta, which only the long way sees.
        let f = Value::var(3);
        let eta = lam(closure(vec![f.clone()], call_last()));
        let a = closure(vec![f], call_last());
        let b = closure(vec![eta], call_last());
        assert!(!same_closure(&a, &b));
        let g = Globals::default();
        assert!(conv_both(&g, &lam(a), &lam(b)).0);
    }

    #[test]
    fn function_types_with_the_same_codomain_are_equal() {
        let pi = |env: Vec<Value>| {
            Value::Pi(
                "x".into(),
                Icit::Explicit,
                Rc::new(Value::Sort(Sort::Type(0))),
                closure(env, call_last()),
            )
        };
        let g = Globals::default();
        let (equal, with, without) =
            conv_both(&g, &pi(vec![Value::var(2)]), &pi(vec![Value::var(2)]));
        assert!(equal);
        assert!(with < without);
        assert!(!conv_both(&g, &pi(vec![Value::var(2)]), &pi(vec![Value::var(5)])).0);
    }
}
