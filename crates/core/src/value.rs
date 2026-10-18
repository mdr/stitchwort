//! Values, evaluation, quotation and conversion (normalisation by evaluation).
//!
//! Variables in values are de Bruijn *levels*: `Var(0)` is the outermost binder.
//!
//! Reduction policy: a definition stays folded (a neutral `Def` head) until it
//! has all its parameters *and* its case tree can take a step. This keeps
//! comparison from unfolding recursive definitions forever. See `docs/core.md`.

use std::rc::Rc;

use num_bigint::BigUint;

use crate::budget::{ResourceError, Result};
use crate::chars::{self, Chars};
use crate::erase::{self, erased};
use crate::globals::Globals;
use crate::native;
use crate::term::{DataId, DefId, Icit, Name, Sort, Term};

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
    Neutral(Head, Vec<Elim>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Head {
    Var(usize),
    Def(DefId),
    Meta(usize),
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
        Value::Neutral(_, spine) => {
            for elim in spine {
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
    Value::Neutral(Head::Var(usize::MAX), Vec::new())
}

impl Value {
    pub fn var(level: usize) -> Value {
        Value::Neutral(Head::Var(level), Vec::new())
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

/// Replaces a solved metavariable at the head of `value` by its solution.
pub fn force(g: &Globals, value: Value) -> Result<Value> {
    match &value {
        Value::Neutral(Head::Meta(m), _) if g.meta_solution(*m).is_some() => {
            run(g, Control::Force(value))
        }
        _ => Ok(value),
    }
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

/// What the machine does next.
enum Control {
    /// Evaluate a term.
    Eval(Rc<Term>, Env),
    /// Apply a value to an argument. (Boxed: it's the largest state, and most
    /// applications happen directly, through [`apply_step`].)
    Apply(Box<(Value, Value, Icit)>),
    /// A definition with these arguments: run its native implementation or
    /// its case tree, or leave it folded.
    Unfold(DefId, Vec<Elim>),
    /// Walk a case tree. If it's stuck, the result is the definition left
    /// folded (or, for a case outside a definition, an internal error).
    Tree(Rc<Term>, Vec<Value>, Option<(DefId, Vec<Elim>)>),
    /// Replace a solved metavariable at the head of a value.
    Force(Value),
    /// Give a value to the frame on top of the stack.
    Return(Value),
}

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
    /// The motive of a stuck `J` (the base is next).
    JMotive {
        term: Rc<Term>,
        env: Env,
        head: Head,
        spine: Vec<Elim>,
    },
    /// The base of a stuck `J`: its head, spine and motive. (Boxed: it's the
    /// largest frame, and rare.)
    JBase(Box<(Head, Vec<Elim>, Value)>),
    /// The forced scrutinee of the case node `tree`.
    Scrutinee {
        tree: Rc<Term>,
        env: Vec<Value>,
        stuck: Option<(DefId, Vec<Elim>)>,
    },
    /// A metavariable's solution, or the result of applying it so far:
    /// apply the eliminations of `spine` from `next` on, then force again.
    Replay { spine: Vec<Elim>, next: usize },
    /// The forced value a `J` elimination at `spine[next]` applies to.
    ReplayJ { spine: Vec<Elim>, next: usize },
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
        other => panic!("internal error: applying {}", describe(&other)),
    }
}

/// Applying a closure: evaluating its body with the argument added.
fn enter(closure: &Closure, arg: Value) -> Control {
    // Built in place, in one allocation.
    let env: Rc<[Value]> = closure
        .env
        .iter()
        .cloned()
        .chain(std::iter::once(arg))
        .collect();
    Control::Eval(closure.body.clone(), Values(env))
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
                apply_step(f, arg, icit)
            }
            Control::Unfold(id, spine) => unfold(g, id, spine)?,
            Control::Tree(node, env, stuck) => {
                let node = Term::strip_loc_rc(&node);
                match &*node {
                    Term::Case(ix, ..) | Term::NumCase(ix, ..) => {
                        let scrutinee = env[env.len() - 1 - ix].clone();
                        if needs_forcing(g, &scrutinee) {
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
                Some(_) if def.arity == 0 => None,
                _ => Some(Value::Neutral(Head::Def(*id), Vec::new())),
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
                Some(body) if def.arity == 0 => Control::Eval(body.clone(), Values::from([])),
                _ => Control::Return(Value::Neutral(Head::Def(*id), Vec::new())),
            }
        }
        Term::Meta(m) => Control::Return(match g.meta_solution(*m) {
            Some(value) => value,
            None => Value::Neutral(Head::Meta(*m), Vec::new()),
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
        Frame::JForced { term, env } => {
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
        Frame::Scrutinee { tree, env, stuck } => branch(g, tree, env, stuck, value)?,
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

/// Whether `value` is headed by a solved metavariable.
fn needs_forcing(g: &Globals, value: &Value) -> bool {
    matches!(value, Value::Neutral(Head::Meta(m), _) if g.meta_solution(*m).is_some())
}

/// The branch of the case node `tree` for the (forced) scrutinee `value`.
fn branch(
    g: &Globals,
    tree: Rc<Term>,
    mut env: Vec<Value>,
    stuck: Option<(DefId, Vec<Elim>)>,
    value: Value,
) -> Result<Control> {
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
    env.extend(fields);
    Ok(Control::Tree(branches[c].body.clone(), env, stuck))
}

/// A case tree that can't take a step: its definition stays folded.
fn stuck_tree(stuck: Option<(DefId, Vec<Elim>)>) -> Control {
    match stuck {
        Some((id, spine)) => Control::Return(Value::Neutral(Head::Def(id), spine)),
        None => panic!("internal error: a case outside a definition's case tree got stuck"),
    }
}

/// A definition applied to `spine`: its native implementation, or its case
/// tree if it has all its arguments, or else it stays folded.
fn unfold(g: &Globals, id: DefId, spine: Vec<Elim>) -> Result<Control> {
    if spine.len() == g.def(id).arity && erases_result(g, id) {
        return Ok(Control::Return(erased()));
    }
    if let Some(op) = g.builtins.native(id)
        && op.arity() == spine.len()
    {
        match native::run(g, id, op, &spine, force)? {
            Some(native::Outcome::Done(value)) => return Ok(Control::Return(value)),
            Some(native::Outcome::Again(spine)) => return Ok(Control::Unfold(id, spine)),
            None => {}
        }
    }
    let def = g.def(id);
    if let Some(body) = &def.body
        && def.arity == spine.len()
    {
        let args: Option<Vec<Value>> = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => Some(v.clone()),
                Elim::J { .. } => None,
            })
            .collect();
        if let Some(args) = args {
            let tree = Term::peel_lams_rc(body, def.arity);
            return Ok(Control::Tree(tree, args, Some((id, spine))));
        }
    }
    Ok(Control::Return(Value::Neutral(Head::Def(id), spine)))
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
/// Solved metavariables are replaced by their solutions.
pub fn quote(g: &Globals, level: usize, value: &Value) -> Result<Term> {
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
                visit(g, level, value, &mut tasks, &mut done)?;
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
                let mut term = head;
                for icit in shape {
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
    Spine(Term, Vec<Option<Icit>>),
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
    tasks: &mut Vec<QuoteTask>,
    done: &mut Vec<Term>,
) -> Result<()> {
    // Parts are pushed last-first, so they're finished first-first.
    let visit_all = |tasks: &mut Vec<QuoteTask>, values: &[Value]| {
        for v in values.iter().rev() {
            tasks.push(QuoteTask::Visit(level, v.clone()));
        }
    };
    match force(g, value)? {
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
                Head::Var(l) => Term::Var(level - 1 - l),
                Head::Def(id) => Term::Def(id),
                Head::Meta(m) => Term::Meta(m),
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
    }
    Ok(())
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
        (Value::Lam(_, _, b1), Value::Lam(_, _, b2)) => {
            work.push(ConvTask::Values(
                level + 1,
                b1.apply(g, fresh.clone())?,
                b2.apply(g, fresh)?,
            ));
            true
        }
        // Eta: `f` and `\x -> f x` are equal.
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
