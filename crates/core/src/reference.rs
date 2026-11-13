//! A reference evaluator, for testing the real one
//! (docs/proposals/stack-safe-evaluation.md).
//!
//! This is the straightforward recursive evaluator the abstract machine in
//! `value.rs` was derived from. It's kept so the two can be compared on the
//! same programs: they have different control flow, so a mistake in one
//! (frames applied in the wrong order, a lost argument, a wrong environment)
//! shows up as a disagreement.
//!
//! It must stay independent: it shares the data types (`Term`, `Value`,
//! `Kernel`) and the native number functions, which it calls with its own
//! `force`, but never calls anything in `value.rs` that evaluates. It isn't
//! optimised, and only changes when the language's evaluation rules do. It
//! recurses on the Rust stack, so it's only for small inputs, and it counts
//! no resources unless a test sets it a step budget ([`set_budget`]).
//!
//! Only compiled for tests (the `reference` feature).
//!
//! **The plain evaluator.** [`set_plain`] turns every fold off on this
//! thread (docs/proposals/equality-in-the-round.md, T1): the evaluator that
//! says what is *equal*, against which each lazy mode must agree. In plain
//! mode no value is kept folded or compact, so every call computes as
//! written, whenever its case tree can step:
//!
//! - [`folds`], [`folds_on_lift`] and [`folds_mul`] are false, and they are
//!   the only places this module asks whether a call stays folded
//!   (dictionaries, theorems, `decreasing` definitions, calls folded on a
//!   `Quot.lift`, `k * x`); so `is_folded` and `unfold_folded` find nothing.
//!   Fields of calls follow: `(f x).i` projects the computed value.
//! - A number is built from `Zero` and `Succ` only: [`Term::Nat`], a
//!   constructor term ([`native::ctor`] is not used), a compact list's
//!   character codes and the result of `+`'s rules R3 and R4 ([`nat`]).
//! - The number natives are not run (`Nat.add` and the others compute by
//!   their definitions). Float primitives have no definition to run, so
//!   they still do.
//! - It never glues, as always, and a compact list is expanded on sight.
//!
//! What it still keeps is `+`'s rules R3 and R4 (they define what is equal,
//! not how it's computed) and the number view that a number `match` reads
//! its `Succ`s through, which is a way of looking at a chain of `Succ`s, not
//! a second spelling of one. [`compact_or_lazy`] checks a value for any
//! compact spelling or glued call that slipped in.

use crate::ev::Ev;
use std::rc::Rc;

use crate::budget::Result;
use crate::native;
use crate::term::{Branch, DefId, Icit, QuotForm, Sort, Term};
use crate::value::{Closure, Elim, Head, Mode, Shared, Spine, Value, quot_mk_rep, quot_value};

thread_local! {
    static PLAIN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Turns the plain evaluator (see the module doc) on or off on this thread.
/// Not reachable from the CLI: only tests call it.
pub fn set_plain(plain: bool) {
    PLAIN.with(|p| p.set(plain));
}

fn plain() -> bool {
    PLAIN.with(|p| p.get())
}

thread_local! {
    /// Steps left to the plain evaluator.
    static PLAIN_STEPS: std::cell::Cell<u64> = const { std::cell::Cell::new(u64::MAX) };
}

/// Gives the plain evaluator `steps` evaluations and comparisons before it
/// fails with [`crate::budget::ResourceError::Work`] (never "different":
/// D2543), so that a term that computes slowly can't hang a test. The
/// ordinary reference evaluator counts nothing.
pub fn set_plain_budget(steps: u64) {
    PLAIN_STEPS.with(|s| s.set(steps));
}

thread_local! {
    /// Steps left to the evaluator in any mode, or `None` for no limit.
    static STEPS: std::cell::Cell<Option<u64>> = const { std::cell::Cell::new(None) };
}

/// Gives this thread's reference evaluator, plain or not, `steps`
/// evaluations, read-back nodes and comparisons before it fails with
/// [`crate::budget::ResourceError::Work`]; `None` removes the limit (the
/// default). It shares nothing, so a normal form that is exponentially large
/// takes exponentially many steps to read back or compare: the budget lets a
/// test report that it is too big instead of filling memory. A run that
/// finishes within it gives the same result as one with no budget.
pub fn set_budget(steps: Option<u64>) {
    STEPS.with(|s| s.set(steps));
}

/// One step of the evaluator, counted against [`set_budget`]'s budget and,
/// in plain mode, [`set_plain_budget`]'s.
fn step() -> Result<()> {
    STEPS.with(|s| match s.get() {
        None => Ok(()),
        Some(0) => Err(crate::budget::ResourceError::Work),
        Some(left) => {
            s.set(Some(left - 1));
            Ok(())
        }
    })?;
    plain_step()
}

/// One step of the plain evaluator.
fn plain_step() -> Result<()> {
    if !plain() {
        return Ok(());
    }
    PLAIN_STEPS.with(|s| match s.get().checked_sub(1) {
        Some(left) => {
            s.set(left);
            Ok(())
        }
        None => Err(crate::budget::ResourceError::Work),
    })
}

/// The number `n` as the evaluator builds it: compact, or in plain mode
/// `Succ` applied to `Zero` that many times.
fn nat(g: &Ev, n: &num_bigint::BigUint) -> Value {
    if !plain() {
        return Value::Nat(Rc::new(n.clone()));
    }
    let data = g.env.builtins().nat.expect("a number needs `Nat`");
    let mut value = Value::Ctor(data, 0, Vec::new().into());
    let mut left = n.clone();
    while !num_traits::Zero::is_zero(&left) {
        value = Value::Ctor(data, 1, vec![value].into());
        left -= 1u32;
    }
    value
}

/// `k + base` as `Succ` applied `k` times, or compact outside plain mode.
fn nat_from_view(g: &Ev, k: num_bigint::BigUint, base: Option<Value>) -> Value {
    if !plain() {
        return native::from_view(k, base);
    }
    let data = g.env.builtins().nat.expect("a number needs `Nat`");
    let mut value = base.unwrap_or_else(|| Value::Ctor(data, 0, Vec::new().into()));
    let mut left = k;
    while !num_traits::Zero::is_zero(&left) {
        value = Value::Ctor(data, 1, vec![value].into());
        left -= 1u32;
    }
    value
}

/// [`native::folds_mul`], never in plain mode.
fn folds_mul(g: &Ev, id: DefId, spine: &[Elim]) -> bool {
    !plain() && native::folds_mul(g, id, spine)
}

/// A compact number or list, a glued call or a lazy field of a call
/// anywhere in `value`: what plain mode must never produce. Looks through
/// constructors, data types, equations and spines, not into closures, nor
/// into a `Float`, whose bits the float primitives always make a number.
pub fn compact_or_lazy(g: &Ev, value: &Value) -> Option<&'static str> {
    let find = |xs: &[Value]| xs.iter().find_map(|v| compact_or_lazy(g, v));
    match value {
        Value::Nat(_) | Value::NatAdd(..) => Some("a compact number"),
        Value::Chars(_) => Some("a compact list"),
        Value::Call(..) => Some("a glued call"),
        Value::Ctor(d, _, _) if Some(*d) == g.env.builtins().float.data => None,
        Value::Ctor(_, _, xs) => find(xs),
        Value::Data(_, xs) => find(xs),
        Value::Eq(t, a, b) => [t, a, b].into_iter().find_map(|v| compact_or_lazy(g, v)),
        Value::Pi(_, _, a, _) => compact_or_lazy(g, a),
        Value::Neutral(_, spine) => spine.iter().find_map(|e| match e {
            Elim::App(v, _) => compact_or_lazy(g, v),
            Elim::J { motive, base } => {
                compact_or_lazy(g, motive).or_else(|| compact_or_lazy(g, base))
            }
            Elim::Proj(..) => None,
        }),
        _ => None,
    }
}

pub fn eval(g: &Ev, env: &[Value], term: &Term) -> Result<Value> {
    step()?;
    let eval_all = |args: &[Rc<Term>]| -> Result<Vec<Value>> {
        args.iter().map(|a| eval(g, env, a)).collect()
    };
    Ok(match term {
        Term::Var(ix) => env[env.len() - 1 - ix].clone(),
        Term::Def(id) => {
            let def = g.def(*id);
            match seen(g, *id) {
                Some(body) if def.arity == 0 && !folds(g, *id) => eval(g, &[], body)?,
                _ => Value::Neutral(Head::Def(*id), Spine::new()),
            }
        }
        Term::Meta(m) => match g.meta_solution(*m) {
            Some(value) => value,
            None => Value::Neutral(Head::Meta(*m), Spine::new()),
        },
        Term::Data(d, args) => Value::Data(*d, eval_all(args)?.into()),
        Term::Ctor(d, c, args) if plain() => Value::Ctor(*d, *c, eval_all(args)?.into()),
        Term::Ctor(d, c, args) => native::ctor(g, *d, *c, eval_all(args)?),
        Term::Nat(n) => nat(g, n),
        // A compact list is its expansion, built here in full: this evaluator
        // doesn't share the machine's rules for ranges.
        Term::Chars(chars) => expand(g, chars.as_slice()),
        Term::Sort(s) => Value::Sort(*s),
        Term::Pi(x, i, a, b) => Value::Pi(
            x.clone(),
            *i,
            Shared::new(eval(g, env, a)?),
            Closure {
                env: env.into(),
                body: b.clone(),
            },
        ),
        Term::Lam(x, i, b) => Value::Lam(
            x.clone(),
            *i,
            Closure {
                env: env.into(),
                body: b.clone(),
            },
        ),
        Term::App(f, a, i) => {
            let f = eval(g, env, f)?;
            apply_icit(g, f, eval(g, env, a)?, *i)?
        }
        Term::Ann(e, _) => eval(g, env, e)?,
        Term::Let(_, _, value, body, _) => {
            let mut env = env.to_vec();
            env.push(eval(g, &env, value)?);
            eval(g, &env, body)?
        }
        Term::Case(..) | Term::NumCase(..) => eval_tree(g, env.to_vec(), term, false, false)?
            .expect("internal error: a case outside a definition's case tree got stuck"),
        Term::Eq(ty, a, b) => Value::Eq(
            Shared::new(eval(
                g,
                env,
                ty.as_ref()
                    .expect("internal error: evaluating an unchecked equation"),
            )?),
            Shared::new(eval(g, env, a)?),
            Shared::new(eval(g, env, b)?),
        ),
        Term::Refl => Value::Refl,
        Term::J(motive, base, proof) => match unfold_folded(g, force(g, eval(g, env, proof)?)?)? {
            Value::Refl => eval(g, env, base)?,
            Value::Neutral(head, mut spine) => {
                spine.push(Elim::J {
                    motive: Box::new(eval(g, env, motive)?),
                    base: Box::new(eval(g, env, base)?),
                });
                Value::Neutral(head, spine)
            }
            _ => panic!("internal error: J applied to a non-proof"),
        },
        // The one computation rule: `Quot.lift f h (Quot.mk a)` is `f a`.
        Term::Quot(form, args, _) => eval_quot(g, env, *form, args)?,
        Term::Loc(_, t) => eval(g, env, t)?,
        Term::Proj(d, i, t) => project(g, *d, *i, eval(g, env, t)?)?,
    })
}

/// Field `i` of a value of data type `d`, which has eta: the constructor's
/// field, or the projection stuck on an unknown.
fn project(g: &Ev, d: crate::term::DataId, i: usize, value: Value) -> Result<Value> {
    Ok(match unfold_folded(g, force(g, value)?)? {
        Value::Ctor(d2, 0, fields) if d2 == d => fields[i].clone(),
        Value::Neutral(head, mut spine) => {
            spine.push(Elim::Proj(d, i));
            Value::Neutral(head, spine)
        }
        _ => panic!("internal error: a projection of a non-record"),
    })
}

/// Whether a `case` on type `d` takes its only branch on a neutral by
/// record eta's rule 2: `d` has eta.
fn eta_case(g: &Ev, d: crate::term::DataId) -> bool {
    g.env.datas().get(d.0).is_some_and(|data| data.eta())
}

pub fn apply_closure(g: &Ev, closure: &Closure, arg: Value) -> Result<Value> {
    let mut env = closure.env.to_vec();
    env.push(arg);
    eval(g, &env, &closure.body)
}

pub fn apply_icit(g: &Ev, f: Value, arg: Value, icit: Icit) -> Result<Value> {
    match f {
        Value::Lam(_, _, closure) => apply_closure(g, &closure, arg),
        Value::Neutral(Head::Def(id), mut spine) => {
            spine.push(Elim::App(arg, icit));
            unfold(g, id, spine.into_vec())
        }
        Value::Neutral(head, mut spine) => {
            spine.push(Elim::App(arg, icit));
            Ok(Value::Neutral(head, spine))
        }
        _ => panic!("internal error: applying a non-function"),
    }
}

fn apply_spine(g: &Ev, mut value: Value, spine: &[Elim]) -> Result<Value> {
    for elim in spine {
        value = match elim {
            Elim::App(arg, icit) => apply_icit(g, value, arg.clone(), *icit)?,
            Elim::J { base, .. } => match unfold_folded(g, force(g, value)?)? {
                Value::Refl => (**base).clone(),
                Value::Neutral(head, mut spine) => {
                    spine.push(elim.clone());
                    Value::Neutral(head, spine)
                }
                _ => panic!("internal error: J applied to a non-proof"),
            },
            Elim::Proj(d, i) => project(g, *d, *i, value)?,
        };
    }
    Ok(value)
}

/// `Cons (MkChar c rfl) … Nil`, for the characters `chars`: what a compact
/// list means (docs/proposals/compact-text.md, "Expansion"), written out
/// from the prelude's constructors, independently of [`crate::chars`].
fn expand(g: &Ev, chars: &[char]) -> Value {
    let list = g
        .env
        .registry()
        .data(crate::registry::Builtin::List)
        .expect("a compact list needs `List`");
    let char = g
        .env
        .registry()
        .data(crate::registry::Builtin::Char)
        .expect("a compact list needs `Char`");
    let mut value = Value::Ctor(list, 0, Vec::new().into());
    for c in chars.iter().rev() {
        let code = nat(g, &u32::from(*c).into());
        let head = Value::Ctor(char, 0, vec![code, Value::Refl].into());
        value = Value::Ctor(list, 1, vec![head, value].into());
    }
    value
}

/// `term` with every compact list replaced by its expansion, as constructor
/// terms: for comparing the machine's quotation, which keeps compact lists,
/// with this evaluator's, which never makes them.
pub fn expand_term(g: &Ev, term: &Term) -> Term {
    let go = |t: &Rc<Term>| Rc::new(expand_term(g, t));
    match term {
        Term::Chars(chars) => {
            let list = g
                .env
                .registry()
                .data(crate::registry::Builtin::List)
                .expect("a compact list needs `List`");
            let char = g
                .env
                .registry()
                .data(crate::registry::Builtin::Char)
                .expect("a compact list needs `Char`");
            let mut out = Term::Ctor(list, 0, Vec::new());
            for c in chars.as_slice().iter().rev() {
                let code = Term::Nat(Rc::new(u32::from(*c).into()));
                let head = Term::ctor(char, 0, vec![code, Term::Refl]);
                out = Term::ctor(list, 1, vec![head, out]);
            }
            out
        }
        Term::Var(_) | Term::Def(_) | Term::Nat(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => {
            term.clone()
        }
        Term::Data(d, args) => Term::Data(*d, args.iter().map(go).collect()),
        Term::Ctor(d, c, args) => Term::Ctor(*d, *c, args.iter().map(go).collect()),
        Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, go(a), go(b)),
        Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, go(b)),
        Term::App(f, a, i) => Term::App(go(f), go(a), *i),
        Term::Ann(e, t) => Term::Ann(go(e), go(t)),
        Term::Let(x, a, v, b, e) => Term::Let(x.clone(), go(a), go(v), go(b), *e),
        Term::Case(ix, d, branches) => Term::Case(
            *ix,
            *d,
            branches
                .iter()
                .map(|b| Branch {
                    names: b.names.clone(),
                    body: b.body.as_ref().map(go),
                })
                .collect(),
        ),
        Term::NumCase(ix, arms, default) => Term::NumCase(
            *ix,
            arms.iter()
                .map(|a| crate::term::NumArm {
                    value: a.value.clone(),
                    body: go(&a.body),
                })
                .collect(),
            go(default),
        ),
        Term::Eq(ty, a, b) => Term::Eq(ty.as_ref().map(go), go(a), go(b)),
        Term::J(m, b, p) => Term::J(go(m), go(b), go(p)),
        Term::Proj(d, i, t) => Term::Proj(*d, *i, go(t)),
        Term::Quot(form, args, e) => Term::Quot(*form, args.iter().map(go).collect(), *e),
        Term::Loc(span, t) => Term::Loc(*span, go(t)),
    }
}

/// Replaces a solved metavariable at the head of `value` by its solution, and
/// expands a compact list (which only a metavariable's solution, made by the
/// machine, can hold).
pub fn force(g: &Ev, value: Value) -> Result<Value> {
    if let Value::Chars(chars) = &value {
        return Ok(expand(g, chars.as_slice()));
    }
    match &value {
        Value::Neutral(Head::Meta(m), spine) => match g.meta_solution(*m) {
            Some(solution) => {
                let applied = apply_spine(g, solution, spine)?;
                force(g, applied)
            }
            None => Ok(value),
        },
        _ => Ok(value),
    }
}

fn unfold(g: &Ev, id: DefId, spine: Vec<Elim>) -> Result<Value> {
    if crate::value::hidden(g, id) {
        return Ok(Value::Neutral(Head::Def(id), spine.into()));
    }
    if let Some(value) = crate::float::run(g, id, &spine, force)? {
        return Ok(value);
    }
    if let Some(op) = g.env.builtins().native(id).filter(|_| !plain())
        && op.arity() == spine.len()
    {
        match native::run(g, id, op, &spine, force)? {
            Some(native::Outcome::Done(value)) => return Ok(value),
            Some(native::Outcome::Again(spine)) => return unfold(g, id, spine),
            Some(native::Outcome::Succs(k, spine)) => {
                let rest = unfold(g, id, spine)?;
                let (k2, base) = native::view_with(g, &rest, force)?;
                return Ok(native::from_view(k + k2, base));
            }
            None => {}
        }
    }
    let def = g.def(id);
    if let Some(body) = &def.body
        && def.arity == spine.len()
        && !folds(g, id)
        && !folds_mul(g, id, &spine)
    {
        let args: Option<Vec<Value>> = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => Some(v.clone()),
                Elim::J { .. } | Elim::Proj(..) => None,
            })
            .collect();
        if let Some(args) = args
            && let Some(value) = eval_tree(
                g,
                args,
                body.peel_lams(def.arity),
                folds_on_lift(g, id),
                crate::value::eta_held(g, id),
            )?
        {
            return Ok(value);
        }
        // Stuck: `Nat.add` stuck on its first argument may compute on its
        // second (R3 and R4, `nat_add.rs`).
        if let [Elim::App(m, _), Elim::App(n, _)] = &spine[..]
            && let Some((k, rest)) = crate::nat_add::stuck(g, id, m, n, force)?
        {
            return Ok(nat_from_view(g, k, Some(rest)));
        }
    }
    Ok(Value::Neutral(Head::Def(id), spine.into()))
}

/// Definition `id`'s body, unless it's opaque and hidden now
/// ([`crate::value::hidden`]).
fn seen<'a>(g: &Ev<'a>, id: DefId) -> Option<&'a Rc<Term>> {
    g.def(id)
        .body
        .as_ref()
        .filter(|_| !crate::value::hidden(g, id))
}

/// Whether a dictionary (`Def::fold`) or a theorem stays folded when it has
/// all its arguments, except while a program runs.
fn folds(g: &Ev, id: DefId) -> bool {
    let def = g.def(id);
    !plain() && (def.fold || def.theorem) && !g.machine.erasure.program_running()
}

/// Whether a definition with all its arguments stays folded when its case
/// tree reaches a `Quot.lift` on a quotient that isn't a `Quot.mk`, except
/// while a program runs.
fn folds_on_lift(g: &Ev, id: DefId) -> bool {
    !plain() && g.def(id).lift_leaf && !g.machine.erasure.program_running()
}

/// Whether `value` is a folded definition with all its arguments (or may
/// be, folded on a `Quot.lift`), or `k * x` left folded
/// (`native::folds_mul`).
fn is_folded(g: &Ev, value: &Value) -> bool {
    matches!(value, Value::Neutral(Head::Def(id), spine)
        if (folds(g, *id) || folds_on_lift(g, *id) || folds_mul(g, *id, spine))
            && spine.len() == g.def(*id).arity
            && seen(g, *id).is_some())
}

/// A dictionary or theorem left folded (or a definition folded on a
/// `Quot.lift`), unfolded (repeatedly) for a `case` or `J` to take it apart,
/// or a comparison; anything else as it is.
fn unfold_folded(g: &Ev, value: Value) -> Result<Value> {
    if let Value::Neutral(Head::Def(id), spine) = &value
        && (folds(g, *id) || folds_on_lift(g, *id) || folds_mul(g, *id, spine))
        && spine.len() == g.def(*id).arity
        && let Some(body) = seen(g, *id).cloned()
    {
        let args: Option<Vec<Value>> = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => Some(v.clone()),
                Elim::J { .. } | Elim::Proj(..) => None,
            })
            .collect();
        if let Some(args) = args
            && let Some(next) = eval_tree(
                g,
                args,
                body.peel_lams(g.def(*id).arity),
                false,
                crate::value::eta_held(g, *id),
            )?
        {
            return unfold_folded(g, force(g, next)?);
        }
    }
    Ok(value)
}

/// A `case`'s scrutinee with its head computed: folded calls unfolded, and
/// a stuck `m + n` read by R3 and R4 through a folded `n` (G2).
fn scrutinee(g: &Ev, value: Value) -> Result<Value> {
    let value = unfold_folded(g, force(g, value)?)?;
    Ok(match reread_sum(g, &value)? {
        Some(value) => unfold_folded(g, force(g, value)?)?,
        None => value,
    })
}

/// `nat_add::reread` with this evaluator's unfolding: a stuck `m + n` with
/// a folded call in `n`, as what R3 and R4 make of it.
fn reread_sum(g: &Ev, value: &Value) -> Result<Option<Value>> {
    // Without a record of the sums found to have nothing to read
    // (`nat_add::Unread`): this evaluator rereads a chain at each level.
    let unread = &mut crate::nat_add::Unread::default();
    crate::nat_add::reread(
        g,
        value,
        force,
        |x| {
            if !is_folded(g, x) {
                return Ok(None);
            }
            let x2 = unfold_folded(g, x.clone())?;
            Ok(match (x, &x2) {
                (Value::Neutral(Head::Def(i1), s1), Value::Neutral(Head::Def(i2), s2))
                    if i1 == i2 && s1.ptr_eq(s2) =>
                {
                    None
                }
                _ => Some(x2),
            })
        },
        unread,
    )
}

/// The number `value` is, as `k` plus what's unknown, a folded definition
/// taken apart first as `value.rs` does. Its own frame, so `eval_tree`'s
/// recursion keeps a small one.
#[inline(never)]
fn number_view(g: &Ev, value: &Value) -> Result<(num_bigint::BigUint, Option<Value>)> {
    let value = unfold_folded(g, force(g, value.clone())?)?;
    let (k, base) = native::view_with(g, &value, force)?;
    match base
        .as_ref()
        .map(|b| reread_sum(g, b))
        .transpose()?
        .flatten()
    {
        Some(base) => number_view(g, &native::from_view(k, Some(base))),
        None => Ok((k, base)),
    }
}

fn eval_tree(
    g: &Ev,
    mut env: Vec<Value>,
    term: &Term,
    fold_lifts: bool,
    eta_held: bool,
) -> Result<Option<Value>> {
    match term.strip_loc() {
        Term::Case(ix, d, branches) => {
            let (c, fields) = match scrutinee(g, env[env.len() - 1 - ix].clone())? {
                // Another type's constructor, from an ill-typed term the
                // elaborator ran (SW-2961), stays stuck, as in `value.rs`.
                Value::Ctor(d2, c, fields) if d2 == *d => (c, fields.to_vec()),
                // Record eta, rule 2: the only branch, with the fields
                // projected.
                n @ Value::Neutral(..) if eta_case(g, *d) && !eta_held => {
                    let k = g.data(*d).ctors[0].fields.len();
                    let fields = (0..k)
                        .map(|i| project(g, *d, i, n.clone()))
                        .collect::<Result<Vec<_>>>()?;
                    (0, fields)
                }
                other @ (Value::Nat(_) | Value::NatAdd(..)) if Some(*d) == g.env.builtins().nat => {
                    match native::split_value(&other) {
                        Some(split) => split,
                        None => return Ok(None),
                    }
                }
                _ => return Ok(None),
            };
            let Branch { body, .. } = &branches[c];
            let Some(body) = body else {
                return Ok(None);
            };
            env.extend(fields);
            eval_tree(g, env, body, fold_lifts, eta_held)
        }
        Term::NumCase(ix, arms, default) => {
            let (k, base) = number_view(g, &env[env.len() - 1 - ix])?;
            let body = if base.is_none() {
                match arms.iter().find(|a| *a.value == k) {
                    Some(arm) => &arm.body,
                    None => default,
                }
            } else if arms.iter().all(|a| *a.value < k) {
                // `k + x` is at least `k`.
                default
            } else if let Some(Value::Neutral(Head::Var(_, apart), spine)) = &base
                && spine.is_empty()
                && arms.iter().all(|a| {
                    *a.value < k || apart.numbers(g).binary_search(&(&*a.value - &k)).is_ok()
                })
            {
                // `x` is a variable known not to be any arm's number less `k`.
                default
            } else {
                return Ok(None);
            };
            eval_tree(g, env, body, fold_lifts, eta_held)
        }
        // A `Quot.lift` leaf counts as a case on its quotient: stuck, the
        // definition stays folded (`fold_lifts`: only one marked for it,
        // `folds_on_lift`).
        Term::Quot(QuotForm::Lift, args, _)
            if fold_lifts && args.len() == QuotForm::Lift.arity() =>
        {
            lift_leaf(g, &env, args)
        }
        other => eval(g, &env, other).map(Some),
    }
}

/// A `Quot.lift` leaf of a case tree: `f a` on `Quot.mk a`, else stuck.
#[inline(never)]
fn lift_leaf(g: &Ev, env: &[Value], args: &[std::rc::Rc<Term>]) -> Result<Option<Value>> {
    Ok(lift(g, env, args)?.ok())
}

/// A quotient form applied to `args`. The one computation rule:
/// `Quot.lift f h (Quot.mk a)` is `f a`.
#[inline(never)]
fn eval_quot(g: &Ev, env: &[Value], form: QuotForm, args: &[std::rc::Rc<Term>]) -> Result<Value> {
    let eval_all = |args: &[std::rc::Rc<Term>]| -> Result<Vec<Value>> {
        args.iter().map(|a| eval(g, env, a)).collect()
    };
    if form == QuotForm::Lift && args.len() == QuotForm::Lift.arity() {
        return match lift(g, env, args)? {
            Ok(value) => Ok(value),
            Err(q) => {
                let mut values = eval_all(&args[..5])?;
                values.push(q);
                Ok(quot_value(QuotForm::Lift, values))
            }
        };
    }
    Ok(quot_value(form, eval_all(args)?))
}

/// `Quot.lift` applied to `args`: `f a` if the quotient is `Quot.mk a`, else
/// the quotient's value. Its own frame, so `eval`'s and `eval_tree`'s
/// recursion keep small ones (io.sw's long chain of prints recurses deeply).
#[inline(never)]
fn lift(
    g: &Ev,
    env: &[Value],
    args: &[std::rc::Rc<Term>],
) -> Result<std::result::Result<Value, Value>> {
    let q = unfold_folded(g, force(g, eval(g, env, &args[5])?)?)?;
    Ok(match quot_mk_rep(&q) {
        Some(a) => Ok(apply_icit(
            g,
            eval(g, env, &args[3])?,
            a.clone(),
            Icit::Explicit,
        )?),
        None => Err(q),
    })
}

/// Converts a value back into a term, with `level` variables in scope.
pub fn quote(g: &Ev, level: usize, value: &Value) -> Result<Term> {
    step()?;
    let q = |v: &Value| quote(g, level, v);
    Ok(match force(g, value.clone())? {
        Value::Sort(s) => Term::Sort(s),
        Value::Pi(x, i, a, b) => Term::Pi(
            x.clone(),
            i,
            Rc::new(q(&a)?),
            Rc::new(quote(
                g,
                level + 1,
                &apply_closure(g, &b, Value::var(level))?,
            )?),
        ),
        Value::Lam(x, i, b) => Term::Lam(
            x.clone(),
            i,
            Rc::new(quote(
                g,
                level + 1,
                &apply_closure(g, &b, Value::var(level))?,
            )?),
        ),
        Value::Data(d, args) => Term::Data(
            d,
            args.iter()
                .map(|a| q(a).map(Rc::new))
                .collect::<Result<_>>()?,
        ),
        Value::Ctor(d, c, args) => Term::Ctor(
            d,
            c,
            args.iter()
                .map(|a| q(a).map(Rc::new))
                .collect::<Result<_>>()?,
        ),
        Value::Nat(n) => Term::Nat(n),
        Value::Chars(_) => unreachable!("forcing expands compact lists"),
        Value::NatAdd(k, base) => native::nat_add_term(g, &k, q(&base)?),
        Value::Eq(ty, a, b) => Term::Eq(Some(Rc::new(q(&ty)?)), Rc::new(q(&a)?), Rc::new(q(&b)?)),
        Value::Refl => Term::Refl,
        Value::Neutral(head, spine) => {
            let (mut term, rest) = match head {
                Head::Var(l, _) => (Term::Var(level - 1 - l), &spine[..]),
                Head::Def(id) => (Term::Def(id), &spine[..]),
                Head::Meta(m) => (Term::Meta(m), &spine[..]),
                Head::Quot(form) => quote_quot(g, level, form, &spine)?,
            };
            for elim in rest {
                term = match elim {
                    Elim::App(v, i) => Term::app_icit(term, q(v)?, *i),
                    Elim::J { motive, base } => {
                        Term::J(Rc::new(q(motive)?), Rc::new(q(base)?), Rc::new(term))
                    }
                    Elim::Proj(d, i) => Term::Proj(*d, *i, Rc::new(term)),
                };
            }
            term
        }
        Value::Call(..) => unreachable!("the reference evaluator never glues"),
        Value::Resumption(_) => {
            panic!("internal error: a handler's resumption reached the checker")
        }
    })
}

/// A quotient form's own arguments, the first eliminations of `spine`,
/// quoted, as the form applied to them; and the eliminations after them,
/// which apply its result. Its own frame, as `lift` is.
#[inline(never)]
fn quote_quot<'s>(
    g: &Ev,
    level: usize,
    form: QuotForm,
    spine: &'s [Elim],
) -> Result<(Term, &'s [Elim])> {
    let n = spine
        .iter()
        .take(form.arity())
        .take_while(|e| matches!(e, Elim::App(..)))
        .count();
    let args = spine[..n]
        .iter()
        .map(|e| match e {
            Elim::App(v, _) => quote(g, level, v).map(Rc::new),
            Elim::J { .. } | Elim::Proj(..) => unreachable!("counted applications"),
        })
        .collect::<Result<_>>()?;
    Ok((Term::Quot(form, args, false), &spine[n..]))
}

/// Definitional equality (the recursive version `value::conv` was derived
/// from), with the same precondition: `a` and `b` have the same type, as
/// proofs are skipped by position.
pub fn conv(g: &Ev, level: usize, a: &Value, b: &Value) -> Result<bool> {
    conv_in(g, level, a, b, Mode::Normal)
}

/// [`conv`] in `mode` (`value::Mode`: constructors' proof fields are
/// compared in shortcut mode). The shortcuts here are the folded calls,
/// partially applied definitions and hidden opaque calls, each compared by
/// its spine in shortcut mode.
fn conv_in(g: &Ev, level: usize, a: &Value, b: &Value, mode: Mode) -> Result<bool> {
    step()?;
    // Folded calls: the same one applied to equal arguments is equal;
    // otherwise they're compared unfolded.
    if is_folded(g, a) || is_folded(g, b) {
        if let (Value::Neutral(Head::Def(i1), s1), Value::Neutral(Head::Def(i2), s2)) = (a, b)
            && i1 == i2
            && s1.len() == s2.len()
            && conv_spines(g, level, Some(*i1), s1, s2, Mode::Shortcut)?
        {
            return Ok(true);
        }
        let a2 = unfold_folded(g, a.clone())?;
        let b2 = unfold_folded(g, b.clone())?;
        let moved = |x: &Value, y: &Value| match (x, y) {
            (Value::Neutral(Head::Def(i1), s1), Value::Neutral(Head::Def(i2), s2)) => {
                !(i1 == i2 && s1.ptr_eq(s2))
            }
            _ => true,
        };
        if (is_folded(g, a) && moved(a, &a2)) || (is_folded(g, b) && moved(b, &b2)) {
            return conv_in(g, level, &a2, &b2, mode);
        }
    }
    // A sum stuck on its first argument, with a folded call in its second,
    // as what R3 and R4 make of it (G2).
    if let Some(a2) = reread_sum(g, a)? {
        return conv_in(g, level, &a2, b, mode);
    }
    if let Some(b2) = reread_sum(g, b)? {
        return conv_in(g, level, a, &b2, mode);
    }
    if matches!(a, Value::Chars(_)) || matches!(b, Value::Chars(_)) {
        return conv_in(g, level, &force(g, a.clone())?, &force(g, b.clone())?, mode);
    }
    // A base left against a different count of `Succ`s is unequal unless
    // it's a folded call, compared unfolded as above (SW-2157).
    if native::nat_like(g, a) || native::nat_like(g, b) {
        return native::compare_with(
            g,
            a,
            b,
            |x, y| conv_in(g, level, x, y, mode),
            |x, rest| {
                if let Some(x2) = reread_sum(g, x)? {
                    return conv_in(g, level, &x2, rest, mode);
                }
                if !is_folded(g, x) {
                    return Ok(false);
                }
                let x2 = unfold_folded(g, x.clone())?;
                match (x, &x2) {
                    (Value::Neutral(Head::Def(i1), s1), Value::Neutral(Head::Def(i2), s2))
                        if i1 == i2 && s1.ptr_eq(s2) =>
                    {
                        Ok(false)
                    }
                    _ => conv_in(g, level, &x2, rest, mode),
                }
            },
            force,
        );
    }
    let fresh = Value::var(level);
    let apply = |c: &Closure, v: Value| apply_closure(g, c, v);
    Ok(match (a, b) {
        (Value::Sort(s), Value::Sort(t)) => s == t,
        (Value::Pi(_, i1, a1, b1), Value::Pi(_, i2, a2, b2)) => {
            i1 == i2
                && conv_in(g, level, a1, a2, mode)?
                && conv_in(
                    g,
                    level + 1,
                    &apply(b1, fresh.clone())?,
                    &apply(b2, fresh)?,
                    mode,
                )?
        }
        (Value::Lam(_, _, b1), Value::Lam(_, _, b2)) => conv_in(
            g,
            level + 1,
            &apply(b1, fresh.clone())?,
            &apply(b2, fresh)?,
            mode,
        )?,
        (Value::Lam(_, i, b), other) | (other, Value::Lam(_, i, b)) => conv_in(
            g,
            level + 1,
            &apply(b, fresh.clone())?,
            &apply_icit(g, other.clone(), fresh, *i)?,
            mode,
        )?,
        // Proof parameters and proof fields aren't compared.
        (Value::Data(d1, a1), Value::Data(d2, a2)) => {
            let proof = |k| crate::value::proof_param(g, *d1, k);
            d1 == d2 && all_conv_but(g, level, a1, a2, proof, mode)?
        }
        (Value::Ctor(d1, c1, a1), Value::Ctor(d2, c2, a2)) => {
            d1 == d2 && c1 == c2 && {
                let proof = |k| mode == Mode::Normal && crate::value::proof_field(g, *d1, *c1, k);
                all_conv_but(g, level, a1, a2, proof, mode)?
            }
        }
        (Value::Eq(t1, x1, y1), Value::Eq(t2, x2, y2)) => {
            conv_in(g, level, t1, t2, mode)?
                && conv_in(g, level, x1, x2, mode)?
                && conv_in(g, level, y1, y2, mode)?
        }
        (Value::Refl, Value::Refl) => true,
        // Two calls stuck on a `case`: by their case trees. For two calls of
        // one definition, equal arguments are enough, but different ones
        // aren't a difference (G6, docs/core.md).
        (Value::Neutral(Head::Def(i1), s1), Value::Neutral(Head::Def(i2), s2))
            if crate::value::opens_by_tree(g, a) && crate::value::opens_by_tree(g, b) =>
        {
            // Pairs already found equal, or different, in the outermost
            // tree comparison get the same answer again (SW-395, SW-2269):
            // without this, a chain of helpers each calling the next in two
            // branches takes 2^n comparisons here too, and so do nested
            // calls of one definition that differ, whose arguments and then
            // scrutinees compare the same inner pair. Nothing is solved
            // here, so "different" lasts as "equal" does. Looked up by the
            // quoted pair, printed: its own key, not the machine's
            // `identical`.
            let open = OpenTrees::enter();
            let key = (
                mode,
                level,
                format!("{:?}", quote(g, level, a)?),
                format!("{:?}", quote(g, level, b)?),
            );
            if let Some(same) = open.known(&key) {
                same
            } else {
                let same = (i1 == i2 && conv_spines(g, level, Some(*i1), s1, s2, mode)?)
                    || same_trees(g, level, tree_of(g, a), tree_of(g, b), mode)?;
                open.record(key, same);
                same
            }
        }
        // Record eta, rule 1: a constructor against an unknown, field by
        // field against its projections.
        (Value::Ctor(d, 0, fs), n @ Value::Neutral(..))
        | (n @ Value::Neutral(..), Value::Ctor(d, 0, fs))
            if g.env.datas().get(d.0).is_some_and(|data| data.eta()) =>
        {
            for (k, x) in fs.iter().enumerate() {
                let proof = mode == Mode::Normal && crate::value::proof_field(g, *d, 0, k);
                if !proof && !conv_in(g, level, x, &project(g, *d, k, n.clone())?, mode)? {
                    return Ok(false);
                }
            }
            true
        }
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) => {
            let def = match h1 {
                Head::Def(f) => Some(*f),
                _ => None,
            };
            // A partially applied definition, a hidden opaque call, or a
            // call of a member of the group being checked could still unfold
            // (applied to more, where it's transparent, or once the group is
            // admitted): its spine is compared in shortcut mode. A stuck
            // call's isn't.
            let could_unfold =
                def.is_some_and(|f| crate::value::sealed(g, f) || s1.len() < g.def(f).arity);
            let spine_mode = if could_unfold { Mode::Shortcut } else { mode };
            (h1 == h2 && s1.len() == s2.len() && conv_spines(g, level, def, s1, s2, spine_mode)?)
                || eta(g, level, a, b, mode)?
        }
        _ => eta(g, level, a, b, mode)?,
    })
}

/// A pair of calls compared by their trees: the mode, the level and the
/// two, quoted.
type CallPair = (Mode, usize, String, String);

thread_local! {
    /// How many tree comparisons are open, and the pairs of calls found
    /// equal or different since the outermost one started.
    static KNOWN_CALLS: std::cell::RefCell<(usize, crate::collections::HashMap<CallPair, bool>)> =
        std::cell::RefCell::new((0, crate::collections::HashMap::default()));
}

/// One open tree comparison; the record is dropped with the outermost.
struct OpenTrees;

impl OpenTrees {
    fn enter() -> OpenTrees {
        KNOWN_CALLS.with(|m| m.borrow_mut().0 += 1);
        OpenTrees
    }

    fn known(&self, pair: &CallPair) -> Option<bool> {
        KNOWN_CALLS.with(|m| m.borrow().1.get(pair).copied())
    }

    fn record(&self, pair: CallPair, same: bool) {
        KNOWN_CALLS.with(|m| m.borrow_mut().1.insert(pair, same));
    }
}

impl Drop for OpenTrees {
    fn drop(&mut self) {
        KNOWN_CALLS.with(|m| {
            let mut m = m.borrow_mut();
            m.0 -= 1;
            if m.0 == 0 {
                m.1.clear();
            }
        });
    }
}

/// A case tree in its environment, with [`crate::value::eta_held`] of the
/// definition it belongs to.
struct Tree {
    term: Rc<Term>,
    env: Vec<Value>,
    held: bool,
}

/// A stuck call's case tree and arguments.
fn tree_of(g: &Ev, value: &Value) -> Tree {
    let Value::Neutral(Head::Def(id), spine) = value else {
        unreachable!()
    };
    let def = g.def(*id);
    let args = spine
        .iter()
        .map(|e| match e {
            Elim::App(v, _) => v.clone(),
            Elim::J { .. } | Elim::Proj(..) => unreachable!(),
        })
        .collect();
    Tree {
        term: Term::peel_lams_rc(def.body().expect("a body"), def.arity),
        env: args,
        held: crate::value::eta_held(g, *id),
    }
}

/// Two case trees in their environments: both stuck on equal scrutinees with
/// equal branches (fields as fresh variables), or both leaves with equal
/// values. A constructor scrutinee takes its branch first.
fn same_trees(g: &Ev, level: usize, mut a: Tree, mut b: Tree, mode: Mode) -> Result<bool> {
    // Steps a tree along constructor scrutinees, and by rule 2 unless its
    // definition is held, as `eval_tree` does; `None` if it reaches anything
    // but a stuck `Case` or a leaf.
    let settle = |tree: &mut Tree| -> Result<Option<(Rc<Term>, Option<Value>)>> {
        let mut t = tree.term.clone();
        let (e, held) = (&mut tree.env, tree.held);
        loop {
            match t.strip_loc() {
                Term::Case(ix, d, branches) => {
                    // Rule E: the scrutinee's head, a folded call unfolded
                    // and a number split, as `eval_tree` takes it (G1, G3).
                    let s = unfold_folded(g, force(g, e[e.len() - 1 - ix].clone())?)?;
                    let split = match &s {
                        Value::Ctor(d2, c, fields) if d2 == d => Some((*c, fields.to_vec())),
                        Value::Nat(_) | Value::NatAdd(..) if Some(*d) == g.env.builtins().nat => {
                            native::split_value(&s)
                        }
                        _ => None,
                    };
                    if let Some((c, fields)) = split {
                        match &branches[c].body {
                            Some(body) => {
                                e.extend(fields);
                                t = body.clone();
                            }
                            None => return Ok(None),
                        }
                        continue;
                    }
                    match &s {
                        Value::Neutral(..) if !is_folded(g, &s) && !held && eta_case(g, *d) => {
                            match &branches[0].body {
                                Some(body) => {
                                    let k = g.data(*d).ctors[0].fields.len();
                                    for i in 0..k {
                                        e.push(project(g, *d, i, s.clone())?);
                                    }
                                    t = body.clone();
                                }
                                None => return Ok(None),
                            }
                        }
                        Value::Neutral(..) if !is_folded(g, &s) => return Ok(Some((t, Some(s)))),
                        _ => return Ok(None),
                    }
                }
                Term::NumCase(..) => return Ok(None),
                _ => return Ok(Some((t, None))),
            }
        }
    };
    let (Some((t1, s1)), Some((t2, s2))) = (settle(&mut a)?, settle(&mut b)?) else {
        return Ok(false);
    };
    let (e1, e2) = (a.env, b.env);
    match (s1, s2) {
        (None, None) => conv_in(g, level, &eval(g, &e1, &t1)?, &eval(g, &e2, &t2)?, mode),
        (Some(s1), Some(s2)) => {
            let (Term::Case(_, d1, b1), Term::Case(_, d2, b2)) = (t1.strip_loc(), t2.strip_loc())
            else {
                unreachable!()
            };
            if d1 != d2 || b1.len() != b2.len() {
                return Ok(false);
            }
            // Never computes, whatever the scrutinees: equal.
            if b1.iter().chain(b2.iter()).all(|b| b.body.is_none()) {
                return Ok(true);
            }
            if !conv_in(g, level, &s1, &s2, mode)? {
                return Ok(false);
            }
            for (c, (x, y)) in b1.iter().zip(b2.iter()).enumerate() {
                match (&x.body, &y.body) {
                    (None, None) => {}
                    (Some(x), Some(y)) => {
                        let k = g.data(*d1).ctors[c].fields.len();
                        let fresh: Vec<Value> = (level..level + k).map(Value::var).collect();
                        let mut f1 = e1.clone();
                        let mut f2 = e2.clone();
                        f1.extend(fresh.iter().cloned());
                        f2.extend(fresh);
                        let x = Tree {
                            term: x.clone(),
                            env: f1,
                            held: a.held,
                        };
                        let y = Tree {
                            term: y.clone(),
                            env: f2,
                            held: b.held,
                        };
                        if !same_trees(g, level + k, x, y, mode)? {
                            return Ok(false);
                        }
                    }
                    _ => return Ok(false),
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

/// Whether `xs` and `ys` are equal at every position `skip` doesn't name.
fn all_conv_but(
    g: &Ev,
    level: usize,
    xs: &[Value],
    ys: &[Value],
    skip: impl Fn(usize) -> bool,
    mode: Mode,
) -> Result<bool> {
    if xs.len() != ys.len() {
        return Ok(false);
    }
    for (k, (x, y)) in xs.iter().zip(ys).enumerate() {
        if !skip(k) && !conv_in(g, level, x, y, mode)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Two spines, compared pair by pair; for a definition `def`, its inert
/// arguments (the leading applications at its marked positions) aren't.
fn conv_spines(
    g: &Ev,
    level: usize,
    def: Option<DefId>,
    s1: &[Elim],
    s2: &[Elim],
    mode: Mode,
) -> Result<bool> {
    // How many leading entries are applications: the definition's
    // arguments.
    let leading = s1.iter().take_while(|e| matches!(e, Elim::App(..))).count();
    for (k, pair) in s1.iter().zip(s2).enumerate() {
        let same = match pair {
            (Elim::App(..), Elim::App(..))
                if k < leading && def.is_some_and(|f| g.def(f).is_inert(k)) =>
            {
                true
            }
            (Elim::App(x, _), Elim::App(y, _)) => conv_in(g, level, x, y, mode)?,
            (Elim::Proj(d1, i1), Elim::Proj(d2, i2)) => d1 == d2 && i1 == i2,
            (
                Elim::J {
                    motive: m1,
                    base: b1,
                },
                Elim::J {
                    motive: m2,
                    base: b2,
                },
            ) => conv_in(g, level, m1, m2, mode)? && conv_in(g, level, b1, b2, mode)?,
            _ => false,
        };
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Eta for partially applied definitions: both sides applied to a fresh
/// variable.
fn eta(g: &Ev, level: usize, a: &Value, b: &Value, mode: Mode) -> Result<bool> {
    let underapplied = |v| crate::value::underapplied(g, v);
    let Some(icit) = underapplied(a).or_else(|| underapplied(b)) else {
        return Ok(false);
    };
    let fresh = Value::var(level);
    conv_in(
        g,
        level + 1,
        &apply_icit(g, a.clone(), fresh.clone(), icit)?,
        &apply_icit(g, b.clone(), fresh, icit)?,
        mode,
    )
}

/// Checks that every inert mark of the definitions `ids` is justified by
/// its body, given every definition's final marks, and panics if one isn't
/// (docs/proposals/proof-irrelevance.md §7.3). Written apart from the
/// analysis (`crate::inert`), as one pass: each occurrence of a marked
/// parameter must be *shielded* (inside an argument at an inert position of
/// a call of a definition, or inside a `let`'s or an annotation's type),
/// and a `case` on one must have no possible branch. It checks only that
/// the marks are sound, not that they're the most there could be.
pub fn validate_inert(g: &Ev, ids: &[DefId]) {
    for id in ids {
        let def = g.def(*id);
        let Some(body) = &def.body else {
            assert!(
                def.inert_params().is_empty(),
                "`{}` has inert marks but no body",
                def.name()
            );
            continue;
        };
        let marks = def.inert_params();
        if !marks.iter().any(|m| *m) {
            continue;
        }
        assert!(
            marks.len() == def.arity,
            "`{}`: marks beyond its arity",
            def.name()
        );
        if let Some(i) = not_a_proof(g, *id) {
            panic!(
                "internal error: parameter {i} of `{}` is marked inert, but its type isn't a proposition",
                def.name()
            );
        }
        if let Some((i, what)) = unshielded(g, body, def.arity, marks) {
            panic!(
                "internal error: parameter {i} of `{}` is marked inert, but {what}",
                def.name()
            );
        }
    }
}

/// The first marked parameter of `id` whose type isn't in `Prop`. `None`
/// if there's none, or if finding out runs out of resources: the validator
/// gives no answer then, as the kernel would.
///
/// The type is evaluated by the kernel, glued, and only up to the last
/// mark, not by this module's evaluator: that one has no stack guard and
/// computes every closed value in a type (an equation about
/// `List.replicate 20000 'a'`), where a parameter's sort needs none of it.
fn not_a_proof(g: &Ev, id: DefId) -> Option<usize> {
    let def = g.def(id);
    let marks = def.inert_params();
    let last = marks.iter().rposition(|m| *m)?;
    let _set = g.machine.transparent.set(def.transparent.clone());
    let was = g.machine.glue.replace(true);
    // `None` inside: it ran out.
    let found = (|| -> Option<Option<usize>> {
        let mut cx = crate::check::Ctx::new(g, def.span);
        let mut ty = crate::value::eval(g, &[], &def.ty).ok()?;
        for (k, marked) in marks.iter().enumerate().take(last + 1) {
            let Value::Pi(x, _, dom, cod) = crate::value::force(g, ty.clone()).ok()? else {
                // More parameters than the type shows: a mark from here on
                // has no type to justify it.
                return Some(marks[k..].iter().position(|m| *m).map(|i| k + i));
            };
            if *marked && crate::check::sort_of(&mut cx, &dom).ok()? != Sort::Prop {
                return Some(Some(k));
            }
            if k < last {
                let next = cod.apply(g, Value::var(cx.level())).ok()?;
                cx.bind(x.clone(), (*dom).clone());
                ty = next;
            }
        }
        Some(None)
    })();
    g.machine.glue.set(was);
    found.flatten()
}

/// The first marked parameter (by position) of `body`, a definition's body
/// with its `arity` lambdas, used where it isn't shielded, and how.
fn unshielded(g: &Ev, body: &Term, arity: usize, marks: &[bool]) -> Option<(usize, &'static str)> {
    // (term, binders above it counting the parameters, shielded)
    let mut todo: Vec<(&Term, usize, bool)> = vec![(body, 0, false)];
    let marked_param = |ix: usize, binders: usize| -> Option<usize> {
        // Parameter `p` is bound at binder `p`; at `binders` deep it is
        // `Var(binders - 1 - p)`.
        let p = binders.checked_sub(ix + 1)?;
        (p < arity && marks[p]).then_some(p)
    };
    while let Some((t, binders, shielded)) = todo.pop() {
        match t {
            Term::Var(ix) => {
                if !shielded && let Some(p) = marked_param(*ix, binders) {
                    return Some((p, "it is used outside an inert argument"));
                }
            }
            Term::Case(ix, d, branches) => {
                if branches.iter().any(|b| b.body.is_some())
                    && let Some(p) = marked_param(*ix, binders)
                {
                    return Some((p, "it is matched with a possible branch"));
                }
                for (c, b) in branches.iter().enumerate() {
                    if let Some(body) = &b.body {
                        let k = g.data(*d).ctors[c].fields.len();
                        todo.push((body, binders + k, shielded));
                    }
                }
            }
            Term::NumCase(ix, arms, default) => {
                if let Some(p) = marked_param(*ix, binders) {
                    return Some((p, "it is matched as a number"));
                }
                todo.extend(arms.iter().map(|a| (&*a.body, binders, shielded)));
                todo.push((default, binders, shielded));
            }
            Term::App(..) => {
                let mut spine = Vec::new();
                let mut f = t;
                loop {
                    match f {
                        Term::App(h, a, _) => {
                            spine.push(&**a);
                            f = h;
                        }
                        Term::Loc(_, inner) => f = inner,
                        _ => break,
                    }
                }
                spine.reverse();
                let callee = match f {
                    Term::Def(callee) => Some(g.def(*callee)),
                    _ => None,
                };
                todo.push((f, binders, shielded));
                for (k, a) in spine.into_iter().enumerate() {
                    let inert_arg = callee.is_some_and(|d| d.is_inert(k));
                    todo.push((a, binders, shielded || inert_arg));
                }
            }
            Term::Lam(_, _, b) => todo.push((b, binders + 1, shielded)),
            Term::Pi(_, _, a, b) => {
                todo.push((a, binders, shielded));
                todo.push((b, binders + 1, shielded));
            }
            Term::Ann(e, ty) => {
                todo.push((e, binders, shielded));
                todo.push((ty, binders, true));
            }
            Term::Let(_, ty, v, b, _) => {
                todo.push((ty, binders, true));
                todo.push((v, binders, shielded));
                todo.push((b, binders + 1, shielded));
            }
            Term::Loc(_, e) => todo.push((e, binders, shielded)),
            Term::Data(_, xs) | Term::Ctor(_, _, xs) | Term::Quot(_, xs, _) => {
                todo.extend(xs.iter().map(|x| (&**x, binders, shielded)));
            }
            Term::Eq(ty, a, b) => {
                todo.extend(ty.iter().map(|x| (&**x, binders, shielded)));
                todo.push((a, binders, shielded));
                todo.push((b, binders, shielded));
            }
            Term::J(m, b, p) => {
                todo.push((m, binders, shielded));
                todo.push((b, binders, shielded));
                todo.push((p, binders, shielded));
            }
            // A projection of a marked parameter takes it apart.
            Term::Proj(_, _, t) => {
                if let Term::Var(ix) = t.strip_loc()
                    && let Some(p) = marked_param(*ix, binders)
                {
                    return Some((p, "it is taken apart by a projection"));
                }
                todo.push((t, binders, shielded));
            }
            Term::Def(_)
            | Term::Nat(_)
            | Term::Chars(_)
            | Term::Sort(_)
            | Term::Refl
            | Term::Meta(_) => {}
        }
    }
    None
}
