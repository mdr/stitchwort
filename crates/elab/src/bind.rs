//! Binding instead of evaluating (docs/proposals/checker-evaluation.md,
//! option (a)).
//!
//! The evaluator is strict, so putting an argument's value into a type
//! computes the argument completely, and the kernel, checking the result,
//! computes it again. Where only the type of a use of the argument is
//! needed, and that type doesn't depend on the argument's value, the use is
//! elaborated with a variable in its place, and the program is
//! `(x => use x) arg`: exactly how a pure `let` is elaborated. Neither the
//! elaborator nor the kernel then computes `arg` (the kernel's application
//! rule computes an argument only if the function's type mentions it), and
//! at run time `arg` is computed once, before the use, as it was before:
//! application is strict, so nothing is reordered, repeated or dropped.
//!
//! Where the type might depend on the argument (it mentions the variable at
//! all, even inside a stuck call `F x`), everything the attempt did is
//! undone and the caller does what it did before.

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{eval, force, unused};
use stitchwort_core::{Icit, Name, Term, Value};

use crate::check::{Ctx, Result, builtin_data, builtin_def};

/// Whether computing `term` costs nothing worth avoiding: it's small and
/// built from variables, literals and constructors only (a text literal,
/// `Some 3`). Binding those would only make the program longer.
pub(crate) fn cheap(term: &Term) -> bool {
    const SMALL: usize = 64;
    let mut nodes = term.subterms();
    nodes.by_ref().take(SMALL).all(|(t, _)| {
        matches!(
            t,
            Term::Loc(..)
                | Term::Var(_)
                | Term::Nat(_)
                | Term::Chars(_)
                | Term::Sort(_)
                | Term::Refl
                | Term::Ctor(..)
        )
    }) && nodes.next().is_none()
}

/// Whether `term`, in the scope of the first `outer` variables of `cx`, is
/// a variable for a `let` whose value isn't [`cheap`]. Such a variable is
/// cheap to write but not to compute: the kernel computes a `let`'s value
/// when a type it evaluates mentions the variable, and its evaluator is
/// strict. So `let x := solve input; x == 42` decided as
/// `toBool {x = 42} (Nat.decEq x 42)` computes `solve input` while it's
/// type-checked; bound, `(y => toBool {y = 42} (Nat.decEq y 42)) x`, the
/// types mention only `y` (SW-412: day 9's real-input test spent 2 minutes
/// in the kernel).
fn costly_let(cx: &Ctx, outer: usize, term: &Term) -> bool {
    let Term::Var(index) = term.strip_loc() else {
        return false;
    };
    let Some(level) = outer.checked_sub(index + 1) else {
        return false;
    };
    matches!(cx.lets.get(level), Some(Some(def)) if !cheap(&def.value))
}

/// `use arg`, for `arg : dom` (already checked), elaborated without
/// computing `arg`: `(name => use name) arg`, if the use's type doesn't
/// depend on `arg`. `use` elaborates the use, given the term standing for
/// the argument, and gives it with its type; `whole` gives the type of the
/// use's term from that type, if they differ (an operation's result type,
/// and its computation type). The result is the term and the use's type.
///
/// `None` (with everything undone) if `arg` is cheap anyway, or the type
/// might depend on it, or `use` fails with the variable (the caller then
/// elaborates it with `arg`, and reports any error from that).
pub(crate) fn bind_argument(
    cx: &mut Ctx,
    name: &str,
    dom: &Value,
    arg: &Term,
    use_: impl FnOnce(&mut Ctx, Term) -> Result<(Term, Value)>,
    whole: impl FnOnce(&Ctx, &Value) -> Result<Value>,
) -> Result<Option<(Term, Value)>> {
    if cheap(arg) {
        return Ok(None);
    }
    crate::undo::transaction(cx, |cx| {
        let mark = cx.mark();
        cx.bind_hidden(name.into(), dom.clone());
        let (inner, ty) = match use_(cx, Term::Var(0)) {
            Ok(found) => found,
            Err(e) if crate::undo::fatal(&e) => return Err(e),
            Err(_) => return Ok(None),
        };
        let ty_term = cx.quote(&ty)?;
        if ty_term.mentions(0) {
            return Ok(None);
        }
        let whole_term = cx.quote(&whole(cx, &ty)?)?;
        if whole_term.mentions(0) {
            return Ok(None);
        }
        cx.reset(mark);
        let lam = Term::Lam(name.into(), Icit::Explicit, Rc::new(inner));
        let pi = Term::Pi(
            name.into(),
            Icit::Explicit,
            Rc::new(cx.quote(dom)?),
            Rc::new(whole_term),
        );
        // The use's type, outside the binder: it doesn't mention it.
        let mut env = cx.env.clone();
        env.push(unused());
        let ty = eval(cx.g(), &env, &ty_term)?;
        Ok(Some((
            Term::app(Term::Ann(Rc::new(lam), Rc::new(pi)), arg.clone()),
            ty,
        )))
    })
}

/// A decision procedure for a proposition: a term of type `Decidable prop`.
#[derive(Clone)]
pub(crate) enum Decision {
    /// Found for the proposition as it is.
    Plain(Term),
    /// Found for the proposition with its operands bound as variables
    /// (`bound_decision`).
    Bound(Bound),
}

/// A decision found with the proposition's operands bound as variables:
/// inside `binders`, `decision : Decidable prop`.
#[derive(Clone)]
pub(crate) struct Bound {
    /// Each binder's name and type, the type in the scope of the binders
    /// before it.
    binders: Vec<(Name, Term)>,
    /// The operands, in the outer scope, in source order.
    operands: Vec<Term>,
    /// The proposition, with the operands replaced by the binders.
    prop: Term,
    decision: Term,
}

impl Bound {
    /// `(x… => body) operands…`, where `body : ty` inside the binders.
    fn apply(self, body: Term, ty: Term) -> Term {
        let (lam, pi) = self
            .binders
            .iter()
            .rev()
            .fold((body, ty), |(lam, pi), (x, dom)| {
                (
                    Term::Lam(x.clone(), Icit::Explicit, Rc::new(lam)),
                    Term::Pi(x.clone(), Icit::Explicit, Rc::new(dom.clone()), Rc::new(pi)),
                )
            });
        self.operands
            .into_iter()
            .fold(Term::Ann(Rc::new(lam), Rc::new(pi)), Term::app)
    }
}

impl Decision {
    /// A term of type `Decidable prop`, in the outer scope:
    /// `(x… => d) operands…`.
    pub(crate) fn term(self, cx: &Ctx) -> Result<Term> {
        match self {
            Decision::Plain(d) => Ok(d),
            Decision::Bound(b) => {
                let decidable = builtin_data(cx, Builtin::Decidable)?;
                let ty = Term::data(decidable, vec![b.prop.clone()]);
                let d = b.decision.clone();
                Ok(b.apply(d, ty))
            }
        }
    }

    /// `Decidable.toBool {prop} d`, in the outer scope. With the operands
    /// bound, the whole of it goes under the binders,
    /// `(x… => toBool {prop'} d) operands…`, so that its type, `Bool`,
    /// doesn't mention them and the kernel doesn't compute them either.
    pub(crate) fn into_bool(self, cx: &Ctx, prop: Term) -> Result<Term> {
        let to_bool = Term::Def(builtin_def(cx, Builtin::ToBool)?);
        let bool_ty = Term::data(builtin_data(cx, Builtin::Bool)?, Vec::new());
        let of = |prop: Term, d: Term| {
            // The standard decision of `m <= n` is `Bool.decTrue (Nat.leq m n)`,
            // and its `Bool` is `Nat.leq m n` itself: written that way, it
            // prints and computes as the comparison, not as `toBool (decTrue …)`
            // (SW-206 item 4).
            if let Some(direct) = comparison(cx, &d) {
                return direct;
            }
            Term::app(Term::app_icit(to_bool.clone(), prop, Icit::Implicit), d)
        };
        Ok(match self {
            Decision::Plain(d) => of(prop, d),
            Decision::Bound(b) => {
                let body = of(b.prop.clone(), b.decision.clone());
                b.apply(body, bool_ty)
            }
        })
    }
}

/// The comparison a standard decision stands for, as the `Bool` it decides:
/// `Nat.decLessEq m n` is `Nat.leq m n`, `Nat.decLessThan m n` is
/// `Nat.leq (Succ m) n`, and the `Int` ones are `Int.leq m n` and
/// `Int.less m n`.
fn comparison(cx: &Ctx, d: &Term) -> Option<Term> {
    let (head, args) = d.spine();
    let Term::Def(id) = head else {
        return None;
    };
    let reg = &cx.g().registry;
    let [m, n] = args[..] else {
        return None;
    };
    let (m, n) = (m.clone(), n.clone());
    let is = |b| reg.def(b) == Some(*id);
    let (leq, succ) = if is(Builtin::DecLessEqNat) {
        (Builtin::Leq, false)
    } else if is(Builtin::DecLessThanNat) {
        (Builtin::Leq, true)
    } else if is(Builtin::DecLessEqInt) {
        (Builtin::IntLeq, false)
    } else if is(Builtin::DecLessThanInt) {
        (Builtin::IntLess, false)
    } else {
        return None;
    };
    let m = if succ {
        let (nat, c) = reg.ctor(Builtin::Succ)?;
        Term::Ctor(nat, c, vec![Rc::new(m)])
    } else {
        m
    };
    Some(Term::app(Term::app(Term::Def(reg.def(leq)?), m), n))
}

/// A decision procedure for `prop` (a term in the current scope). The
/// search is first made with the proposition's operands bound as variables
/// (`200000 = 5` is searched as `x = y`), so it doesn't compute them and its
/// solutions mention the variables, not the computed values. Some
/// procedures apply only to particular values (one deciding `n = 0`), so if
/// that search finds nothing, everything it did is undone and the search is
/// made on the computed proposition, as before; its error, if any, is the
/// one reported.
pub(crate) fn decide(cx: &mut Ctx, prop: &Term) -> Result<Decision> {
    if let Some(bound) = crate::undo::transaction(cx, |cx| bound_decision(cx, prop))? {
        return Ok(Decision::Bound(bound));
    }
    let value = cx.eval(prop)?;
    Ok(Decision::Plain(decide_written(cx, prop, &value)?))
}

/// A decision of `prop` (`value` is its value): a relation method applied to
/// a dictionary as written, `Ord.lessThan [ord := d] x y`, by its decider
/// from the same dictionary (docs/proposals/interfaces.md §5.16 step 2); an
/// equation as written, `x = y`, through its type's `DecEq` instance (step
/// 3); anything else by the search (`auto.rs`, which also makes step 2 on
/// what `prop` computes to).
fn decide_written(cx: &mut Ctx, prop: &Term, value: &Value) -> Result<Term> {
    if let Some(decision) = crate::interfaces::written_relation_decider(cx.e, prop) {
        return Ok(decision);
    }
    if let Term::Eq(Some(ty), a, b) = prop.strip_loc()
        && crate::interfaces::dec_eq(cx.e).is_some()
    {
        let ty = cx.eval(ty)?;
        // The operands as written, not read back from their values: a
        // `let`-bound variable would be written out as its value (SW-345).
        return crate::interfaces::decide_eq_of(cx, &ty, (**a).clone(), (**b).clone());
    }
    crate::auto::decide(cx, value, 0)
}

/// A proposition's structure down to its operands: the operands are data
/// (not types or propositions) and not cheap.
enum Shape {
    /// A part kept as it is, in the outer scope.
    Kept(Term),
    /// The `i`th operand.
    Operand(usize),
    Eq(Rc<Term>, Box<Shape>, Box<Shape>),
    App(Box<Shape>, Box<Shape>, Icit),
}

impl Shape {
    /// The proposition inside `n` binders, one per operand.
    fn build(&self, cx: &Ctx, n: usize) -> Result<Term> {
        Ok(match self {
            Shape::Kept(t) => t.shift(cx.g(), n, 0)?,
            Shape::Operand(i) => Term::Var(n - 1 - i),
            Shape::Eq(ty, a, b) => Term::Eq(
                Some(Rc::new(ty.shift(cx.g(), n, 0)?)),
                Rc::new(a.build(cx, n)?),
                Rc::new(b.build(cx, n)?),
            ),
            Shape::App(f, a, icit) => Term::app_icit(f.build(cx, n)?, a.build(cx, n)?, *icit),
        })
    }
}

/// The search of [`decide`] with the operands bound, for
/// [`crate::undo::transaction`]: `None` if `prop` has no operand worth
/// binding, or the search finds nothing.
fn bound_decision(cx: &mut Ctx, prop: &Term) -> Result<Option<Bound>> {
    let mark = cx.mark();
    let outer = cx.env.clone();
    let mut binders = Vec::new();
    let mut operands = Vec::new();
    let shape = shape(cx, &outer, prop, &mut binders, &mut operands)?;
    if operands.is_empty() {
        return Ok(None);
    }
    let prop = shape.build(cx, operands.len())?;
    let value = cx.eval(&prop)?;
    let decision = match decide_written(cx, &prop, &value) {
        Ok(decision) => decision,
        Err(e) if crate::undo::fatal(&e) => return Err(e),
        Err(_) => return Ok(None),
    };
    cx.reset(mark);
    Ok(Some(Bound {
        binders,
        operands,
        prop,
        decision,
    }))
}

/// `prop`'s [`Shape`], binding each operand found (in `cx`, and in
/// `binders` and `operands`) as it goes. `outer` is the environment `prop`
/// is in. Only equations and applications of definitions are looked into;
/// anything else is kept.
fn shape(
    cx: &mut Ctx,
    outer: &[Value],
    prop: &Term,
    binders: &mut Vec<(Name, Term)>,
    operands: &mut Vec<Term>,
) -> Result<Shape> {
    let g = cx.g();
    match prop.strip_loc() {
        Term::Eq(Some(ty), a, b) => {
            let dom = eval(g, outer, ty)?;
            let a = operand(cx, outer.len(), &dom, a, binders, operands)?;
            let b = operand(cx, outer.len(), &dom, b, binders, operands)?;
            Ok(Shape::Eq(ty.clone(), Box::new(a), Box::new(b)))
        }
        term @ Term::App(..) => {
            let (head, args) = term.spine();
            let Term::Def(id) = head.strip_loc() else {
                return Ok(Shape::Kept(term.clone()));
            };
            let mut ty = g.def(*id).ty_value.clone();
            let mut built = Shape::Kept(head.clone());
            for arg in args {
                let Value::Pi(_, icit, dom, cod) = force(g, ty)? else {
                    return Ok(Shape::Kept(term.clone()));
                };
                let level = cx.level();
                let part = match force(g, (*dom).clone())? {
                    // A proposition or type: looked into.
                    Value::Sort(_) => shape(cx, outer, arg, binders, operands)?,
                    _ if icit == Icit::Explicit => {
                        operand(cx, outer.len(), &dom, arg, binders, operands)?
                    }
                    _ => Shape::Kept(arg.clone()),
                };
                ty = match part {
                    Shape::Operand(_) => cod.apply(g, Value::var(level))?,
                    _ => cod.apply_lazy(g, || eval(g, outer, arg))?,
                };
                built = Shape::App(Box::new(built), Box::new(part), icit);
            }
            Ok(built)
        }
        _ => Ok(Shape::Kept(prop.clone())),
    }
}

/// An operand `arg : dom` of a proposition, in the scope of the first
/// `outer` variables: bound as the next variable, unless it's cheap.
fn operand(
    cx: &mut Ctx,
    outer: usize,
    dom: &Value,
    arg: &Term,
    binders: &mut Vec<(Name, Term)>,
    operands: &mut Vec<Term>,
) -> Result<Shape> {
    if cheap(arg) && !costly_let(cx, outer, arg) {
        return Ok(Shape::Kept(arg.clone()));
    }
    let name: Name = format!("%{}", operands.len()).as_str().into();
    binders.push((name.clone(), cx.quote(dom)?));
    cx.bind_hidden(name, dom.clone());
    operands.push(arg.clone());
    Ok(Shape::Operand(operands.len() - 1))
}
