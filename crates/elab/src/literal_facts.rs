//! `auto` for `x ≠ lit`, where `lit` is a number, character or text literal
//! (or a constructor tree of them) and `x` is known to differ from it
//! because a `match` above took its catch-all arm
//! (docs/proposals/catch-all-facts.md, B).
//!
//! The catch-all knows its argument is none of the arms' literals only as a
//! mark on the value (literal-match-facts.md), so there is no proof to find.
//! The proof is made from the mark: transport `h: x = lit` along a motive
//! that is `Unit` where a `match` on the literal takes its catch-all and
//! `Void` at the literal,
//!
//! ```text
//! h => J (y q => match y with | lit => Void | _ => Unit) Trivial h
//! ```
//!
//! which the kernel accepts exactly when `x` computes the motive to `Unit`,
//! that is, when `x` is marked apart from `lit`. The motive is evaluated
//! here first, so a goal the marks don't support gives no proof and `auto`
//! goes on to its other steps.

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::{apart_of, force};
use stitchwort_core::{DataId, Icit, Sort, Term, Value};

use crate::check::{Ctx, Result, builtin_ctor, builtin_data};

/// A proof of `x ≠ lit` (or `lit ≠ x`) from what `x`'s marks say, or `None`.
pub(crate) fn prove(cx: &mut Ctx, goal: &Value) -> Result<Option<Term>> {
    let g = cx.g();
    let Value::Pi(_, Icit::Explicit, dom, closure) = force(&g, goal.clone())? else {
        return Ok(None);
    };
    if closure.body.mentions(0) {
        return Ok(None);
    }
    let void = builtin_data(cx, Builtin::Void)?;
    if !matches!(force(&g, closure.apply(&g, Value::Refl)?)?, Value::Data(d, p) if d == void && p.is_empty())
    {
        return Ok(None);
    }
    let Value::Eq(ty, left, right) = force(&g, (*dom).clone())? else {
        return Ok(None);
    };
    let (left, right) = (force(&g, (*left).clone())?, force(&g, (*right).clone())?);
    // `lit_on_right`: the equation is `x = lit`; otherwise it's `lit = x`
    // and is turned round first.
    let (x, lit, lit_on_right) = if closed_literal(&right) && !closed_literal(&left) {
        (left, right, true)
    } else if closed_literal(&left) && !closed_literal(&right) {
        (right, left, false)
    } else {
        return Ok(None);
    };
    let ty = (*ty).clone();

    // The motive's tree, in the context `.., h, y, q`: `y` is variable 1.
    let Some(tree) = tree(cx, vec![(1, lit.clone())])? else {
        return Ok(None);
    };
    if differs(cx, &x, &lit)? != Some(true) {
        return Ok(None);
    }

    let mark = cx.mark();
    cx.bind_hidden("h".into(), (*dom).clone());
    let y = cx.level();
    cx.bind_hidden("y".into(), ty.clone());
    cx.bind_hidden(
        "q".into(),
        Value::Eq(
            Rc::new(ty.clone()).into(),
            Rc::new(x).into(),
            Rc::new(Value::var(y)).into(),
        ),
    );
    let call = crate::lift::draft(
        cx,
        cx.level(),
        Vec::new(),
        tree,
        &Value::Sort(Sort::Prop),
        cx.span,
    );
    cx.reset(mark);
    let motive = Term::Lam(
        "y".into(),
        Icit::Explicit,
        Rc::new(Term::Lam("q".into(), Icit::Explicit, Rc::new(call?))),
    );
    let trivial = builtin_ctor(cx, Builtin::Trivial)?;
    let mut h = Term::Var(0);
    if !lit_on_right {
        // `h: lit = x` turned into `x = lit` by `J (y q => y = lit) byComputing h`.
        let ty_term = cx.quote_or_written(&ty)?.shift(&g, 3, 0)?;
        let lit_term = cx.quote_or_written(&lit)?.shift(&g, 3, 0)?;
        let body = Term::Eq(
            Some(Rc::new(ty_term)),
            Rc::new(Term::Var(1)),
            Rc::new(lit_term),
        );
        let flip = Term::Lam(
            "y".into(),
            Icit::Explicit,
            Rc::new(Term::Lam("q".into(), Icit::Explicit, Rc::new(body))),
        );
        h = Term::J(Rc::new(flip), Rc::new(Term::Refl), Rc::new(h));
    }
    let transport = Term::J(
        Rc::new(motive),
        Rc::new(Term::ctor(trivial.0, trivial.1, Vec::new())),
        Rc::new(h),
    );
    Ok(Some(Term::Lam(
        "h".into(),
        Icit::Explicit,
        Rc::new(transport),
    )))
}

/// A value built only from numbers, characters, texts and constructors
/// applied to such (and erased proofs).
fn closed_literal(value: &Value) -> bool {
    match value {
        Value::Nat(_) | Value::Chars(_) | Value::Refl => true,
        Value::Ctor(_, _, fields) => fields.iter().all(closed_literal),
        _ => false,
    }
}

/// The case tree that is `Void` where every `(variable, literal)` in
/// `todo` matches (variables as de Bruijn indices at that point) and `Unit`
/// where one doesn't, or `None` for a literal it can't match on.
fn tree(cx: &Ctx, mut todo: Vec<(usize, Value)>) -> Result<Option<Term>> {
    let g = cx.g();
    let unit = Term::data(builtin_data(cx, Builtin::Unit)?, Vec::new());
    let Some((ix, lit)) = todo.pop() else {
        return Ok(Some(Term::data(
            builtin_data(cx, Builtin::Void)?,
            Vec::new(),
        )));
    };
    let (d, ctor, fields): (DataId, usize, Vec<Value>) = match force(&g, lit)? {
        Value::Nat(n) => {
            let Some(rest) = tree(cx, todo)? else {
                return Ok(None);
            };
            let arm = NumArm {
                value: n,
                body: Rc::new(rest),
            };
            return Ok(Some(Term::NumCase(ix, Rc::from(vec![arm]), Rc::new(unit))));
        }
        Value::Ctor(d, c, fields) => (d, c, fields.iter().cloned().collect()),
        Value::Chars(chars) => {
            let Some(text) = g.env.builtins().text.as_ref() else {
                return Ok(None);
            };
            let (c, fields) = stitchwort_core::chars::split(text, &chars);
            (text.list, c, fields)
        }
        _ => return Ok(None),
    };
    let data = g.data(d);
    if !data.indices().is_empty() {
        return Ok(None);
    }
    let mut branches = Vec::new();
    for (k, c) in data.ctors().iter().enumerate() {
        let names = c.fields.iter().map(|(n, _)| n.clone()).collect();
        if k != ctor {
            branches.push(Branch {
                names,
                body: Some(Rc::new(unit.clone())),
            });
            continue;
        }
        let n = fields.len();
        // Pending matches move under this branch's `n` field binders; the
        // fields' own come first.
        let mut inner: Vec<(usize, Value)> = todo.iter().map(|(i, v)| (i + n, v.clone())).collect();
        for (i, field) in fields.iter().enumerate().rev() {
            if !c.field_erased[i] {
                inner.push((n - 1 - i, field.clone()));
            }
        }
        let Some(body) = tree(cx, inner)? else {
            return Ok(None);
        };
        branches.push(Branch {
            names,
            body: Some(Rc::new(body)),
        });
    }
    Ok(Some(Term::Case(ix, d, branches.into())))
}

/// What the case tree [`tree`] makes of `lit` computes to at `x`: `Some(true)`
/// for `Unit` (`x` is not `lit`), `Some(false)` for `Void` (it is), `None`
/// where it would be stuck. The same steps as the evaluator's case nodes,
/// since a case outside a definition's tree can't be run to find out.
fn differs(cx: &Ctx, x: &Value, lit: &Value) -> Result<Option<bool>> {
    let g = cx.g();
    let (x, lit) = (force(&g, x.clone())?, force(&g, lit.clone())?);
    if let Value::Nat(n) = &lit {
        return Ok(match stitchwort_core::native::view(&g, &x)? {
            (k, None) => Some(k != **n),
            (k, Some(base)) => {
                if **n < k
                    || apart_of(&base)
                        .numbers(&g)
                        .binary_search(&(&**n - &k))
                        .is_ok()
                {
                    Some(true)
                } else {
                    None
                }
            }
        });
    }
    let text = g.env.builtins().text.as_ref();
    let expand = |v: &Value| match (v, text) {
        (Value::Chars(chars), Some(text)) => {
            let (c, fields) = stitchwort_core::chars::split(text, chars);
            Some((text.list, c, fields))
        }
        (Value::Ctor(d, c, fields), _) => Some((*d, *c, fields.iter().cloned().collect())),
        _ => None,
    };
    let (Some((d, c, fields)), Some((d2, c2, fields2))) = (expand(&lit), expand(&x)) else {
        return Ok(None);
    };
    if d != d2 {
        return Ok(None);
    }
    if c != c2 {
        return Ok(Some(true));
    }
    let ctor = &g.data(d).ctors()[c];
    for (i, (a, b)) in fields2.iter().zip(&fields).enumerate() {
        if ctor.field_erased[i] {
            continue;
        }
        match differs(cx, a, b)? {
            Some(false) => {}
            other => return Ok(other),
        }
    }
    Ok(Some(false))
}
