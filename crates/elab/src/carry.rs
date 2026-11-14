//! A decision's proofs carried along an equation of its test.
//!
//! An `if` on a decided proposition is `Decidable.elim d y n`, and `d`, once
//! computed, is a record `{ holds = s, sound = S, complete = C }` with `S: s =
//! True → p`. A `match` on `s` or a `rewrite` of it replaces `s` by a variable
//! `X` throughout the goal, which would leave `S` in a field now typed `X =
//! True → p`: an ill-formed motive, unless `p` is `s = True` itself (a
//! comparison on numbers), where `p` is replaced too. So where the record
//! (or `d.sound a`, `d.complete a` for a decision `d` whose test is `s`) is
//! met, its proofs are carried along the equation `c: s = X` the `match` or
//! the `rewrite`'s `J` provides:
//!
//! `{ holds = X, sound = e => S (J (y _ => y = True → s = True) (e => e) c
//! e), complete = h => J (y _ => y = True) (C h) c }`
//!
//! Proofs compare equal whatever they are, so in each arm, or once `X` is
//! the other side, the record is the decision the `if` holds. Where `p`
//! mentions `s` the usual generalisation is already well-formed, and
//! carrying would make it ill-formed: so `matching.rs` and `rewrite.rs`
//! carry only when the usual motive fails (for `rewrite.rs`, or can't be
//! checked yet), `rewrite.rs` first only where `p` doesn't mention the left
//! side, then everywhere.

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, Ev, Icit, Term};

use crate::check::{Ctx, Result, builtin_ctor, builtin_data};

pub(crate) struct Carry {
    pub(crate) decidable: DataId,
    bool_ty: Term,
    tru: Term,
}

/// The parts of a decision met in a term: a record built in place, or a
/// proof field of some decision applied to an argument.
pub(crate) enum Met<'a> {
    /// `{ holds, sound, complete }`: the proofs.
    Record(&'a Term, &'a Term),
    /// `d.sound a`: `d` and `a`.
    Sound(&'a Term, &'a Term, Icit),
    /// `d.complete a`.
    Complete(&'a Term, &'a Term, Icit),
}

impl Met<'_> {
    /// The decision's `sound`, whose type says what it decides.
    pub(crate) fn sound(&self, decidable: DataId) -> Term {
        match self {
            Met::Record(sound, _) => (*sound).clone(),
            Met::Sound(d, ..) | Met::Complete(d, ..) => {
                Term::Proj(decidable, 1, Rc::new((*d).clone()))
            }
        }
    }
}

impl Carry {
    pub(crate) fn new(cx: &Ctx) -> Result<Carry> {
        let (bool_data, tru) = builtin_ctor(cx, Builtin::True)?;
        Ok(Carry {
            decidable: builtin_data(cx, Builtin::Decidable)?,
            bool_ty: Term::Data(bool_data, Vec::new()),
            tru: Term::Ctor(bool_data, tru, Vec::new()),
        })
    }

    /// `t` as one of the forms whose proofs need carrying, with the test it
    /// is about: the record's `holds`, or `d.holds`.
    pub(crate) fn met<'a>(&self, t: &'a Term) -> Option<(Met<'a>, Term)> {
        match t.strip_loc() {
            Term::Ctor(d, 0, fields) if *d == self.decidable && fields.len() == 3 => {
                Some((Met::Record(&fields[1], &fields[2]), (*fields[0]).clone()))
            }
            Term::App(f, a, icit) => match f.strip_loc() {
                Term::Proj(d, k @ (1 | 2), r) if *d == self.decidable => {
                    let holds = Term::Proj(*d, 0, Rc::clone(r));
                    let met = if *k == 1 {
                        Met::Sound(r, a, *icit)
                    } else {
                        Met::Complete(r, a, *icit)
                    };
                    Some((met, holds))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// `met` rebuilt with `x` for its test: its parts (`part` replaces
    /// inside each, in the same context as `t`), carried along `c: s = x`.
    /// `s`, `c` and `x` are terms in the result's context.
    pub(crate) fn carried(
        &self,
        g: &Ev,
        met: Met,
        s: &Term,
        c: &Term,
        x: Term,
        part: &dyn Fn(&Term) -> Result<Term>,
    ) -> Result<Term> {
        let field = |d: Term, k| Term::Proj(self.decidable, k, Rc::new(d));
        Ok(match met {
            Met::Record(sound, complete) => {
                let sound = part(sound)?.shift(g, 1, 0)?;
                let complete = part(complete)?.shift(g, 1, 0)?;
                let (s1, c1) = (s.shift(g, 1, 0)?, c.shift(g, 1, 0)?);
                let e = self.forward(g, &s1, &c1, Term::Var(0))?;
                // The kernel can't infer a lambda's type, so a redex `(h =>
                // S) e` wouldn't check (`Nat.decEq`'s proofs are lambdas):
                // `S` takes `e` through a `let`, and `complete`'s body takes
                // its argument, a variable, by substitution.
                let sound = match sound.strip_loc() {
                    Term::Lam(h, Icit::Explicit, body) => {
                        Term::let_(h.clone(), self.is_true(s1), e, (**body).clone())
                    }
                    _ => Term::app(sound, e),
                };
                let complete = match complete.strip_loc() {
                    Term::Lam(_, Icit::Explicit, body) => body.instantiate_var(g, 0)?,
                    _ => Term::app(complete, Term::Var(0)),
                };
                let complete = self.backward(&c1, complete);
                let lam =
                    |x: &str, body| Rc::new(Term::Lam(x.into(), Icit::Explicit, Rc::new(body)));
                Term::Ctor(
                    self.decidable,
                    0,
                    vec![Rc::new(x), lam("e", sound), lam("h", complete)],
                )
            }
            Met::Sound(d, a, icit) => {
                let e = self.forward(g, s, c, part(a)?)?;
                Term::App(Rc::new(field(part(d)?, 1)), Rc::new(e), icit)
            }
            Met::Complete(d, a, icit) => {
                let h = Term::App(Rc::new(field(part(d)?, 2)), Rc::new(part(a)?), icit);
                self.backward(c, h)
            }
        })
    }

    /// `s = True` from `e: X = True`: `J (y _ => y = True → s = True) (e =>
    /// e) c e`, by `J` on `c` so that it computes away where `c` is `rfl`.
    fn forward(&self, g: &Ev, s: &Term, c: &Term, e: Term) -> Result<Term> {
        let is_true = |t| self.is_true(t);
        let body = Term::Pi(
            "_".into(),
            Icit::Explicit,
            Rc::new(is_true(Term::Var(1))),
            Rc::new(is_true(s.shift(g, 3, 0)?)),
        );
        let id = Term::Lam("e".into(), Icit::Explicit, Rc::new(Term::Var(0)));
        let along = Term::J(Rc::new(motive(body)), Rc::new(id), Rc::new(c.clone()));
        Ok(Term::app(along, e))
    }

    /// `t = True`.
    fn is_true(&self, t: Term) -> Term {
        Term::Eq(
            Some(Rc::new(self.bool_ty.clone())),
            Rc::new(t),
            Rc::new(self.tru.clone()),
        )
    }

    /// `X = True` from `h: s = True`: `J (y _ => y = True) h c`.
    fn backward(&self, c: &Term, h: Term) -> Term {
        let body = Term::Eq(
            Some(Rc::new(self.bool_ty.clone())),
            Rc::new(Term::Var(1)),
            Rc::new(self.tru.clone()),
        );
        Term::J(Rc::new(motive(body)), Rc::new(h), Rc::new(c.clone()))
    }

    /// `s = t[X]` from `c: s0 = X`, where `s = t[s0]`: `J (y _ => s = t[y])
    /// rfl c`. `ty` is `t[y]` under the motive's two binders.
    pub(crate) fn along(&self, g: &Ev, s: &Term, ty: Term, c: &Term) -> Result<Term> {
        let body = Term::Eq(
            Some(Rc::new(self.bool_ty.clone())),
            Rc::new(s.shift(g, 2, 0)?),
            Rc::new(ty),
        );
        Ok(Term::J(
            Rc::new(motive(body)),
            Rc::new(Term::Refl),
            Rc::new(c.clone()),
        ))
    }

    /// `lhs = y` from `k: lhs = rhs` and `q: rhs = y`: `J (y _ => lhs = y) k q`.
    /// `lhs` is a term in the result's context.
    pub(crate) fn then(&self, g: &Ev, lhs: &Term, k: Term, q: Term) -> Result<Term> {
        let body = Term::Eq(
            Some(Rc::new(self.bool_ty.clone())),
            Rc::new(lhs.shift(g, 2, 0)?),
            Rc::new(Term::Var(1)),
        );
        Ok(Term::J(Rc::new(motive(body)), Rc::new(k), Rc::new(q)))
    }

    /// `lhs = rhs` from `p: rhs = lhs`: `J (y _ => y = rhs) rfl p`.
    pub(crate) fn sym(&self, g: &Ev, rhs: &Term, p: Term) -> Result<Term> {
        let body = Term::Eq(
            Some(Rc::new(self.bool_ty.clone())),
            Rc::new(Term::Var(1)),
            Rc::new(rhs.shift(g, 2, 0)?),
        );
        Ok(Term::J(
            Rc::new(motive(body)),
            Rc::new(Term::Refl),
            Rc::new(p),
        ))
    }
}

/// `y q => body`, a `J` motive.
fn motive(body: Term) -> Term {
    let lam = |b: Term, x: &str| Term::Lam(x.into(), Icit::Explicit, Rc::new(b));
    lam(lam(body, "q"), "y")
}

/// The helper `Decidable.elim` computes to, `Decidable.elim.%match1 p a d
/// yes no t e`: a case on the test `t` (`d.holds`) with its equation `e`.
/// An `if` on a decided proposition, once computed, is a call of it stuck
/// on the test.
pub(crate) fn elim_helper(g: &Ev) -> Option<stitchwort_core::DefId> {
    let elim = g.env.registry().def(Builtin::ElimDec)?;
    let mut body = g.def(elim).body()?.strip_loc();
    while let Term::Lam(_, _, b) = body {
        body = b.strip_loc();
    }
    match body.spine().0.strip_loc() {
        Term::Def(id) => Some(*id),
        _ => None,
    }
}

/// `value` as an `if`, if it is a decision's `if` computed to
/// [`elim_helper`]'s call: the test, and each branch given a proof its
/// body doesn't look at.
pub(crate) fn as_if(
    g: &Ev,
    helper: Option<stitchwort_core::DefId>,
    value: &stitchwort_core::Value,
) -> stitchwort_core::budget::Result<
    Option<(
        stitchwort_core::Value,
        stitchwort_core::Value,
        stitchwort_core::Value,
    )>,
> {
    use stitchwort_core::value::{Elim, Head, Value, apply};
    let (Some(helper), Value::Neutral(Head::Def(id), spine)) = (helper, value) else {
        return Ok(None);
    };
    if *id != helper {
        return Ok(None);
    }
    let args: Option<Vec<&Value>> = spine
        .iter()
        .map(|e| match e {
            Elim::App(v, _) => Some(v),
            _ => None,
        })
        .collect();
    let Some([_, _, _, yes, no, test, _]) = args.as_deref() else {
        return Ok(None);
    };
    Ok(Some((
        (*test).clone(),
        apply(g, (*yes).clone(), Value::Refl)?,
        apply(g, (*no).clone(), Value::Refl)?,
    )))
}
