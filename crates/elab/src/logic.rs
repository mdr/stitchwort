//! `a && b`, `a || b` and `not a`, on `Bool`s or on propositions
//! (docs/syntax.md, "Expressions").
//!
//! Each has two readings:
//! - As a `Bool`: `a && b` is `if a then b else False` and `a || b` is
//!   `if a then True else b`, so `b` is only evaluated (and its operations
//!   only performed) when it's needed; `not a` is `Bool.not a`. Each operand
//!   is a condition, as `if` reads one: a `Bool`, or failing that a
//!   proposition with a decision procedure, decided. As in that `if`, when
//!   `a` is a proposition `b` is checked knowing that it holds (`a && b`) or
//!   doesn't (`a || b`), so `n != 0 && len % n == 0` finds `%`'s proof.
//! - As a proposition: `And a b`, `Or a b` and `Not a`, each operand a
//!   proposition.
//!
//! Where a proposition is expected (a type, as in `if h : p && q`), it's the
//! proposition. Otherwise (a `Bool` expected, or nothing known) the `Bool`
//! reading is tried first, and only if it fails, with everything it did
//! undone, the proposition, as `if c` does. If both fail, the `Bool`
//! reading's error is reported.

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::force;
use stitchwort_core::{DefId, Icit, Sort, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{BinOp, Expr};

use crate::check::{Result, builtin_ctor, builtin_data, builtin_def, check, check_type};
use crate::state::Conjunction;
use crate::{Ctx, Global};

/// One of the logical forms.
#[derive(Clone, Copy)]
pub(crate) enum Logic<'a> {
    And(&'a Expr, &'a Expr),
    Or(&'a Expr, &'a Expr),
    /// `not a`, with the library's `Bool.not`.
    Not(&'a Expr, DefId),
}

impl Logic<'_> {
    fn symbol(self) -> &'static str {
        match self {
            Logic::And(..) => "&&",
            Logic::Or(..) => "||",
            Logic::Not(..) => "not",
        }
    }
}

/// `expr` as a logical form: `a && b`, `a || b`, or `not a` where `not` is
/// the library's (not a local variable or a declaration of the module's own
/// that happens to be called `not`).
pub(crate) fn classify<'a>(cx: &Ctx, expr: &'a Expr) -> Option<Logic<'a>> {
    match expr {
        Expr::Binary(BinOp::And, a, b) => Some(Logic::And(a, b)),
        Expr::Binary(BinOp::Or, a, b) => Some(Logic::Or(a, b)),
        Expr::App(f, a) if !matches!(**a, Expr::NamedArg(..)) => {
            let Expr::Var(name) = &**f else {
                return None;
            };
            if cx.lookup(&name.text).is_some() {
                return None;
            }
            match cx.e.named(&name.text) {
                Some((Global::Def(id), _))
                    if cx.g().env.registry().is_def(Builtin::BoolNot, *id) =>
                {
                    Some(Logic::Not(a, *id))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The addresses of `expr` and of the operands of the `∧`, `∨` and `¬` it
/// is made of, brackets looked through: a side of an `=` between
/// propositions, where a `Bool` isn't read as one (`Decl::not_coerced`).
pub(crate) fn equation_side(cx: &Ctx, expr: &Expr, out: &mut Vec<usize>) {
    out.push(std::ptr::from_ref(expr) as usize);
    match expr {
        Expr::Bracketed(inner, _) => equation_side(cx, inner, out),
        _ => match classify(cx, expr) {
            Some(Logic::And(a, b) | Logic::Or(a, b)) => {
                equation_side(cx, a, out);
                equation_side(cx, b, out);
            }
            Some(Logic::Not(a, _)) => equation_side(cx, a, out),
            None => {}
        },
    }
}

/// A condition, as `if c` reads it.
pub(crate) enum Condition {
    /// A `Bool`.
    Bool(Term),
    /// A proposition, and a decision procedure for it.
    Decided {
        prop: Term,
        decision: crate::bind::Decision,
    },
    /// A proposition whose decision has to wait (`check::decision_blocker`,
    /// step 4.3): a placeholder in it isn't filled yet, or an operator's
    /// dictionary in it isn't known yet. As a `Bool` it is a waiting
    /// decision; where the decision itself is needed as a term, it
    /// waits as a term ([`Condition::decided_now`]).
    Waiting { prop: Term },
    /// `a && b` read as the `Bool` `as_bool`, where `prop`, the conjunction
    /// of its operands, is decided by `decision` too: each operand is a
    /// decided proposition or a `Bool` `c`, read as `c = True`, one at least
    /// a proposition, and `b` was checked without `a`'s proof. For an `if`
    /// whose branches may use its proof (`if b != 0 && c != 0 then a % b`);
    /// anywhere else it's `as_bool`.
    Conjunction {
        as_bool: Term,
        prop: Term,
        decision: Term,
    },
}

/// One operand of a [`Condition::Conjunction`].
pub(crate) struct Conjunct {
    prop: Term,
    decision: Term,
    /// Whether it's a decided proposition, not a `Bool`'s `c = True`.
    decided: bool,
}

impl Conjunct {
    /// `condition` as an operand of a conjunction; `None` for one whose
    /// decision has to wait.
    fn of(cx: &Ctx, condition: &Condition) -> Result<Option<Conjunct>> {
        Ok(Some(match condition {
            Condition::Bool(c) => {
                let dec_true = builtin_def(cx, Builtin::DecTrue)?;
                Conjunct {
                    prop: true_prop(cx, c.clone())?,
                    decision: Term::app(Term::Def(dec_true), c.clone()),
                    decided: false,
                }
            }
            Condition::Decided { prop, decision } => Conjunct {
                prop: prop.clone(),
                decision: decision.clone().term(cx)?,
                decided: true,
            },
            Condition::Conjunction { prop, decision, .. } => Conjunct {
                prop: prop.clone(),
                decision: decision.clone(),
                decided: true,
            },
            Condition::Waiting { .. } => return Ok(None),
        }))
    }

    /// The right operand, checked under the left one's branch binder, in
    /// the scope outside it; `None` if it mentions the binder. Its decision
    /// stays under the binder, as the body of the function
    /// `Decidable.andThen` takes.
    fn outside_binder(self, cx: &Ctx) -> Result<Option<Conjunct>> {
        let level = cx.level();
        let zonked = |term: &Term| -> Result<Term> {
            crate::unify::zonk_in(&cx.u(), level, term, &|_| true, &[]).map_err(|e| match e {
                crate::unify::ZonkError::Resource(e) => Diagnostic::from(e),
                crate::unify::ZonkError::Unsolved(_) => {
                    unreachable!("every unsolved metavariable is kept")
                }
            })
        };
        let prop = zonked(&self.prop)?;
        let decision = zonked(&self.decision)?;
        if prop.mentions(0) || decision.mentions(0) {
            return Ok(None);
        }
        Ok(Some(Conjunct {
            prop: prop.instantiate_var(&cx.g(), 0)?,
            decision,
            decided: self.decided,
        }))
    }
}

/// `a ∧ b`, decided by `Decidable.andThen`, if one operand at least is a
/// decided proposition. `b`'s decision is under one binder.
fn conjunction(cx: &Ctx, a: Conjunct, b: Conjunct) -> Result<Option<(Term, Term)>> {
    if !a.decided && !b.decided {
        return Ok(None);
    }
    let and = builtin_data(cx, Builtin::And)?;
    let prop = Term::data(and, vec![a.prop.clone(), b.prop.clone()]);
    let then = builtin_def(cx, Builtin::DecAndThen)?;
    let head = Term::app_icit(
        Term::app_icit(Term::Def(then), a.prop, Icit::Implicit),
        b.prop,
        Icit::Implicit,
    );
    let later = Term::Lam("_".into(), Icit::Explicit, Rc::new(b.decision));
    Ok(Some((prop, Term::app(Term::app(head, a.decision), later))))
}

/// `c = True`, for a `Bool` `c`.
pub(crate) fn true_prop(cx: &Ctx, c: Term) -> Result<Term> {
    let bool_ty = Term::Data(builtin_data(cx, Builtin::Bool)?, Vec::new());
    let (d, t) = builtin_ctor(cx, Builtin::True)?;
    Ok(Term::Eq(
        Some(Rc::new(bool_ty)),
        Rc::new(c),
        Rc::new(Term::Ctor(d, t, Vec::new())),
    ))
}

/// The address of `a` in a condition `a && b`.
fn conjunction_lhs(cond: &Expr) -> Option<usize> {
    match cond {
        Expr::Binary(BinOp::And, a, _) => Some(std::ptr::from_ref(&**a) as usize),
        Expr::Bracketed(inner, _) => conjunction_lhs(inner),
        _ => None,
    }
}

impl Condition {
    /// A [`Condition::Waiting`] as a decision term, which waits
    /// (`check::decision_or_wait`): for an `if` whose branches may use its
    /// proof. Any other condition as it is.
    pub(crate) fn decided_now(
        self,
        cx: &mut Ctx,
        span: stitchwort_syntax::Span,
    ) -> Result<Condition> {
        match self {
            Condition::Waiting { prop } => {
                let decision = crate::check::decision_or_wait(cx, span, &prop)?;
                Ok(Condition::Decided { prop, decision })
            }
            other => Ok(other),
        }
    }
}

/// `cond` as a `Bool`; or if that fails, with everything it did undone, as a
/// proposition with a decision procedure. If both fail, the `Bool` reading's
/// error, unless `cond` is a proposition nothing decides. `what` is the
/// syntax taking the condition, for that error.
///
/// When the `Bool` reading's error is the one reported, the state is the
/// `Bool` reading's too. The local definitions it met (`local.rs`) may be
/// why it failed: a call of one is a frozen metavariable until it's lifted,
/// and the declaration is elaborated again once they're admitted, which
/// needs their drafts. Undoing the reading drops them, so if it made any,
/// it's done again.
pub(crate) fn condition(cx: &mut Ctx, cond: &Expr, what: &str) -> Result<Condition> {
    if let Some((name, value, body)) = cond.as_chain_let() {
        return chain_condition(cx, name, value, body, what);
    }
    let bool_ty = Value::Data(builtin_data(cx, Builtin::Bool)?, Vec::new().into());
    let snapshot = crate::undo::Snapshot::take(cx);
    let outer =
        cx.e.decl
            .condition
            .replace(std::ptr::from_ref(cond) as usize);
    let outer_conjunction = (cx.e.decl.conjunction)
        .replace(conjunction_lhs(cond).map(|lhs| Conjunction { lhs, found: None }));
    let as_bool = check(cx, cond, &bool_ty);
    let conjunction = (cx.e.decl.conjunction.replace(outer_conjunction)).and_then(|c| c.found);
    cx.e.decl.condition.set(outer);
    let not_bool = match as_bool {
        Ok(as_bool) => {
            return Ok(match conjunction {
                Some((prop, decision)) => Condition::Conjunction {
                    as_bool,
                    prop,
                    decision,
                },
                None => Condition::Bool(as_bool),
            });
        }
        Err(e) if crate::undo::fatal(&e) => return Err(e),
        Err(not_bool) => not_bool,
    };
    let drafted = snapshot.drafted_since(cx);
    snapshot.restore(cx);
    let before = crate::undo::Snapshot::take(cx);
    match decided(cx, cond, what, &not_bool)? {
        Some(found) => Ok(found),
        None if drafted => {
            before.restore(cx);
            check(cx, cond, &bool_ty).map(Condition::Bool)
        }
        None => Err(not_bool),
    }
}

/// A chain of comparisons with a middle operand that is computed
/// (`crate::chain`): the condition of its body, with the operand run once
/// by whatever runs the `Bool` or the decision, and put back in place in
/// the proposition the branches learn.
fn chain_condition(
    cx: &mut Ctx,
    name: &stitchwort_syntax::ast::Name,
    value: &Expr,
    body: &Expr,
    what: &str,
) -> Result<Condition> {
    // The condition's terms are under the variable; the decision is read
    // while the variable is in scope.
    let (inner, binding) = crate::chain::around(cx, name, value, |cx| {
        Ok(match condition(cx, body, what)? {
            Condition::Decided { prop, decision } => Condition::Decided {
                prop,
                decision: crate::bind::Decision::Plain(decision.term(cx)?),
            },
            other => other,
        })
    })?;
    Ok(match inner {
        Condition::Decided { prop, decision } => Condition::Decided {
            prop: binding.inline(cx, &prop)?,
            decision: crate::bind::Decision::Plain(binding.wrap(decision.term(cx)?)),
        },
        Condition::Waiting { prop } => Condition::Waiting {
            prop: binding.inline(cx, &prop)?,
        },
        Condition::Bool(c) => Condition::Bool(binding.wrap(c)),
        Condition::Conjunction {
            as_bool,
            prop,
            decision,
        } => Condition::Conjunction {
            as_bool: binding.wrap(as_bool),
            prop: binding.inline(cx, &prop)?,
            decision: binding.wrap(decision),
        },
    })
}

/// `cond` as a decided proposition, for [`condition`]; `None` if the `Bool`
/// reading's error `not_bool` is the one to report.
fn decided(
    cx: &mut Ctx,
    cond: &Expr,
    what: &str,
    not_bool: &Diagnostic,
) -> Result<Option<Condition>> {
    let Some((prop, Sort::Prop)) = crate::undo::attempt(cx, |cx| check_type(cx, cond))? else {
        return Ok(None);
    };
    if crate::check::decision_blocker(cx, &prop, crate::check::Depth::Written)?.is_some() {
        return Ok(Some(Condition::Waiting { prop }));
    }
    // No decision procedure. If the `Bool` reading already found an operand
    // nothing decides (`x < 3 && g = h`), that's the more precise error.
    // Otherwise say so at the condition, keeping the search's explanations
    // (its notes after the first).
    let decision = match crate::bind::decide(cx, &prop) {
        Ok(decision) => decision,
        Err(e)
            if e.code == "E-AUTO-NONE"
                && matches!(not_bool.code, "E-AUTO-NONE" | "E-INSTANCE-NONE") =>
        {
            return Ok(None);
        }
        Err(mut e) if e.code == "E-AUTO-NONE" && !e.notes.is_empty() => {
            e.labels.clear();
            e.notes[0] = format!(
                "`{what}` takes a `Bool`, or a proposition with a decision procedure: an \
                 `instance` returning `Decidable …`"
            );
            return Err(e.with_label(cond.span(), "this is a proposition, and nothing decides it"));
        }
        Err(e) => return Err(e),
    };
    Ok(Some(Condition::Decided { prop, decision }))
}

/// `expr` as a `Bool`: a decided proposition is `Decidable.toBool` of its
/// decision.
pub(crate) fn bool_operand(cx: &mut Ctx, expr: &Expr, what: &str) -> Result<Term> {
    let condition = condition(cx, expr, what)?;
    condition_bool(cx, expr, condition)
}

/// [`bool_operand`] of the condition `expr` reads as.
fn condition_bool(cx: &mut Ctx, expr: &Expr, condition: Condition) -> Result<Term> {
    let term = match condition {
        Condition::Bool(term) | Condition::Conjunction { as_bool: term, .. } => term,
        Condition::Decided { prop, decision } => decision.into_bool(cx, prop)?,
        Condition::Waiting { prop } => {
            let bool_ty = Value::Data(builtin_data(cx, Builtin::Bool)?, Vec::new().into());
            crate::check::decide_or_wait(
                cx,
                expr.span(),
                &prop,
                &bool_ty,
                crate::check::Depth::Written,
            )?
        }
    };
    crate::probe::record_truth(cx, expr, &term);
    Ok(term)
}

/// The `Bool` reading.
fn as_bool(cx: &mut Ctx, logic: Logic) -> Result<Term> {
    let what = logic.symbol();
    let (a, b) = match logic {
        Logic::Not(a, not) => {
            let a = bool_operand(cx, a, what)?;
            return Ok(Term::app(Term::Def(not), a));
        }
        Logic::And(a, b) | Logic::Or(a, b) => (a, b),
    };
    let and = matches!(logic, Logic::And(..));
    let bool_ty = Term::Data(builtin_data(cx, Builtin::Bool)?, Vec::new());
    let constant = |cx: &mut Ctx, which| -> Result<Term> {
        let (d, c) = builtin_ctor(cx, which)?;
        Ok(Term::Ctor(d, c, Vec::new()))
    };
    // The condition `logic::condition` is reading: what it decides as a
    // conjunction is found on the way.
    let wanted = and
        && (cx.e.decl.conjunction.borrow().as_ref())
            .is_some_and(|c| c.lhs == std::ptr::from_ref(a) as usize);
    if !wanted {
        return short_circuit(
            cx,
            and,
            a,
            what,
            bool_ty,
            &mut |cx| bool_operand(cx, b, what),
            &constant,
            None,
        );
    }
    let mut lhs = None;
    let mut rhs = None;
    let term = short_circuit(
        cx,
        and,
        a,
        what,
        bool_ty,
        &mut |cx| {
            let condition = condition(cx, b, what)?;
            rhs = match Conjunct::of(cx, &condition)? {
                Some(part) => part.outside_binder(cx)?,
                None => None,
            };
            condition_bool(cx, b, condition)
        },
        &constant,
        Some(&mut lhs),
    )?;
    if let (Some(lhs), Some(rhs)) = (lhs, rhs)
        && let Some(found) = conjunction(cx, lhs, rhs)?
        && let Some(slot) = cx.e.decl.conjunction.borrow_mut().as_mut()
    {
        slot.found = Some(found);
    }
    Ok(term)
}

/// `a && b` (if `and`) or `a || b`, with `a` a condition and branches of
/// type `result`: `rhs` elaborates `b`, and `constant` the `True` or `False`
/// branch, each under the branch's binder. The `Bool` reading has `Bool`
/// branches; a `b` that performs operations has computations as branches.
/// `lhs`, if given, is set to `a` as a [`Conjunct`] when `b` didn't need its
/// proof.
#[allow(clippy::too_many_arguments)]
pub(crate) fn short_circuit(
    cx: &mut Ctx,
    and: bool,
    a: &Expr,
    what: &str,
    result: Term,
    rhs: &mut dyn FnMut(&mut Ctx) -> Result<Term>,
    constant: &dyn Fn(&mut Ctx, Builtin) -> Result<Term>,
    lhs_part: Option<&mut Option<Conjunct>>,
) -> Result<Term> {
    let lhs = a;
    let unit = Value::Data(builtin_data(cx, Builtin::Unit)?, Vec::new().into());
    let ite = builtin_def(cx, Builtin::IfThenElse)?;
    let ite = Term::app_icit(Term::Def(ite), result.clone(), Icit::Implicit);
    // `b` is checked as the branch of `if a` that needs it: assuming `a`
    // (in `a && b`) or `Not a` (in `a || b`) when `a` is a proposition, so
    // `n != 0 && len % n == 0` finds `%`'s proof; or, for a `Bool` `a`, an
    // unused proof of `Unit`, as the branches of `Bool.ifThenElse` take.
    let condition = condition(cx, a, what)?;
    let part = match lhs_part {
        Some(slot) => Some((slot, Conjunct::of(cx, &condition)?)),
        None => None,
    };
    let (head, a, b) = match condition {
        Condition::Bool(a) | Condition::Conjunction { as_bool: a, .. } => {
            if let Some((slot, part)) = part {
                *slot = part;
            }
            crate::probe::record_truth(cx, lhs, &a);
            let mark = cx.mark();
            cx.bind("_", unit.clone());
            let b = rhs(cx);
            cx.reset(mark);
            (ite, a, b?)
        }
        condition @ (Condition::Decided { .. } | Condition::Waiting { .. }) => {
            // A decision that waits is made here, as a term, only if `b`
            // needs `a`'s proof (`elimDec`, below); as the `Bool` of `if a
            // then b else False` it waits (`check::decide_or_wait`).
            let (prop, decision) = match condition {
                Condition::Decided { prop, decision } => (prop, Some(decision)),
                Condition::Waiting { prop } => (prop, None),
                Condition::Bool(_) | Condition::Conjunction { .. } => {
                    unreachable!("matched above")
                }
            };
            // The assumption's type is `a`'s value, and the evaluator is
            // strict: evaluating `cost < 5` computes `cost`. So `b` is
            // checked first with the assumption's type left as `Unit`, and
            // `a` is evaluated only if `b` turns out to need it. Only the
            // search for an auto argument's proof looks at the type, so if
            // `b` checks, the obligations it recorded are given the real
            // type afterwards; if it doesn't, it's checked again assuming
            // `a`, in case a search made while checking it needed `a`.
            let level = cx.level();
            let before = cx.e.attempt.obligations.borrow().len();
            let first = crate::undo::attempt(cx, |cx| {
                let mark = cx.mark();
                cx.bind("_", unit.clone());
                let b = rhs(cx);
                cx.reset(mark);
                b
            })?;
            let b = match first {
                Some(b) => {
                    if needs_proofs(cx, before)? {
                        let assumption = assumption(cx, &prop, and)?;
                        for ob in &mut cx.e.attempt.obligations.borrow_mut()[before..] {
                            if ob.types.len() > level {
                                ob.types[level] = assumption.clone();
                            }
                        }
                    }
                    b
                }
                None => {
                    let assumption = assumption(cx, &prop, and)?;
                    let mark = cx.mark();
                    cx.bind("_", assumption);
                    let b = rhs(cx);
                    cx.reset(mark);
                    b?
                }
            };
            if needs_proofs(cx, before)? {
                // `if _ : a then b else False`, as `if` makes it: `elimDec`.
                let elim = builtin_def(cx, Builtin::ElimDec)?;
                let decision = match decision {
                    Some(decision) => decision,
                    None => crate::check::decision_or_wait(cx, lhs.span(), &prop)?,
                };
                if let Ok(truth) = decision.clone().into_bool(cx, prop.clone()) {
                    crate::probe::record_truth(cx, lhs, &truth);
                }
                let head = Term::app_icit(
                    Term::app_icit(Term::Def(elim), prop, Icit::Implicit),
                    result,
                    Icit::Implicit,
                );
                (head, decision.term(cx)?, b)
            } else {
                // Nothing in `b` can have used the assumption (only the
                // search for an auto argument's proof sees it), so it's
                // `if a then b else False` on the decision's `Bool`, as
                // ever: the same term as `Bool.and (toBool …) b` reads, so
                // the library's facts about `&&` on `Bool`s apply to it.
                let truth = match decision {
                    Some(decision) => decision.into_bool(cx, prop)?,
                    None => {
                        let bool_ty =
                            Value::Data(builtin_data(cx, Builtin::Bool)?, Vec::new().into());
                        crate::check::decide_or_wait(
                            cx,
                            lhs.span(),
                            &prop,
                            &bool_ty,
                            crate::check::Depth::Written,
                        )?
                    }
                };
                crate::probe::record_truth(cx, lhs, &truth);
                if let Some((slot, part)) = part {
                    *slot = part;
                }
                (ite, truth, b)
            }
        }
    };
    let mark = cx.mark();
    cx.bind("_", unit.clone());
    let fixed = constant(cx, if and { Builtin::False } else { Builtin::True });
    cx.reset(mark);
    let (then, otherwise) = if and { (b, fixed?) } else { (fixed?, b) };
    let branch = |body| Term::Lam("_".into(), Icit::Explicit, Rc::new(body));
    Ok(Term::app(
        Term::app(Term::app(head, a), branch(then)),
        branch(otherwise),
    ))
}

/// What `b` may assume in `a && b` (`a`) or `a || b` (`Not a`), for the
/// proposition `a`.
fn assumption(cx: &mut Ctx, prop: &Term, and: bool) -> Result<Value> {
    let prop_value = cx.eval(prop)?;
    if and {
        return Ok(prop_value);
    }
    let not = cx.eval(&Term::Def(builtin_def(cx, Builtin::Not)?))?;
    Ok(stitchwort_core::value::apply(&cx.g(), not, prop_value)?)
}

/// Whether an obligation recorded since the first `before` needs a proof:
/// an auto argument (not an instance to find), whose search sees the
/// hypotheses in scope.
fn needs_proofs(cx: &Ctx, before: usize) -> Result<bool> {
    let goals: Vec<Value> = cx.e.attempt.obligations.borrow()[before..]
        .iter()
        .map(|ob| ob.goal.clone())
        .collect();
    for goal in &goals {
        if crate::interfaces::interface_goal(cx.e, goal)?.is_none() {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The proposition reading.
///
/// Each operand is a proposition, and a `Bool` operand `b` is read as `b =
/// True` on its own (`check::bool_as_prop`), so `a ∧ b` on two `Bool`s is
/// `a = True ∧ b = True`, never the test `(a && b) = True`: an operator
/// written where a proposition is expected is always the logical one
/// (D3486, docs/proposals/bool-as-proposition.md §4.3). This is the one
/// place that rule is made; the printer's half of it is
/// `Printer::bare_test` in `stitchwort_core::pretty`.
pub(crate) fn as_prop(cx: &mut Ctx, logic: Logic) -> Result<Term> {
    let what = logic.symbol();
    let operand = |cx: &mut Ctx, e: &Expr| -> Result<Term> {
        match crate::check::check_type_defaulting(cx, e, Sort::Prop) {
            Ok((term, Sort::Prop)) => Ok(term),
            Ok(_) => Err(
                Diagnostic::error("E-TYPE-MISMATCH", "expected a proposition")
                    .with_label(e.span(), "this is a type of data, not a proposition")
                    .with_note(format!("`{what}` here is on propositions")),
            ),
            Err(err) => Err(err),
        }
    };
    Ok(match logic {
        Logic::Not(a, _) => {
            let a = operand(cx, a)?;
            Term::app(Term::Def(builtin_def(cx, Builtin::Not)?), a)
        }
        Logic::And(a, b) | Logic::Or(a, b) => {
            let a = operand(cx, a)?;
            let b = operand(cx, b)?;
            let d = builtin_data(
                cx,
                match logic {
                    Logic::And(..) => Builtin::And,
                    _ => Builtin::Or,
                },
            )?;
            Term::data(d, vec![a, b])
        }
    })
}

/// With nothing expected: the `Bool` reading, or failing that the
/// proposition.
pub(crate) fn infer(cx: &mut Ctx, logic: Logic) -> Result<(Term, Value)> {
    let snapshot = crate::undo::Snapshot::take(cx);
    let not_bool = match as_bool(cx, logic) {
        Ok(term) => {
            let bool_data = builtin_data(cx, Builtin::Bool)?;
            return Ok((term, Value::Data(bool_data, Vec::new().into())));
        }
        Err(e) if crate::undo::fatal(&e) => return Err(e),
        Err(not_bool) => not_bool,
    };
    snapshot.restore(cx);
    match crate::undo::attempt(cx, |cx| as_prop(cx, logic))? {
        Some(term) => Ok((term, Value::Sort(Sort::Prop))),
        None => Err(not_bool),
    }
}

/// Against `expected`: a `Bool`, a proposition where a type is expected, and
/// otherwise as `infer` finds it.
pub(crate) fn check_against(cx: &mut Ctx, logic: Logic, expected: &Value) -> Result<Term> {
    let bool_data = builtin_data(cx, Builtin::Bool)?;
    let (term, found) = match force(&cx.g(), expected.clone())? {
        Value::Data(d, _) if d == bool_data => return as_bool(cx, logic),
        Value::Sort(Sort::Prop) => return as_prop(cx, logic),
        Value::Sort(_) => (as_prop(cx, logic)?, Value::Sort(Sort::Prop)),
        _ => infer(cx, logic)?,
    };
    crate::check::compare(cx, term, &found, expected)
}

/// The name of the `let` that carries the `Bool` an `if` on a conjunction is
/// on, around its decision ([`tag_decision`]). No source can write it.
const TAG: &str = "%conj";

/// `decision`, a conjunction's `Decidable.andThen dp dq`, as `let %conj :=
/// tag in decision`: `tag`, the `Bool` the `if` is on, is kept where the term
/// is written until [`settle_tagged`] knows whether the branches use the
/// proof. Only the elaborator writes the `let`, so settling trusts that `tag`
/// and the decision agree.
pub(crate) fn tag_decision(cx: &Ctx, decision: &Term, tag: &Term) -> Result<Term> {
    let bool_ty = Term::Data(builtin_data(cx, Builtin::Bool)?, Vec::new());
    Ok(Term::let_(
        TAG.into(),
        bool_ty,
        tag.clone(),
        decision.shift(&cx.g(), 1, 0)?,
    ))
}

/// The name of the `let` that carries the `Bool` a plain `if` in a
/// `decreasing` body is on, around the decision its branches' proofs come
/// from ([`tag_plain`]). No source can write it.
pub(crate) const PLAIN: &str = "%plain";

/// Whether a `decreasing` definition's body is being elaborated, where a
/// plain `if` gives its branches its condition
/// (docs/proposals/decreasing-with-hypothesis.md, stage 1).
pub(crate) fn in_decreasing(cx: &Ctx) -> bool {
    cx.e.decl.decreasing.borrow().is_some()
}

/// `decided`, `elimDec [p] [a] decision y n` for a plain `if` in a
/// `decreasing` body, with its decision as `let %plain := plain in
/// decision`: `plain`, the `Bool` the `if` is on when its branches don't use
/// the proof. [`settle_tagged`] makes it the plain `if` if they don't, and
/// otherwise keeps the tag for `f.unfold` (`decreasing.rs`, `plain_view`)
/// while the step's own body is finished, or drops it.
pub(crate) fn tag_plain(cx: &Ctx, decided: &Term, plain: &Term) -> Result<Term> {
    let Term::App(rest, otherwise, i3) = decided else {
        return Ok(decided.clone());
    };
    let Term::App(rest, then, i2) = &**rest else {
        return Ok(decided.clone());
    };
    let Term::App(head, decision, i1) = &**rest else {
        return Ok(decided.clone());
    };
    let bool_ty = Term::Data(builtin_data(cx, Builtin::Bool)?, Vec::new());
    let tagged = Term::let_(
        PLAIN.into(),
        bool_ty,
        plain.clone(),
        decision.shift(&cx.g(), 1, 0)?,
    );
    cx.e.decl.tagged_conjunctions.set(true);
    let rebuilt = Term::App(Rc::clone(head), Rc::new(tagged), *i1);
    let rebuilt = Term::App(Rc::new(rebuilt), Rc::clone(then), *i2);
    Ok(Term::App(Rc::new(rebuilt), Rc::clone(otherwise), *i3))
}

/// An `if` on a conjunction whose branches' helpers weren't lifted when it
/// was written ([`tag_decision`]), in `term`, a finished body: on its `Bool`
/// if neither branch mentions the proof, as `unused_proof_if` makes one whose
/// branches are known not to; otherwise on the plain decision.
pub(crate) fn settle_tagged(e: &crate::Elaborator, term: &Term, keep_plain: bool) -> Result<Term> {
    let g = &e.ev();
    let registry = g.env.registry();
    let (Some(elim), Some(ite)) = (
        registry.def(Builtin::ElimDec),
        registry.def(Builtin::IfThenElse),
    ) else {
        return Ok(term.clone());
    };
    Ok(term.rewrite_up(g, &mut |node| {
        let (head, args) = spine_icit(node);
        if !matches!(head, Term::Def(id) if *id == elim) || args.len() != 5 {
            return Ok(None);
        }
        let Term::Let(name, _, tag, decision, _) = args[2].0.strip_loc() else {
            return Ok(None);
        };
        let plain = &**name == PLAIN;
        if &**name != TAG && !plain {
            return Ok(None);
        }
        let unused = |branch: &Term| {
            matches!(branch.strip_loc(), Term::Lam(_, _, body) if !body.mentions(0))
        };
        if unused(&args[3].0) && unused(&args[4].0) {
            let head = Term::app_icit(Term::Def(ite), args[1].0.clone(), Icit::Implicit);
            let node = Term::app(
                Term::app(Term::app(head, (**tag).clone()), args[3].0.clone()),
                args[4].0.clone(),
            );
            return Ok(Some(node));
        }
        if plain && keep_plain {
            return Ok(None);
        }
        let decision = decision.instantiate_var(g, 0)?;
        let mut out = Term::Def(elim);
        for (i, (arg, icit)) in args.iter().enumerate() {
            let arg = if i == 2 { decision.clone() } else { arg.clone() };
            out = Term::app_icit(out, arg, *icit);
        }
        Ok(Some(out))
    })?)
}

fn spine_icit(t: &Term) -> (&Term, Vec<(Term, Icit)>) {
    let mut args = Vec::new();
    let mut head = t.strip_loc();
    while let Term::App(f, a, icit) = head {
        args.push(((**a).clone(), *icit));
        head = f.strip_loc();
    }
    args.reverse();
    (head, args)
}
