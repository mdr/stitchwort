//! `+` computes on both sides (SW-787, D1771; docs/proposals/nat-add-recursion.md).
//!
//! The prelude defines `Nat.add` by recursion on its first argument:
//!
//! ```text
//! R1  add Zero n     → n
//! R2  add (Succ m) n → Succ (add m n)
//! ```
//!
//! The kernel adds two rules for its second argument, the equations of the
//! prelude's theorems `Nat.addZero` and `Nat.addSucc`, read left to right:
//!
//! ```text
//! R3  add m Zero     → m
//! R4  add m (Succ n) → Succ (add m n)
//! ```
//!
//! So `x + 1` is `Succ x`, `x + 0` is `x` and `x + 3` is `3 + x` by
//! computation, while `x + y = y + x` stays a theorem.
//!
//! **How the evaluators use them.** The rewrite relation R1 to R4 overlaps
//! (`Succ m + Succ n` can take R2 or R4). The evaluators are deterministic:
//! they run `add`'s case tree first (R1, R2, or the natives' shortcut for
//! them), and only when that is stuck, because the first argument is not a
//! number or a constructor, do they look at the second ([`stuck`]): a
//! number `k` (or `Zero`) gives `k + m`; `k + n'` with `k > 0` gives
//! `k + add m n'`; anything else leaves the call stuck. That is R4 taken `k`
//! times and then R3 or nothing, in one step, as the natives take R2 `k`
//! times in one step. Both evaluators (the machine, `value.rs`, and the
//! reference, `reference.rs`) call [`stuck`] at the point where `add`'s case
//! tree gets stuck, with natives on or off: the rule is not a native, and
//! switching the natives off doesn't switch it off.
//!
//! Looking at the second argument while evaluating forces it (a glued call
//! is unfolded, a solved metavariable replaced), but does not unfold a call
//! left folded by name (a `decreasing` definition's, or `k * x` with `x` a
//! variable, `native::folds_mul`): evaluation leaves `x + two 0` as written.
//! The comparisons and eliminations that read such a sum unfold those calls
//! with [`reread`], as rule E asks (docs/core.md, "The equality rule").
//!
//! **Why it's sound** (the argument in full, with its assumptions, is in the
//! proposal's §9): R3 and R4 are typed, left-linear, first-order rules on
//! constructor patterns, whose equations are derivable from the definition.
//! Their overlaps with R1 and R2 are the four critical pairs
//! [`critical_pairs`] lists; with the derivable "parallel rule"
//! `Succ m + Succ n → Succ (Succ (m + n))` each joins in one parallel step,
//! the triangle property of the Taming of the Rew (Example 4.3), which
//! gives confluence without termination (proposal §9.4). A `Nat.add` head is
//! rigid (it is a constant, never the result of substitution), so these are
//! the only overlaps with the rest of the kernel's reduction. Each of R2 and
//! R4 replaces a sum by a sum of proper subterms under a `Succ`, and R1 and
//! R3 remove the sum, so the four rules terminate (§9.5). The test
//! `crates/driver/tests/proofs/nat_add_rule.rs` checks the critical pairs, and that
//! the evaluators reach the parallel rule's right side, with both
//! evaluators, natives on and off.
//!
//! **Binding.** The rules are only for the library's own `Nat.add`, by
//! content hash (its pin in [`crate::pins`], which covers `Nat` too), and are switched
//! on when the prelude binds `Nat.addSucc`, after checking that it and
//! `Nat.addZero` have the types of R3 and R4 ([`register`]); for another
//! `Nat.add` they stay off. The theorems
//! are a safety net against binding the rules to the wrong definition, not
//! the soundness argument: the kernel trusts this code to implement R3 and
//! R4, as it trusts the natives (DESIGN.md §13).

use crate::ev::Ev;
use crate::machine::in_kernel_modes;
use std::rc::Rc;

use num_bigint::BigUint;
use num_traits::Zero;
use stitchwort_syntax::{Diagnostic, Span};

use crate::budget;
use crate::globals::{Kernel, State};
use crate::native::{Force, view_with};
use crate::registry::Builtin;
use crate::term::{DefId, Icit, Term};
use crate::value::{Elim, Head, Value, conv, eval};

/// `add m n`, already stuck on `m` (not a number, `Zero` or a `Succ`):
/// what R3 and R4 make of it, as `k + rest`, or `None` if it stays stuck
/// (the rules aren't bound to `id`, or `n` isn't a number, `Zero` or a
/// `Succ` either). `n` is forced with `force`, the evaluator's own.
pub fn stuck(
    g: &Ev,
    id: DefId,
    m: &Value,
    n: &Value,
    force: Force,
) -> budget::Result<Option<(BigUint, Value)>> {
    if g.env.builtins().nat_add_rule != Some(id) {
        return Ok(None);
    }
    let (k, base) = view_with(g, n, force)?;
    Ok(match base {
        // `m + k`: R4 `k` times, then R3.
        None => Some((k, m.clone())),
        // Stuck on both sides.
        Some(_) if k.is_zero() => None,
        // `m + (k + n')`: R4 `k` times.
        Some(base) => Some((k, call(id, m.clone(), base))),
    })
}

/// [`stuck`] as a value, for an evaluator to return.
pub fn stuck_value(
    g: &Ev,
    id: DefId,
    m: &Value,
    n: &Value,
    force: Force,
) -> budget::Result<Option<Value>> {
    Ok(stuck(g, id, m, n, force)?.map(|(k, rest)| crate::native::from_view(k, Some(rest))))
}

/// `value` read by rule E (docs/core.md, "The equality rule"; SW-2251 F6),
/// if it's a stuck `m + n` whose second argument, under its `Succ`s, is a
/// call folded by name, or another such sum: R3 and R4 read the head of
/// `n`, unfolding a folded call with `unfold` (the evaluator's own, `None`
/// when there's nothing to unfold) and reading a stuck sum by this rule in
/// turn (`x + (y + two 0)` is `2 + (x + y)`, SW-2874), and this is what
/// they make of the sum. `None` if `value` isn't such a sum, or nothing
/// unfolds, or the sum stays stuck once `n` is read.
///
/// Evaluation doesn't do this (it reads `n` with `force` only), so goals
/// and read-back keep `x + two 0`, and `rewrite` and `match` find the sum
/// as written; only the comparisons and `case`s that read the sum call it.
///
/// The walk goes to the bottom of a right-nested chain of sums, including
/// one that unfolding builds (`y + f m y` for each `m` below `f 200 y`);
/// the one cut is a folded `k * x`, whose head is `x`'s. It's a loop, not
/// a recursion, and takes a step per sum it goes down to, so a deep chain
/// costs budget and not stack. A comparison reads the chain's sums one
/// after another as it goes down the two sides, so `unread` keeps the sums
/// a walk found nothing to unfold in, and a later walk stops at one: a
/// chain `rep 10000 x` is walked once, not once per level (SW-2875).
/// `unread` must only be kept while `force` and `unfold` would give the
/// same answers, as within one comparison with no metavariable solved.
pub fn reread(
    g: &Ev,
    value: &Value,
    force: Force,
    unfold: impl Fn(&Value) -> budget::Result<Option<Value>>,
    unread: &mut Unread,
) -> budget::Result<Option<Value>> {
    let Some(mut sum) = Sum::of(g, value) else {
        return Ok(None);
    };
    if unread.contains(value) {
        return Ok(None);
    }
    // The sums `sum` is below, outermost first, each with the `Succ`s over
    // the next one's.
    let mut above: Vec<(Sum, BigUint)> = Vec::new();
    let mut walked = vec![value.clone()];
    let mut unfolded_any = false;
    loop {
        let (k, base) = view_with(g, &sum.n, force)?;
        let next = match base {
            None => None,
            // `k * x` left folded unfolds to `x + (k - 1) * x`, and so on `k`
            // levels down, all stuck on the variable `x`: R3 and R4 never
            // find a `Zero` or a `Succ` in it, and `k` can be 2^53.
            Some(Value::Neutral(Head::Def(f), args)) if crate::native::folds_mul(g, f, &args) => {
                None
            }
            Some(base) => match unfold(&base)? {
                Some(next) => {
                    unfolded_any = true;
                    Some(next)
                }
                None => match Sum::of(g, &base) {
                    Some(below) if !unread.contains(&base) => {
                        g.machine.budget.step()?;
                        walked.push(base);
                        above.push((std::mem::replace(&mut sum, below), k));
                        continue;
                    }
                    _ => None,
                },
            },
        };
        if let Some(next) = next {
            sum.n = crate::native::from_view(k, Some(next));
            sum.unfolded = true;
            continue;
        }
        // `sum` is read as far as it goes; hand what it reads to (by R3 and
        // R4 on the `n` it's part of) the sums above, until one of them has
        // more to read.
        let mut read = sum.read(g, force)?;
        loop {
            let Some((mut parent, k)) = above.pop() else {
                // Nothing unfolded: a walk from any sum below the first
                // goes over the same sums from there down, unfolding
                // nothing either, so each reads as nothing.
                if !unfolded_any {
                    unread.extend(walked);
                }
                return Ok(read);
            };
            if let Some(next) = read {
                parent.n = crate::native::from_view(k, Some(next));
                parent.unfolded = true;
                sum = parent;
                break;
            }
            read = parent.read(g, force)?;
        }
    }
}

/// A stuck `m + n` of the `Nat.add` the rules are bound to, as
/// [`reread`] reads it: `n` as read so far, and whether anything in it
/// was unfolded.
struct Sum {
    id: DefId,
    m: Value,
    n: Value,
    unfolded: bool,
}

impl Sum {
    fn of(g: &Ev, value: &Value) -> Option<Sum> {
        let Value::Neutral(Head::Def(id), spine) = value else {
            return None;
        };
        let [Elim::App(m, _), Elim::App(n, _)] = &spine[..] else {
            return None;
        };
        (g.env.builtins().nat_add_rule == Some(*id)).then(|| Sum {
            id: *id,
            m: m.clone(),
            n: n.clone(),
            unfolded: false,
        })
    }

    /// What R3 and R4 make of the sum with `n` as read, if anything in it
    /// was unfolded.
    fn read(&self, g: &Ev, force: Force) -> budget::Result<Option<Value>> {
        if !self.unfolded {
            return Ok(None);
        }
        stuck_value(g, self.id, &self.m, &self.n, force)
    }
}

/// The stuck sums [`reread`] found nothing to unfold in, kept for the rest
/// of a comparison. Filed by the addresses of their spines, and holding the
/// values so an address isn't reused while it's filed. With the shortcuts
/// off (`value::set_shortcuts_disabled`) nothing is filed, so each walk is
/// made in full.
#[derive(Default)]
pub struct Unread {
    spines: crate::collections::HashSet<usize>,
    kept: Vec<Value>,
}

impl Unread {
    /// The key of `value`, a sum [`Sum::of`] accepted: its spine holds the
    /// two arguments, so it has an address of its own.
    fn key(value: &Value) -> usize {
        let Value::Neutral(Head::Def(_), spine) = value else {
            unreachable!("only sums are filed")
        };
        debug_assert_eq!(spine.len(), 2, "only sums are filed");
        spine.addr()
    }

    fn contains(&self, value: &Value) -> bool {
        self.spines.contains(&Self::key(value))
    }

    fn extend(&mut self, values: Vec<Value>) {
        if crate::value::shortcuts_disabled() {
            return;
        }
        for value in values {
            if self.spines.insert(Self::key(&value)) {
                self.kept.push(value);
            }
        }
    }
}

/// The stuck call `add m n`.
pub fn call(id: DefId, m: Value, n: Value) -> Value {
    Value::Neutral(
        Head::Def(id),
        vec![Elim::App(m, Icit::Explicit), Elim::App(n, Icit::Explicit)].into(),
    )
}

/// One critical pair of R1 to R4: a sum two rules both rewrite, and the
/// two results, before either is evaluated further. `m` and `n` are the
/// variables at levels 0 and 1.
pub struct CriticalPair {
    pub name: &'static str,
    pub sum: Term,
    pub left: Term,
    pub right: Term,
}

/// The overlaps of R1 and R2 (on the first argument) with R3 and R4 (on the
/// second), which are every overlap among the four: R1 against R2, and R3
/// against R4, are on different constructors, and no left side has a sum
/// inside it. As terms, for `add` and `Nat`'s constructors, in a context of
/// two variables, `m` (level 0) and `n` (level 1): each sum with what the
/// first rule rewrites it to and what the second does.
pub fn critical_pairs(g: &Ev, id: DefId) -> Option<Vec<CriticalPair>> {
    let nat = g.env.builtins().nat?;
    let zero = || Term::Ctor(nat, 0, Vec::new());
    let succ = |t: Term| Term::ctor(nat, 1, vec![t]);
    let add = |a: Term, b: Term| Term::app(Term::app(Term::Def(id), a), b);
    // Levels 0 and 1 in a context of two: indices 1 and 0.
    let m = || Term::Var(1);
    let n = || Term::Var(0);
    Some(vec![
        CriticalPair {
            name: "Zero + Zero (R1, R3)",
            sum: add(zero(), zero()),
            left: zero(),
            right: zero(),
        },
        CriticalPair {
            name: "Zero + Succ n (R1, R4)",
            sum: add(zero(), succ(n())),
            left: succ(n()),
            right: succ(add(zero(), n())),
        },
        CriticalPair {
            name: "Succ m + Zero (R2, R3)",
            sum: add(succ(m()), zero()),
            left: succ(add(m(), zero())),
            right: succ(m()),
        },
        CriticalPair {
            name: "Succ m + Succ n (R2, R4)",
            sum: add(succ(m()), succ(n())),
            left: succ(add(m(), succ(n()))),
            right: succ(add(succ(m()), n())),
        },
    ])
}

fn refused(span: Span, why: &str) -> Diagnostic {
    Diagnostic::error(
        "E-BUILTIN",
        "the library's `Nat.add` isn't the declaration the compiler's rules for `+` were written for",
    )
    .with_label(span, why.to_string())
}

/// The content hash of the bound `Nat.add`, if it has one: for the test
/// that fails when the library changes it, which prints the new one.
pub fn add_hash(g: &Ev) -> Option<String> {
    crate::pins::def_hex(g, g.env.registry().def(Builtin::Add)?)
}

/// Switches R3 and R4 on for the prelude's `Nat.add`, when it binds
/// `Nat.addSucc` (`add_succ`), which comes after `Nat.addZero`, if
/// `Nat.add` has the pinned content hash (otherwise they stay off). Then the
/// two theorems must have the types `(n: Nat) → n + 0 = n` and `(n: Nat) → (m: Nat) → n + Succ m =
/// Succ (n + m)`, and be theorems that aren't themselves assumptions (a
/// stand-in or a goal's, whatever binds them). The theorems are checked as a
/// safety net against binding the rules to the wrong definition: what makes
/// the rules sound is the argument in the module comment, not their proofs.
pub fn register(g: &mut Kernel, add_succ: DefId) -> Result<(), Diagnostic> {
    in_kernel_modes(g, |g| {
        let span = g.def(add_succ).span;
        let (Some(nat), Some(add), Some(add_zero)) = (
            g.env.builtins().nat,
            g.env.registry().def(Builtin::Add),
            g.env.registry().def(Builtin::NatAddZero),
        ) else {
            return Err(refused(
                span,
                "`Nat`, `Nat.add` or `Nat.addZero` isn't bound",
            ));
        };
        // Another `Nat.add` (or `Nat`): the rules stay off, and `+` is its
        // definition alone. Its native has refused the library already,
        // unless a test let stale pins fall back.
        if !crate::pins::holds(&g.ev(), add, Builtin::Add) {
            return Ok(());
        }
        let nat_ty = || Term::Data(nat, Vec::new());
        let pi =
            |dom: Term, cod: Term| Term::Pi("n".into(), Icit::Explicit, Rc::new(dom), Rc::new(cod));
        let plus = |a: Term, b: Term| Term::app(Term::app(Term::Def(add), a), b);
        let succ = |t: Term| Term::ctor(nat, 1, vec![t]);
        let eq = |a: Term, b: Term| Term::Eq(Some(Rc::new(nat_ty())), Rc::new(a), Rc::new(b));
        // (n: Nat) → n + 0 = n
        let zero_ty = pi(
            nat_ty(),
            eq(
                plus(Term::Var(0), Term::Ctor(nat, 0, Vec::new())),
                Term::Var(0),
            ),
        );
        // (n: Nat) → (m: Nat) → n + Succ m = Succ (n + m)
        let succ_ty = pi(
            nat_ty(),
            pi(
                nat_ty(),
                eq(
                    plus(Term::Var(1), succ(Term::Var(0))),
                    succ(plus(Term::Var(1), Term::Var(0))),
                ),
            ),
        );
        for (id, expected, name) in [
            (add_zero, zero_ty, "Nat.addZero"),
            (add_succ, succ_ty, "Nat.addSucc"),
        ] {
            let def = g.def(id);
            let fits = def.state == State::Final
                && def.theorem
                && def.assumption.is_none()
                && conv(&g.ev(), 0, &eval(&g.ev(), &[], &expected)?, &def.ty_value)?;
            if !fits {
                return Err(Diagnostic::error(
                "E-BUILTIN",
                format!(
                    "the library's `{name}` doesn't have the type the compiler's rules for `+` need"
                ),
            )
            .with_label(def.span, "here"));
            }
        }
        g.env.builtins_mut().nat_add_rule = Some(add);
        Ok(())
    })
}
