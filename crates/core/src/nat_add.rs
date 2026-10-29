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
//! Looking at the second argument forces it (a glued call is unfolded, a
//! solved metavariable replaced), but does not unfold a call left folded
//! by name. The only such call of type `Nat` is `k * x` with `x` a variable
//! (`native::folds_mul`), which unfolds to `x + (k - 1) * x`, stuck on `x`:
//! never `Zero` or a `Succ`, so nothing is missed.
//!
//! **Why it's sound** (the argument in full, with its assumptions, is in the
//! proposal's §9): R3 and R4 are typed, left-linear, first-order rules on
//! constructor patterns, whose equations are derivable from the definition.
//! Their overlaps with R1 and R2 are the four critical pairs
//! [`critical_pairs`] lists, which all join; a `Nat.add` head is rigid (it
//! is a constant, never the result of substitution), so these are the only
//! overlaps with the rest of the kernel's reduction. Each of R2 and R4
//! replaces a sum by a sum of proper subterms under a `Succ`, and R1 and R3
//! remove the sum, so the four rules terminate. The test
//! `crates/driver/tests/nat_add_rule.rs` checks the critical pairs with both
//! evaluators, natives on and off.
//!
//! **Binding.** The rules are only for the library's own `Nat.add`, by
//! content hash ([`NAT_ADD_HASH`], which covers `Nat` too), and are switched
//! on when the prelude binds `Nat.addSucc`, after checking that it and
//! `Nat.addZero` have the types of R3 and R4 ([`register`]). The theorems
//! are a safety net against binding the rules to the wrong definition, not
//! the soundness argument: the kernel trusts this code to implement R3 and
//! R4, as it trusts the natives (DESIGN.md §13).

use std::rc::Rc;

use num_bigint::BigUint;
use num_traits::Zero;
use stitchwort_syntax::{Diagnostic, Span};

use crate::budget::{self, Limits};
use crate::globals::{Globals, State};
use crate::hash::def_hash;
use crate::native::{Force, view_with};
use crate::registry::Builtin;
use crate::term::{DefId, Icit, Term};
use crate::value::{Elim, Head, Value, conv, eval};

/// The content hash (DESIGN.md §11) of the prelude's `Nat.add`, which
/// covers `Nat`: the definition R3 and R4 were written for.
pub const NAT_ADD_HASH: &str = "f3f3581f05751a4470b1254229a1905626119a6eff6ac5a241a62568d7111af1";

/// `add m n`, already stuck on `m` (not a number, `Zero` or a `Succ`):
/// what R3 and R4 make of it, as `k + rest`, or `None` if it stays stuck
/// (the rules aren't bound to `id`, or `n` isn't a number, `Zero` or a
/// `Succ` either). `n` is forced with `force`, the evaluator's own.
pub fn stuck(
    g: &Globals,
    id: DefId,
    m: &Value,
    n: &Value,
    force: Force,
) -> budget::Result<Option<(BigUint, Value)>> {
    if g.builtins.nat_add_rule != Some(id) {
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
    g: &Globals,
    id: DefId,
    m: &Value,
    n: &Value,
    force: Force,
) -> budget::Result<Option<Value>> {
    Ok(stuck(g, id, m, n, force)?.map(|(k, rest)| crate::native::from_view(k, Some(rest))))
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
pub fn critical_pairs(g: &Globals, id: DefId) -> Option<Vec<CriticalPair>> {
    let nat = g.builtins.nat?;
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
    .with_note(
        "`Nat.add`'s content hash is pinned in crates/core/src/nat_add.rs",
    )
}

/// The content hash of the bound `Nat.add`, if it has one: for the test
/// that fails when the library changes it, which prints the new one.
pub fn add_hash(g: &Globals) -> Option<String> {
    let id = g.registry.def(Builtin::Add)?;
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    def_hash(g, id).ok().flatten().map(|h| h.hex())
}

/// Switches R3 and R4 on for the prelude's `Nat.add`, when it binds
/// `Nat.addSucc` (`add_succ`), which comes after `Nat.addZero`. `Nat.add`
/// must have the pinned content hash, and the two theorems must have the
/// types `(n: Nat) → n + 0 = n` and `(n: Nat) → (m: Nat) → n + Succ m =
/// Succ (n + m)`. The theorems are checked as a safety net against binding
/// the rules to the wrong definition: what makes the rules sound is the
/// argument in the module comment, not their proofs.
pub fn register(g: &mut Globals, add_succ: DefId) -> Result<(), Diagnostic> {
    let span = g.def(add_succ).span;
    let (Some(nat), Some(add), Some(add_zero)) = (
        g.builtins.nat,
        g.registry.def(Builtin::Add),
        g.registry.def(Builtin::NatAddZero),
    ) else {
        return Err(refused(
            span,
            "`Nat`, `Nat.add` or `Nat.addZero` isn't bound",
        ));
    };
    let hash = add_hash(g);
    if hash.as_deref() != Some(NAT_ADD_HASH) {
        return Err(refused(
            g.def(add).span,
            &format!(
                "its content hash, {}, isn't the pinned one",
                hash.as_deref().unwrap_or("none")
            ),
        ));
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
            && conv(g, 0, &eval(g, &[], &expected)?, &def.ty_value)?;
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
    g.builtins.nat_add_rule = Some(add);
    Ok(())
}
