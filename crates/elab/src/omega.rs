//! `omega` (docs/syntax.md, "omega"; docs/proposals/omega.md, milestone 1b):
//! a proof of a linear arithmetic goal about `Nat`s from the facts in scope.
//!
//! ```text
//! omega              -- every arithmetic fact in scope
//! omega [e1, e2]     -- and these, by term
//! ```
//!
//! The proof is an application of a theorem from `Std.Omega`:
//!
//! ```text
//! Std.Omega.prove (MkEnv [atoms] []) [facts] goal cert rfl (Both p1 (… Trivial))
//! Std.Omega.proveEq env facts a b cert1 cert2 rfl rfl proofs      -- for `a = b`
//! ```
//!
//! where the facts and the goal are syntax trees over numbered atoms, the
//! certificate says how to combine them into something false (found by
//! `omega_search.rs`, untrusted), `rfl` is the kernel running
//! `Std.Omega.check` on them, and each `p` is a hypothesis or a bridge lemma
//! applied to one. Nothing here is trusted: a mistake is a type error.
//!
//! **Reading** (§6.4, §6.5). A proposition is read after computing it, the
//! way the checker sees it: `a <= b` is `Nat.leq a b = True`. A fact is one
//! of `a <= b` (which `a < b` computes to, as `Succ a <= b`), `a = b` on
//! `Nat`, or `Not (a <= b)`; other forms reach these through proved bridge
//! lemmas, applied in the emitted term: `Nat.leq a b = False`
//! (`Nat.leqFalse`), `(p && q) = True` (`Bool.andLeft`/`andRight`),
//! `Decidable.toBool d = True`/`False`, which is how `a <= b` inside `&&`
//! comes out (`Decidable.toBoolSound`/`toBoolFalse`), and `And p q`
//! (`And.left`/`right`). Each is read again until it's arithmetic.
//!
//! **Quoting** mirrors the computed value's shape, so the tree's meaning
//! computes to exactly the source: a number is `NLit`, `k + x` (what `Succ`
//! makes) is `NSucc` or `NAdd (NLit k)`, a stuck `a + b` is `NAdd`, `x * k`
//! is `MulRight`, and `k * x`, which has computed to `x + (x + … + 0)`, is
//! `MulLeft k x` (up to [`MUL_LEFT_LIMIT`]). Anything else is an atom: two
//! subterms are one atom if they're the same term, or if a bounded
//! conversion check says so; an inconclusive check keeps them apart. A
//! metavariable inside an atom is part of the atom; one in the goal's
//! arithmetic is an error.
//!
//! **Emitting** (§6.8): every fact is a candidate, but only the facts and
//! atoms the certificate uses are written, renumbered. Before returning, the
//! term is checked here the way the kernel will (the checker computes to
//! `True`, and each part's type matches), so a bug is reported as an
//! internal error naming `omega`.

use std::collections::BTreeSet;
use std::rc::Rc;
use std::sync::LazyLock;

use num_bigint::BigUint;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Elim, Head, apply, conv, force};
use stitchwort_core::{DataId, DefId, Icit, Limits, Term, Value};
use stitchwort_syntax::ast::{self, Expr};
use stitchwort_syntax::{Diagnostic, Span};

use crate::Global;
use crate::check::{Ctx, Result, builtin_ctor, builtin_data, builtin_def, infer, insert};
use crate::omega_search::{self as search, Cert, Failure, Problem, Rat, Row, Source, Step};

/// The largest `k` in `k * x` that is quoted: `k * x` unfolds `k` times
/// whenever its type is compared, so larger ones are refused
/// (docs/proposals/omega.md, "As built (milestone 1a)", costs).
const MUL_LEFT_LIMIT: u32 = 1000;

/// The library names the emitted proofs use: the pre-pass loads their files
/// wherever `omega` is written (`module.rs`, `free_names`).
const LIBRARY: &[&str] = &[
    "Std.Omega.prove",
    "Std.Omega.proveEq",
    "Std.Omega.check",
    "Std.Nat.leqFalse",
    "Std.Nat.leqFalseOfLess",
    "Std.Bool.andLeft",
    "Std.Bool.andRight",
    "Std.Bool.andIntro",
    "Std.Decidable.toBoolSound",
    "Std.Decidable.toBoolFalse",
    "Std.Decidable.toBoolOf",
    "Std.Decidable.toBoolOfNot",
];

pub(crate) static LIBRARY_NAMES: LazyLock<Vec<ast::Name>> = LazyLock::new(|| {
    LIBRARY
        .iter()
        .map(|text| ast::Name {
            text: (*text).to_string(),
            span: Span::NOWHERE,
        })
        .collect()
});

/// `omega` where nothing says what it should prove.
pub(crate) fn no_goal(_cx: &Ctx, expr: &Expr) -> Diagnostic {
    Diagnostic::error("E-OMEGA", "`omega` needs to know what it proves")
        .with_label(expr.span(), "the expected type isn't known here")
        .with_note("give it a type: `(omega: a <= b)`")
}

/// `omega` against the goal `expected`.
pub(crate) fn check_omega(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let Expr::Omega { facts, span } = expr else {
        unreachable!("only called on `omega`")
    };
    let mut extra = Vec::new();
    for (i, fact) in facts.iter().enumerate() {
        let (term, ty) = infer(cx, fact)?;
        let (term, ty) = insert(cx, term, ty)?;
        extra.push(Extra {
            term,
            ty,
            name: format!("listed fact {}", i + 1),
        });
    }
    let lib = Lib::new(cx, *span)?;
    prove_goal(cx, &lib, expected, &extra, *span)
}

/// A fact given by term (`omega [e]`), elaborated in the context of the
/// `omega`.
#[derive(Clone)]
struct Extra {
    term: Term,
    ty: Value,
    name: String,
}

/// The definitions and constructors the proof is made of.
struct Lib {
    prove: DefId,
    prove_eq: DefId,
    check: DefId,
    fact_holds: DefId,
    leq_false: DefId,
    leq_false_of_less: DefId,
    and_left: DefId,
    and_right: DefId,
    and_intro: DefId,
    to_bool_sound: DefId,
    to_bool_false: DefId,
    to_bool_of: DefId,
    to_bool_of_not: DefId,
    and_fst: DefId,
    and_snd: DefId,
    mk_env: (DataId, usize),
    nv: (DataId, usize),
    nlit: (DataId, usize),
    nadd: (DataId, usize),
    nsucc: (DataId, usize),
    mul_left: (DataId, usize),
    mul_right: (DataId, usize),
    fle: (DataId, usize),
    feq: (DataId, usize),
    fnotle: (DataId, usize),
    gle: (DataId, usize),
    gvoid: (DataId, usize),
    mk_row: (DataId, usize),
    input: (DataId, usize),
    neg_goal: (DataId, usize),
    nat_nonneg: (DataId, usize),
    combine: (DataId, usize),
    divide: (DataId, usize),
    close: (DataId, usize),
    then: (DataId, usize),
    split: (DataId, usize),
    // The core's.
    leq: DefId,
    add: DefId,
    mul: DefId,
    ite: DefId,
    to_bool: DefId,
    not: DefId,
    less_than: DefId,
    nat: DataId,
    bool: DataId,
    void: DataId,
    and: DataId,
    unit: DataId,
    tru: (DataId, usize),
    fls: (DataId, usize),
    nil: (DataId, usize),
    cons: (DataId, usize),
    mk_pair: (DataId, usize),
    of_nat: (DataId, usize),
    neg_succ: (DataId, usize),
}

impl Lib {
    fn new(cx: &Ctx, span: Span) -> Result<Lib> {
        let missing = |key: &str| {
            internal(
                span,
                format!("`{key}` isn't available (the library file that declares it isn't loaded)"),
            )
        };
        let def = |key: &str| match cx.e.named(key) {
            Some((Global::Def(id), _)) => Ok(*id),
            _ => Err(missing(key)),
        };
        let ctor = |key: &str| match cx.e.named(key) {
            Some((Global::Ctor(d, i), _)) => Ok((*d, *i)),
            _ => Err(missing(key)),
        };
        Ok(Lib {
            prove: def("Std.Omega.prove")?,
            prove_eq: def("Std.Omega.proveEq")?,
            check: def("Std.Omega.check")?,
            fact_holds: def("Std.Omega.Fact.holds")?,
            leq_false: def("Std.Nat.leqFalse")?,
            leq_false_of_less: def("Std.Nat.leqFalseOfLess")?,
            and_left: def("Std.Bool.andLeft")?,
            and_right: def("Std.Bool.andRight")?,
            and_intro: def("Std.Bool.andIntro")?,
            to_bool_sound: def("Std.Decidable.toBoolSound")?,
            to_bool_false: def("Std.Decidable.toBoolFalse")?,
            to_bool_of: def("Std.Decidable.toBoolOf")?,
            to_bool_of_not: def("Std.Decidable.toBoolOfNot")?,
            and_fst: def("Std.And.left")?,
            and_snd: def("Std.And.right")?,
            mk_env: ctor("Std.Omega.Env.MkEnv")?,
            nv: ctor("Std.Omega.NTerm.NV")?,
            nlit: ctor("Std.Omega.NTerm.NLit")?,
            nadd: ctor("Std.Omega.NTerm.NAdd")?,
            nsucc: ctor("Std.Omega.NTerm.NSucc")?,
            mul_left: ctor("Std.Omega.NTerm.MulLeft")?,
            mul_right: ctor("Std.Omega.NTerm.MulRight")?,
            fle: ctor("Std.Omega.Fact.FLe")?,
            feq: ctor("Std.Omega.Fact.FEq")?,
            fnotle: ctor("Std.Omega.Fact.FNotLe")?,
            gle: ctor("Std.Omega.Goal.GLe")?,
            gvoid: ctor("Std.Omega.Goal.GVoid")?,
            mk_row: ctor("Std.Omega.Row.MkRow")?,
            input: ctor("Std.Omega.Step.Input")?,
            neg_goal: ctor("Std.Omega.Step.NegGoal")?,
            nat_nonneg: ctor("Std.Omega.Step.NatNonneg")?,
            combine: ctor("Std.Omega.Step.Combine")?,
            divide: ctor("Std.Omega.Step.Divide")?,
            close: ctor("Std.Omega.Cert.Close")?,
            then: ctor("Std.Omega.Cert.Then")?,
            split: ctor("Std.Omega.Cert.Split")?,
            leq: builtin_def(cx, Builtin::Leq)?,
            add: builtin_def(cx, Builtin::Add)?,
            mul: builtin_def(cx, Builtin::Mul)?,
            ite: builtin_def(cx, Builtin::IfThenElse)?,
            to_bool: builtin_def(cx, Builtin::ToBool)?,
            not: builtin_def(cx, Builtin::Not)?,
            less_than: builtin_def(cx, Builtin::LessThan)?,
            nat: builtin_data(cx, Builtin::Nat)?,
            bool: builtin_data(cx, Builtin::Bool)?,
            void: builtin_data(cx, Builtin::Void)?,
            and: builtin_data(cx, Builtin::And)?,
            unit: builtin_data(cx, Builtin::Unit)?,
            tru: builtin_ctor(cx, Builtin::True)?,
            fls: builtin_ctor(cx, Builtin::False)?,
            nil: builtin_ctor(cx, Builtin::Nil)?,
            cons: builtin_ctor(cx, Builtin::Cons)?,
            mk_pair: builtin_ctor(cx, Builtin::MkPair)?,
            of_nat: builtin_ctor(cx, Builtin::OfNat)?,
            neg_succ: builtin_ctor(cx, Builtin::NegSucc)?,
        })
    }

    fn ctor(&self, which: (DataId, usize), fields: Vec<Term>) -> Term {
        Term::ctor(which.0, which.1, fields)
    }

    fn list(&self, items: Vec<Term>) -> Term {
        let mut list = self.ctor(self.nil, Vec::new());
        for item in items.into_iter().rev() {
            list = self.ctor(self.cons, vec![item, list]);
        }
        list
    }

    fn int(&self, v: i128) -> Term {
        if v >= 0 {
            self.ctor(self.of_nat, vec![nat_term(v.unsigned_abs())])
        } else {
            self.ctor(self.neg_succ, vec![nat_term((-(v + 1)).unsigned_abs())])
        }
    }
}

fn nat_term(n: impl Into<BigUint>) -> Term {
    Term::Nat(Rc::new(n.into()))
}

fn internal(span: Span, message: String) -> Diagnostic {
    Diagnostic::error("E-OMEGA-INTERNAL", "`omega` made a proof that doesn't check")
        .with_label(span, message)
        .with_note("this is a bug in the compiler's `omega`, not in the program")
}

/// What `omega` was asked to prove, as far as it's linear: `a <= b`, `a = b`
/// on `Nat`, or `Void`.
enum Goal {
    Le(Value, Value),
    Eq(Value, Value),
    Void,
}

/// The data constructor `which` of `value`, if it is one.
fn is_ctor(cx: &Ctx, value: &Value, which: (DataId, usize)) -> Result<bool> {
    Ok(matches!(force(cx.g(), value.clone())?, Value::Ctor(d, c, _) if (d, c) == which))
}

fn is_data(cx: &Ctx, value: &Value, which: DataId) -> Result<bool> {
    Ok(matches!(force(cx.g(), value.clone())?, Value::Data(d, _) if d == which))
}

/// `def` applied to exactly these explicit and implicit arguments.
fn call_args(value: &Value, def: DefId) -> Option<Vec<Value>> {
    match value {
        Value::Neutral(Head::Def(id), spine) if *id == def => spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => Some(v.clone()),
                Elim::J { .. } => None,
            })
            .collect(),
        _ => None,
    }
}

/// A `Bool` reading of `l`: `Nat.leq x y`, `p && q`, or `Decidable.toBool d`
/// (with the proposition it decides).
enum BoolForm {
    Leq(Value, Value),
    And(Value, Value),
    ToBool(Value, Value),
}

fn bool_form(cx: &Ctx, lib: &Lib, l: &Value) -> Result<Option<BoolForm>> {
    let l = force(cx.g(), l.clone())?;
    // A comparison that has computed all the way: `True` is `Nat.leq 0 0`
    // and `False` is `Nat.leq 1 0`, so `h: 3 < 2` (`False = True`) is a fact.
    let number = |k: u32| Value::Nat(Rc::new(BigUint::from(k)));
    if is_ctor(cx, &l, lib.tru)? {
        return Ok(Some(BoolForm::Leq(number(0), number(0))));
    }
    if is_ctor(cx, &l, lib.fls)? {
        return Ok(Some(BoolForm::Leq(number(1), number(0))));
    }
    if let Some([x, y]) = call_args(&l, lib.leq).as_deref() {
        return Ok(Some(BoolForm::Leq(x.clone(), y.clone())));
    }
    if let Some([p, d]) = call_args(&l, lib.to_bool).as_deref() {
        return Ok(Some(BoolForm::ToBool(p.clone(), d.clone())));
    }
    // `p && q` is `Bool.ifThenElse p (u => q) (u => False)`.
    if let Some([_, p, t, e]) = call_args(&l, lib.ite).as_deref() {
        let trivial = cx.eval(&Term::ctor(lib.unit, 0, Vec::new()))?;
        let otherwise = apply(cx.g(), e.clone(), trivial.clone())?;
        if is_ctor(cx, &otherwise, lib.fls)? {
            let q = apply(cx.g(), t.clone(), trivial)?;
            return Ok(Some(BoolForm::And(p.clone(), q)));
        }
    }
    Ok(None)
}

/// `Not p` as a value (`p -> Void`, or the folded `Not p`): `p`.
fn negated(cx: &Ctx, lib: &Lib, value: &Value) -> Result<Option<Value>> {
    let value = force(cx.g(), value.clone())?;
    if let Some([p]) = call_args(&value, lib.not).as_deref() {
        return Ok(Some(p.clone()));
    }
    if let Value::Pi(_, Icit::Explicit, dom, cod) = &value {
        let result = cod.apply(cx.g(), Value::var(cx.level()))?;
        if is_data(cx, &result, lib.void)? {
            return Ok(Some((**dom).clone()));
        }
    }
    Ok(None)
}

/// `which` applied to `args` (terms with their values), and its type.
fn lemma(cx: &Ctx, which: DefId, args: &[(Term, Value)]) -> Result<(Term, Value)> {
    let g = cx.g();
    let mut term = Term::Def(which);
    let mut ty = g.def(which).ty_value.clone();
    for (arg, value) in args {
        let Value::Pi(_, icit, _, cod) = force(g, ty)? else {
            return Err(internal(cx.span, "a bridge lemma has fewer parameters than expected".into()));
        };
        term = Term::app_icit(term, arg.clone(), icit);
        ty = cod.apply(g, value.clone())?;
    }
    Ok((term, ty))
}

/// A value with its term.
fn both(cx: &Ctx, value: &Value) -> Result<(Term, Value)> {
    Ok((cx.quote(value)?, value.clone()))
}

/// Proves `expected`, taking it apart where it's a logical form around
/// arithmetic.
fn prove_goal(cx: &mut Ctx, lib: &Lib, expected: &Value, extra: &[Extra], span: Span) -> Result<Term> {
    let goal = force(cx.g(), expected.clone())?;
    match &goal {
        Value::Eq(ty, l, r) if is_data(cx, ty, lib.nat)? => {
            return linear(cx, lib, Goal::Eq((**l).clone(), (**r).clone()), expected, extra, span);
        }
        Value::Eq(ty, l, r) if is_data(cx, ty, lib.bool)? => {
            let truth = if is_ctor(cx, r, lib.tru)? {
                Some(true)
            } else if is_ctor(cx, r, lib.fls)? {
                Some(false)
            } else {
                None
            };
            match (truth, bool_form(cx, lib, l)?) {
                (Some(true), Some(BoolForm::Leq(x, y))) => {
                    return linear(cx, lib, Goal::Le(x, y), expected, extra, span);
                }
                // `Nat.leq x y = False` from `y < x`.
                (Some(false), Some(BoolForm::Leq(x, y))) => {
                    let less = Term::app(
                        Term::app(Term::Def(lib.less_than), cx.quote(&y)?),
                        cx.quote(&x)?,
                    );
                    let less = cx.eval(&less)?;
                    let proof = prove_goal(cx, lib, &less, extra, span)?;
                    let (y, x) = (both(cx, &y)?, both(cx, &x)?);
                    let proof = (proof, less);
                    return Ok(lemma(cx, lib.leq_false_of_less, &[y, x, proof])?.0);
                }
                (Some(true), Some(BoolForm::ToBool(p, d))) => {
                    let proof = prove_goal(cx, lib, &p, extra, span)?;
                    let args = [both(cx, &p)?, both(cx, &d)?, (proof, p.clone())];
                    return Ok(lemma(cx, lib.to_bool_of, &args)?.0);
                }
                (Some(false), Some(BoolForm::ToBool(p, d))) => {
                    let proof = refute_hypothesis(cx, lib, &p, extra, span)?;
                    let not_p = cx.eval(&Term::app(Term::Def(lib.not), cx.quote(&p)?))?;
                    let args = [both(cx, &p)?, both(cx, &d)?, (proof, not_p)];
                    return Ok(lemma(cx, lib.to_bool_of_not, &args)?.0);
                }
                (Some(true), Some(BoolForm::And(p, q))) => {
                    let true_v = cx.eval(&Term::ctor(lib.tru.0, lib.tru.1, Vec::new()))?;
                    let bool_ty = Rc::new(Value::Data(lib.bool, Vec::new()));
                    let p_true = Value::Eq(bool_ty.clone(), Rc::new(p.clone()), Rc::new(true_v.clone()));
                    let q_true = Value::Eq(bool_ty, Rc::new(q.clone()), Rc::new(true_v));
                    let hp = prove_goal(cx, lib, &p_true, extra, span)?;
                    let hq = prove_goal(cx, lib, &q_true, extra, span)?;
                    let args = [both(cx, &p)?, both(cx, &q)?, (hp, p_true), (hq, q_true)];
                    return Ok(lemma(cx, lib.and_intro, &args)?.0);
                }
                _ => {}
            }
        }
        Value::Data(d, _) if *d == lib.void => {
            return linear(cx, lib, Goal::Void, expected, extra, span);
        }
        Value::Data(d, params) if *d == lib.and && params.len() == 2 => {
            let p = prove_goal(cx, lib, &params[0], extra, span)?;
            let q = prove_goal(cx, lib, &params[1], extra, span)?;
            return Ok(Term::ctor(lib.and, 0, vec![p, q]));
        }
        _ => {}
    }
    if let Some(p) = negated(cx, lib, &goal)? {
        return refute_hypothesis(cx, lib, &p, extra, span);
    }
    Err(unsupported_goal(cx, &goal, span))
}

/// `Not p`, as `h => …` proving `Void` with `h: p` in scope.
fn refute_hypothesis(cx: &mut Ctx, lib: &Lib, p: &Value, extra: &[Extra], span: Span) -> Result<Term> {
    let void = Value::Data(lib.void, Vec::new());
    let mut shifted = Vec::new();
    for e in extra {
        shifted.push(Extra {
            term: e.term.shift(cx.g(), 1, 0)?,
            ty: e.ty.clone(),
            name: e.name.clone(),
        });
    }
    let mark = cx.mark();
    cx.bind_hidden("h".into(), p.clone());
    let body = prove_goal(cx, lib, &void, &shifted, span);
    cx.reset(mark);
    Ok(Term::Lam("h".into(), Icit::Explicit, Rc::new(body?)))
}

fn unsupported_goal(cx: &Ctx, goal: &Value, span: Span) -> Diagnostic {
    Diagnostic::error("E-OMEGA", format!("`omega` can't prove `{}`", cx.show(goal)))
        .with_label(span, "unsupported structure: this goal isn't linear arithmetic on `Nat`")
        .with_note(
            "`omega` proves `a <= b`, `a < b` and `a = b` between `Nat`s built from `+`, numbers and multiplication by a number, `Void`, and `Not`, `&&` and `Nat.leq … = True`/`False` around them",
        )
}

/// A fact the search may use: `a <= b`, `a = b` or `Not (a <= b)`, with a
/// proof of exactly `prop`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Le,
    Eq,
    NotLe,
}

#[derive(Clone)]
struct Fact {
    kind: Kind,
    a: Value,
    b: Value,
    proof: Term,
    prop: Value,
    /// The hypothesis it comes from, for messages.
    origin: String,
}

/// Reads hypotheses into facts.
struct Reader<'l> {
    lib: &'l Lib,
    facts: Vec<Fact>,
    /// Hypotheses about `Nat` that aren't in the fragment, for messages.
    skipped: Vec<String>,
}

impl Reader<'_> {
    fn read(&mut self, cx: &Ctx, proof: Term, prop: &Value, origin: &str, depth: usize) -> Result<()> {
        if depth > 16 {
            return Ok(());
        }
        let lib = self.lib;
        let value = force(cx.g(), prop.clone())?;
        let fact = |kind, a: &Value, b: &Value| Fact {
            kind,
            a: a.clone(),
            b: b.clone(),
            proof: proof.clone(),
            prop: prop.clone(),
            origin: origin.to_string(),
        };
        match &value {
            Value::Eq(ty, a, b) if is_data(cx, ty, lib.nat)? => {
                self.facts.push(fact(Kind::Eq, a, b));
            }
            Value::Eq(ty, l, r) if is_data(cx, ty, lib.bool)? => {
                let truth = if is_ctor(cx, r, lib.tru)? {
                    true
                } else if is_ctor(cx, r, lib.fls)? {
                    false
                } else {
                    return Ok(());
                };
                match (truth, bool_form(cx, lib, l)?) {
                    (true, Some(BoolForm::Leq(x, y))) => self.facts.push(fact(Kind::Le, &x, &y)),
                    (false, Some(BoolForm::Leq(x, y))) => {
                        let args = [both(cx, &x)?, both(cx, &y)?, (proof.clone(), prop.clone())];
                        let (p, ty) = lemma(cx, lib.leq_false, &args)?;
                        self.read(cx, p, &ty, origin, depth + 1)?;
                    }
                    (true, Some(BoolForm::And(p, q))) => {
                        let args = [both(cx, &p)?, both(cx, &q)?, (proof.clone(), prop.clone())];
                        let (left, ty) = lemma(cx, lib.and_left, &args)?;
                        self.read(cx, left, &ty, origin, depth + 1)?;
                        let (right, ty) = lemma(cx, lib.and_right, &args)?;
                        self.read(cx, right, &ty, origin, depth + 1)?;
                    }
                    (true, Some(BoolForm::ToBool(p, d))) => {
                        let args = [both(cx, &p)?, both(cx, &d)?, (proof.clone(), prop.clone())];
                        let (sound, ty) = lemma(cx, lib.to_bool_sound, &args)?;
                        self.read(cx, sound, &ty, origin, depth + 1)?;
                    }
                    (false, Some(BoolForm::ToBool(p, d))) => {
                        let args = [both(cx, &p)?, both(cx, &d)?, (proof.clone(), prop.clone())];
                        let (not_p, ty) = lemma(cx, lib.to_bool_false, &args)?;
                        self.read(cx, not_p, &ty, origin, depth + 1)?;
                    }
                    _ => {}
                }
            }
            Value::Data(d, params) if *d == lib.and && params.len() == 2 => {
                let args = [
                    both(cx, &params[0])?,
                    both(cx, &params[1])?,
                    (proof.clone(), prop.clone()),
                ];
                let (left, ty) = lemma(cx, lib.and_fst, &args)?;
                self.read(cx, left, &ty, origin, depth + 1)?;
                let (right, ty) = lemma(cx, lib.and_snd, &args)?;
                self.read(cx, right, &ty, origin, depth + 1)?;
            }
            _ => {
                let Some(p) = negated(cx, lib, &value)? else {
                    return Ok(());
                };
                let p = force(cx.g(), p)?;
                match &p {
                    Value::Eq(ty, l, r) if is_data(cx, ty, lib.bool)? && is_ctor(cx, r, lib.tru)? => {
                        if let Some(BoolForm::Leq(x, y)) = bool_form(cx, lib, l)? {
                            self.facts.push(fact(Kind::NotLe, &x, &y));
                        }
                    }
                    Value::Eq(ty, _, _) if is_data(cx, ty, lib.nat)? => {
                        self.skipped.push(format!(
                            "`{origin}`: `a != b` facts need case splits (stage 2 of docs/proposals/omega.md)"
                        ));
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }
}

/// A quoted `Nat` term over numbered atoms (`Std.Omega.NTerm`).
#[derive(Clone, Debug)]
enum NTerm {
    V(usize),
    Lit(BigUint),
    Add(Box<NTerm>, Box<NTerm>),
    Succ(Box<NTerm>),
    MulLeft(BigUint, Box<NTerm>),
    MulRight(Box<NTerm>, BigUint),
}

impl NTerm {
    fn atoms(&self, out: &mut BTreeSet<usize>) {
        match self {
            NTerm::V(i) => {
                out.insert(*i);
            }
            NTerm::Lit(_) => {}
            NTerm::Add(a, b) => {
                a.atoms(out);
                b.atoms(out);
            }
            NTerm::Succ(a) | NTerm::MulLeft(_, a) | NTerm::MulRight(a, _) => a.atoms(out),
        }
    }

    fn renumber(&self, map: &[Option<usize>]) -> NTerm {
        match self {
            NTerm::V(i) => NTerm::V(map[*i].expect("a used atom")),
            NTerm::Lit(n) => NTerm::Lit(n.clone()),
            NTerm::Add(a, b) => NTerm::Add(Box::new(a.renumber(map)), Box::new(b.renumber(map))),
            NTerm::Succ(a) => NTerm::Succ(Box::new(a.renumber(map))),
            NTerm::MulLeft(k, a) => NTerm::MulLeft(k.clone(), Box::new(a.renumber(map))),
            NTerm::MulRight(a, k) => NTerm::MulRight(Box::new(a.renumber(map)), k.clone()),
        }
    }

    /// Its linear form: `Std.Omega.NTerm.lin`.
    fn lin(&self, n: usize) -> Option<Row> {
        Some(match self {
            NTerm::V(i) => {
                let mut row = Row::zero(n);
                row.a[*i] = 1;
                row
            }
            NTerm::Lit(k) => Row {
                c: i128::try_from(k).ok()?,
                a: vec![0; n],
            },
            NTerm::Add(a, b) => add(&a.lin(n)?, &b.lin(n)?, 1)?,
            NTerm::Succ(a) => {
                let mut row = a.lin(n)?;
                row.c = row.c.checked_add(1)?;
                row
            }
            NTerm::MulLeft(k, a) | NTerm::MulRight(a, k) => scale(&a.lin(n)?, i128::try_from(k).ok()?)?,
        })
    }

    fn term(&self, lib: &Lib) -> Term {
        match self {
            NTerm::V(i) => lib.ctor(lib.nv, vec![nat_term(*i as u64)]),
            NTerm::Lit(k) => lib.ctor(lib.nlit, vec![nat_term(k.clone())]),
            NTerm::Add(a, b) => lib.ctor(lib.nadd, vec![a.term(lib), b.term(lib)]),
            NTerm::Succ(a) => lib.ctor(lib.nsucc, vec![a.term(lib)]),
            NTerm::MulLeft(k, a) => lib.ctor(lib.mul_left, vec![nat_term(k.clone()), a.term(lib)]),
            NTerm::MulRight(a, k) => lib.ctor(lib.mul_right, vec![a.term(lib), nat_term(k.clone())]),
        }
    }
}

/// `r + k * s`.
fn add(r: &Row, s: &Row, k: i128) -> Option<Row> {
    let mut out = r.clone();
    out.c = out.c.checked_add(k.checked_mul(s.c)?)?;
    for (x, &y) in out.a.iter_mut().zip(&s.a) {
        *x = x.checked_add(k.checked_mul(y)?)?;
    }
    Some(out)
}

fn scale(r: &Row, k: i128) -> Option<Row> {
    add(&Row::zero(r.a.len()), r, k)
}

/// `b - a`: the row `0 <= b - a` that `a <= b` gives (`Std.Omega.leRow`).
fn le_row(a: &NTerm, b: &NTerm, n: usize) -> Option<Row> {
    add(&b.lin(n)?, &a.lin(n)?, -1)
}

/// An atom: a `Nat` subterm `omega` doesn't look inside.
struct Atom {
    value: Value,
    term: Term,
    /// Why it's an atom, if that's because the fragment doesn't cover it.
    unsupported: Option<&'static str>,
}

#[derive(Default)]
struct Quoter {
    atoms: Vec<Atom>,
}

/// Quoting stopped at an unsolved metavariable.
struct Unknown;

impl Quoter {
    fn quote(&mut self, cx: &Ctx, lib: &Lib, value: &Value, span: Span) -> Result<std::result::Result<NTerm, Unknown>> {
        let g = cx.g();
        let value = force(g, value.clone())?;
        let (k, base) = stitchwort_core::native::view(g, &value)?;
        let Some(base) = base else {
            return Ok(Ok(NTerm::Lit(k)));
        };
        if k != BigUint::default() {
            let inner = match self.quote(cx, lib, &base, span)? {
                Ok(t) => t,
                Err(u) => return Ok(Err(u)),
            };
            return Ok(Ok(if k == BigUint::from(1u32) {
                NTerm::Succ(Box::new(inner))
            } else {
                NTerm::Add(Box::new(NTerm::Lit(k)), Box::new(inner))
            }));
        }
        let base = force(g, base)?;
        if let Value::Neutral(Head::Meta(_), _) = base {
            return Ok(Err(Unknown));
        }
        if let Some([a, b]) = call_args(&base, lib.add).as_deref() {
            if let Some((k, t)) = self.mul_left(cx, lib, &base)? {
                if k > MUL_LEFT_LIMIT {
                    return Err(Diagnostic::error(
                        "E-OMEGA",
                        format!("`omega` doesn't take `{k} * …`: the number is too large"),
                    )
                    .with_label(span, format!("the goal or a fact multiplies by {k} on the left"))
                    .with_note(format!(
                        "`k * x` computes to `x + (x + … + 0)` with `k` copies, which is slow to check for large `k`; `omega` takes `k` up to {MUL_LEFT_LIMIT}"
                    ))
                    .with_note("write `x * k` instead, which stays as it is"));
                }
                let inner = match self.quote(cx, lib, &t, span)? {
                    Ok(t) => t,
                    Err(u) => return Ok(Err(u)),
                };
                return Ok(Ok(NTerm::MulLeft(BigUint::from(k), Box::new(inner))));
            }
            let a = match self.quote(cx, lib, a, span)? {
                Ok(t) => t,
                Err(u) => return Ok(Err(u)),
            };
            let b = match self.quote(cx, lib, b, span)? {
                Ok(t) => t,
                Err(u) => return Ok(Err(u)),
            };
            return Ok(Ok(NTerm::Add(Box::new(a), Box::new(b))));
        }
        if let Some([a, b]) = call_args(&base, lib.mul).as_deref() {
            let (k, rest) = stitchwort_core::native::view(g, b)?;
            if rest.is_none() {
                let a = match self.quote(cx, lib, a, span)? {
                    Ok(t) => t,
                    Err(u) => return Ok(Err(u)),
                };
                return Ok(Ok(NTerm::MulRight(Box::new(a), k)));
            }
            return Ok(Ok(NTerm::V(self.atom(cx, base, Some("a product of two unknowns isn't linear"))?)));
        }
        Ok(Ok(NTerm::V(self.atom(cx, base, None)?)))
    }

    /// `k * t` as it computes: `t + (t + … + (t + 0))` with `k >= 2` copies.
    fn mul_left(&self, cx: &Ctx, lib: &Lib, value: &Value) -> Result<Option<(u32, Value)>> {
        let g = cx.g();
        let args = call_args(value, lib.add);
        let Some([t, _]) = args.as_deref() else {
            return Ok(None);
        };
        let t = t.clone();
        let t_term = cx.quote(&t)?;
        let mut count: u32 = 0;
        let mut current = value.clone();
        loop {
            let current_forced = force(g, current)?;
            match call_args(&current_forced, lib.add).as_deref() {
                Some([x, rest]) => {
                    if !crate::matching::same(&cx.quote(x)?, &t_term) {
                        return Ok(None);
                    }
                    count = count.saturating_add(1);
                    current = rest.clone();
                }
                _ => {
                    let (k, base) = stitchwort_core::native::view(g, &current_forced)?;
                    let zero = base.is_none() && k == BigUint::default();
                    return Ok((zero && count >= 2).then_some((count, t)));
                }
            }
        }
    }

    /// The atom `value` is, adding it if it's new.
    fn atom(&mut self, cx: &Ctx, value: Value, unsupported: Option<&'static str>) -> Result<usize> {
        let term = cx.quote(&value)?;
        if let Some(i) = self
            .atoms
            .iter()
            .position(|a| crate::matching::same(&a.term, &term))
        {
            return Ok(i);
        }
        let g = cx.g();
        for (i, a) in self.atoms.iter().enumerate() {
            let _op = g.budget.operation(Limits {
                work: 20_000,
                stack: 128 * 1024,
                size: 10_000,
                frames: 10_000,
            });
            if conv(g, cx.level(), &a.value, &value) == Ok(true) {
                return Ok(i);
            }
        }
        self.atoms.push(Atom {
            value,
            term,
            unsupported,
        });
        Ok(self.atoms.len() - 1)
    }
}

/// A fact with its sides quoted.
struct Quoted {
    fact: Fact,
    a: NTerm,
    b: NTerm,
}

impl Quoted {
    /// Its rows, as `Std.Omega.Fact.rows` makes them.
    fn rows(&self, n: usize) -> Option<Vec<Row>> {
        Some(match self.fact.kind {
            Kind::Le => vec![le_row(&self.a, &self.b, n)?],
            Kind::Eq => vec![le_row(&self.a, &self.b, n)?, le_row(&self.b, &self.a, n)?],
            Kind::NotLe => vec![le_row(&NTerm::Succ(Box::new(self.b.clone())), &self.a, n)?],
        })
    }

    fn term(&self, lib: &Lib, map: &[Option<usize>]) -> Term {
        let which = match self.fact.kind {
            Kind::Le => lib.fle,
            Kind::Eq => lib.feq,
            Kind::NotLe => lib.fnotle,
        };
        lib.ctor(which, vec![self.a.renumber(map).term(lib), self.b.renumber(map).term(lib)])
    }
}

/// The negated goal `Not (a <= b)`'s row (`Std.Omega.Goal.negRow` of `GLe a b`).
fn neg_goal_row(a: &NTerm, b: &NTerm, n: usize) -> Option<Row> {
    le_row(&NTerm::Succ(Box::new(b.clone())), a, n)
}

/// Proves a linear goal (or `Void`) from the facts in scope and `extra`.
fn linear(cx: &mut Ctx, lib: &Lib, goal: Goal, expected: &Value, extra: &[Extra], span: Span) -> Result<Term> {
    let mut reader = Reader {
        lib,
        facts: Vec::new(),
        skipped: Vec::new(),
    };
    for level in 0..cx.level() {
        let name = cx
            .name_of_level(level)
            .map_or_else(|| cx.names[level].to_string(), str::to_string);
        let proof = Term::Var(cx.level() - 1 - level);
        let ty = cx.types[level].clone();
        reader.read(cx, proof, &ty, &name, 0)?;
    }
    for (name, term, ty) in cx.visible_locals()? {
        reader.read(cx, term, &ty, &name, 0)?;
    }
    for e in extra {
        reader.read(cx, e.term.clone(), &e.ty, &e.name, 0)?;
    }
    let mut quoter = Quoter::default();
    let unknown = |what: &str| {
        Diagnostic::error("E-OMEGA", "`omega` needs to know the goal")
            .with_label(span, format!("{what} still has unknowns the compiler hasn't worked out"))
            .with_note("give the missing arguments, or a type annotation, so the goal is known before `omega`")
    };
    let sides = match &goal {
        Goal::Le(a, b) | Goal::Eq(a, b) => {
            let a = quoter.quote(cx, lib, a, span)?.map_err(|_| unknown("the goal"))?;
            let b = quoter.quote(cx, lib, b, span)?.map_err(|_| unknown("the goal"))?;
            Some((a, b))
        }
        Goal::Void => None,
    };
    let mut quoted: Vec<Quoted> = Vec::new();
    for fact in reader.facts {
        let Ok(a) = quoter.quote(cx, lib, &fact.a, span)? else {
            continue;
        };
        let Ok(b) = quoter.quote(cx, lib, &fact.b, span)? else {
            continue;
        };
        quoted.push(Quoted { fact, a, b });
    }
    let n = quoter.atoms.len();
    let too_large = || {
        Diagnostic::error("E-OMEGA", "`omega` can't handle numbers this large")
            .with_label(span, "a number in the goal or a fact is too large for the search")
    };
    // The facts' rows, flattened, and which fact each comes from.
    let mut rows: Vec<(Source, Row)> = Vec::new();
    let mut fact_of_row: Vec<(usize, usize)> = Vec::new();
    for (f, q) in quoted.iter().enumerate() {
        for (offset, row) in q.rows(n).ok_or_else(too_large)?.into_iter().enumerate() {
            rows.push((Source::Input(rows.len()), row));
            fact_of_row.push((f, offset));
        }
    }
    let shown = show_goal(cx, &quoter, &goal, sides.as_ref(), expected);
    // One refutation per goal row: `Not (a <= b)` (and `Not (b <= a)` for `=`).
    let negations: Vec<Option<Row>> = match &sides {
        Some((a, b)) => {
            let mut v = vec![Some(neg_goal_row(a, b, n).ok_or_else(too_large)?)];
            if matches!(goal, Goal::Eq(..)) {
                v.push(Some(neg_goal_row(b, a, n).ok_or_else(too_large)?));
            }
            v
        }
        None => vec![None],
    };
    let mut certs: Vec<Cert> = Vec::new();
    for neg in &negations {
        let mut problem_rows = rows.clone();
        if let Some(neg) = neg {
            problem_rows.push((Source::NegGoal, neg.clone()));
        }
        let problem = Problem {
            n,
            rows: problem_rows,
        };
        match search::refute(&problem, search::LIMITS) {
            Ok(cert) => {
                if !search::replay(&problem, &cert) {
                    return Err(internal(span, "the search's certificate doesn't replay".into()));
                }
                certs.push(cert);
            }
            Err(failure) => {
                return Err(failed(cx, &shown, &quoted, &quoter, &reader.skipped, &failure, span));
            }
        }
    }
    emit(cx, lib, &goal, expected, sides, &quoted, &fact_of_row, &quoter, &certs, span)
}

/// A quoted term as a message shows it: `k * x`, `x + 1`, atoms as the
/// compiler prints them.
fn render(cx: &Ctx, quoter: &Quoter, t: &NTerm) -> String {
    let inner = |t: &NTerm| -> String {
        let s = render(cx, quoter, t);
        if matches!(t, NTerm::Lit(_) | NTerm::V(_)) && !s.contains(' ') {
            s
        } else {
            format!("({s})")
        }
    };
    match t {
        NTerm::V(i) => cx.show(&quoter.atoms[*i].value),
        NTerm::Lit(k) => k.to_string(),
        NTerm::Add(a, b) => {
            let right = if matches!(**b, NTerm::Add(..) | NTerm::Succ(_)) {
                format!("({})", render(cx, quoter, b))
            } else {
                render(cx, quoter, b)
            };
            let left = match &**a {
                NTerm::V(_) => inner(a),
                _ => render(cx, quoter, a),
            };
            format!("{left} + {right}")
        }
        NTerm::Succ(a) => match &**a {
            NTerm::V(_) => format!("{} + 1", inner(a)),
            _ => format!("{} + 1", render(cx, quoter, a)),
        },
        NTerm::MulLeft(k, a) => format!("{k} * {}", inner(a)),
        NTerm::MulRight(a, k) => format!("{} * {k}", inner(a)),
    }
}

/// `a <= b`, or `a' < b` when `a` is `a' + 1`.
fn render_le(cx: &Ctx, quoter: &Quoter, a: &NTerm, b: &NTerm) -> String {
    match a {
        NTerm::Succ(p) => format!("{} < {}", render(cx, quoter, p), render(cx, quoter, b)),
        _ => format!("{} <= {}", render(cx, quoter, a), render(cx, quoter, b)),
    }
}

/// The goal as a message shows it.
fn show_goal(cx: &Ctx, quoter: &Quoter, goal: &Goal, sides: Option<&(NTerm, NTerm)>, expected: &Value) -> String {
    match (goal, sides) {
        (Goal::Le(..), Some((a, b))) => render_le(cx, quoter, a, b),
        (Goal::Eq(..), Some((a, b))) => format!("{} = {}", render(cx, quoter, a), render(cx, quoter, b)),
        _ => cx.show(expected),
    }
}

fn show_fact(cx: &Ctx, quoter: &Quoter, q: &Quoted) -> String {
    match q.fact.kind {
        Kind::Le => render_le(cx, quoter, &q.a, &q.b),
        Kind::Eq => format!("{} = {}", render(cx, quoter, &q.a), render(cx, quoter, &q.b)),
        Kind::NotLe => format!("not ({})", render_le(cx, quoter, &q.a, &q.b)),
    }
}

/// `E-OMEGA` for a goal the search couldn't prove, labelled with what it
/// found (docs/proposals/omega.md §6.8). Nothing here claims the goal is false.
fn failed(
    cx: &Ctx,
    shown: &str,
    quoted: &[Quoted],
    quoter: &Quoter,
    skipped: &[String],
    failure: &Failure,
    span: Span,
) -> Diagnostic {
    let atom_name = |i: usize| cx.show(&quoter.atoms[i].value);
    let model = |values: &[Rat]| -> String {
        values
            .iter()
            .enumerate()
            .map(|(i, v)| format!("{} = {v}", atom_name(i)))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let label = match failure {
        Failure::Integer(_) => "an integer model of the arithmetic abstraction satisfies the facts and the goal's negation",
        Failure::Rational(_) => "a rational model of the relaxation satisfies the facts and the goal's negation",
        Failure::Budget => "budget exhausted: the search stopped before finishing",
    };
    let mut d = Diagnostic::error("E-OMEGA", format!("`omega` can't prove `{shown}`")).with_label(span, label);
    let facts: Vec<String> = quoted
        .iter()
        .map(|q| format!("`{}` ({})", show_fact(cx, quoter, q), q.fact.origin))
        .collect();
    d = d.with_note(if facts.is_empty() {
        "facts: none in scope".to_string()
    } else {
        format!("facts: {}", facts.join(", "))
    });
    if !quoter.atoms.is_empty() {
        let atoms: Vec<String> = (0..quoter.atoms.len()).map(|i| format!("`{}`", atom_name(i))).collect();
        d = d.with_note(format!("atoms: {}", atoms.join(", ")));
    }
    d = match failure {
        Failure::Integer(values) if !values.is_empty() => d.with_note(format!(
            "an integer model of the arithmetic abstraction (it may not be a real counterexample): {}",
            model(values)
        )),
        Failure::Integer(_) => d.with_note("an integer model of the arithmetic abstraction: the facts and the goal's negation hold with no atoms at all"),
        Failure::Rational(values) => d.with_note(format!(
            "a rational model of the relaxation (not a counterexample: whole numbers may still rule it out, but the search's case splits didn't): {}",
            model(values)
        )),
        Failure::Budget => d.with_note(format!(
            "budget exhausted: the search may make {} rows and {} levels of case splits; nothing is claimed about the goal",
            search::LIMITS.rows,
            search::LIMITS.depth
        )),
    };
    for atom in &quoter.atoms {
        if let Some(why) = atom.unsupported {
            d = d.with_note(format!(
                "unsupported structure: `{}` is an atom ({why})",
                cx.show(&atom.value)
            ));
        }
    }
    for s in skipped {
        d = d.with_note(format!("unsupported structure: {s}"));
    }
    d
}

/// The input rows (flattened fact rows) a certificate uses.
fn used_inputs(cert: &Cert, out: &mut BTreeSet<usize>, atoms: &mut BTreeSet<usize>) {
    match cert {
        Cert::Close(_) => {}
        Cert::Then(step, rest) => {
            match step {
                Step::Input(i) => {
                    out.insert(*i);
                }
                Step::NatNonneg(i) => {
                    atoms.insert(*i);
                }
                _ => {}
            }
            used_inputs(rest, out, atoms);
        }
        Cert::Split(l, left, right) => {
            atoms.extend(l.a.iter().enumerate().filter(|(_, x)| **x != 0).map(|(j, _)| j));
            used_inputs(left, out, atoms);
            used_inputs(right, out, atoms);
        }
    }
}

/// The certificate as a term, with inputs and atoms renumbered.
fn cert_term(lib: &Lib, cert: &Cert, inputs: &[Option<usize>], atoms: &[Option<usize>], n: usize) -> Term {
    match cert {
        Cert::Close(r) => lib.ctor(lib.close, vec![nat_term(*r as u64)]),
        Cert::Then(step, rest) => {
            let step = match step {
                Step::Input(i) => lib.ctor(lib.input, vec![nat_term(inputs[*i].expect("a used input") as u64)]),
                Step::NegGoal => lib.ctor(lib.neg_goal, Vec::new()),
                Step::NatNonneg(i) => lib.ctor(
                    lib.nat_nonneg,
                    vec![nat_term(atoms[*i].expect("a used atom") as u64)],
                ),
                Step::Combine(terms) => {
                    let pairs = terms
                        .iter()
                        .map(|&(k, r)| lib.ctor(lib.mk_pair, vec![nat_term(k.unsigned_abs()), nat_term(r as u64)]))
                        .collect();
                    lib.ctor(lib.combine, vec![lib.list(pairs)])
                }
                Step::Divide(r, d) => lib.ctor(lib.divide, vec![nat_term(*r as u64), nat_term(d.unsigned_abs())]),
            };
            lib.ctor(lib.then, vec![step, cert_term(lib, rest, inputs, atoms, n)])
        }
        Cert::Split(l, left, right) => {
            let mut coeffs = vec![0i128; n];
            for (j, &x) in l.a.iter().enumerate() {
                if x != 0 {
                    coeffs[atoms[j].expect("a used atom")] = x;
                }
            }
            while coeffs.last() == Some(&0) {
                coeffs.pop();
            }
            let row = lib.ctor(
                lib.mk_row,
                vec![
                    lib.int(l.c),
                    lib.list(coeffs.into_iter().map(|x| lib.int(x)).collect()),
                    lib.list(Vec::new()),
                ],
            );
            lib.ctor(
                lib.split,
                vec![
                    row,
                    cert_term(lib, left, inputs, atoms, n),
                    cert_term(lib, right, inputs, atoms, n),
                ],
            )
        }
    }
}

/// Writes the proof: only the facts and atoms the certificates use,
/// renumbered; then checks it as the kernel will.
#[allow(clippy::too_many_arguments)]
fn emit(
    cx: &mut Ctx,
    lib: &Lib,
    goal: &Goal,
    expected: &Value,
    sides: Option<(NTerm, NTerm)>,
    quoted: &[Quoted],
    fact_of_row: &[(usize, usize)],
    quoter: &Quoter,
    certs: &[Cert],
    span: Span,
) -> Result<Term> {
    let mut inputs: BTreeSet<usize> = BTreeSet::new();
    let mut atoms: BTreeSet<usize> = BTreeSet::new();
    for cert in certs {
        used_inputs(cert, &mut inputs, &mut atoms);
    }
    let used_facts: BTreeSet<usize> = inputs.iter().map(|&i| fact_of_row[i].0).collect();
    if let Some((a, b)) = &sides {
        a.atoms(&mut atoms);
        b.atoms(&mut atoms);
    }
    for &f in &used_facts {
        quoted[f].a.atoms(&mut atoms);
        quoted[f].b.atoms(&mut atoms);
    }
    let mut atom_map: Vec<Option<usize>> = vec![None; quoter.atoms.len()];
    for (new, &old) in atoms.iter().enumerate() {
        atom_map[old] = Some(new);
    }
    // Each kept fact's first row number, in the kept facts' order.
    let mut first_row: Vec<Option<usize>> = vec![None; quoted.len()];
    let mut next = 0;
    for &f in &used_facts {
        first_row[f] = Some(next);
        next += if quoted[f].fact.kind == Kind::Eq { 2 } else { 1 };
    }
    let input_map: Vec<Option<usize>> = fact_of_row
        .iter()
        .map(|&(f, offset)| first_row[f].map(|r| r + offset))
        .collect();
    let n = atoms.len();
    let env = lib.ctor(
        lib.mk_env,
        vec![
            lib.list(atoms.iter().map(|&i| quoter.atoms[i].term.clone()).collect()),
            lib.list(Vec::new()),
        ],
    );
    let fact_terms: Vec<Term> = used_facts.iter().map(|&f| quoted[f].term(lib, &atom_map)).collect();
    let facts = lib.list(fact_terms.clone());
    let mut proofs = Term::ctor(lib.unit, 0, Vec::new());
    for &f in used_facts.iter().rev() {
        proofs = Term::ctor(lib.and, 0, vec![quoted[f].fact.proof.clone(), proofs]);
    }
    let cert_terms: Vec<Term> = certs
        .iter()
        .map(|c| cert_term(lib, c, &input_map, &atom_map, n))
        .collect();
    let goal_le = |a: &NTerm, b: &NTerm| {
        lib.ctor(lib.gle, vec![a.renumber(&atom_map).term(lib), b.renumber(&atom_map).term(lib)])
    };
    // The goals the certificates refute, for the pre-check.
    let (term, goals) = match (goal, &sides) {
        (Goal::Le(..), Some((a, b))) => {
            let g = goal_le(a, b);
            let term = apps(
                Term::Def(lib.prove),
                vec![env.clone(), facts.clone(), g.clone(), cert_terms[0].clone(), Term::Refl, proofs],
            );
            (term, vec![g])
        }
        (Goal::Eq(..), Some((a, b))) => {
            let term = apps(
                Term::Def(lib.prove_eq),
                vec![
                    env.clone(),
                    facts.clone(),
                    a.renumber(&atom_map).term(lib),
                    b.renumber(&atom_map).term(lib),
                    cert_terms[0].clone(),
                    cert_terms[1].clone(),
                    Term::Refl,
                    Term::Refl,
                    proofs,
                ],
            );
            (term, vec![goal_le(a, b), goal_le(b, a)])
        }
        _ => {
            let g = lib.ctor(lib.gvoid, Vec::new());
            let term = apps(
                Term::Def(lib.prove),
                vec![env.clone(), facts.clone(), g.clone(), cert_terms[0].clone(), Term::Refl, proofs],
            );
            (term, vec![g])
        }
    };
    // The pre-check: the checker accepts, each fact's meaning is its proof's
    // type, and the whole proves the goal.
    for (g, c) in goals.iter().zip(&cert_terms) {
        let ok = cx.eval(&apps(Term::Def(lib.check), vec![facts.clone(), g.clone(), c.clone()]))?;
        if !is_ctor(cx, &ok, lib.tru)? {
            return Err(internal(span, "`Std.Omega.check` refuses the certificate".into()));
        }
    }
    for (&f, t) in used_facts.iter().zip(&fact_terms) {
        let meaning = cx.eval(&apps(Term::Def(lib.fact_holds), vec![env.clone(), t.clone()]))?;
        if !cx.unify(&meaning, &quoted[f].fact.prop)? {
            return Err(internal(
                span,
                format!(
                    "the fact from `{}` is quoted as `{}`, which isn't its type `{}`",
                    quoted[f].fact.origin,
                    cx.show(&meaning),
                    cx.show(&quoted[f].fact.prop)
                ),
            ));
        }
    }
    let proved = match goal {
        Goal::Le(..) | Goal::Void => {
            lemma_result(cx, lib.prove, &[env.clone(), facts.clone(), goals[0].clone()], 3)?
        }
        Goal::Eq(..) => {
            let (a, b) = sides.as_ref().expect("an equation has sides");
            lemma_result(
                cx,
                lib.prove_eq,
                &[env.clone(), facts.clone(), a.renumber(&atom_map).term(lib), b.renumber(&atom_map).term(lib)],
                5,
            )?
        }
    };
    if !cx.unify(&proved, expected)? {
        return Err(internal(
            span,
            format!(
                "the quoted goal means `{}`, not the goal `{}`",
                cx.show(&proved),
                cx.show(expected)
            ),
        ));
    }
    Ok(term)
}

/// `f a1 … an`.
fn apps(f: Term, args: Vec<Term>) -> Term {
    args.into_iter().fold(f, Term::app)
}

/// The type `which` proves once given `args` and then `rest` more
/// arguments its result doesn't depend on.
fn lemma_result(cx: &Ctx, which: DefId, args: &[Term], rest: usize) -> Result<Value> {
    let g = cx.g();
    let mut ty = g.def(which).ty_value.clone();
    for arg in args {
        let Value::Pi(_, _, _, cod) = force(g, ty)? else {
            return Err(internal(cx.span, "`Std.Omega.prove` has fewer parameters than expected".into()));
        };
        ty = cod.apply(g, cx.eval(arg)?)?;
    }
    // The certificates and proofs: the result doesn't depend on them.
    let mut remaining = rest;
    while remaining > 0 {
        let Value::Pi(_, _, _, cod) = force(g, ty)? else {
            return Err(internal(cx.span, "`Std.Omega.prove` has fewer parameters than expected".into()));
        };
        ty = cod.apply(g, Value::var(cx.level()))?;
        remaining -= 1;
    }
    Ok(ty)
}
