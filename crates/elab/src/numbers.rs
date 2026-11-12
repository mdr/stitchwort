//! Numbers: literals at `Nat` and `Int`, and arithmetic and comparisons, which
//! are typed a *group* at a time (docs/proposals/integers.md, "Literals" and
//! "Numeric expressions").
//!
//! A group is a maximal tree of `+ - * / %` and prefix `-`, or a comparison
//! (`=`, `!=`, `==`, `<`, `<=`) with the trees on both sides. Everything else
//! in it is a *leaf*. The group gets one operand type `T`, decided by, in
//! order (D732, docs/proposals/float.md §2.4): the expected type, a decimal
//! or exponent literal (`Float`), the leaves without literals, a prefix `-`
//! (which makes an otherwise undecided group `Int`), the other leaves, and
//! finally a default of `Nat`. The leaves are only *typed* out of order: the
//! term built keeps every leaf in its place, so evaluation is still left to
//! right.

use std::rc::Rc;
use stitchwort_core::Ev;

use num_bigint::BigUint;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, eval, force};
use stitchwort_core::{DataId, DefId, Icit, Sort, Term, Value};
use stitchwort_syntax::ast::{BinOp, Expr, NegForm};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{
    Ctx, PASS, Result, builtin_ctor, builtin_data, builtin_def, check, infer, insert, nat,
};

/// A metavariable that became `Nat` because the ladder's `apply_default`
/// found nothing else said what it was: remembered so that a later
/// mismatch can say why (the "defaulted literal" note), and so that
/// `queue::kept_receiver` can assert no default was applied inside a kept
/// receiver.
pub(crate) struct Defaulted {
    meta: usize,
    span: Span,
    /// The literal, or `None` for a number group defaulted as a whole.
    literal: Option<BigUint>,
}

#[cfg(test)]
impl Defaulted {
    /// `meta` made `Nat` for a literal at `span`.
    pub(crate) fn literal(meta: usize, span: Span, k: u32) -> Self {
        Defaulted {
            meta,
            span,
            literal: Some(k.into()),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Nat,
    Int,
    /// The library's `Float` (std/Float/Float.sw), a double.
    Float,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Kind::Nat => "a `Nat`",
            Kind::Int => "an `Int`",
            Kind::Float => "a `Float`",
        }
    }
}

/// What a type is, as far as numbers are concerned.
enum Class {
    Num(Kind),
    /// An unsolved metavariable: defaulting may still settle it.
    Unknown,
    /// Any other type, including a user's own type named `Int`.
    Other,
}

/// Classifies `ty`, after substituting solved metavariables. Definitions
/// such as `Price = Int` are already unfolded by evaluation.
fn classify(cx: &Ctx, ty: &Value) -> Result<Class> {
    let g = cx.g();
    Ok(match force(&g, ty.clone())? {
        Value::Data(d, params) if params.is_empty() && Some(d) == g.env.builtins().nat => {
            Class::Num(Kind::Nat)
        }
        Value::Data(d, params)
            if params.is_empty() && Some(d) == g.env.registry().data(Builtin::Int) =>
        {
            Class::Num(Kind::Int)
        }
        Value::Data(d, params)
            if params.is_empty() && Some(d) == g.env.registry().loaded_data(Builtin::Float) =>
        {
            Class::Num(Kind::Float)
        }
        Value::Neutral(Head::Meta(_), _) => Class::Unknown,
        _ => Class::Other,
    })
}

fn num_type(cx: &Ctx, kind: Kind) -> Result<Value> {
    let d = match kind {
        Kind::Nat => nat(cx)?,
        Kind::Int => builtin_data(cx, Builtin::Int)?,
        Kind::Float => float_data(cx)?,
    };
    Ok(Value::Data(d, Vec::new().into()))
}

/// The library's `Float`, which a decimal literal loads (its references
/// include `Std.Float`, `module.rs`).
fn float_data(cx: &Ctx) -> Result<DataId> {
    cx.g()
        .env
        .registry()
        .loaded_data(Builtin::Float)
        .ok_or_else(|| {
            cx.error(
                "E-UNKNOWN-NAME",
                "a decimal literal is a `Float`, and the library's `Std.Float` isn't loaded",
                "here",
            )
        })
}

/// One of the library's `Float` definitions.
fn float_def(cx: &Ctx, b: Builtin) -> Result<DefId> {
    cx.g().env.registry().loaded_def(b).ok_or_else(|| {
        cx.error(
            "E-UNKNOWN-NAME",
            format!("this needs the library's `{}`", b.name()),
            "here",
        )
    })
}

// Literals

/// `k` or `-k`, for a numeral `k`: the number, whether it's negative, and
/// where it is.
pub(crate) fn literal(expr: &Expr) -> Option<(&BigUint, bool)> {
    match expr {
        Expr::Num(k, _) => Some((k, false)),
        Expr::Neg(inner, _, _) => match &**inner {
            Expr::Num(k, _) => Some((k, true)),
            _ => None,
        },
        _ => None,
    }
}

/// `d` or `-d`, for a decimal or exponent literal `d`: its text, and
/// whether it's negative.
pub(crate) fn decimal(expr: &Expr) -> Option<(&str, bool)> {
    match expr {
        Expr::Float(d, _) => Some((d, false)),
        Expr::Neg(inner, _, _) => match &**inner {
            Expr::Float(d, _) => Some((d, true)),
            _ => None,
        },
        _ => None,
    }
}

/// Whether `expr` is a literal on its own, `k`, `d`, `-k` or `-d`: it takes
/// its type from where it's used.
pub(crate) fn any_literal(expr: &Expr) -> bool {
    literal(expr).is_some() || decimal(expr).is_some()
}

/// The double a decimal literal stands for: the decimal value, correctly
/// rounded (ties to even), by Rust's `str::parse::<f64>`. Refused when it
/// overflows to an infinity, or when it isn't zero but rounds to zero
/// (docs/proposals/float.md §2.3). `negative` is only for the message: the
/// literal's own text has no sign.
fn decimal_bits(cx: &Ctx, text: &str, negative: bool) -> Result<u64> {
    let value: f64 = text
        .parse()
        .expect("the lexer only makes decimal and exponent literals");
    if value.is_infinite() {
        return Err(cx
            .error(
                "E-FLOAT-LITERAL",
                format!(
                    "`{}{text}` is too large for a `Float`",
                    if negative { "-" } else { "" }
                ),
                "this would be an infinity",
            )
            .with_note(if negative {
                "write `-Float.infinity` if an infinity is meant"
            } else {
                "write `Float.infinity` if an infinity is meant"
            }));
    }
    let mantissa = text.split(['e', 'E']).next().unwrap_or(text);
    if value == 0.0 && mantissa.bytes().any(|b| (b'1'..=b'9').contains(&b)) {
        let zero = if negative { "-0.0" } else { "0.0" };
        return Err(cx
            .error(
                "E-FLOAT-LITERAL",
                format!(
                    "`{}{text}` is too small for a `Float`: it would be `{zero}`",
                    if negative { "-" } else { "" }
                ),
                "this isn't zero, but the nearest double is",
            )
            .with_note(format!("write `{zero}` if zero is meant")));
    }
    Ok(value.to_bits())
}

/// The double a whole literal `k` stands for at `Float`: exactly `k`, or
/// refused if `k` isn't a double (a whole literal reads as exact, so it
/// isn't rounded; docs/proposals/float.md §2.3).
fn whole_bits(cx: &Ctx, k: &BigUint, negative: bool) -> Result<u64> {
    let sign = if negative { "-" } else { "" };
    let value: f64 = k.to_string().parse().expect("digits are a valid `f64`");
    if value.is_infinite() {
        return Err(cx
            .error(
                "E-FLOAT-LITERAL",
                format!("`{sign}{k}` is too large for a `Float`"),
                "this would be an infinity",
            )
            .with_note("write `Float.infinity` if an infinity is meant"));
    }
    // Rust prints a double with a precision exactly, so this is the whole
    // number the double is.
    let show = |x: f64| format!("{x:.0}");
    if show(value) != k.to_string() {
        let (below, above) = if show(value).parse::<BigUint>().is_ok_and(|v| v > *k) {
            (value.next_down(), value)
        } else {
            (value, value.next_up())
        };
        return Err(cx
            .error(
                "E-FLOAT-LITERAL",
                format!("`{sign}{k}` isn't exactly a `Float`"),
                format!(
                    "the nearest are `{sign}{}` and `{sign}{}`",
                    show(below),
                    show(above)
                ),
            )
            .with_note(format!(
                "a whole number reads as exact; write one of those, or `{sign}{k}.0` to ask for rounding"
            )));
    }
    Ok(value.to_bits())
}

/// The term for the double with `bits`, as a literal (`{ bits = k, valid =
/// Eq.refl True }`, the record the kernel's float rules build), negated by
/// `Float.neg` if `negative`: so `-0` at `Float` is `-0.0`, as in JS.
fn float_term(cx: &Ctx, bits: u64, negative: bool) -> Result<Term> {
    let term = stitchwort_core::float::literal_term(float_data(cx)?, bits);
    Ok(if negative {
        Term::app(Term::Def(float_def(cx, Builtin::FloatNeg)?), term)
    } else {
        term
    })
}

/// Checks the decimal literal `text` (or its negation) against `expected`,
/// which must be `Float` (or still unknown, when it becomes `Float`).
pub(crate) fn check_decimal(
    cx: &mut Ctx,
    text: &str,
    negative: bool,
    expected: &Value,
) -> Result<Term> {
    let float = num_type(cx, Kind::Float)?;
    match classify(cx, expected)? {
        Class::Num(Kind::Float) => {}
        Class::Unknown if cx.unify(&float, expected)? => {}
        _ => {
            return Err(cx
                .mismatch(expected, &float)
                .with_note("a decimal or exponent literal is a `Float`"));
        }
    }
    float_term(cx, decimal_bits(cx, text, negative)?, negative)
}

/// A decimal literal with nothing expected: a `Float`.
pub(crate) fn infer_decimal(cx: &mut Ctx, text: &str) -> Result<(Term, Value)> {
    let float = num_type(cx, Kind::Float)?;
    Ok((
        float_term(cx, decimal_bits(cx, text, false)?, false)?,
        float,
    ))
}

/// Checks the literal `k` (or `-k`) against `expected`: a `Nat` is the
/// number, an `Int` is `OfNat k` or `NegSucc (k - 1)` (and `-0` is
/// `OfNat 0`). An unknown type becomes `Nat` (or `Int`, for `-k`).
pub(crate) fn check_literal(
    cx: &mut Ctx,
    k: &BigUint,
    negative: bool,
    expected: &Value,
) -> Result<Term> {
    check_literal_with(cx, k, negative, expected, || Rc::new(k.clone()))
}

/// [`check_literal`], with `shared` giving the number as a `Nat`'s term
/// holds it: a waiting literal ([`Number`]) shares the one it keeps.
fn check_literal_with(
    cx: &mut Ctx,
    k: &BigUint,
    negative: bool,
    expected: &Value,
    shared: impl FnOnce() -> Rc<BigUint>,
) -> Result<Term> {
    match classify(cx, expected)? {
        Class::Num(Kind::Nat) if negative => Err(negative_nat()
            .with_label(cx.span, "this is negative, but a `Nat` is expected here")
            .with_note("use an `Int` for numbers that can be negative")),
        Class::Num(Kind::Nat) => Ok(Term::Nat(shared())),
        Class::Num(Kind::Int) => int_literal(cx, k, negative),
        Class::Num(Kind::Float) => float_term(cx, whole_bits(cx, k, negative)?, negative),
        // `-k` can only be an `Int` or a `Float`, and is an `Int` at once,
        // as a group with a `-` is (step 4 of `group_in`).
        Class::Unknown if negative => {
            let found = num_type(cx, Kind::Int)?;
            if !cx.unify(&found, expected)? {
                return Err(cx.mismatch(expected, &found));
            }
            int_literal(cx, k, true)
        }
        Class::Unknown => queue_number(cx, k, expected),
        Class::Other => {
            if let Some(term) = fin_literal(cx, k, negative, expected)? {
                return Ok(term);
            }
            if let Some(term) = safe_literal(cx, k, negative, expected)? {
                return Ok(term);
            }
            let found = num_type(cx, if negative { Kind::Int } else { Kind::Nat })?;
            let e = cx
                .mismatch(expected, &found)
                .with_note("a numeral can only be the prelude's `Nat` or `Int`");
            // Where the type has `Add` (generic code, a user's `Point`), say
            // what to write instead (docs/proposals/interfaces.md §5.13).
            if let Some(add) = crate::interfaces::library_interface(cx.e, "Std.Add")
                && crate::interfaces::findable(
                    cx,
                    &Value::Data(add, vec![expected.clone()].into()),
                )?
                .is_none()
            {
                return Err(
                    e.with_note("for another type's zero or one, write `Add.zero` or `Mul.one`")
                );
            }
            Err(e)
        }
    }
}

/// K4 (docs/proposals/postponement.md §5.4): the literal `k` checked against
/// `expected`, whose head is an unknown, waits for it instead of making it
/// `Nat` at once. It keeps only its syntax, the number. Resumed, it is
/// [`check_literal`] at the type now known (a `Nat`, an `Int`, a `Float`, a
/// `Fin n`, a `SafeNat` or `SafeInt`, or the error any other type gives);
/// its default, in the ladder after the field-name rule, is `Nat` (D2013),
/// noted as the literal that made the type `Nat` ([`explain_default`]).
fn queue_number(cx: &mut Ctx, k: &BigUint, expected: &Value) -> Result<Term> {
    let number = Number {
        k: Rc::new(k.clone()),
        expected: expected.clone(),
        span: cx.span,
    };
    // Its error is made only if it is reported ([`Number::stuck_error`]): a
    // list of thousands of numbers queues thousands of these (SW-1048).
    crate::queue::queue_without_error(cx, Rc::new(number), expected.clone(), expected.clone())
}

/// A number literal waiting for its type ([`queue_number`]). Messages show
/// its placeholder as the number (D2091), from [`Check::literal`].
///
/// [`Check::literal`]: crate::queue::Check::literal
struct Number {
    /// Shared by what holds the number: the unifier's table of waiting
    /// literals, the printer's, and the term it is filled with at `Nat`.
    k: Rc<BigUint>,
    expected: Value,
    span: Span,
}

impl crate::queue::Check for Number {
    fn literal(&self) -> Option<Rc<BigUint>> {
        Some(self.k.clone())
    }

    fn stuck_error(&self, _e: &crate::Elaborator, _blocker: Option<usize>) -> Option<Diagnostic> {
        Some(
            Diagnostic::error(
                "E-CANNOT-INFER",
                format!("can't tell what type the number `{}` is", self.k),
            )
            .with_label(self.span, "nothing here says what type it should have"),
        )
    }

    fn resume(&self, cx: &mut Ctx) -> Result<crate::queue::Resumed> {
        let term = check_literal_with(cx, &self.k, false, &self.expected, || self.k.clone())?;
        Ok(crate::queue::Resumed::Done(term))
    }

    fn default_priority(&self) -> Option<crate::queue::Priority> {
        Some(crate::queue::Priority::Nat)
    }

    fn apply_default(&self, cx: &mut Ctx) -> Result<bool> {
        debug_assert!(
            cx.e.attempt.queue.settling(),
            "a number literal was defaulted before the end (invariant 7)"
        );
        let meta = head_meta(cx, &self.expected)?;
        if !cx.unify(&num_type(cx, Kind::Nat)?, &self.expected)? {
            return Ok(false);
        }
        if let Some(meta) = meta {
            cx.e.attempt.defaulted.borrow_mut().push(Defaulted {
                meta,
                span: self.span,
                literal: Some((*self.k).clone()),
            });
        }
        Ok(true)
    }
}

/// The bound `n` of `ty` if `ty` is the library's `Fin n`: `Some(Some(n))`
/// when n computes to a number, `Some(None)` when it doesn't (a variable, an
/// unsolved metavariable), and `None` for any other type.
pub(crate) fn fin_bound(g: &Ev, ty: &Value) -> Result<Option<Option<BigUint>>> {
    let Some(fin) = g.env.registry().loaded_data(Builtin::Fin) else {
        return Ok(None);
    };
    match force(g, ty.clone())? {
        Value::Data(d, params) if d == fin && params.len() == 1 => {
            Ok(Some(stitchwort_core::native::as_nat(g, &params[0])?))
        }
        _ => Ok(None),
    }
}

/// The numeral `k` (or `-k`) checked against `expected` if that's `Fin n`
/// (docs/proposals/fin-literals.md): `Fin.ofNatLt n k rfl` when n is a
/// known number above k, where the kernel confirms `k < n` by computing it.
/// `None` if `expected` isn't a `Fin`.
fn fin_literal(cx: &Ctx, k: &BigUint, negative: bool, expected: &Value) -> Result<Option<Term>> {
    let Some(bound) = fin_bound(&cx.g(), expected)? else {
        return Ok(None);
    };
    let shown = cx.show(expected);
    if negative {
        return Err(cx
            .error(
                "E-FIN-LITERAL",
                format!("a `{shown}` can't be negative"),
                format!("this is negative, but a `{shown}` is expected here"),
            )
            .with_note("a `Fin n` is a number from 0 up to n - 1"));
    }
    let Some(n) = bound else {
        let unsolved = match force(&cx.g(), expected.clone())? {
            Value::Data(_, params) => matches!(
                force(&cx.g(), params[0].clone())?,
                Value::Neutral(Head::Meta(_), _)
            ),
            _ => false,
        };
        let e = cx.error(
            "E-FIN-LITERAL",
            format!("`{k}` can't be checked to be below the bound of `{shown}`"),
            "a numeral can be a `Fin n` only where n is a known number",
        );
        return Err(if unsolved {
            e.with_note(format!(
                "nothing here says what n is yet: write it, as in `({k}: Fin 10)`"
            ))
        } else {
            e.with_note(format!(
                "build it with `Fin.ofNatLt`, giving a proof that `{k}` is below the bound"
            ))
        });
    };
    if *k >= n {
        return Err(cx
            .error(
                "E-FIN-LITERAL",
                format!("{k} isn't below {n}, so it can't be a `{shown}`"),
                if n.bits() == 0 {
                    format!("`{shown}` has no values")
                } else {
                    format!("a `{shown}` is a number from 0 to {}", n.clone() - 1u32)
                },
            )
            .with_note(format!("a `Fin {n}` is a number below {n}")));
    }
    let of_nat_lt = cx
        .g()
        .env
        .registry()
        .loaded_def(Builtin::FinOfNatLt)
        .ok_or_else(|| {
            cx.error(
                "E-UNKNOWN-NAME",
                "a numeral as a `Fin` needs the library's `Fin.ofNatLt`",
                "here",
            )
        })?;
    let call = Term::app(Term::Def(of_nat_lt), Term::Nat(Rc::new(n)));
    let call = Term::app(call, Term::Nat(Rc::new(k.clone())));
    Ok(Some(Term::app(call, Term::Refl)))
}

/// The bound of the library's `SafeNat` and `SafeInt` (std/Int/Safe.sw):
/// 2^53 - 1, JS's `Number.MAX_SAFE_INTEGER`.
const SAFE_BOUND: u64 = 9_007_199_254_740_991;

/// The numeral `k` (or `-k`) checked against `expected` if that's the
/// library's `SafeNat` or `SafeInt` (SW-354): the record `{ value = k, fits =
/// rfl }`, with `k` as a `Nat` or an `Int`, where the kernel confirms the
/// bound by computing it, as for a `Fin` literal. `None` for any other type.
fn safe_literal(cx: &Ctx, k: &BigUint, negative: bool, expected: &Value) -> Result<Option<Term>> {
    let g = cx.g();
    let Value::Data(d, params) = force(&g, expected.clone())? else {
        return Ok(None);
    };
    if !params.is_empty() {
        return Ok(None);
    }
    let (name, int) = if Some(d) == g.env.registry().loaded_data(Builtin::SafeNat) {
        ("SafeNat", false)
    } else if Some(d) == g.env.registry().loaded_data(Builtin::SafeInt) {
        ("SafeInt", true)
    } else {
        return Ok(None);
    };
    if negative && !int {
        return Err(cx
            .error(
                "E-SAFE-LITERAL",
                "a `SafeNat` can't be negative",
                "this is negative, but a `SafeNat` is expected here",
            )
            .with_note("use a `SafeInt` for numbers that can be negative"));
    }
    if *k > BigUint::from(SAFE_BOUND) {
        let sign = if negative { "-" } else { "" };
        let range = if int {
            format!("a `SafeInt` is a whole number from -{SAFE_BOUND} to {SAFE_BOUND}")
        } else {
            format!("a `SafeNat` is a whole number from 0 to {SAFE_BOUND}")
        };
        return Err(cx
            .error(
                "E-SAFE-LITERAL",
                format!("`{sign}{k}` is out of range for a `{name}`"),
                range,
            )
            .with_note(format!(
                "{SAFE_BOUND} is 2^53 - 1, the largest whole number a JS `number` holds \
                 exactly; use {} for larger numbers",
                if int { "an `Int`" } else { "a `Nat`" }
            )));
    }
    let value = if int {
        int_literal(cx, k, negative)?
    } else {
        Term::Nat(Rc::new(k.clone()))
    };
    Ok(Some(Term::ctor(d, 0, vec![value, Term::Refl])))
}

fn int_literal(cx: &Ctx, k: &BigUint, negative: bool) -> Result<Term> {
    let (int, of_nat) = builtin_ctor(cx, Builtin::OfNat)?;
    let (_, neg_succ) = builtin_ctor(cx, Builtin::NegSucc)?;
    let zero = BigUint::default();
    Ok(if negative && *k != zero {
        let pred = k - 1u32;
        Term::ctor(int, neg_succ, vec![Term::Nat(Rc::new(pred))])
    } else {
        Term::ctor(int, of_nat, vec![Term::Nat(Rc::new(k.clone()))])
    })
}

fn negative_nat() -> Diagnostic {
    Diagnostic::error("E-TYPE-MISMATCH", "a `Nat` can't be negative")
}

/// Adds the "defaulted literal" explanation to `d` if one of `types` is a
/// metavariable that a literal made `Nat`.
pub(crate) fn explain_default(cx: &Ctx, d: Diagnostic, types: &[&Value]) -> Diagnostic {
    if d.code != "E-TYPE-MISMATCH" || d.notes.iter().any(|n| n.contains("because of the literal")) {
        return d;
    }
    let defaulted = cx.e.attempt.defaulted.borrow();
    for ty in types {
        let Value::Neutral(Head::Meta(m), _) = ty else {
            continue;
        };
        if let Some((found, k)) = (defaulted.iter())
            .find_map(|x| Some((x, x.literal.as_ref()?)).filter(|(x, _)| x.meta == *m))
        {
            return d
                .with_label(found.span, "this literal made it a `Nat`")
                .with_note(format!(
                    "this type became `Nat` because of the literal `{k}`, checked before \
                     anything said otherwise; write `({k}: Int)` if an `Int` was meant"
                ));
        }
    }
    d
}

// Groups

/// The part of a group above its leaves.
enum Node {
    Leaf(usize),
    Op(BinOp, Box<Node>, Box<Node>, Span),
    Neg(Box<Node>, Span),
}

struct Leaf<'a> {
    expr: &'a Expr,
    /// The operator it's an operand of, for error messages.
    op: &'static str,
    /// A literal `k`, `-k`, `d` or `-d` on its own: it waits until `T` is
    /// decided.
    bare: bool,
    /// An operand of `=` that is a computation: inferred without running it
    /// (D1140 (a), docs/proposals/effect-polymorphism.md).
    passed: bool,
    state: State,
}

#[derive(Clone)]
enum State {
    Waiting,
    Inferred(Term, Value),
    /// Couldn't be inferred: checked against `T` at the end.
    Failed(Diagnostic),
    Done(Term),
}

#[derive(Default)]
struct Group<'a> {
    leaves: Vec<Leaf<'a>>,
    /// The first prefix `-`, including a negative literal's.
    minus: Option<Span>,
    /// The first decimal or exponent literal on its own, which makes it a
    /// `Float` group.
    decimal: Option<usize>,
    /// Whether it has an arithmetic operator.
    arith: bool,
    /// Whether it's `<` or `<=`.
    ordering: bool,
    /// The first operator in it that only `Nat` and `Int` have (`-`, `/`,
    /// `%`, prefix `-`): without one, it may be on any type with the
    /// instances its operators need (docs/proposals/interfaces.md §5.13).
    numeric_only: Option<&'static str>,
    /// Whether it has `+`, and `*`.
    adds: bool,
    muls: bool,
    /// An equation read again with its comparison sides as `Bool`s
    /// ([`group_tried`]): a side that is `<` or `<=` doesn't decide the
    /// group's type, and is checked against the type the others decide.
    bool_comparisons: bool,
}

/// What decided the group's type, for error messages.
#[derive(Clone, Copy)]
enum Decider {
    Expected,
    Leaf(usize),
    Minus(Span),
    Default,
}

pub(crate) fn is_arith(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
    )
}

fn is_comparison(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::EqEq | BinOp::Lt | BinOp::Le
    )
}

pub(crate) fn op_text(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Eq => "=",
        BinOp::Ne => "!=",
        BinOp::EqEq => "==",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Append => "++",
        BinOp::Range => "..<",
        BinOp::RangeThrough => "..=",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::In(_) => "in",
    }
}

impl<'a> Group<'a> {
    fn tree(&mut self, cx: &Ctx, expr: &'a Expr, op: &'static str) -> Result<Node> {
        cx.g().machine.budget.nesting(PASS)?;
        match expr {
            Expr::Binary(o, a, b) if is_arith(*o) => {
                self.arith = true;
                match o {
                    BinOp::Add => self.adds = true,
                    BinOp::Mul => self.muls = true,
                    _ => {
                        self.numeric_only.get_or_insert(op_text(*o));
                    }
                }
                let a = self.tree(cx, a, op_text(*o))?;
                let b = self.tree(cx, b, op_text(*o))?;
                Ok(Node::Op(*o, Box::new(a), Box::new(b), expr.span()))
            }
            Expr::Neg(inner, span, _) => {
                self.minus.get_or_insert(*span);
                self.numeric_only.get_or_insert("-");
                if any_literal(expr) {
                    return Ok(self.leaf(expr, op));
                }
                Ok(Node::Neg(Box::new(self.tree(cx, inner, "-")?), *span))
            }
            _ => Ok(self.leaf(expr, op)),
        }
    }

    fn leaf(&mut self, expr: &'a Expr, op: &'static str) -> Node {
        if decimal(expr).is_some() && self.decimal.is_none() {
            self.decimal = Some(self.leaves.len());
        }
        self.leaves.push(Leaf {
            expr,
            op,
            bare: any_literal(expr),
            passed: false,
            state: State::Waiting,
        });
        Node::Leaf(self.leaves.len() - 1)
    }

    /// Whether the group may be on a type other than `Nat` and `Int`: it has
    /// only `+`, `*`, `<` and `<=` (or is an equation), and the library's
    /// `Add`, `Mul` and `Ord` are declared (after the prelude's bootstrap
    /// phase, D187).
    fn generic(&self, cx: &Ctx) -> bool {
        self.numeric_only.is_none()
            && ["Std.Add", "Std.Mul", "Std.Ord"]
                .iter()
                .all(|path| crate::interfaces::library_interface(cx.e, path).is_some())
    }

    /// Why the group can't be on `t`, a type other than `Nat` and `Int`: an
    /// operator only those have (an empty note), or an instance its
    /// operators need that `t` doesn't have (a note saying so). `None` if it
    /// can.
    fn unsupported(&self, cx: &mut Ctx, t: &Value) -> Result<Option<String>> {
        if !self.generic(cx) {
            return Ok(Some(String::new()));
        }
        let needed = [
            (self.adds, "Add", "+", "add"),
            (self.muls, "Mul", "*", "mul"),
            (self.ordering, "Ord", "<", "lessThan"),
        ];
        for (used, name, op, field) in needed {
            let Some(interface) =
                crate::interfaces::library_interface(cx.e, &format!("Std.{name}"))
            else {
                continue;
            };
            if used
                && crate::interfaces::findable(cx, &Value::Data(interface, vec![t.clone()].into()))?
                    .is_some()
            {
                return Ok(Some(format!(
                    "on other types `{op}` is `{name}.{field}`, and there's no `{name}` instance for `{}` here",
                    cx.show(t)
                )));
            }
        }
        Ok(None)
    }

    /// Whether leaf `i` waits for the others to decide the group's type: a
    /// comparison side read as a `Bool` ([`Group::bool_comparisons`]).
    fn waits(&self, i: usize) -> bool {
        self.bool_comparisons && is_order(self.leaves[i].expr)
    }

    /// Whether the group has numeric syntax, so that it defaults to `Nat`.
    fn numeric(&self) -> bool {
        self.arith || self.ordering || self.minus.is_some() || self.leaves.iter().any(|l| l.bare)
    }
}

/// Rebuilds the group `expr` with each leaf replaced by `f` of it, in source
/// order (for computation mode, which runs effectful leaves first).
pub(crate) fn map_leaves(
    cx: &mut Ctx,
    expr: &Expr,
    f: &mut dyn FnMut(&mut Ctx, &Expr) -> Result<Expr>,
) -> Result<Expr> {
    fn tree(
        cx: &mut Ctx,
        expr: &Expr,
        f: &mut dyn FnMut(&mut Ctx, &Expr) -> Result<Expr>,
    ) -> Result<Expr> {
        cx.g().machine.budget.nesting(PASS)?;
        match expr {
            Expr::Binary(op, a, b) if is_arith(*op) => {
                let a = tree(cx, a, f)?;
                let b = tree(cx, b, f)?;
                Ok(Expr::Binary(*op, Box::new(a), Box::new(b)))
            }
            Expr::Neg(inner, span, form) if !any_literal(expr) => {
                Ok(Expr::Neg(Box::new(tree(cx, inner, f)?), *span, *form))
            }
            _ => f(cx, expr),
        }
    }
    match expr {
        Expr::Binary(op, a, b) if is_comparison(*op) => {
            let a = tree(cx, a, f)?;
            let b = tree(cx, b, f)?;
            Ok(Expr::Binary(*op, Box::new(a), Box::new(b)))
        }
        _ => tree(cx, expr, f),
    }
}

/// Elaborates the group `expr` (arithmetic, a comparison, or a prefix `-`
/// that isn't part of a negative literal), against `expected` if
/// it's an arithmetic tree and that's given: its term and type.
pub(crate) fn group(cx: &mut Ctx, expr: &Expr, expected: Option<&Value>) -> Result<(Term, Value)> {
    // An equation with a comparison as a side: the comparison is a
    // proposition, so the equation is between propositions. If that fails
    // (the other side is a `Bool`, as in `(m < k) = (m < k && b)`), with
    // everything it did undone, the comparison sides are read as `Bool`s,
    // as if written `((m < k): Bool)` (SW-944). If that fails too, the
    // first error is reported.
    if let Expr::Binary(BinOp::Eq | BinOp::Ne, a, b) = expr
        && (is_order(a) || is_order(b))
        && cx.e.decl.late_literals.get() == 0
    {
        let snapshot = crate::undo::Snapshot::take(cx);
        let first = match group_literals(cx, expr, expected, false) {
            Err(e) if !crate::undo::fatal(&e) && !snapshot.drafted_since(cx) => e,
            done => return done,
        };
        snapshot.restore(cx);
        let again = crate::undo::Snapshot::take(cx);
        return match group_literals(cx, expr, expected, true) {
            Err(e) if !crate::undo::fatal(&e) => {
                again.restore(cx);
                Err(first)
            }
            done => done,
        };
    }
    group_literals(cx, expr, expected, false)
}

/// Whether `expr` is `a < b` or `a <= b` (`>` and `>=` are written with
/// them).
fn is_order(expr: &Expr) -> bool {
    matches!(expr, Expr::Binary(BinOp::Lt | BinOp::Le, ..))
}

fn group_literals(
    cx: &mut Ctx,
    expr: &Expr,
    expected: Option<&Value>,
    bool_comparisons: bool,
) -> Result<(Term, Value)> {
    let group_in = |cx: &mut Ctx, expr: &Expr, expected: Option<&Value>| {
        group_with(cx, expr, expected, bool_comparisons)
    };
    if !matches!(expr, Expr::Neg(_, _, NegForm::Argument)) {
        return group_in(cx, expr, expected);
    }
    crate::queue::framed(
        cx,
        |cx| group_in(cx, expr, expected),
        |_| NegatedFrame { expr: expr.clone() },
    )
}

/// An unbracketed negative argument, as an error frame (D2091):
/// [`function_operand_note`], also for a check inside it that waits and
/// fails later.
struct NegatedFrame {
    expr: Expr,
}

impl crate::queue::ErrorFrame for NegatedFrame {
    fn map(&self, cx: &mut Ctx, e: Diagnostic) -> Diagnostic {
        function_operand_note(cx, &self.expr, e)
    }
}

/// `f -g x` is `f (-g) x`: when `g` is a function, the mismatch on it is
/// explained (docs/proposals/negative-arguments.md §4.2, D1467).
#[inline(never)]
fn function_operand_note(cx: &mut Ctx, expr: &Expr, e: Diagnostic) -> Diagnostic {
    let Expr::Neg(inner, _, NegForm::Argument) = expr else {
        return e;
    };
    if e.code != "E-TYPE-MISMATCH" || any_literal(inner) {
        return e;
    }
    let name = match &**inner {
        Expr::Var(name) => name.text.clone(),
        Expr::Field(..) => "this".into(),
        _ => return e,
    };
    let is_function = matches!(
        attempt(cx, |cx| infer(cx, inner)),
        Ok(Some((_, ty))) if matches!(force(&cx.g(), ty.clone()), Ok(Value::Pi(..)))
    );
    if !is_function {
        return e;
    }
    e.with_note(format!(
        "`-{name}` negates `{name}` alone here, not a call of it (a `-` right before an argument \
         negates just that argument); to negate a call such as `g x`, write `(-(g x))`"
    ))
}

/// The two sides of a comparison, or the one tree of an arithmetic group.
type Sides = (Node, Option<Node>);

/// The group `expr` taken apart into its leaves, none elaborated yet: the
/// group, its comparison if it is one, and its sides. With
/// `bool_comparisons`, its comparison sides are read as `Bool`s (SW-944).
fn prepare<'a>(
    cx: &mut Ctx,
    expr: &'a Expr,
    bool_comparisons: bool,
) -> Result<(Group<'a>, Option<BinOp>, Sides)> {
    let mut g = Group {
        bool_comparisons,
        ..Group::default()
    };
    let (top, sides) = match expr {
        Expr::Binary(op, a, b) if is_comparison(*op) => {
            g.ordering = matches!(op, BinOp::Lt | BinOp::Le);
            let a = g.tree(cx, a, op_text(*op))?;
            let b = g.tree(cx, b, op_text(*op))?;
            if *op == BinOp::Eq {
                for side in [&a, &b] {
                    if let Node::Leaf(i) = side
                        && crate::effects::passed_operand(cx, g.leaves[*i].expr)?
                    {
                        g.leaves[*i].passed = true;
                    }
                }
            }
            (Some(*op), (a, Some(b)))
        }
        _ => (None, (g.tree(cx, expr, "")?, None)),
    };
    Ok((g, top, sides))
}

/// What the group is called in messages.
fn what(top: Option<BinOp>) -> &'static str {
    if top.is_some() {
        "comparison"
    } else {
        "arithmetic"
    }
}

fn group_with(
    cx: &mut Ctx,
    expr: &Expr,
    expected: Option<&Value>,
    bool_comparisons: bool,
) -> Result<(Term, Value)> {
    let (mut g, top, sides) = prepare(cx, expr, bool_comparisons)?;
    // Comparisons constrain their operands, not their result.
    let expected = if top.is_some() { None } else { expected };
    let what = what(top);
    // An equation with no arithmetic in it may be on any type.
    let equality =
        matches!(top, Some(BinOp::Eq | BinOp::Ne | BinOp::EqEq)) && !g.arith && g.minus.is_none();
    let mut decided: Option<(Value, Decider)> = None;

    // 1. The expected type.
    if let Some(e) = expected {
        match classify(cx, e)? {
            Class::Num(kind) => decided = Some((num_type(cx, kind)?, Decider::Expected)),
            Class::Unknown => {}
            Class::Other => match g.unsupported(cx, e)? {
                None => decided = Some((e.clone(), Decider::Expected)),
                Some(note) => {
                    let op = match &sides.0 {
                        Node::Op(op, ..) => op_text(*op),
                        _ => "-",
                    };
                    let error = cx.error(
                        "E-TYPE-MISMATCH",
                        format!("`{op}` gives a `Nat` or an `Int`"),
                        format!("but `{}` is expected here", cx.show(e)),
                    );
                    return Err(if note.is_empty() {
                        error
                    } else {
                        error.with_note(note)
                    });
                }
            },
        }
    }

    // 2. A decimal or exponent literal: a `Float`.
    if decided.is_none()
        && let Some(i) = g.decimal
    {
        decided = Some((num_type(cx, Kind::Float)?, Decider::Leaf(i)));
    }

    // 3. Pass 1: leaves that can't default anything. With a prefix `-` in
    // the group, only an `Int` or a `Float` leaf decides here: any other
    // leaf is left inferred, and the `-` below makes the group `Int`, so the
    // leaf's mismatch is reported against the `-` (as when the `-` came
    // first).
    for i in 0..g.leaves.len() {
        if decided.is_some() {
            break;
        }
        let expr = g.leaves[i].expr;
        if !matches!(expr, Expr::Ann(..)) && (has_number(expr) || hopeless(expr)) {
            continue;
        }
        if g.minus.is_some() {
            if let Some((term, ty)) = probe_leaf(cx, &mut g, i)? {
                if let Class::Num(kind @ (Kind::Int | Kind::Float)) = classify(cx, &ty)? {
                    decided = Some((num_type(cx, kind)?, Decider::Leaf(i)));
                }
                g.leaves[i].state = State::Inferred(term, ty);
            }
            continue;
        }
        if !g.waits(i) {
            decided = infer_leaf(cx, &mut g, i, equality)?;
        }
    }

    // 4. Minus signs: an otherwise undecided group is an `Int`.
    if let Some(span) = g.minus {
        match &decided {
            None => decided = Some((num_type(cx, Kind::Int)?, Decider::Minus(span))),
            Some((t, _)) if matches!(classify(cx, t)?, Class::Num(Kind::Nat)) => {
                return Err(negative_nat()
                    .with_label(
                        span,
                        "this `-` needs an `Int`, but a `Nat` is expected here",
                    )
                    .with_note("use an `Int` for numbers that can be negative"));
            }
            Some(_) => {}
        }
    }

    // 5. Pass 2: the rest, except bare literals.
    for i in 0..g.leaves.len() {
        if g.leaves[i].bare || !matches!(g.leaves[i].state, State::Waiting) {
            continue;
        }
        match &decided {
            Some((t, decider)) => {
                let (t, decider) = (t.clone(), *decider);
                let term = check_leaf(cx, &g, i, &t, decider, what)?;
                g.leaves[i].state = State::Done(term);
            }
            None if g.waits(i) => {}
            None => decided = infer_leaf(cx, &mut g, i, equality)?,
        }
    }

    // 6. Defaulting.
    if decided.is_none() {
        for (i, leaf) in g.leaves.iter().enumerate() {
            if let State::Inferred(_, ty) = &leaf.state
                && let Class::Num(kind) = classify(cx, ty)?
            {
                decided = Some((num_type(cx, kind)?, Decider::Leaf(i)));
                break;
            }
        }
    }
    if decided.is_none() {
        if g.numeric() {
            // Nothing in it says its type (K4). With only `+`, `*`, `<`,
            // `<=` and equations, which any type with the instances has, it
            // is built now at an unknown type: its bare literals wait for
            // it (`queue_number`), its operators' dictionaries are
            // obligations on it, and its shape (`a = b`, `a < b`) is known
            // at once, as Lean elaborates `@Eq ?α 0 0`. `Nat` is the
            // literals' default, in the ladder (D2013); the operators are
            // then specialised at the end (§5.10). With `-`, `/` or `%`,
            // only a number type will do, and the group waits whole.
            if !g.generic(cx) {
                return queue_group(cx, expr, g, top, expected);
            }
            let t = match expected {
                Some(e) => e.clone(),
                None => {
                    let meta = cx.fresh_meta();
                    cx.eval(&meta)?
                }
            };
            for (i, leaf) in g.leaves.iter().enumerate() {
                if let State::Inferred(_, ty) = &leaf.state
                    && !unify_leaf(cx, ty, &t)?
                {
                    return Err(mixed(cx, &g, i, ty, &t, Decider::Default, what));
                }
            }
            // Its type defaults to `Nat` where nothing else says, as its
            // literals' would, also when it has none (`_ ≤ _`, `a < b` with
            // `a` and `b` of unknown type): a default of the type alone.
            if let Some(m) = head_meta(cx, &t)? {
                let error = cx.error(
                    "E-CANNOT-INFER",
                    format!("can't tell what type this {what} is on"),
                    "nothing here says what type its numbers are",
                );
                let check = GroupType {
                    t: t.clone(),
                    span: expr.span(),
                };
                crate::queue::queue_constraint(cx, Rc::new(check), m, error)?;
            }
            decided = Some((t, Decider::Default));
        } else {
            // An equality with nothing numeric about it: the first leaf's
            // type, as before groups.
            for (i, leaf) in g.leaves.iter().enumerate() {
                if let State::Inferred(_, ty) = &leaf.state {
                    decided = Some((ty.clone(), Decider::Leaf(i)));
                    break;
                }
            }
        }
    }
    let Some((t, decider)) = decided else {
        if g.bool_comparisons {
            return Err(Diagnostic::error(
                "E-TYPE-MISMATCH",
                "no side of the equation decides its type",
            ));
        }
        // Nothing could be inferred.
        let failed = g.leaves.into_iter().rev().find_map(|l| match l.state {
            State::Failed(e) => Some(e),
            _ => None,
        });
        return Err(failed.expect("a group with no type has a leaf that failed"));
    };
    finish(cx, expr, g, top, sides, expected, &t, decider)
}

/// A leaf's inferred type `ty` against the group's type `t`: they unify, or
/// the comparison waits for an unknown the postponement queue will settle
/// (a leaf `f x` whose function's result type is a waiting dot call's, as
/// in `let f := (s) => s.size`, `f (Circle 4) == 4`).
fn unify_leaf(cx: &mut Ctx, ty: &Value, t: &Value) -> Result<bool> {
    Ok(cx.unify(ty, t)?
        || crate::queue::compare_waiting(cx, ty, t, crate::queue::Failure::Mismatch)?)
}

/// Steps 7 and 8 of a group whose type `t` is decided: its leaves finished
/// at `t`, and its term built.
#[expect(
    clippy::too_many_arguments,
    reason = "the group's parts, as `group_in` has them"
)]
fn finish(
    cx: &mut Ctx,
    expr: &Expr,
    mut g: Group,
    top: Option<BinOp>,
    sides: Sides,
    expected: Option<&Value>,
    t: &Value,
    decider: Decider,
) -> Result<(Term, Value)> {
    let what = what(top);
    // 7. Finish the leaves.
    for i in 0..g.leaves.len() {
        let state = std::mem::replace(&mut g.leaves[i].state, State::Waiting);
        let term = match state {
            State::Done(term) => term,
            State::Inferred(term, ty) => {
                if !unify_leaf(cx, &ty, t)? {
                    return Err(mixed(cx, &g, i, &ty, t, decider, what));
                }
                term
            }
            State::Waiting | State::Failed(_) => check_leaf(cx, &g, i, t, decider, what)?,
        };
        g.leaves[i].state = State::Done(term);
    }

    // 8. Build.
    let kind = match classify(cx, t)? {
        Class::Num(kind) => Some(kind),
        _ => None,
    };
    let mut leaves: Vec<Option<Term>> = g
        .leaves
        .into_iter()
        .map(|l| match l.state {
            State::Done(term) => Some(term),
            _ => unreachable!("every leaf is finished"),
        })
        .collect();
    let a = build(cx, sides.0, t, kind, &mut leaves)?;
    let Some(op) = top else {
        if let Some(e) = expected
            && !cx.unify(t, e)?
        {
            return Err(cx.mismatch(e, t));
        }
        return Ok((a, t.clone()));
    };
    let b = build(
        cx,
        sides.1.expect("a comparison has two sides"),
        t,
        kind,
        &mut leaves,
    )?;
    crate::probe::record_sides(cx, expr, op, &a, &b);
    let prop = Value::Sort(Sort::Prop);
    match op {
        BinOp::Lt | BinOp::Le => Ok((operator(cx, op, t, kind, a, b)?, prop)),
        _ => equation(cx, op, a, b, t),
    }
}

/// K4 for a group (docs/proposals/postponement.md §5.4): a group that
/// nothing decides (no expected type, no leaf of a known type, no `-`, no
/// decimal) waits for its type instead of becoming `Nat` at once. The type
/// is the expected type, an unknown, for arithmetic, or a fresh unknown.
/// Every leaf inferred so far has an unknown type, and each is made that
/// type now, so that whatever fixes one of them later fixes the group. The
/// leaves inferred are kept as terms: their unknowns were made inside the
/// group, so undoing them would lose what fixes it (as for a `.field`'s
/// receiver, invariant 6). The bare literals and the leaves that failed are
/// still syntax. Resumed, the group is finished at its type as if that had
/// decided it from the start; its default, in the ladder after the
/// field-name rule, is `Nat` (D2013).
fn queue_group(
    cx: &mut Ctx,
    expr: &Expr,
    g: Group,
    top: Option<BinOp>,
    expected: Option<&Value>,
) -> Result<(Term, Value)> {
    let t = match expected {
        Some(e) => e.clone(),
        None => {
            let meta = cx.fresh_meta();
            cx.eval(&meta)?
        }
    };
    for (i, leaf) in g.leaves.iter().enumerate() {
        if let State::Inferred(_, ty) = &leaf.state
            && !unify_leaf(cx, ty, &t)?
        {
            return Err(mixed(cx, &g, i, ty, &t, Decider::Default, what(top)));
        }
    }
    let ty = match top {
        None => t.clone(),
        Some(BinOp::EqEq) => Value::Data(builtin_data(cx, Builtin::Bool)?, Vec::new().into()),
        Some(_) => Value::Sort(Sort::Prop),
    };
    let error = cx.error(
        "E-CANNOT-INFER",
        format!("can't tell what type this {} is on", what(top)),
        "nothing here says what type its numbers are",
    );
    let item = NumberGroup {
        expr: expr.clone(),
        bool_comparisons: g.bool_comparisons,
        states: g.leaves.into_iter().map(|l| l.state).collect(),
        expected: expected.cloned(),
        t: t.clone(),
    };
    let placeholder = crate::queue::queue(cx, Rc::new(item), t, ty.clone(), error)?;
    Ok((placeholder, ty))
}

/// A group waiting for its type (K4, [`queue_group`]): its syntax, what
/// each leaf had come to, and its type.
struct NumberGroup {
    expr: Expr,
    /// As the group was read (SW-944).
    bool_comparisons: bool,
    states: Vec<State>,
    expected: Option<Value>,
    t: Value,
}

impl crate::queue::Check for NumberGroup {
    fn display(&self, _cx: &Ctx) -> Option<String> {
        // The group as written (D2091).
        Some(crate::queue::syntax(&self.expr))
    }

    fn resume(&self, cx: &mut Ctx) -> Result<crate::queue::Resumed> {
        let (mut g, top, sides) = prepare(cx, &self.expr, self.bool_comparisons)?;
        for (leaf, state) in g.leaves.iter_mut().zip(&self.states) {
            leaf.state = state.clone();
        }
        let t = force(&cx.g(), self.t.clone())?;
        let defaulted = (cx.e.attempt.defaulted.borrow().iter())
            .any(|d| d.literal.is_none() && d.span == self.expr.span());
        // What a message says decided it: the ladder's default; the
        // expected type; or the first leaf whose type is now known.
        let decider = if defaulted {
            Decider::Default
        } else if self.expected.is_some() {
            Decider::Expected
        } else {
            let mut leaf = Decider::Default;
            for (i, l) in g.leaves.iter().enumerate() {
                if let State::Inferred(_, ty) = &l.state
                    && !matches!(classify(cx, ty)?, Class::Unknown)
                {
                    leaf = Decider::Leaf(i);
                    break;
                }
            }
            leaf
        };
        // A type other than `Nat`, `Int` and `Float` must have what the
        // operators need, as when it is expected from the start (step 1).
        let equality = matches!(top, Some(BinOp::Eq | BinOp::Ne | BinOp::EqEq)) && !g.arith;
        if !equality
            && matches!(classify(cx, &t)?, Class::Other)
            && let Some(note) = g.unsupported(cx, &t)?
        {
            let op = match &sides.0 {
                Node::Op(op, ..) => op_text(*op),
                _ => top.map_or("-", op_text),
            };
            let error = cx.error(
                "E-TYPE-MISMATCH",
                format!("`{op}` works on `Nat` and `Int`"),
                format!("but this is on `{}`", cx.show(&t)),
            );
            return Err(if note.is_empty() {
                error
            } else {
                error.with_note(note)
            });
        }
        let (term, _) = finish(
            cx,
            &self.expr,
            g,
            top,
            sides,
            self.expected.as_ref(),
            &t,
            decider,
        )?;
        Ok(crate::queue::Resumed::Done(term))
    }

    fn default_priority(&self) -> Option<crate::queue::Priority> {
        Some(crate::queue::Priority::Nat)
    }

    fn apply_default(&self, cx: &mut Ctx) -> Result<bool> {
        debug_assert!(
            cx.e.attempt.queue.settling(),
            "a number group was defaulted before the end (invariant 7)"
        );
        let meta = head_meta(cx, &self.t)?;
        if !cx.unify(&num_type(cx, Kind::Nat)?, &self.t)? {
            return Ok(false);
        }
        if let Some(meta) = meta {
            cx.e.attempt.defaulted.borrow_mut().push(Defaulted {
                meta,
                span: self.expr.span(),
                literal: None,
            });
        }
        Ok(true)
    }
}

/// The type of a group built at an unknown type (K4), waiting to be said:
/// nothing to resume (the group is built), only its `Nat` default, in the
/// ladder after the field-name rule (D2013), as its literals have.
struct GroupType {
    t: Value,
    span: Span,
}

impl crate::queue::Check for GroupType {
    fn resume(&self, _cx: &mut Ctx) -> Result<crate::queue::Resumed> {
        Ok(crate::queue::Resumed::Holds)
    }

    fn default_priority(&self) -> Option<crate::queue::Priority> {
        Some(crate::queue::Priority::Nat)
    }

    fn apply_default(&self, cx: &mut Ctx) -> Result<bool> {
        debug_assert!(
            cx.e.attempt.queue.settling(),
            "a group's type was defaulted outside invariant 7's points"
        );
        let meta = head_meta(cx, &self.t)?;
        if !cx.unify(&num_type(cx, Kind::Nat)?, &self.t)? {
            return Ok(false);
        }
        if let Some(meta) = meta {
            cx.e.attempt.defaulted.borrow_mut().push(Defaulted {
                meta,
                span: self.span,
                literal: None,
            });
        }
        Ok(true)
    }
}

/// The unknown at the head of `v`, if it is one.
fn head_meta(cx: &Ctx, v: &Value) -> Result<Option<usize>> {
    Ok(match force(&cx.g(), v.clone())? {
        Value::Neutral(Head::Meta(m), _) => Some(m),
        _ => None,
    })
}

/// `a = b`, `a != b` or `a == b`, with both sides of type `t`.
fn equation(cx: &mut Ctx, op: BinOp, a: Term, b: Term, t: &Value) -> Result<(Term, Value)> {
    let prop = Value::Sort(Sort::Prop);
    let ty = cx.quote(t)?;
    let eq = Term::Eq(Some(Rc::new(ty)), Rc::new(a), Rc::new(b));
    match op {
        BinOp::Eq => Ok((eq, prop)),
        // `a != b` means `Not (a = b)`.
        BinOp::Ne => {
            let not = builtin_def(cx, Builtin::Not)?;
            Ok((Term::app(Term::Def(not), eq), prop))
        }
        // `a == b` is `holds d`, for a decision procedure `d` for `a = b`,
        // found as for `if h : a = b`.
        // The search sees the operands as variables where it can
        // (`bind.rs`), so they aren't computed here or by the kernel.
        // An operand still waiting (a literal whose type nothing has said
        // yet, K4) is waited for (`check::decide_or_wait`), so the search
        // sees it as written, as it would have had nothing waited.
        _ => {
            let bool_ty = Value::Data(builtin_data(cx, Builtin::Bool)?, Vec::new().into());
            if crate::check::decision_blocker(cx, &eq, crate::check::Depth::Written)?.is_some() {
                let span = cx.span;
                let waiting = crate::check::decide_or_wait(
                    cx,
                    span,
                    &eq,
                    &bool_ty,
                    crate::check::Depth::Written,
                )?;
                return Ok((waiting, bool_ty));
            }
            let decision = crate::bind::decide(cx, &eq)?;
            Ok((decision.into_bool(cx, eq)?, bool_ty))
        }
    }
}

/// Runs `f`, or if it fails (other than by running out of resources),
/// undoes what it did (`undo.rs`) and gives `None`.
pub(crate) fn attempt<T>(cx: &mut Ctx, f: impl FnOnce(&mut Ctx) -> Result<T>) -> Result<Option<T>> {
    crate::undo::attempt(cx, f)
}

/// Infers leaf `i` (steps 3 and 4): the decision it makes, if any. A leaf
/// that can't be inferred is left for step 6, with everything its attempt
/// did undone.
fn infer_leaf(
    cx: &mut Ctx,
    g: &mut Group,
    i: usize,
    equality: bool,
) -> Result<Option<(Value, Decider)>> {
    let expr = g.leaves[i].expr;
    let (term, ty) = match speculate(cx, expr, g.leaves[i].passed)? {
        Ok(found) => found,
        Err(e) => {
            g.leaves[i].state = State::Failed(e);
            return Ok(None);
        }
    };
    let decision = match classify(cx, &ty)? {
        Class::Num(kind) => Some((num_type(cx, kind)?, Decider::Leaf(i))),
        Class::Unknown => None,
        Class::Other if equality => Some((ty.clone(), Decider::Leaf(i))),
        Class::Other => match g.unsupported(cx, &ty)? {
            None => Some((ty.clone(), Decider::Leaf(i))),
            Some(note) => {
                let op = match g.leaves[i].op {
                    "+" | "*" | "<" | "<=" => g.numeric_only.unwrap_or(g.leaves[i].op),
                    op => op,
                };
                let error = Diagnostic::error(
                    "E-TYPE-MISMATCH",
                    format!("`{op}` works on `Nat` and `Int`"),
                )
                .with_label(expr.span(), format!("this is `{}`", cx.show(&ty)));
                return Err(if note.is_empty() {
                    error
                } else {
                    error.with_note(note)
                });
            }
        },
    };
    g.leaves[i].state = State::Inferred(term, ty);
    Ok(decision)
}

/// Infers leaf `i` in pass 1 of a group with a prefix `-`: its term and
/// type, or `None` if it can't be inferred (left for later, with everything
/// its attempt did undone). Unlike [`infer_leaf`], a type the group's
/// operators don't support isn't an error here: the leaf is checked against
/// the group's type at the end.
fn probe_leaf(cx: &mut Ctx, g: &mut Group, i: usize) -> Result<Option<(Term, Value)>> {
    match speculate(cx, g.leaves[i].expr, g.leaves[i].passed)? {
        Ok(found) => Ok(Some(found)),
        Err(e) => {
            g.leaves[i].state = State::Failed(e);
            Ok(None)
        }
    }
}

/// Infers `expr`, or `Ok(Err(…))` if it can't be inferred, undoing whatever
/// the attempt did to metavariables and auto obligations: unification isn't
/// atomic, so a failed attempt may have solved some. A `passed` leaf (an
/// operand of `=` that is a computation, D1140 (a)) isn't run.
fn speculate(
    cx: &mut Ctx,
    expr: &Expr,
    passed: bool,
) -> Result<std::result::Result<(Term, Value), Diagnostic>> {
    let snapshot = crate::undo::Snapshot::take(cx);
    let inferred = if passed {
        crate::check::infer_unrun(cx, expr)
    } else {
        infer(cx, expr)
    }
    .and_then(|(term, ty)| insert(cx, term, ty));
    match inferred {
        Ok(found) => Ok(Ok(found)),
        Err(e) if e.code == "E-CANNOT-INFER" => {
            snapshot.restore(cx);
            crate::queue::note_leaf_uninferred(cx.e);
            Ok(Err(e))
        }
        Err(e) => Err(e),
    }
}

/// Checks leaf `i` against the group's type `t`, saying what decided `t`
/// if the leaf doesn't fit.
fn check_leaf(
    cx: &mut Ctx,
    g: &Group,
    i: usize,
    t: &Value,
    decider: Decider,
    what: &str,
) -> Result<Term> {
    let expr = g.leaves[i].expr;
    // A local variable is inferred, so a mismatch can say what it is.
    if let Expr::Var(name) = expr
        && cx.lookup(&name.text).is_some()
        && matches!(classify(cx, t)?, Class::Num(_))
    {
        let (term, ty) = infer(cx, expr)?;
        let (term, ty) = insert(cx, term, ty)?;
        if !cx.unify(&ty, t)? {
            return Err(mixed(cx, g, i, &ty, t, decider, what));
        }
        return Ok(term);
    }
    // A side of an `=` between propositions isn't one a `Bool` is read as a
    // proposition at (docs/proposals/bool-as-proposition.md §4.1).
    let mut sides = Vec::new();
    if matches!(force(&cx.g(), t.clone())?, Value::Sort(Sort::Prop)) {
        crate::logic::equation_side(cx, expr, &mut sides);
    }
    crate::check::without_coercion(cx, sides, |cx| {
        crate::queue::framed(
            cx,
            |cx| check(cx, expr, t),
            |_| LeafFrame {
                leaf: expr.clone(),
                decided: decided_leaf(g, decider).map(|(e, op)| (e.clone(), op)),
                t: t.clone(),
                decider,
                what: what.to_string(),
            },
        )
    })
}

/// What decided a group's type, if a leaf did: that leaf's expression and
/// operator.
fn decided_leaf<'a>(g: &Group<'a>, decider: Decider) -> Option<(&'a Expr, &'static str)> {
    match decider {
        Decider::Leaf(j) => Some((g.leaves[j].expr, g.leaves[j].op)),
        _ => None,
    }
}

/// A group's leaf checked against the group's type, as an error frame
/// (D2091): [`check_leaf`]'s explanation of what decided the type, also for
/// a check inside the leaf that waits and fails later.
struct LeafFrame {
    leaf: Expr,
    decided: Option<(Expr, &'static str)>,
    t: Value,
    decider: Decider,
    what: String,
}

impl crate::queue::ErrorFrame for LeafFrame {
    fn map(&self, cx: &mut Ctx, e: Diagnostic) -> Diagnostic {
        let decided = self.decided.as_ref().map(|(e, op)| (e, *op));
        if let Some(d) = prop_not_equal(cx, &e, &self.leaf, &self.t, decided) {
            d
        } else if e.code == "E-TYPE-MISMATCH" && e.primary_span() == Some(self.leaf.span()) {
            let at = decided.map(|(e, _)| e.span());
            decided_by(cx, e, &self.t, self.decider, at, &self.what)
        } else {
            e
        }
    }
}

/// `leaf` isn't a proposition, but the group is on propositions because
/// another side, `decided` (with its operator), is `x != y`, which in a
/// statement is `Not (x = y)`: the error is reported at that `!=`, saying
/// how to get the `Bool` instead.
fn prop_not_equal(
    cx: &Ctx,
    e: &Diagnostic,
    leaf: &Expr,
    t: &Value,
    decided: Option<(&Expr, &str)>,
) -> Option<Diagnostic> {
    if !matches!(e.code, "E-NOT-A-TYPE" | "E-TYPE-MISMATCH")
        || !matches!(force(&cx.g(), t.clone()), Ok(Value::Sort(Sort::Prop)))
    {
        return None;
    }
    let (mut decided, op) = decided?;
    while let Expr::Bracketed(inner, _) = decided {
        decided = inner;
    }
    if !matches!(decided, Expr::Binary(BinOp::Ne, ..)) {
        return None;
    }
    Some(
        Diagnostic::error(
            "E-NOT-A-TYPE",
            "in a statement, `!=` is the proposition, not a `Bool`",
        )
        .with_label(
            decided.span(),
            format!(
                "this `!=` is `Not (… = …)`, a proposition, so this `{}` compares propositions",
                op
            ),
        )
        .with_label(leaf.span(), "but this isn't a proposition")
        .with_note(
            "for the `Bool` that `!=` computes, ascribe it: `((x != y): Bool)`; or compare \
             with `==` instead, as `(x == y) = False`",
        ),
    )
}

/// Leaf `i`, of type `found`, isn't the group's type `t`.
fn mixed(
    cx: &Ctx,
    g: &Group,
    i: usize,
    found: &Value,
    t: &Value,
    decider: Decider,
    what: &str,
) -> Diagnostic {
    let span = g.leaves[i].expr.span();
    let d = match (classify(cx, found), classify(cx, t)) {
        (Ok(Class::Num(f)), Ok(Class::Num(k))) => {
            Diagnostic::error("E-TYPE-MISMATCH", "type mismatch")
                .with_label(
                    span,
                    format!(
                        "this is {}, but this {what} is on `{}`",
                        f.name(),
                        cx.show(t)
                    ),
                )
                .with_note(match (f, k) {
                    (Kind::Nat, Kind::Int) => {
                        "a `Nat` becomes an `Int` with `.toInt`, as in `n.toInt`"
                    }
                    (Kind::Int, Kind::Nat) => {
                        "an `Int` becomes a `Nat` with `Int.toNat` (negatives become 0) or \
                     `Int.toNatChecked`"
                    }
                    (Kind::Nat, Kind::Float) => {
                        "a `Nat` becomes a `Float` with `Float.ofNat`, as in `Float.ofNat n`"
                    }
                    (Kind::Int, Kind::Float) => {
                        "an `Int` becomes a `Float` with `Float.ofInt`, as in `Float.ofInt i`"
                    }
                    _ => {
                        "a `Float` becomes an `Int` with `Float.toInt`, which is `None` unless \
                     it is a whole number"
                    }
                })
        }
        _ => Diagnostic::error("E-TYPE-MISMATCH", "type mismatch").with_label(
            span,
            format!(
                "expected `{}`, but this has type `{}`",
                cx.show(t),
                cx.show(found)
            ),
        ),
    };
    let d = explain_default(cx, d, &[found]);
    let at = decided_leaf(g, decider).map(|(e, _)| e.span());
    decided_by(cx, d, t, decider, at, what)
}

/// Adds to `d` what decided the group's type `t`; `at` is where the leaf
/// that decided it is, if one did.
fn decided_by(
    cx: &Ctx,
    d: Diagnostic,
    t: &Value,
    decider: Decider,
    at: Option<Span>,
    what: &str,
) -> Diagnostic {
    let shown = cx.show(t);
    match (decider, at) {
        (Decider::Expected, _) => d.with_note(format!(
            "this {what} is on `{shown}` because `{shown}` is expected here"
        )),
        (Decider::Leaf(_), Some(at)) => {
            d.with_label(at, format!("this {what} is on `{shown}` because of this"))
        }
        (Decider::Leaf(_), None) => d,
        (Decider::Minus(span), _) => d.with_label(span, "this `-` makes it an `Int`"),
        (Decider::Default, _) => d.with_note(format!(
            "this {what} is on `Nat` because nothing in it says otherwise"
        )),
    }
}

/// Assembles the term for `node`, on the type `t` (the number type `kind`,
/// if it's one).
fn build(
    cx: &mut Ctx,
    node: Node,
    t: &Value,
    kind: Option<Kind>,
    leaves: &mut [Option<Term>],
) -> Result<Term> {
    cx.g().machine.budget.nesting(PASS)?;
    match node {
        Node::Leaf(i) => Ok(leaves[i].take().expect("each leaf is used once")),
        Node::Op(op, a, b, span) => {
            let a = build(cx, *a, t, kind, leaves)?;
            let b = build(cx, *b, t, kind, leaves)?;
            // The obligation `d != 0` of `/` and `%`, or a missing instance,
            // is reported at the operation.
            let saved = std::mem::replace(&mut cx.span, span);
            let term = operator(cx, op, t, kind, a, b);
            cx.span = saved;
            Ok(Term::Loc(span, Rc::new(term?)))
        }
        Node::Neg(x, span) => {
            let x = build(cx, *x, t, kind, leaves)?;
            let neg = if kind == Some(Kind::Float) {
                float_def(cx, Builtin::FloatNeg)?
            } else {
                builtin_def(cx, Builtin::IntNeg)?
            };
            Ok(Term::Loc(span, Rc::new(Term::app(Term::Def(neg), x))))
        }
    }
}

/// `a op b` on the type `t` (the number type `kind`, if it's one).
///
/// `+`, `*`, `<` and `<=` mean the field `add`, `mul`, `lessThan` or
/// `lessEq` of the dictionary of `Add`, `Mul` or `Ord` that §5.5 finds for
/// `t`, projected if it's a global instance (docs/proposals/interfaces.md
/// §5.13: `Nat.add a b`). On `Nat` and `Int`, with no dictionary of the
/// interface in scope, §5.5 can only find the library's instance, whose
/// fields are the built-in operations, so the projection's term is built
/// directly; so it is in the prelude before those instances are ready
/// (the bootstrap phase, D187). The rest are on `Nat` and `Int` only.
fn operator(
    cx: &mut Ctx,
    op: BinOp,
    t: &Value,
    kind: Option<Kind>,
    a: Term,
    b: Term,
) -> Result<Term> {
    // `Float` has no `Add` or `Mul`: doubles break their laws
    // (docs/proposals/float.md §2.4). Its `+ - * / %` are the primitives
    // (`/` and `%` need no proof: `1.0 / 0.0` is `Float.infinity`).
    // `<` and `<=` go through `Ord`, as on any other type.
    if kind == Some(Kind::Float) {
        let prim = match op {
            BinOp::Add => Builtin::FloatAdd,
            BinOp::Sub => Builtin::FloatSub,
            BinOp::Mul => Builtin::FloatMul,
            BinOp::Div => Builtin::FloatDiv,
            BinOp::Mod => Builtin::FloatRem,
            BinOp::Lt | BinOp::Le => Builtin::Float,
            _ => {
                return Err(cx.error(
                    "E-TYPE-MISMATCH",
                    format!("`{}` isn't defined on `Float`", op_text(op)),
                    "this is on `Float`",
                ));
            }
        };
        if prim != Builtin::Float {
            return apply_def(cx, float_def(cx, prim)?, vec![a, b]);
        }
    }
    let through = match op {
        BinOp::Add => Some(("Std.Add", "add")),
        BinOp::Mul => Some(("Std.Mul", "mul")),
        BinOp::Lt => Some(("Std.Ord", "lessThan")),
        BinOp::Le => Some(("Std.Ord", "lessEq")),
        _ => None,
    };
    if let Some((path, field)) = through
        && let Some(interface) = crate::interfaces::library_interface(cx.e, path)
    {
        let dictionary = match kind {
            None | Some(Kind::Float) => true,
            Some(k) => {
                let head = match k {
                    Kind::Nat => nat(cx)?,
                    Kind::Int | Kind::Float => builtin_data(cx, Builtin::Int)?,
                };
                crate::interfaces::instance_ready(cx.e, interface, head)
                    && (cx.e.options.uniform_operators
                        || crate::interfaces::local_dictionary(cx, interface)?)
            }
        };
        if dictionary {
            return crate::interfaces::method_call(cx, interface, field, t, vec![a, b]).map_err(
                |e| {
                    if e.code == "E-INSTANCE-NONE" {
                        let name = path.trim_start_matches("Std.");
                        e.with_note(format!(
                            "`{}` is `{name}.{field}`, from the `{name}` instance for the operands' type",
                            op_text(op)
                        ))
                    } else {
                        e
                    }
                },
            );
        }
    }
    let Some(kind) = kind else {
        return Err(cx.error(
            "E-TYPE-MISMATCH",
            format!("`{}` works on `Nat` and `Int`", op_text(op)),
            format!("this is on `{}`", cx.show(t)),
        ));
    };
    let builtin = match (op, kind) {
        (BinOp::Add, Kind::Nat) => Builtin::Add,
        (BinOp::Sub, Kind::Nat) => Builtin::Sub,
        (BinOp::Mul, Kind::Nat) => Builtin::Mul,
        (BinOp::Div, Kind::Nat) => Builtin::Div,
        (BinOp::Mod, Kind::Nat) => Builtin::Mod,
        (BinOp::Lt, Kind::Nat) => Builtin::LessThan,
        (BinOp::Le, Kind::Nat) => Builtin::LessEq,
        (BinOp::Add, Kind::Int) => Builtin::IntAdd,
        (BinOp::Sub, Kind::Int) => Builtin::IntSub,
        (BinOp::Mul, Kind::Int) => Builtin::IntMul,
        (BinOp::Div, Kind::Int) => Builtin::IntDiv,
        (BinOp::Mod, Kind::Int) => Builtin::IntMod,
        (BinOp::Lt, Kind::Int) => Builtin::IntLessThan,
        (BinOp::Le, Kind::Int) => Builtin::IntLessEq,
        _ => unreachable!("only arithmetic and ordering operators"),
    };
    apply_def(cx, builtin_def(cx, builtin)?, vec![a, b])
}

/// `id args`, with any implicit or auto parameters after them inserted.
fn apply_def(cx: &mut Ctx, id: DefId, args: Vec<Term>) -> Result<Term> {
    let g = cx.g();
    let mut term = Term::Def(id);
    let mut ty = g.def(id).ty_value().clone();
    for arg in args {
        let Value::Pi(_, Icit::Explicit, _, cod) = force(&g, ty)? else {
            unreachable!("built-in operators take two explicit arguments");
        };
        ty = cod.apply_lazy(&g, || eval(&g, &cx.env, &arg))?;
        term = Term::app(term, arg);
    }
    Ok(insert(cx, term, ty)?.0)
}

/// Whether inferring `expr` is sure to fail, so pass 1 doesn't try.
fn hopeless(expr: &Expr) -> bool {
    matches!(expr, Expr::Lam(..) | Expr::Record { base: None, .. })
}

/// Whether `expr` contains a numeric literal anywhere.
pub(crate) fn has_number(expr: &Expr) -> bool {
    let mut stack = vec![expr];
    while let Some(e) = stack.pop() {
        match e {
            Expr::Num(..) | Expr::Float(..) => return true,
            Expr::Var(_)
            | Expr::Str(..)
            | Expr::Include(..)
            | Expr::Char(..)
            | Expr::Type(..)
            | Expr::Prop(_)
            | Expr::Hole(_)
            | Expr::Goal(_)
            | Expr::Unit(_) => {}
            Expr::App(a, b)
            | Expr::Arrow(a, b)
            | Expr::Binary(_, a, b)
            | Expr::Seq(a, b)
            | Expr::Pipe(a, b)
            | Expr::Tuple(a, b, _) => {
                stack.extend([&**a, &**b]);
            }
            Expr::Neg(a, _, _)
            | Expr::Bracketed(a, _)
            | Expr::Interpolated(a, _)
            | Expr::NamedArg(_, a, _, _)
            | Expr::Field(a, _) => stack.push(a),
            Expr::Lam(_, body, _) => stack.push(body),
            Expr::TypedLam(_, _, ty, body, _) => stack.extend([&**ty, &**body]),
            Expr::Pi { dom, cod, .. } => stack.extend([&**dom, &**cod]),
            Expr::If {
                cond,
                then,
                otherwise,
                ..
            } => stack.extend([&**cond, &**then, &**otherwise]),
            Expr::Ann(e, t, _) => stack.extend([&**e, &**t]),
            Expr::List(items, _) => stack.extend(items),
            Expr::Spread(e, _) => stack.push(e),
            Expr::Record { base, fields, .. } => {
                stack.extend(base.as_deref());
                stack.extend(fields.iter().map(|(_, e)| e));
            }
            Expr::CtorFields { fields, .. } => stack.extend(fields.iter().map(|(_, e)| e)),
            Expr::Effect(row, ty) => {
                stack.extend(&row.abilities);
                stack.push(ty);
            }
            Expr::Let {
                ty, value, body, ..
            } => {
                stack.extend(ty.as_deref());
                stack.extend([&**value, &**body]);
            }
            // The definitions are elaborated on their own.
            Expr::LocalDefs { body, .. } => stack.push(body),
            Expr::Omega { facts, .. } | Expr::Ring { facts, .. } => stack.extend(facts),
            Expr::Cases { body, .. } => stack.extend(body.as_deref()),
            Expr::Calc { first, steps, .. } => {
                stack.push(first);
                for step in steps {
                    stack.push(&step.rhs);
                    stack.extend(step.proof.as_ref());
                }
            }
            Expr::Rewrite {
                rules,
                target,
                body,
                ..
            } => {
                stack.extend(rules.iter().map(|r| &r.proof));
                stack.extend(target.as_deref());
                stack.extend(body.as_deref());
            }
            Expr::Match {
                scrutinees, alts, ..
            } => {
                stack.extend(scrutinees.iter().map(|s| &s.expr));
                stack.extend(alts.iter().flat_map(|a| a.guard.iter().map(|g| &g.cond)));
                stack.extend(alts.iter().filter_map(|a| a.body.as_ref()));
            }
            Expr::Induct { call, alts, .. } => {
                stack.push(call);
                stack.extend(alts.iter().map(|a| &a.body));
            }
            Expr::Handle { body, clauses, .. }
            | Expr::Reify {
                thunk: body,
                clauses,
                ..
            } => {
                stack.push(body);
                for clause in clauses {
                    stack.push(match clause {
                        stitchwort_syntax::ast::Clause::Return { body, .. }
                        | stitchwort_syntax::ast::Clause::Op { body, .. } => body,
                    });
                }
            }
        }
    }
    false
}
