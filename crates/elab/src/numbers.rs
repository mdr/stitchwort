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

use num_bigint::BigUint;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, eval, force};
use stitchwort_core::{DataId, DefId, Icit, Sort, Term, Value};
use stitchwort_syntax::ast::{BinOp, Expr};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{
    Ctx, PASS, Result, builtin_ctor, builtin_data, builtin_def, check, infer, insert, nat,
};

/// A metavariable that became `Nat` because a literal was checked against it
/// before anything else said what it was: remembered so that a later
/// mismatch can say why (the "defaulted literal" note).
pub(crate) struct Defaulted {
    meta: usize,
    span: Span,
    literal: BigUint,
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
    Ok(match force(g, ty.clone())? {
        Value::Data(d, params) if params.is_empty() && Some(d) == g.builtins.nat => {
            Class::Num(Kind::Nat)
        }
        Value::Data(d, params) if params.is_empty() && Some(d) == g.registry.data(Builtin::Int) => {
            Class::Num(Kind::Int)
        }
        Value::Data(d, params)
            if params.is_empty() && Some(d) == g.registry.loaded_data(Builtin::Float) =>
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
    Ok(Value::Data(d, Vec::new()))
}

/// The library's `Float`, which a decimal literal loads (its references
/// include `Std.Float`, `module.rs`).
fn float_data(cx: &Ctx) -> Result<DataId> {
    cx.g().registry.loaded_data(Builtin::Float).ok_or_else(|| {
        cx.error(
            "E-UNKNOWN-NAME",
            "a decimal literal is a `Float`, and the library's `Std.Float` isn't loaded",
            "here",
        )
    })
}

/// One of the library's `Float` definitions.
fn float_def(cx: &Ctx, b: Builtin) -> Result<DefId> {
    cx.g().registry.loaded_def(b).ok_or_else(|| {
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
        Expr::Neg(inner, _) => match &**inner {
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
        Expr::Neg(inner, _) => match &**inner {
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
    match classify(cx, expected)? {
        Class::Num(Kind::Nat) if negative => Err(negative_nat()
            .with_label(cx.span, "this is negative, but a `Nat` is expected here")
            .with_note("use an `Int` for numbers that can be negative")),
        Class::Num(Kind::Nat) => Ok(Term::Nat(Rc::new(k.clone()))),
        Class::Num(Kind::Int) => int_literal(cx, k, negative),
        Class::Num(Kind::Float) => float_term(cx, whole_bits(cx, k, negative)?, negative),
        Class::Unknown => {
            let kind = if negative { Kind::Int } else { Kind::Nat };
            let found = num_type(cx, kind)?;
            let meta = match force(cx.g(), expected.clone())? {
                Value::Neutral(Head::Meta(m), _) => Some(m),
                _ => None,
            };
            if !cx.unify(&found, expected)? {
                return Err(cx.mismatch(expected, &found));
            }
            if negative {
                return int_literal(cx, k, true);
            }
            if let Some(meta) = meta {
                cx.e.defaulted.borrow_mut().push(Defaulted {
                    meta,
                    span: cx.span,
                    literal: k.clone(),
                });
            }
            Ok(Term::Nat(Rc::new(k.clone())))
        }
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
                && crate::interfaces::findable(cx, &Value::Data(add, vec![expected.clone()]))?
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

/// The bound `n` of `ty` if `ty` is the library's `Fin n`: `Some(Some(n))`
/// when n computes to a number, `Some(None)` when it doesn't (a variable, an
/// unsolved metavariable), and `None` for any other type.
pub(crate) fn fin_bound(
    g: &stitchwort_core::Globals,
    ty: &Value,
) -> Result<Option<Option<BigUint>>> {
    let Some(fin) = g.registry.loaded_data(Builtin::Fin) else {
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
    let Some(bound) = fin_bound(cx.g(), expected)? else {
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
        let unsolved = match force(cx.g(), expected.clone())? {
            Value::Data(_, params) => matches!(
                force(cx.g(), params[0].clone())?,
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
        .registry
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
    let Value::Data(d, params) = force(g, expected.clone())? else {
        return Ok(None);
    };
    if !params.is_empty() {
        return Ok(None);
    }
    let (name, int) = if Some(d) == g.registry.loaded_data(Builtin::SafeNat) {
        ("SafeNat", false)
    } else if Some(d) == g.registry.loaded_data(Builtin::SafeInt) {
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
    let defaulted = cx.e.defaulted.borrow();
    for ty in types {
        let Value::Neutral(Head::Meta(m), _) = ty else {
            continue;
        };
        if let Some(found) = defaulted.iter().find(|x| x.meta == *m) {
            let k = &found.literal;
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
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::In(_) => "in",
    }
}

impl<'a> Group<'a> {
    fn tree(&mut self, cx: &Ctx, expr: &'a Expr, op: &'static str) -> Result<Node> {
        cx.g().budget.nesting(PASS)?;
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
            Expr::Neg(inner, span) => {
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
                && crate::interfaces::findable(cx, &Value::Data(interface, vec![t.clone()]))?
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
        cx.g().budget.nesting(PASS)?;
        match expr {
            Expr::Binary(op, a, b) if is_arith(*op) => {
                let a = tree(cx, a, f)?;
                let b = tree(cx, b, f)?;
                Ok(Expr::Binary(*op, Box::new(a), Box::new(b)))
            }
            Expr::Neg(inner, span) if !any_literal(expr) => {
                Ok(Expr::Neg(Box::new(tree(cx, inner, f)?), *span))
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
    // A comparison with a constructor with number literals as an operand: as
    // written first, and if that fails, with that operand last.
    if let Expr::Binary(op, a, b) = expr
        && is_comparison(*op)
        && (crate::check::defers_literal(cx, a)? || crate::check::defers_literal(cx, b)?)
    {
        return crate::check::retrying(cx, |cx| group_in(cx, expr, expected));
    }
    group_in(cx, expr, expected)
}

fn group_in(cx: &mut Ctx, expr: &Expr, expected: Option<&Value>) -> Result<(Term, Value)> {
    let mut g = Group::default();
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
    // Comparisons constrain their operands, not their result.
    let expected = if top.is_some() { None } else { expected };
    let what = if top.is_some() {
        "comparison"
    } else {
        "arithmetic"
    };
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
        decided = infer_leaf(cx, &mut g, i, equality)?;
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
    // A constructor with a number in it comes last, so it doesn't settle the
    // group's type (`Point 1 "p" 10 == m`: a `Mark Nat …`) before the others.
    let mut order = Vec::new();
    let mut late = Vec::new();
    for (i, leaf) in g.leaves.iter().enumerate() {
        if cx.e.late_literals.get() > 0 && crate::check::defers_literal(cx, leaf.expr)? {
            late.push(i);
        } else {
            order.push(i);
        }
    }
    order.extend(late);
    for i in order {
        if g.leaves[i].bare || !matches!(g.leaves[i].state, State::Waiting) {
            continue;
        }
        match &decided {
            Some((t, decider)) => {
                let (t, decider) = (t.clone(), *decider);
                let term = check_leaf(cx, &g, i, &t, decider, what)?;
                g.leaves[i].state = State::Done(term);
            }
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
            decided = Some((num_type(cx, Kind::Nat)?, Decider::Default));
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
        // Nothing could be inferred.
        let failed = g.leaves.into_iter().rev().find_map(|l| match l.state {
            State::Failed(e) => Some(e),
            _ => None,
        });
        return Err(failed.expect("a group with no type has a leaf that failed"));
    };

    // 7. Finish the leaves.
    for i in 0..g.leaves.len() {
        let state = std::mem::replace(&mut g.leaves[i].state, State::Waiting);
        let term = match state {
            State::Done(term) => term,
            State::Inferred(term, ty) => {
                if !cx.unify(&ty, &t)? {
                    return Err(mixed(cx, &g, i, &ty, &t, decider, what));
                }
                term
            }
            State::Waiting | State::Failed(_) => check_leaf(cx, &g, i, &t, decider, what)?,
        };
        g.leaves[i].state = State::Done(term);
    }

    // 8. Build.
    let kind = match classify(cx, &t)? {
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
    let a = build(cx, sides.0, &t, kind, &mut leaves)?;
    let Some(op) = top else {
        if let Some(e) = expected
            && !cx.unify(&t, e)?
        {
            return Err(cx.mismatch(e, &t));
        }
        return Ok((a, t));
    };
    let b = build(
        cx,
        sides.1.expect("a comparison has two sides"),
        &t,
        kind,
        &mut leaves,
    )?;
    crate::probe::record_sides(cx, expr, op, &a, &b);
    let prop = Value::Sort(Sort::Prop);
    match op {
        BinOp::Lt | BinOp::Le => Ok((operator(cx, op, &t, kind, a, b)?, prop)),
        _ => equation(cx, op, a, b, &t),
    }
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
        // `a == b` is `toBool d`, for a decision procedure `d` for `a = b`,
        // found as for `if h : a = b`.
        // The search sees the operands as variables where it can
        // (`bind.rs`), so they aren't computed here or by the kernel.
        _ => {
            let decision = crate::bind::decide(cx, &eq)?;
            let bool_data = builtin_data(cx, Builtin::Bool)?;
            Ok((
                decision.into_bool(cx, eq)?,
                Value::Data(bool_data, Vec::new()),
            ))
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
    };
    match inferred.and_then(|(term, ty)| insert(cx, term, ty)) {
        Ok(found) => Ok(Ok(found)),
        Err(e) if e.code == "E-CANNOT-INFER" => {
            snapshot.restore(cx);
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
    check(cx, expr, t).map_err(|e| {
        if let Some(d) = prop_not_equal(cx, g, &e, i, t, decider) {
            d
        } else if e.code == "E-TYPE-MISMATCH" && e.primary_span() == Some(expr.span()) {
            decided_by(cx, g, e, t, decider, what)
        } else {
            e
        }
    })
}

/// Leaf `i` isn't a proposition, but the group is on propositions because
/// another side is `x != y`, which in a statement is `Not (x = y)`: the
/// error is reported at that `!=`, saying how to get the `Bool` instead.
fn prop_not_equal(
    cx: &Ctx,
    g: &Group,
    e: &Diagnostic,
    i: usize,
    t: &Value,
    decider: Decider,
) -> Option<Diagnostic> {
    if !matches!(e.code, "E-NOT-A-TYPE" | "E-TYPE-MISMATCH")
        || !matches!(force(cx.g(), t.clone()), Ok(Value::Sort(Sort::Prop)))
    {
        return None;
    }
    let Decider::Leaf(j) = decider else {
        return None;
    };
    let mut decided = g.leaves[j].expr;
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
                g.leaves[j].op
            ),
        )
        .with_label(g.leaves[i].expr.span(), "but this isn't a proposition")
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
    decided_by(cx, g, d, t, decider, what)
}

/// Adds to `d` what decided the group's type `t`.
fn decided_by(
    cx: &Ctx,
    g: &Group,
    d: Diagnostic,
    t: &Value,
    decider: Decider,
    what: &str,
) -> Diagnostic {
    let shown = cx.show(t);
    match decider {
        Decider::Expected => d.with_note(format!(
            "this {what} is on `{shown}` because `{shown}` is expected here"
        )),
        Decider::Leaf(j) => d.with_label(
            g.leaves[j].expr.span(),
            format!("this {what} is on `{shown}` because of this"),
        ),
        Decider::Minus(span) => d.with_label(span, "this `-` makes it an `Int`"),
        Decider::Default => d.with_note(format!(
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
    cx.g().budget.nesting(PASS)?;
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
                    && (cx.e.uniform_operators
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
    let mut ty = g.def(id).ty_value.clone();
    for arg in args {
        let Value::Pi(_, Icit::Explicit, _, cod) = force(g, ty)? else {
            unreachable!("built-in operators take two explicit arguments");
        };
        ty = cod.apply_lazy(g, || eval(g, &cx.env, &arg))?;
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
            Expr::Neg(a, _)
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
