//! A tiny reference interpreter for the IR, to test lowering by running what
//! it makes: a tree walker on the Rust stack, with eval/apply for calls of
//! function values. Pure code only: it refuses `Delay`'s constants. Not the
//! stage 2 machine, and not part of the crate's interface.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use num_bigint::{BigInt, BigUint, Sign};
use stitchwort_core::native::Native;
use stitchwort_rt::Program;
use stitchwort_rt::ir::{Expr, GlobalId, GlobalKind, Lit, MatchKind, PrimOp};
use stitchwort_rt::natives::{FloatPrim, IntNative, TextNative};

#[derive(Clone, Debug)]
pub enum V {
    Nat(BigUint),
    Int(BigInt),
    Text(Rc<str>),
    /// A `Float`, by its bits, the NaN canonical.
    Float(u64),
    Ctor(u32, Rc<[V]>),
    Fun(Rc<Fun>),
    Erased,
}

#[derive(Debug)]
pub enum Fun {
    /// A lambda with what it captured, applied to `args` so far.
    Closure(u32, Rc<[V]>, Vec<V>),
    /// A global function or native, applied to `args` so far.
    Pap(GlobalId, Vec<V>),
    DoneK,
}

type R<T> = Result<T, String>;

const FALSE: u32 = 0;
const TRUE: u32 = 1;

fn ctor(c: u32, fields: Vec<V>) -> V {
    V::Ctor(c, fields.into())
}

fn boolean(b: bool) -> V {
    ctor(if b { TRUE } else { FALSE }, vec![])
}

/// `Yes` and `No`, with their proofs erased.
fn decision(b: bool) -> V {
    ctor(if b { 0 } else { 1 }, vec![])
}

fn some(v: V) -> V {
    ctor(1, vec![v])
}

fn none() -> V {
    ctor(0, vec![])
}

fn char_value(c: char) -> V {
    ctor(0, vec![V::Nat(BigUint::from(u32::from(c)))])
}

fn list(items: Vec<V>) -> V {
    items
        .into_iter()
        .rev()
        .fold(ctor(0, vec![]), |tail, head| ctor(1, vec![head, tail]))
}

fn chars(text: &str) -> V {
    list(text.chars().map(char_value).collect())
}

pub struct Interp<'p> {
    p: &'p Program,
    constants: RefCell<HashMap<u32, V>>,
}

struct Frame<'a> {
    slots: Vec<Option<V>>,
    captured: &'a [V],
}

impl<'p> Interp<'p> {
    pub fn new(p: &'p Program) -> Self {
        Interp {
            p,
            constants: RefCell::new(HashMap::new()),
        }
    }

    /// The value of global `g`.
    pub fn global(&self, g: GlobalId) -> R<V> {
        let global = &self.p.globals[g.0 as usize];
        match &global.kind {
            GlobalKind::Constant { body } => {
                if let Some(v) = self.constants.borrow().get(&g.0) {
                    return Ok(v.clone());
                }
                let mut frame = Frame {
                    slots: vec![None; body.frame as usize],
                    captured: &[],
                };
                let v = self.eval(&mut frame, &body.expr)?;
                self.constants.borrow_mut().insert(g.0, v.clone());
                Ok(v)
            }
            _ => Ok(V::Fun(Rc::new(Fun::Pap(g, Vec::new())))),
        }
    }

    fn call(&self, g: GlobalId, args: Vec<V>) -> R<V> {
        let global = &self.p.globals[g.0 as usize];
        match &global.kind {
            GlobalKind::Function { body, .. } => {
                let mut slots = vec![None; body.frame as usize];
                for (slot, arg) in slots.iter_mut().zip(args) {
                    *slot = Some(arg);
                }
                let mut frame = Frame {
                    slots,
                    captured: &[],
                };
                self.eval(&mut frame, &body.expr)
            }
            GlobalKind::Native(op) => self.prim(*op, args),
            GlobalKind::Constant { .. } => Err("called a constant".into()),
        }
    }

    /// Applies a function value to arguments (eval/apply).
    pub fn apply(&self, f: V, mut args: Vec<V>) -> R<V> {
        let mut f = f;
        while !args.is_empty() {
            let V::Fun(fun) = f else {
                return Err(format!("applied a non-function {f:?}"));
            };
            let (arity, have) = match &*fun {
                Fun::Closure(l, _, have) => (self.p.lambdas[*l as usize].params, have.len()),
                Fun::Pap(g, have) => (self.p.globals[g.0 as usize].kind.params(), have.len()),
                Fun::DoneK => (1, 0),
            };
            let need = arity as usize - have;
            if args.len() < need {
                let mut all = match &*fun {
                    Fun::Closure(_, _, have) | Fun::Pap(_, have) => have.clone(),
                    Fun::DoneK => Vec::new(),
                };
                all.extend(args);
                return Ok(V::Fun(Rc::new(match &*fun {
                    Fun::Closure(l, c, _) => Fun::Closure(*l, c.clone(), all),
                    Fun::Pap(g, _) => Fun::Pap(*g, all),
                    Fun::DoneK => unreachable!(),
                })));
            }
            let rest = args.split_off(need);
            let mut all = match &*fun {
                Fun::Closure(_, _, have) | Fun::Pap(_, have) => have.clone(),
                Fun::DoneK => Vec::new(),
            };
            all.extend(args);
            f = match &*fun {
                Fun::Closure(l, captured, _) => {
                    let lambda = &self.p.lambdas[*l as usize];
                    let mut slots = vec![None; lambda.body.frame as usize];
                    for (slot, arg) in slots.iter_mut().zip(all) {
                        *slot = Some(arg);
                    }
                    let mut frame = Frame { slots, captured };
                    self.eval(&mut frame, &lambda.body.expr)?
                }
                Fun::Pap(g, _) => self.call(*g, all)?,
                Fun::DoneK => ctor(0, all),
            };
            args = rest;
        }
        Ok(f)
    }

    fn evals(&self, frame: &mut Frame, exprs: &[Expr]) -> R<Vec<V>> {
        exprs.iter().map(|e| self.eval(frame, e)).collect()
    }

    fn eval(&self, frame: &mut Frame, expr: &Expr) -> R<V> {
        Ok(match expr {
            Expr::Local(s) => frame.slots[*s as usize]
                .clone()
                .ok_or_else(|| format!("v{s} is empty"))?,
            Expr::Captured(i) => frame.captured[*i as usize].clone(),
            Expr::Global(g) => self.global(*g)?,
            Expr::Erased => V::Erased,
            Expr::Lit(lit) => match lit {
                Lit::Nat(n) => V::Nat(n.clone()),
                Lit::Int(n) => V::Int(n.clone()),
                Lit::Text(t) => V::Text(t.clone()),
                Lit::Chars(t) => chars(t),
                Lit::Float(bits) => V::Float(*bits),
            },
            Expr::DoneK => V::Fun(Rc::new(Fun::DoneK)),
            Expr::Call(g, args) => {
                let args = self.evals(frame, args)?;
                self.call(*g, args)?
            }
            Expr::Prim(op, args) => {
                let args = self.evals(frame, args)?;
                self.prim(*op, args)?
            }
            Expr::PartialApp(g, args) => {
                let args = self.evals(frame, args)?;
                V::Fun(Rc::new(Fun::Pap(*g, args)))
            }
            Expr::Apply(f, args) => {
                let f = self.eval(frame, f)?;
                let args = self.evals(frame, args)?;
                self.apply(f, args)?
            }
            Expr::Closure(l, captures) => {
                let captured = self.evals(frame, captures)?;
                V::Fun(Rc::new(Fun::Closure(l.0, captured.into(), Vec::new())))
            }
            Expr::Ctor(_, c, fields) => {
                let fields = self.evals(frame, fields)?;
                ctor(*c, fields)
            }
            Expr::Let(slot, value, body) => {
                let v = self.eval(frame, value)?;
                frame.slots[*slot as usize] = Some(v);
                self.eval(frame, body)?
            }
            Expr::If(cond, then, otherwise) => match self.eval(frame, cond)? {
                V::Ctor(TRUE, _) => self.eval(frame, then)?,
                V::Ctor(FALSE, _) => self.eval(frame, otherwise)?,
                other => return Err(format!("if on {other:?}")),
            },
            Expr::NumSwitch(scrutinee, arms, default) => {
                let V::Nat(n) = self.eval(frame, scrutinee)? else {
                    return Err("switch on a non-number".into());
                };
                match arms.iter().find(|(k, _)| *k == n) {
                    Some((_, body)) => self.eval(frame, body)?,
                    None => self.eval(frame, default)?,
                }
            }
            Expr::Match(scrutinee, kind, arms) => {
                let v = self.eval(frame, scrutinee)?;
                let (c, fields): (usize, Vec<V>) = match (kind, v) {
                    (MatchKind::Data(_), V::Ctor(c, fields)) => (c as usize, fields.to_vec()),
                    (MatchKind::Nat, V::Nat(n)) => {
                        if n == BigUint::ZERO {
                            (0, vec![])
                        } else {
                            (1, vec![V::Nat(n - 1u32)])
                        }
                    }
                    (MatchKind::Int, V::Int(n)) => {
                        if n.sign() == Sign::Minus {
                            let m: BigInt = -n - 1;
                            (1, vec![V::Nat(m.to_biguint().expect("not negative"))])
                        } else {
                            (0, vec![V::Nat(n.to_biguint().expect("not negative"))])
                        }
                    }
                    (MatchKind::Text, V::Text(t)) => (0, vec![chars(&t)]),
                    (kind, v) => return Err(format!("{kind:?} match on {v:?}")),
                };
                let arm = &arms[c];
                for (i, slot) in &arm.fields {
                    frame.slots[*slot as usize] = Some(fields[*i as usize].clone());
                }
                self.eval(frame, &arm.body)?
            }
            Expr::Unreachable => return Err("reached unreachable".into()),
        })
    }

    fn prim(&self, op: PrimOp, args: Vec<V>) -> R<V> {
        let nat = |v: &V| match v {
            V::Nat(n) => Ok(n.clone()),
            other => Err(format!("{op:?}: expected a Nat, got {other:?}")),
        };
        let int = |v: &V| match v {
            V::Int(n) => Ok(n.clone()),
            other => Err(format!("{op:?}: expected an Int, got {other:?}")),
        };
        let text = |v: &V| match v {
            V::Text(t) => Ok(t.clone()),
            other => Err(format!("{op:?}: expected a Text, got {other:?}")),
        };
        let chr = |v: &V| match v {
            V::Ctor(0, f) => match &f[0] {
                V::Nat(n) => u32::try_from(n)
                    .ok()
                    .and_then(char::from_u32)
                    .ok_or_else(|| "bad char".to_string()),
                _ => Err("bad char".into()),
            },
            _ => Err("expected a Char".into()),
        };
        let int_nat = |n: BigInt| n.to_biguint().expect("not negative");
        Ok(match op {
            PrimOp::Nat(n) => {
                let a = nat(&args[0])?;
                match n {
                    Native::Add => V::Nat(a + nat(&args[1])?),
                    Native::Sub => {
                        let b = nat(&args[1])?;
                        V::Nat(if a >= b { a - b } else { BigUint::ZERO })
                    }
                    Native::Mul => V::Nat(a * nat(&args[1])?),
                    Native::Leq => boolean(a <= nat(&args[1])?),
                    Native::EqNat => boolean(a == nat(&args[1])?),
                    Native::DecEqNat => decision(a == nat(&args[1])?),
                    Native::DivFuel => {
                        let (n, d) = (nat(&args[1])?, nat(&args[2])?);
                        if d == BigUint::ZERO {
                            V::Nat(a)
                        } else {
                            V::Nat((n / d).min(a))
                        }
                    }
                    Native::EqNatRefl | Native::EqNatSound => V::Erased,
                }
            }
            PrimOp::NegSucc => V::Int(-BigInt::from(nat(&args[0])?) - 1),
            PrimOp::IntEqual => boolean(int(&args[0])? == int(&args[1])?),
            PrimOp::TextEqual => boolean(text(&args[0])? == text(&args[1])?),
            PrimOp::Int(i) => {
                use IntNative::*;
                let euclid = |a: &BigInt, d: &BigInt| {
                    let (q, r) = (a / d, a % d);
                    if r.sign() == Sign::Minus {
                        if d.sign() == Sign::Plus {
                            (q - 1, r + d)
                        } else {
                            (q + 1, r - d)
                        }
                    } else {
                        (q, r)
                    }
                };
                let floor = |a: &BigInt, d: &BigInt| {
                    let (q, r) = (a / d, a % d);
                    if r.sign() != Sign::NoSign
                        && (r.sign() == Sign::Minus) != (d.sign() == Sign::Minus)
                    {
                        (q - 1, r + d)
                    } else {
                        (q, r)
                    }
                };
                match i {
                    NatToInt => V::Int(BigInt::from(nat(&args[0])?)),
                    TextToInt => {
                        let t = text(&args[0])?;
                        let digits = t.strip_prefix('-').unwrap_or(&t);
                        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
                            none()
                        } else {
                            let n: BigInt = digits.parse().expect("digits");
                            some(V::Int(if digits.len() == t.len() { n } else { -n }))
                        }
                    }
                    _ => {
                        let a = int(&args[0])?;
                        match i {
                            IntNeg => V::Int(-a),
                            IntAdd => V::Int(a + int(&args[1])?),
                            IntSub => V::Int(a - int(&args[1])?),
                            IntMul => V::Int(a * int(&args[1])?),
                            IntDiv => V::Int(euclid(&a, &int(&args[1])?).0),
                            IntMod => V::Int(euclid(&a, &int(&args[1])?).1),
                            IntTDiv => V::Int(&a / int(&args[1])?),
                            IntTMod => V::Int(&a % int(&args[1])?),
                            IntFDiv => V::Int(floor(&a, &int(&args[1])?).0),
                            IntFMod => V::Int(floor(&a, &int(&args[1])?).1),
                            IntModNat => {
                                let d = BigInt::from(nat(&args[1])?);
                                V::Nat(int_nat(euclid(&a, &d).1))
                            }
                            DecEqInt => decision(a == int(&args[1])?),
                            IntLeq => boolean(a <= int(&args[1])?),
                            IntLess => boolean(a < int(&args[1])?),
                            IntCompare => ctor((a.cmp(&int(&args[1])?) as i8 + 1) as u32, vec![]),
                            IntNatAbs => V::Nat(a.magnitude().clone()),
                            IntAbs => V::Int(BigInt::from(a.magnitude().clone())),
                            IntToNat => V::Nat(if a.sign() == Sign::Minus {
                                BigUint::ZERO
                            } else {
                                int_nat(a)
                            }),
                            IntToNatChecked => {
                                if a.sign() == Sign::Minus {
                                    none()
                                } else {
                                    some(V::Nat(int_nat(a)))
                                }
                            }
                            IntSign => V::Int(BigInt::from(match a.sign() {
                                Sign::Minus => -1,
                                Sign::NoSign => 0,
                                Sign::Plus => 1,
                            })),
                            IntToText => V::Text(a.to_string().into()),
                            NatToInt | TextToInt => unreachable!(),
                        }
                    }
                }
            }
            PrimOp::Text(t) => {
                use TextNative::*;
                match t {
                    TextToList => chars(&text(&args[0])?),
                    TextFromList => {
                        let mut out = String::new();
                        let mut l = args[0].clone();
                        while let V::Ctor(1, cell) = l {
                            out.push(chr(&cell[0])?);
                            l = cell[1].clone();
                        }
                        V::Text(out.into())
                    }
                    TextAppend => V::Text(format!("{}{}", text(&args[0])?, text(&args[1])?).into()),
                    TextLength => V::Nat(BigUint::from(text(&args[0])?.chars().count())),
                    TextIsEmpty => boolean(text(&args[0])?.is_empty()),
                    DecEqText => decision(text(&args[0])? == text(&args[1])?),
                    TextCompare => {
                        let (a, b) = (text(&args[0])?, text(&args[1])?);
                        ctor((a.chars().cmp(b.chars()) as i8 + 1) as u32, vec![])
                    }
                    TextUncons => {
                        let t = text(&args[0])?;
                        let mut it = t.chars();
                        match it.next() {
                            None => none(),
                            Some(c) => {
                                some(ctor(0, vec![char_value(c), V::Text(it.as_str().into())]))
                            }
                        }
                    }
                    TextFold => {
                        let t = text(&args[2])?;
                        let mut acc = args[1].clone();
                        for c in t.chars().rev() {
                            acc = self.apply(args[0].clone(), vec![char_value(c), acc])?;
                        }
                        acc
                    }
                    TextTrim => {
                        let space =
                            |c: char| matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r');
                        V::Text(text(&args[0])?.trim_matches(space).into())
                    }
                    TextTake | TextDrop => {
                        let n = usize::try_from(&nat(&args[0])?).unwrap_or(usize::MAX);
                        let whole = text(&args[1])?;
                        let (taken, dropped): (String, String) = {
                            let mut it = whole.chars();
                            let taken = it.by_ref().take(n).collect();
                            (taken, it.collect())
                        };
                        V::Text(if t == TextTake { taken } else { dropped }.into())
                    }
                    TextContains => boolean(text(&args[1])?.contains(&*text(&args[0])?)),
                    TextSplit => {
                        let s = chr(&args[0])?;
                        let t = text(&args[1])?;
                        list(t.split(s).map(|p| V::Text(p.into())).collect())
                    }
                    TextJoin => {
                        let s = chr(&args[0])?.to_string();
                        let mut parts = Vec::new();
                        let mut l = args[1].clone();
                        while let V::Ctor(1, cell) = l {
                            parts.push(text(&cell[0])?.to_string());
                            l = cell[1].clone();
                        }
                        V::Text(parts.join(&s).into())
                    }
                    NatToText => V::Text(nat(&args[0])?.to_string().into()),
                    TextToNat => {
                        let t = text(&args[0])?;
                        if t.is_empty() || !t.bytes().all(|b| b.is_ascii_digit()) {
                            none()
                        } else {
                            some(V::Nat(t.parse().expect("digits")))
                        }
                    }
                }
            }
            PrimOp::Delay(_) => return Err("unsupported: a partial computation".into()),
            // On the bits, written apart from the runtime's (which works on
            // `f64`s): the model's definitions (std/Float/Float.sw), with
            // `f64` only for the rounding operations.
            PrimOp::Float(f) => {
                const SIGN: u64 = 1 << 63;
                const NAN: u64 = 0x7FF8_0000_0000_0000;
                let bits = |v: &V| match v {
                    V::Float(b) => Ok(*b),
                    _ => Err("expected a Float".to_string()),
                };
                let canonical = |x: f64| if x.is_nan() { NAN } else { x.to_bits() };
                let a = bits(&args[0]);
                match f {
                    FloatPrim::Add => V::Float(canonical(
                        f64::from_bits(a?) + f64::from_bits(bits(&args[1])?),
                    )),
                    FloatPrim::Sub => V::Float(canonical(
                        f64::from_bits(a?) - f64::from_bits(bits(&args[1])?),
                    )),
                    FloatPrim::Neg => V::Float(match a? {
                        NAN => NAN,
                        b => b ^ SIGN,
                    }),
                    FloatPrim::Abs => V::Float(a? & !SIGN),
                    FloatPrim::IsNaN => boolean(a? == NAN),
                    FloatPrim::DecEq => decision(a? == bits(&args[1])?),
                    FloatPrim::IeeeEq => {
                        let (x, y) = (a?, bits(&args[1])?);
                        boolean(x != NAN && (x == y || (x | y) & !SIGN == 0))
                    }
                    FloatPrim::Mul | FloatPrim::Div | FloatPrim::Rem => {
                        use stitchwort_core::float::FloatOp;
                        let op = match f {
                            FloatPrim::Mul => FloatOp::Mul,
                            FloatPrim::Div => FloatOp::Div,
                            _ => FloatOp::Rem,
                        };
                        V::Float(canonical(
                            op.apply(f64::from_bits(a?), f64::from_bits(bits(&args[1])?)),
                        ))
                    }
                    FloatPrim::Floor | FloatPrim::Ceil | FloatPrim::Trunc | FloatPrim::Round => {
                        use stitchwort_core::float::FloatOp;
                        let op = match f {
                            FloatPrim::Floor => FloatOp::Floor,
                            FloatPrim::Ceil => FloatOp::Ceil,
                            FloatPrim::Trunc => FloatOp::Trunc,
                            _ => FloatOp::Round,
                        };
                        V::Float(canonical(op.apply_unary(f64::from_bits(a?))))
                    }
                    FloatPrim::OfInt => V::Float(canonical(stitchwort_core::float::int_to_f64(
                        &int(&args[0])?,
                    ))),
                    FloatPrim::OfNat => V::Float(canonical(stitchwort_core::float::nat_to_f64(
                        &nat(&args[0])?,
                    ))),
                    FloatPrim::ToText => {
                        V::Text(stitchwort_core::float::js_to_string(f64::from_bits(a?)).into())
                    }
                    FloatPrim::IsFinite => boolean(stitchwort_core::float::is_finite(a?)),
                    FloatPrim::IeeeLt => boolean(stitchwort_core::float::ieee_less(
                        a?,
                        bits(&args[1])?,
                        false,
                    )),
                    FloatPrim::IeeeLe => {
                        boolean(stitchwort_core::float::ieee_less(a?, bits(&args[1])?, true))
                    }
                    FloatPrim::ToInt => match stitchwort_core::float::to_int(a?) {
                        Some(n) => some(V::Int(n)),
                        None => none(),
                    },
                    FloatPrim::Compare => ctor(
                        (stitchwort_core::float::total_order(a?, bits(&args[1])?) as i8 + 1) as u32,
                        vec![],
                    ),
                    FloatPrim::FromBits => V::Float(
                        u64::try_from(nat(&args[0])?).map_err(|_| "bits beyond 64".to_string())?,
                    ),
                    FloatPrim::Bits => V::Nat(BigUint::from(a?)),
                }
            }
        })
    }
}
