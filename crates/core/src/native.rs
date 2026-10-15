//! Native numbers (docs/proposals/native-numbers.md).
//!
//! `Nat` is defined in the prelude as `Zero | Succ Nat`, and that's what it
//! means. But a number is *stored* as one arbitrary-precision value,
//! `Value::Nat`, which behaves exactly like its chain of `Succ`s: matching on
//! it takes the `Zero` or `Succ` branch, and conversion treats `3` and
//! `Succ 2` as equal.
//!
//! A few prelude definitions also have a native implementation, used when all
//! their arguments are numbers. Otherwise they unfold as usual, so proofs by
//! induction still work. The native implementations are part of the trusted
//! base (DESIGN.md §13): a bug in one could make the kernel accept `2 + 2 = 5`.
//! The tests compare each one with its definition on many inputs.
//!
//! Built-ins are registered by name, only while the prelude is loaded, and the
//! registration functions check the shapes of the types involved.

use std::collections::HashMap;
use std::rc::Rc;

use num_bigint::BigUint;
use num_traits::Zero;
use stitchwort_syntax::{Diagnostic, Span};

use crate::globals::Globals;
use crate::term::{DataId, DefId, Icit, Sort, Term};
use crate::value::{Elim, Head, Value, conv, eval, force};

/// A definition with a native implementation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Native {
    /// `add m n`
    Add,
    /// `sub m n`, stopping at zero.
    Sub,
    /// `mul m n`
    Mul,
    /// `leq m n : Bool`
    Leq,
    /// `eqNat m n : Bool`
    EqNat,
    /// `divFuel fuel n d`: how many times `d` fits into `n`, at most `fuel`.
    DivFuel,
    /// `decEqNat m n : Decidable (m = n)`
    DecEqNat,
    /// `eqNatRefl n : eqNat n n = True`, which is `rfl` for any number. Without
    /// this, using `natNeq` would count down its first argument.
    EqNatRefl,
}

impl Native {
    pub const ALL: [Native; 8] = [
        Native::Add,
        Native::Sub,
        Native::Mul,
        Native::Leq,
        Native::EqNat,
        Native::DivFuel,
        Native::DecEqNat,
        Native::EqNatRefl,
    ];

    /// The prelude definition this implements.
    pub fn name(self) -> &'static str {
        match self {
            Native::Add => "add",
            Native::Sub => "sub",
            Native::Mul => "mul",
            Native::Leq => "leq",
            Native::EqNat => "eqNat",
            Native::DivFuel => "divFuel",
            Native::DecEqNat => "decEqNat",
            Native::EqNatRefl => "eqNatRefl",
        }
    }

    pub fn arity(self) -> usize {
        match self {
            Native::DivFuel => 3,
            Native::EqNatRefl => 1,
            _ => 2,
        }
    }
}

/// Data types and definitions the evaluator knows about.
#[derive(Default)]
pub struct Builtins {
    /// `Nat`: constructor 0 is `Zero`, constructor 1 is `Succ`.
    pub nat: Option<DataId>,
    /// `Bool`: constructor 0 is `False`, constructor 1 is `True`.
    pub bool: Option<DataId>,
    /// `Decidable p`: constructor 0 is `Yes`, constructor 1 is `No`.
    pub decidable: Option<DataId>,
    /// `natNeq : (m n : Nat) -> eqNat m n = False -> Not (m = n)`, used to
    /// build the refutation in `decEqNat`'s `No`.
    pub nat_neq: Option<DefId>,
    natives: HashMap<DefId, Native>,
    /// Off in tests that compare natives with their definitions.
    pub disable_natives: bool,
}

impl Builtins {
    pub fn native(&self, id: DefId) -> Option<Native> {
        if self.disable_natives {
            return None;
        }
        self.natives.get(&id).copied()
    }
}

type Result<T> = std::result::Result<T, Diagnostic>;

fn shape_error(span: Span, what: &str) -> Diagnostic {
    Diagnostic::error(
        "E-BUILTIN",
        format!("the prelude's `{what}` doesn't have the shape the compiler expects"),
    )
    .with_label(span, "here")
}

fn data_sig(g: &Globals, d: DataId) -> Vec<Vec<usize>> {
    g.data(d)
        .ctors
        .iter()
        .map(|c| c.fields.iter().map(|_| 0).collect())
        .collect()
}

/// Registers `Nat`, which must be `Zero | Succ Nat` with no parameters.
pub fn register_nat(g: &mut Globals, d: DataId) -> Result<()> {
    let data = g.data(d);
    let ok = data.params.is_empty()
        && data.sort == Sort::Type(0)
        && data_sig(g, d) == [vec![], vec![0]]
        && matches!(&data.ctors[1].fields[0].1.strip_loc(), Term::Data(d2, args) if *d2 == d && args.is_empty());
    if !ok {
        return Err(shape_error(data.span, "Nat"));
    }
    g.builtins.nat = Some(d);
    Ok(())
}

/// Registers `Bool`, which must be two constructors without fields.
pub fn register_bool(g: &mut Globals, d: DataId) -> Result<()> {
    let data = g.data(d);
    if !(data.params.is_empty() && data.sort == Sort::Type(0) && data_sig(g, d) == [vec![], vec![]])
    {
        return Err(shape_error(data.span, "Bool"));
    }
    g.builtins.bool = Some(d);
    Ok(())
}

/// Registers `Decidable (p : Prop)`, which must be `Yes p | No (Not p)`.
/// Checked by comparing it with the type it must have, so a native `Yes`
/// built from `rfl` and a native `No` built from `natNeq` are well-typed.
pub fn register_decidable(g: &mut Globals, d: DataId) -> Result<()> {
    let data = g.data(d);
    let p = Value::var(0);
    let void = g.find_data("Void");
    let shaped = data.params.len() == 1
        && data.sort == Sort::Type(0)
        && data_sig(g, d) == [vec![0], vec![0]]
        && void.is_some_and(|void| {
            let params = [p.clone()];
            let yes = eval(g, &params, &data.ctors[0].fields[0].1);
            let no = eval(g, &params, &data.ctors[1].fields[0].1);
            let param = eval(g, &[], &data.params[0].1);
            let not_p = Value::Pi(
                "h".into(),
                Icit::Explicit,
                Rc::new(p.clone()),
                crate::value::Closure {
                    env: Rc::new([p.clone()]),
                    body: Rc::new(Term::Data(void, Vec::new())),
                },
            );
            conv(g, 0, &param, &Value::Sort(Sort::Prop))
                && conv(g, 1, &yes, &p)
                && conv(g, 1, &no, &not_p)
        });
    if !shaped {
        return Err(shape_error(data.span, "Decidable"));
    }
    g.builtins.decidable = Some(d);
    Ok(())
}

/// Registers a native implementation for definition `id`, after checking its
/// type. Natives returning `Bool` or `Decidable` need those registered first.
pub fn register_native(g: &mut Globals, id: DefId, native: Native) -> Result<()> {
    let def = g.def(id);
    let span = def.span;
    let Some(nat) = g.builtins.nat else {
        return Err(shape_error(span, native.name()));
    };
    let nat_ty = || Term::Data(nat, Vec::new());
    let arrow =
        |dom: Term, cod: Term| Term::Pi("x".into(), Icit::Explicit, Rc::new(dom), Rc::new(cod));
    let result = match native {
        Native::Add | Native::Sub | Native::Mul | Native::DivFuel => Some(nat_ty()),
        Native::Leq | Native::EqNat => g.builtins.bool.map(|b| Term::Data(b, Vec::new())),
        // (m : Nat) -> (n : Nat) -> Decidable (m = n), and `natNeq` must exist.
        Native::DecEqNat => g
            .builtins
            .decidable
            .filter(|_| g.builtins.nat_neq.is_some())
            .map(|dec| {
                Term::Data(
                    dec,
                    vec![Term::Eq(
                        Some(Rc::new(nat_ty())),
                        Rc::new(Term::Var(1)),
                        Rc::new(Term::Var(0)),
                    )],
                )
            }),
        // (n : Nat) -> eqNat n n = True
        Native::EqNatRefl => {
            g.builtins
                .bool
                .zip(native_def(g, Native::EqNat))
                .map(|(bool, eq_nat)| {
                    Term::Eq(
                        Some(Rc::new(Term::Data(bool, Vec::new()))),
                        Rc::new(Term::app(
                            Term::app(Term::Def(eq_nat), Term::Var(0)),
                            Term::Var(0),
                        )),
                        Rc::new(Term::Ctor(bool, 1, Vec::new())),
                    )
                })
        }
    };
    let Some(mut expected) = result else {
        return Err(shape_error(span, native.name()));
    };
    for _ in 0..native.arity() {
        expected = arrow(nat_ty(), expected);
    }
    if def.arity != native.arity() || !conv(g, 0, &eval(g, &[], &expected), &def.ty_value) {
        return Err(shape_error(span, native.name()));
    }
    g.builtins.natives.insert(id, native);
    Ok(())
}

/// The definition registered with native implementation `native`.
fn native_def(g: &Globals, native: Native) -> Option<DefId> {
    g.builtins
        .natives
        .iter()
        .find(|(_, n)| **n == native)
        .map(|(id, _)| *id)
}

/// Registers `natNeq : (m n : Nat) -> eqNat m n = False -> Not (m = n)`.
pub fn register_nat_neq(g: &mut Globals, id: DefId) -> Result<()> {
    let def = g.def(id);
    let span = def.span;
    let (Some(nat), Some(bool), Some(eq_nat), Some(void)) = (
        g.builtins.nat,
        g.builtins.bool,
        native_def(g, Native::EqNat),
        g.find_data("Void"),
    ) else {
        return Err(shape_error(span, "natNeq"));
    };
    let pi =
        |dom: Term, cod: Term| Term::Pi("x".into(), Icit::Explicit, Rc::new(dom), Rc::new(cod));
    let nat_ty = || Rc::new(Term::Data(nat, Vec::new()));
    let expected = pi(
        Term::Data(nat, Vec::new()),
        pi(
            Term::Data(nat, Vec::new()),
            pi(
                Term::Eq(
                    Some(Rc::new(Term::Data(bool, Vec::new()))),
                    Rc::new(Term::app(
                        Term::app(Term::Def(eq_nat), Term::Var(1)),
                        Term::Var(0),
                    )),
                    Rc::new(Term::Ctor(bool, 0, Vec::new())),
                ),
                pi(
                    Term::Eq(Some(nat_ty()), Rc::new(Term::Var(2)), Rc::new(Term::Var(1))),
                    Term::Data(void, Vec::new()),
                ),
            ),
        ),
    );
    // It must still need its last argument, so applying it to three stays stuck.
    if def.arity != 4 || !conv(g, 0, &eval(g, &[], &expected), &def.ty_value) {
        return Err(shape_error(span, "natNeq"));
    }
    g.builtins.nat_neq = Some(id);
    Ok(())
}

/// A number value. `Zero` and `Succ` of a number are numbers too.
pub fn nat_value(n: BigUint) -> Value {
    Value::Nat(Rc::new(n))
}

/// Builds a constructor value, keeping numbers compact.
pub fn ctor(g: &Globals, d: DataId, c: usize, fields: Vec<Value>) -> Value {
    if Some(d) == g.builtins.nat {
        match (c, fields.as_slice()) {
            (0, []) => return nat_value(BigUint::zero()),
            (1, [Value::Nat(n)]) => return nat_value(&**n + 1u32),
            _ => {}
        }
    }
    Value::Ctor(d, c, fields)
}

/// The number `value` is, if it's a number (possibly with `Succ`s around it).
pub fn as_nat(g: &Globals, value: &Value) -> Option<BigUint> {
    let mut succs = 0u64;
    let mut value = force(g, value.clone());
    loop {
        match value {
            Value::Nat(n) => return Some(&*n + succs),
            Value::Ctor(d, 0, _) if Some(d) == g.builtins.nat => return Some(BigUint::from(succs)),
            Value::Ctor(d, 1, mut fields) if Some(d) == g.builtins.nat => {
                succs += 1;
                value = force(g, fields.pop()?);
            }
            _ => return None,
        }
    }
}

/// Matching on number `n`: the constructor and its fields.
pub fn split(n: &BigUint) -> (usize, Vec<Value>) {
    if n.is_zero() {
        (0, Vec::new())
    } else {
        (1, vec![nat_value(n - 1u32)])
    }
}

fn bool_value(g: &Globals, b: bool) -> Option<Value> {
    Some(Value::Ctor(g.builtins.bool?, b as usize, Vec::new()))
}

/// Runs a native implementation, if all its arguments are numbers.
pub fn run(g: &Globals, native: Native, spine: &[Elim]) -> Option<Value> {
    let args: Vec<BigUint> = spine
        .iter()
        .map(|e| match e {
            Elim::App(v, Icit::Explicit) => as_nat(g, v),
            _ => None,
        })
        .collect::<Option<_>>()?;
    let nat = |n: BigUint| Some(nat_value(n));
    match (native, args.as_slice()) {
        (Native::Add, [m, n]) => nat(m + n),
        (Native::Sub, [m, n]) => nat(if m >= n { m - n } else { BigUint::zero() }),
        (Native::Mul, [m, n]) => nat(m * n),
        (Native::Leq, [m, n]) => bool_value(g, m <= n),
        (Native::EqNat, [m, n]) => bool_value(g, m == n),
        (Native::DivFuel, [fuel, n, d]) => nat(if d.is_zero() {
            fuel.clone()
        } else {
            fuel.min(&(n / d)).clone()
        }),
        (Native::EqNatRefl, [_]) => Some(Value::Refl),
        (Native::DecEqNat, [m, n]) => {
            let dec = g.builtins.decidable?;
            if m == n {
                Some(Value::Ctor(dec, 0, vec![Value::Refl]))
            } else {
                // `natNeq m n rfl`, which is stuck until it's given a proof
                // of `m = n` (and there isn't one).
                let arg = |v| Elim::App(v, Icit::Explicit);
                let refutation = Value::Neutral(
                    Head::Def(g.builtins.nat_neq?),
                    vec![
                        arg(nat_value(m.clone())),
                        arg(nat_value(n.clone())),
                        arg(Value::Refl),
                    ],
                );
                Some(Value::Ctor(dec, 1, vec![refutation]))
            }
        }
        _ => None,
    }
}
