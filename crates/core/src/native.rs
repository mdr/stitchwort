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
//! Each must compute exactly what its definition computes, as the whole
//! result: for a native returning a proof, the same proof term up to
//! conversion, not just another proof of the same thing (otherwise turning
//! natives on would change which `rfl` proofs check). The tests compare whole
//! results with the definitions on many inputs.
//!
//! Built-ins are registered while the prelude is loaded, for the declarations
//! the registry ([`crate::registry`]) binds, and the registration functions
//! check the shapes of the types involved.
//!
//! A number with unknowns in it is kept compact too: `1000 + x` is
//! `Value::NatAdd(1000, x)`, which means `Succ` applied 1000 times to `x`
//! (exactly what `add` computes by its definition). `sub`, `leq` and `eqNat`
//! take off the `Succ`s two such numbers share in one step, as their
//! definitions do one at a time.

use std::collections::HashMap;
use std::rc::Rc;

use num_bigint::BigUint;
use num_traits::Zero;
use stitchwort_syntax::{Diagnostic, Span};

use crate::budget;
use crate::globals::{Globals, State};
use crate::partial::Primitive;
use crate::registry::Builtin;
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
    /// `decEqNat m n : Decidable (m = n)`: `Yes rfl` or `No (natNeq m n rfl)`,
    /// exactly what its definition computes.
    DecEqNat,
    /// `eqNatRefl n : eqNat n n = True`, which is `rfl` for any number. Without
    /// this, using `natNeq` would count down its first argument.
    EqNatRefl,
    /// `eqNatSound m n h : m = n`, which is `rfl` when `m` and `n` are the same
    /// number, whatever `h` is. Without this, the `Yes` that `decEqNat`'s
    /// definition computes would count down its arguments.
    EqNatSound,
}

impl Native {
    pub const ALL: [Native; 9] = [
        Native::Add,
        Native::Sub,
        Native::Mul,
        Native::Leq,
        Native::EqNat,
        Native::DivFuel,
        Native::DecEqNat,
        Native::EqNatRefl,
        Native::EqNatSound,
    ];

    /// The prelude definition this implements.
    pub fn builtin(self) -> Builtin {
        match self {
            Native::Add => Builtin::Add,
            Native::Sub => Builtin::Sub,
            Native::Mul => Builtin::Mul,
            Native::Leq => Builtin::Leq,
            Native::EqNat => Builtin::EqNat,
            Native::DivFuel => Builtin::DivFuel,
            Native::DecEqNat => Builtin::DecEqNat,
            Native::EqNatRefl => Builtin::EqNatRefl,
            Native::EqNatSound => Builtin::EqNatSound,
        }
    }

    /// The name of the prelude definition this implements.
    pub fn name(self) -> &'static str {
        self.builtin().name()
    }

    pub fn arity(self) -> usize {
        match self {
            Native::DivFuel | Native::EqNatSound => 3,
            Native::EqNatRefl => 1,
            _ => 2,
        }
    }

    /// How many of the arguments are numbers: all of them except
    /// `eqNatSound`'s proof, which it never looks at.
    pub fn numbers(self) -> usize {
        match self {
            Native::EqNatSound => 2,
            _ => self.arity(),
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
    /// `natNeq : (m n : Nat) -> eqNat m n = False -> Not (m = n)`, which
    /// `decEqNat`'s definition puts in its `No`, and so the native does too.
    pub nat_neq: Option<DefId>,
    natives: HashMap<DefId, Native>,
    /// Off in tests that compare natives with their definitions.
    pub disable_natives: bool,
    /// `Delay` and its constants (`partial.rs`), once admitted.
    primitives: HashMap<DefId, Primitive>,
    /// `List` and `Char`, if they're the declarations the compact
    /// representation of text was written for (see [`crate::chars`]).
    pub text: Option<crate::chars::CompactText>,
    /// Text literals are elaborated as constructors, not compactly: for tests
    /// that compare the two. The kernel still accepts compact lists.
    pub disable_compact_text: bool,
}

impl Builtins {
    /// The definition admitted as `prim`, if it has been.
    pub fn primitive_id(&self, prim: Primitive) -> Option<DefId> {
        self.primitives
            .iter()
            .find(|(_, p)| **p == prim)
            .map(|(id, _)| *id)
    }

    /// Which primitive `id` is, if it's one.
    pub fn primitive(&self, id: DefId) -> Option<Primitive> {
        self.primitives.get(&id).copied()
    }

    pub(crate) fn register_primitive(&mut self, prim: Primitive, id: DefId) {
        self.primitives.insert(id, prim);
    }

    pub fn native(&self, id: DefId) -> Option<Native> {
        if self.disable_natives {
            return None;
        }
        self.natives.get(&id).copied()
    }

    /// The compact representation, if text literals should use it.
    pub fn compact_literals(&self) -> Option<&crate::chars::CompactText> {
        self.text.as_ref().filter(|_| !self.disable_compact_text)
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
    let ok = data.state == State::Final
        && data.params.is_empty()
        && data.indices.is_empty()
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
    if !(data.state == State::Final
        && data.params.is_empty()
        && data.indices.is_empty()
        && data.sort == Sort::Type(0)
        && data_sig(g, d) == [vec![], vec![]])
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
    // `No`'s field relies on `Void` being empty, so it must be final.
    let void = g.registry.data(Builtin::Void);
    let shaped = data.state == State::Final
        && data.params.len() == 1
        && data.indices.is_empty()
        && data.sort == Sort::Type(0)
        && data_sig(g, d) == [vec![0], vec![0]];
    let shaped = shaped
        && match void {
            None => false,
            Some(void) => {
                let params = [p.clone()];
                let yes = eval(g, &params, &data.ctors[0].fields[0].1)?;
                let no = eval(g, &params, &data.ctors[1].fields[0].1)?;
                let param = eval(g, &[], &data.params[0].1)?;
                let not_p = Value::Pi(
                    "h".into(),
                    Icit::Explicit,
                    Rc::new(p.clone()),
                    crate::value::Closure {
                        env: [p.clone()].into(),
                        body: Rc::new(Term::Data(void, Vec::new())),
                    },
                );
                conv(g, 0, &param, &Value::Sort(Sort::Prop))?
                    && conv(g, 1, &yes, &p)?
                    && conv(g, 1, &no, &not_p)?
            }
        };
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
    let (State::Final, Some(nat)) = (def.state, g.builtins.nat) else {
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
                Term::data(
                    dec,
                    vec![Term::Eq(
                        Some(Rc::new(nat_ty())),
                        Rc::new(Term::Var(1)),
                        Rc::new(Term::Var(0)),
                    )],
                )
            }),
        // (m : Nat) -> (n : Nat) -> eqNat m n = True -> m = n
        Native::EqNatSound => {
            g.builtins
                .bool
                .zip(native_def(g, Native::EqNat))
                .map(|(bool, eq_nat)| {
                    arrow(
                        Term::Eq(
                            Some(Rc::new(Term::Data(bool, Vec::new()))),
                            Rc::new(Term::app(
                                Term::app(Term::Def(eq_nat), Term::Var(1)),
                                Term::Var(0),
                            )),
                            Rc::new(Term::Ctor(bool, 1, Vec::new())),
                        ),
                        Term::Eq(
                            Some(Rc::new(nat_ty())),
                            Rc::new(Term::Var(2)),
                            Rc::new(Term::Var(1)),
                        ),
                    )
                })
        }
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
    for _ in 0..native.numbers() {
        expected = arrow(nat_ty(), expected);
    }
    if def.arity != native.arity() || !conv(g, 0, &eval(g, &[], &expected)?, &def.ty_value)? {
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
    let (State::Final, Some(nat), Some(bool), Some(eq_nat), Some(void)) = (
        def.state,
        g.builtins.nat,
        g.builtins.bool,
        native_def(g, Native::EqNat),
        g.registry.data(Builtin::Void),
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
    if def.arity != 4 || !conv(g, 0, &eval(g, &[], &expected)?, &def.ty_value)? {
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
            (1, [Value::NatAdd(k, base)]) => {
                return Value::NatAdd(Rc::new(&**k + 1u32), base.clone());
            }
            _ => {}
        }
    }
    Value::Ctor(d, c, fields.into())
}

/// A number as `k + base`: `Succ` applied `k` times to `base`. The base is
/// `None` for `Zero` (so it's the number `k`), or a value that isn't built
/// from numbers (usually stuck on a variable).
pub fn view(g: &Globals, value: &Value) -> budget::Result<(BigUint, Option<Value>)> {
    view_with(g, value, force)
}

/// How an evaluator replaces solved metavariables: each evaluator passes its
/// own, so the reference evaluator shares no evaluation code with the machine.
pub type Force = fn(&Globals, Value) -> budget::Result<Value>;

/// [`view`], forcing with `force`.
pub fn view_with(
    g: &Globals,
    value: &Value,
    force: Force,
) -> budget::Result<(BigUint, Option<Value>)> {
    let mut k = BigUint::zero();
    let mut value = force(g, value.clone())?;
    loop {
        match value {
            Value::Nat(n) => return Ok((k + &*n, None)),
            Value::NatAdd(n, base) => {
                k += &*n;
                value = force(g, (*base).clone())?;
            }
            Value::Ctor(d, 0, _) if Some(d) == g.builtins.nat => return Ok((k, None)),
            Value::Ctor(d, 1, fields) if Some(d) == g.builtins.nat && fields.len() == 1 => {
                k += 1u32;
                value = force(g, fields[0].clone())?;
            }
            other => return Ok((k, Some(other))),
        }
    }
}

/// The value for `k + base` (see [`view`]).
pub fn from_view(k: BigUint, base: Option<Value>) -> Value {
    match base {
        None => nat_value(k),
        Some(base) if k.is_zero() => base,
        Some(base) => Value::NatAdd(Rc::new(k), Rc::new(base)),
    }
}

/// Whether `value` is built from numbers: a number, `k + x`, `Zero` or `Succ`.
pub fn nat_like(g: &Globals, value: &Value) -> bool {
    match value {
        Value::Nat(_) | Value::NatAdd(..) => true,
        Value::Ctor(d, _, _) => Some(*d) == g.builtins.nat,
        _ => false,
    }
}

/// Compares two numbers by their `k + base` forms, after taking off the
/// `Succ`s they share. Two bases are compared with `same`. A base on its own
/// against anything else is handed to `assign`: never equal for conversion,
/// but the unifier can solve a metavariable there.
pub fn compare(
    g: &Globals,
    a: &Value,
    b: &Value,
    same: impl FnOnce(&Value, &Value) -> budget::Result<bool>,
    assign: impl FnOnce(&Value, &Value) -> budget::Result<bool>,
) -> budget::Result<bool> {
    compare_with(g, a, b, same, assign, force)
}

/// [`compare`], forcing with `force`.
pub fn compare_with(
    g: &Globals,
    a: &Value,
    b: &Value,
    same: impl FnOnce(&Value, &Value) -> budget::Result<bool>,
    assign: impl FnOnce(&Value, &Value) -> budget::Result<bool>,
    force: Force,
) -> budget::Result<bool> {
    let (k1, b1) = view_with(g, a, force)?;
    let (k2, b2) = view_with(g, b, force)?;
    let shared = k1.clone().min(k2.clone());
    let (k1, k2) = (k1 - &shared, k2 - &shared);
    match (b1, b2) {
        (None, None) => Ok(k1 == k2),
        (Some(x), Some(y)) if k1.is_zero() && k2.is_zero() => same(&x, &y),
        (Some(x), other) if k1.is_zero() => assign(&x, &from_view(k2, other)),
        (other, Some(y)) if k2.is_zero() => assign(&y, &from_view(k1, other)),
        _ => Ok(false),
    }
}

/// The term for `k + base`: `Succ base` when `k` is 1 (as proofs usually
/// write it), and otherwise an application of `add`.
pub fn nat_add_term(g: &Globals, k: &BigUint, base: Term) -> Term {
    if let Some(nat) = g.builtins.nat
        && *k == BigUint::from(1u32)
    {
        return Term::ctor(nat, 1, vec![base]);
    }
    match native_def(g, Native::Add) {
        Some(add) => Term::app(
            Term::app(Term::Def(add), Term::Nat(Rc::new(k.clone()))),
            base,
        ),
        None => {
            let nat = g.builtins.nat.expect("`k + x` values need `Nat`");
            let mut term = base;
            let mut i = BigUint::zero();
            while &i < k {
                term = Term::ctor(nat, 1, vec![term]);
                i += 1u32;
            }
            term
        }
    }
}

/// Matching on a number value: the constructor and its fields.
pub fn split_value(value: &Value) -> Option<(usize, Vec<Value>)> {
    match value {
        Value::Nat(n) => Some(split(n)),
        Value::NatAdd(k, base) => Some((1, vec![from_view(&**k - 1u32, Some((**base).clone()))])),
        _ => None,
    }
}

/// What a native implementation did.
pub enum Outcome {
    /// Computed the result.
    Done(Value),
    /// Took some steps of the definition at once, and the definition should
    /// now be applied to these arguments instead. (The evaluator does that
    /// itself, so a native never calls back into it.)
    Again(Vec<Elim>),
}

/// Shortcuts for numbers with unknowns in them, each a number of steps of
/// the definition taken at once.
fn run_partial(
    g: &Globals,
    id: DefId,
    native: Native,
    args: &[&Value],
    force: Force,
) -> budget::Result<Option<Outcome>> {
    let view = |v: &Value| view_with(g, v, force);
    let explicit = |v: Value| Elim::App(v, Icit::Explicit);
    match (native, args) {
        // `add (Succ m) n = Succ (add m n)`, so `add (k + m) n = k + add m n`.
        (Native::Add, [m, n]) => {
            let (k, base) = view(m)?;
            Ok(match base {
                None => {
                    let (k2, base2) = view(n)?;
                    Some(Outcome::Done(from_view(k + k2, base2)))
                }
                Some(_) if k.is_zero() => None,
                Some(base) => {
                    let stuck = Value::Neutral(
                        Head::Def(id),
                        vec![explicit(base), explicit((*n).clone())].into(),
                    );
                    Some(Outcome::Done(from_view(k, Some(stuck))))
                }
            })
        }
        // `op (Succ m) (Succ n) = op m n`: take off the shared `Succ`s.
        (Native::Sub | Native::Leq | Native::EqNat, [m, n]) => {
            let (k1, b1) = view(m)?;
            let (k2, b2) = view(n)?;
            let shared = k1.clone().min(k2.clone());
            if shared.is_zero() {
                return Ok(None);
            }
            Ok(Some(Outcome::Again(vec![
                explicit(from_view(k1 - &shared, b1)),
                explicit(from_view(k2 - &shared, b2)),
            ])))
        }
        // `eqNatRefl (Succ n) = eqNatRefl n`.
        (Native::EqNatRefl, [n]) => {
            let (k, base) = view(n)?;
            Ok(base
                .filter(|_| !k.is_zero())
                .map(|base| Outcome::Again(vec![explicit(base)])))
        }
        _ => Ok(None),
    }
}

pub fn as_nat(g: &Globals, value: &Value) -> budget::Result<Option<BigUint>> {
    as_nat_with(g, value, force)
}

/// [`as_nat`], forcing with `force`.
pub fn as_nat_with(g: &Globals, value: &Value, force: Force) -> budget::Result<Option<BigUint>> {
    let mut succs = 0u64;
    let mut value = force(g, value.clone())?;
    loop {
        match value {
            Value::Nat(n) => return Ok(Some(&*n + succs)),
            Value::Ctor(d, 0, _) if Some(d) == g.builtins.nat => {
                return Ok(Some(BigUint::from(succs)));
            }
            Value::Ctor(d, 1, fields) if Some(d) == g.builtins.nat && fields.len() == 1 => {
                succs += 1;
                value = force(g, fields[0].clone())?;
            }
            _ => return Ok(None),
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
    Some(Value::Ctor(g.builtins.bool?, b as usize, [].into()))
}

/// Runs a native implementation of definition `id`, if all its arguments
/// are numbers, or takes a shortcut for some numbers with unknowns in them.
pub fn run(
    g: &Globals,
    id: DefId,
    native: Native,
    spine: &[Elim],
    force: Force,
) -> budget::Result<Option<Outcome>> {
    let Some(values) = spine
        .iter()
        .map(|e| match e {
            Elim::App(v, Icit::Explicit) => Some(v),
            _ => None,
        })
        .collect::<Option<Vec<&Value>>>()
    else {
        return Ok(None);
    };
    let mut args = Vec::new();
    for v in values.iter().take(native.numbers()) {
        match as_nat_with(g, v, force)? {
            Some(n) => args.push(n),
            None => return run_partial(g, id, native, &values, force),
        }
    }
    Ok(run_numbers(g, native, &args).map(Outcome::Done))
}

/// A native implementation on numbers.
fn run_numbers(g: &Globals, native: Native, args: &[BigUint]) -> Option<Value> {
    let nat = |n: BigUint| Some(nat_value(n));
    match (native, args) {
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
        // When the numbers differ, the definition unfolds instead (to a proof
        // from `h`, which can only be a hypothesis).
        (Native::EqNatSound, [m, n]) => (m == n).then_some(Value::Refl),
        (Native::DecEqNat, [m, n]) => {
            let dec = g.builtins.decidable?;
            if m == n {
                Some(Value::Ctor(dec, 0, [Value::Refl].into()))
            } else {
                // `natNeq m n rfl`, as the definition's `False` case gives
                // (`eqNat m n` is `False`, so `h` is `rfl`). It's stuck until
                // it's given a proof of `m = n`, and there isn't one.
                let arg = |v| Elim::App(v, Icit::Explicit);
                let refutation = Value::Neutral(
                    Head::Def(g.builtins.nat_neq?),
                    vec![
                        arg(nat_value(m.clone())),
                        arg(nat_value(n.clone())),
                        arg(Value::Refl),
                    ]
                    .into(),
                );
                Some(Value::Ctor(dec, 1, [refutation].into()))
            }
        }
        _ => None,
    }
}
