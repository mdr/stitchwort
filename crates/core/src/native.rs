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

use crate::collections::HashMap;
use crate::ev::Ev;
use crate::machine::in_kernel_modes;
use std::rc::Rc;

use num_bigint::BigUint;
use num_traits::Zero;
use stitchwort_syntax::{Diagnostic, Span};

use crate::budget;
use crate::globals::{Kernel, State};
use crate::partial::Primitive;
use crate::registry::Builtin;
use crate::term::{DataId, DefId, Icit, Sort, Term};
use crate::value::{Elim, Head, Shared, Value, conv, eval, force};

/// A definition with a native implementation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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
    /// `eqNatRefl n : eqNat n n = True`, which is `rfl` for any number. Without
    /// this, a proof of `eqNat n n = True` would count down `n`.
    EqNatRefl,
    /// `eqNatSound m n h : m = n`, which is `rfl` when `m` and `n` are the same
    /// number, whatever `h` is. Without this, transporting along a decided
    /// equation (`Nat.decEq m n`'s `sound`) would count down its arguments.
    EqNatSound,
}

impl Native {
    pub const ALL: [Native; 8] = [
        Native::Add,
        Native::Sub,
        Native::Mul,
        Native::Leq,
        Native::EqNat,
        Native::DivFuel,
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
    natives: HashMap<DefId, Native>,
    /// The same registrations the other way round: each native is
    /// registered at most once.
    native_defs: HashMap<Native, DefId>,
    /// `Nat.add`, once R3 and R4 (`nat_add.rs`: `+` computes on its second
    /// argument too) are switched on for it. Not a native: switching the
    /// natives off doesn't switch it off.
    pub nat_add_rule: Option<DefId>,
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
    /// The library's `Float` and the theorems a float native refers to
    /// (`float.rs`), once bound.
    pub float: crate::float::FloatBinding,
    /// The float primitives and the definitions with float natives.
    pub(crate) float_defs: HashMap<DefId, crate::float::FloatDef>,
    /// Off in tests that compare the float natives with their definitions
    /// while the number natives stay on (`disable_natives` turns both off).
    /// The float primitives' reduction rule is never off.
    pub disable_float_natives: bool,
    /// The float natives fire outside a running program too: only for the
    /// float gate, which compares them with their definitions as terms
    /// after its program is checked. Never set while anything is checked.
    pub float_natives_outside_runs: bool,
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

    /// What the evaluator computes for float definition `id`: a primitive
    /// always; a native only while a program `running`, and unless natives
    /// are off. Checking computes the natives' definitions.
    #[inline]
    pub fn float_def(&self, id: DefId, running: bool) -> Option<crate::float::FloatDef> {
        if self.float_defs.is_empty() {
            return None;
        }
        match self.float_defs.get(&id).copied()? {
            crate::float::FloatDef::Native(_)
                if self.disable_natives
                    || self.disable_float_natives
                    || !(running || self.float_natives_outside_runs) =>
            {
                None
            }
            def => Some(def),
        }
    }

    /// Whether `id` is a float primitive or has a float native.
    pub fn float_bound(&self, id: DefId) -> bool {
        self.float_defs.contains_key(&id)
    }

    /// Which float primitive `id` is, if it's one.
    pub fn float_primitive(&self, id: DefId) -> Option<crate::float::FloatOp> {
        match self.float_defs.get(&id)? {
            crate::float::FloatDef::Primitive(op) => Some(*op),
            crate::float::FloatDef::Native(_) => None,
        }
    }

    /// Which float native `id` has, if any, whether or not natives are on:
    /// for the runtimes, which bind their own implementations to it.
    pub fn float_native(&self, id: DefId) -> Option<crate::float::FloatNative> {
        match self.float_defs.get(&id)? {
            crate::float::FloatDef::Native(n) => Some(*n),
            crate::float::FloatDef::Primitive(_) => None,
        }
    }

    /// Whether `id` has a native implementation, a number one or a float
    /// one, whatever the switches say: a property of the definition, which
    /// record eta's rule 2 depends on ([`crate::value::eta_held`]), so
    /// conversion is the same with natives on and off.
    pub fn has_native(&self, id: DefId) -> bool {
        self.natives.contains_key(&id) || self.float_native(id).is_some()
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

    /// What [`Builtins::rewind`] puts back. Every field is named, so a new
    /// one has to say how it is undone.
    pub(crate) fn mark(&self) -> BuiltinsMark {
        let Builtins {
            nat,
            bool,
            // Keyed by definition: cut by id.
            natives: _,
            native_defs: _,
            primitives: _,
            float_defs: _,
            nat_add_rule,
            text,
            float,
            // Settings.
            disable_natives: _,
            disable_compact_text: _,
            disable_float_natives: _,
            float_natives_outside_runs: _,
        } = self;
        BuiltinsMark {
            nat: *nat,
            bool: *bool,
            nat_add_rule: *nat_add_rule,
            text: text.clone(),
            float: float.clone(),
        }
    }

    /// Forgets what was registered since `mark`, when the definitions from
    /// `defs` on are removed again ([`crate::Kernel::forget_since`]). The
    /// switches (`disable_*`) are settings, and stay as they are.
    pub(crate) fn rewind(&mut self, mark: &BuiltinsMark, defs: usize) {
        let Builtins {
            nat,
            bool,
            natives,
            native_defs,
            primitives,
            float_defs,
            nat_add_rule,
            text,
            float,
            disable_natives: _,
            disable_compact_text: _,
            disable_float_natives: _,
            float_natives_outside_runs: _,
        } = self;
        natives.retain(|id, _| id.0 < defs);
        native_defs.retain(|_, id| id.0 < defs);
        primitives.retain(|id, _| id.0 < defs);
        float_defs.retain(|id, _| id.0 < defs);
        let BuiltinsMark {
            nat: was_nat,
            bool: was_bool,
            nat_add_rule: was_nat_add_rule,
            text: was_text,
            float: was_float,
        } = mark.clone();
        *nat = was_nat;
        *bool = was_bool;
        *nat_add_rule = was_nat_add_rule;
        *text = was_text;
        *float = was_float;
    }

    /// Every field, as text, in an order that doesn't depend on hashing:
    /// for the check cache's canonical dump and for checking an undo
    /// ([`crate::Kernel::bindings_dump`]). Every field is named, so a new
    /// one isn't printed only if it says why.
    pub fn dump(&self, out: &mut String) {
        use std::fmt::Write;
        let Builtins {
            nat,
            bool,
            natives,
            native_defs,
            primitives,
            float_defs,
            nat_add_rule,
            text,
            float,
            disable_natives,
            disable_compact_text,
            disable_float_natives,
            float_natives_outside_runs,
        } = self;
        let _ = writeln!(
            out,
            "builtins nat {nat:?} bool {bool:?} nat_add_rule {nat_add_rule:?}"
        );
        // `small` is made from the two, so it isn't printed.
        let text = text.as_ref().map(|t| (t.list, t.char));
        let _ = writeln!(out, "builtins text {text:?} float {float:?}");
        let _ = writeln!(
            out,
            "builtins off natives {disable_natives} compact_text {disable_compact_text} \
             float_natives {disable_float_natives} float_outside_runs {float_natives_outside_runs}"
        );
        let mut sorted: Vec<_> = natives.iter().map(|(id, n)| (id.0, *n)).collect();
        sorted.sort_by_key(|(id, _)| *id);
        for (id, n) in sorted {
            let _ = writeln!(out, "native {} = def {id}", n.name());
        }
        let mut sorted: Vec<_> = native_defs.iter().map(|(n, id)| (id.0, *n)).collect();
        sorted.sort_by_key(|(id, _)| *id);
        for (id, n) in sorted {
            let _ = writeln!(out, "native_def {} = def {id}", n.name());
        }
        let mut sorted: Vec<_> = primitives.iter().map(|(id, p)| (id.0, *p)).collect();
        sorted.sort_by_key(|(id, _)| *id);
        for (id, p) in sorted {
            let _ = writeln!(out, "primitive {p:?} = def {id}");
        }
        let mut sorted: Vec<_> = float_defs.iter().map(|(id, f)| (id.0, *f)).collect();
        sorted.sort_by_key(|(id, _)| *id);
        for (id, f) in sorted {
            let _ = writeln!(out, "float {f:?} = def {id}");
        }
    }
}

/// The registrations of [`Builtins`] at a [`crate::globals::KernelMark`].
#[derive(Clone)]
pub(crate) struct BuiltinsMark {
    nat: Option<DataId>,
    bool: Option<DataId>,
    nat_add_rule: Option<DefId>,
    text: Option<crate::chars::CompactText>,
    float: crate::float::FloatBinding,
}

type Result<T> = std::result::Result<T, Diagnostic>;

fn shape_error(span: Span, what: &str) -> Diagnostic {
    Diagnostic::error(
        "E-BUILTIN",
        format!("the prelude's `{what}` doesn't have the shape the compiler expects"),
    )
    .with_label(span, "here")
}

fn data_sig(g: &Ev, d: DataId) -> Vec<Vec<usize>> {
    g.data(d)
        .ctors
        .iter()
        .map(|c| c.fields.iter().map(|_| 0).collect())
        .collect()
}

/// Registers `Nat`, which must be `Zero | Succ Nat` with no parameters.
pub fn register_nat(g: &mut Kernel, d: DataId) -> Result<()> {
    in_kernel_modes(g, |g| {
        let data = g.data(d);
        let ok = data.state == State::Final
            && data.params.is_empty()
            && data.indices.is_empty()
            && data.sort == Sort::Type(0)
            && data_sig(&g.ev(), d) == [vec![], vec![0]]
            && matches!(&data.ctors[1].fields[0].1.strip_loc(), Term::Data(d2, args) if *d2 == d && args.is_empty());
        if !ok {
            return Err(shape_error(data.span, "Nat"));
        }
        g.env.builtins_mut().nat = Some(d);
        Ok(())
    })
}

/// Registers `Bool`, which must be two constructors without fields.
pub fn register_bool(g: &mut Kernel, d: DataId) -> Result<()> {
    in_kernel_modes(g, |g| {
        let data = g.data(d);
        if !(data.state == State::Final
            && data.params.is_empty()
            && data.indices.is_empty()
            && data.sort == Sort::Type(0)
            && data_sig(&g.ev(), d) == [vec![], vec![]])
        {
            return Err(shape_error(data.span, "Bool"));
        }
        g.env.builtins_mut().bool = Some(d);
        Ok(())
    })
}

/// Registers a native implementation for definition `id`, after checking
/// that it is the declaration the native was written for ([`crate::pins`])
/// and its type. Natives returning `Bool` need it registered first. Each native is registered once, and each definition
/// has at most one.
pub fn register_native(g: &mut Kernel, id: DefId, native: Native) -> Result<()> {
    in_kernel_modes(g, |g| {
        crate::pins::check_def(&g.ev(), id, native.builtin())?;
        register_shaped(g, id, native)
    })
}

/// [`register_native`] without the pin: for core's own tests, which build
/// a `Nat.add` of their own.
#[cfg(feature = "test-bypass")]
#[doc(hidden)]
pub fn register_native_unpinned(g: &mut Kernel, id: DefId, native: Native) -> Result<()> {
    in_kernel_modes(g, |g| register_shaped(g, id, native))
}

/// The rest of [`register_native`], in kernel modes: the type, and that
/// neither `id` nor `native` is registered already.
fn register_shaped(g: &mut Kernel, id: DefId, native: Native) -> Result<()> {
    let def = g.def(id);
    let span = def.span;
    let (State::Final, Some(nat)) = (def.state, g.env.builtins().nat) else {
        return Err(shape_error(span, native.name()));
    };
    // An open goal's assumption never computes, by a native or otherwise.
    if def.assumption().is_some() {
        return Err(shape_error(span, native.name()));
    }
    let nat_ty = || Term::Data(nat, Vec::new());
    let arrow =
        |dom: Term, cod: Term| Term::Pi("x".into(), Icit::Explicit, Rc::new(dom), Rc::new(cod));
    let result = match native {
        Native::Add | Native::Sub | Native::Mul | Native::DivFuel => Some(nat_ty()),
        Native::Leq | Native::EqNat => g.env.builtins().bool.map(|b| Term::Data(b, Vec::new())),
        // (m : Nat) -> (n : Nat) -> eqNat m n = True -> m = n
        Native::EqNatSound => g
            .env
            .builtins()
            .bool
            .zip(native_def(&g.ev(), Native::EqNat))
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
            }),
        // (n : Nat) -> eqNat n n = True
        Native::EqNatRefl => g
            .env
            .builtins()
            .bool
            .zip(native_def(&g.ev(), Native::EqNat))
            .map(|(bool, eq_nat)| {
                Term::Eq(
                    Some(Rc::new(Term::Data(bool, Vec::new()))),
                    Rc::new(Term::app(
                        Term::app(Term::Def(eq_nat), Term::Var(0)),
                        Term::Var(0),
                    )),
                    Rc::new(Term::Ctor(bool, 1, Vec::new())),
                )
            }),
    };
    let Some(mut expected) = result else {
        return Err(shape_error(span, native.name()));
    };
    for _ in 0..native.numbers() {
        expected = arrow(nat_ty(), expected);
    }
    if def.arity != native.arity()
        || !conv(&g.ev(), 0, &eval(&g.ev(), &[], &expected)?, &def.ty_value)?
    {
        return Err(shape_error(span, native.name()));
    }
    let builtins = g.env.builtins();
    let second = if let Some(have) = builtins.natives.get(&id) {
        format!(
            "`{}` is bound to `{}` already",
            g.def(id).name(),
            have.name()
        )
    } else if builtins.native_defs.contains_key(&native) {
        format!("`{}` is bound to a definition already", native.name())
    } else {
        String::new()
    };
    if !second.is_empty() {
        return Err(Diagnostic::error("E-BUILTIN", second).with_label(span, "a second binding"));
    }
    let builtins = g.env.builtins_mut();
    builtins.natives.insert(id, native);
    builtins.native_defs.insert(native, id);
    Ok(())
}

/// The definition registered with native implementation `native`.
fn native_def(g: &Ev, native: Native) -> Option<DefId> {
    g.env.builtins().native_defs.get(&native).copied()
}

/// A number value. `Zero` and `Succ` of a number are numbers too.
pub fn nat_value(n: BigUint) -> Value {
    Value::Nat(Rc::new(n))
}

/// Builds a constructor value, keeping numbers compact.
pub fn ctor(g: &Ev, d: DataId, c: usize, fields: Vec<Value>) -> Value {
    if Some(d) == g.env.builtins().nat {
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
pub fn view(g: &Ev, value: &Value) -> budget::Result<(BigUint, Option<Value>)> {
    view_with(g, value, force)
}

/// How an evaluator replaces solved metavariables: each evaluator passes its
/// own, so the reference evaluator shares no evaluation code with the machine.
pub type Force = fn(&Ev, Value) -> budget::Result<Value>;

/// [`view`], forcing with `force`.
pub fn view_with(g: &Ev, value: &Value, force: Force) -> budget::Result<(BigUint, Option<Value>)> {
    let mut k = BigUint::zero();
    let mut value = force(g, value.clone())?;
    loop {
        match value {
            Value::Nat(n) => return Ok((k + &*n, None)),
            Value::NatAdd(n, base) => {
                k += &*n;
                value = force(g, (*base).clone())?;
            }
            Value::Ctor(d, 0, _) if Some(d) == g.env.builtins().nat => return Ok((k, None)),
            Value::Ctor(d, 1, fields) if Some(d) == g.env.builtins().nat && fields.len() == 1 => {
                k += 1u32;
                value = force(g, fields[0].clone())?;
            }
            other => return Ok((k, Some(other))),
        }
    }
}

/// [`view_with`], but with the base as it was before forcing: as a case
/// tree that peels the `Succ`s binds it, so a glued call in it stays the
/// call. `None` for a number, as there.
fn view_keeping(g: &Ev, value: &Value, force: Force) -> budget::Result<(BigUint, Option<Value>)> {
    let mut k = BigUint::zero();
    let mut unforced = value.clone();
    let mut value = force(g, unforced.clone())?;
    loop {
        let next = match &value {
            Value::Nat(n) => return Ok((k + &**n, None)),
            Value::NatAdd(n, base) => {
                k += &**n;
                (**base).clone()
            }
            Value::Ctor(d, 0, _) if Some(*d) == g.env.builtins().nat => return Ok((k, None)),
            Value::Ctor(d, 1, fields) if Some(*d) == g.env.builtins().nat && fields.len() == 1 => {
                k += 1u32;
                fields[0].clone()
            }
            _ => return Ok((k, Some(unforced))),
        };
        value = force(g, next.clone())?;
        unforced = next;
    }
}

/// The value for `k + base` (see [`view`]).
pub fn from_view(k: BigUint, base: Option<Value>) -> Value {
    match base {
        None => nat_value(k),
        Some(base) if k.is_zero() => base,
        Some(base) => Value::NatAdd(Rc::new(k), Shared::new(base)),
    }
}

/// Whether `mul k x`, for a number `k > 0` and an `x` that is a variable
/// (applied to anything), stays folded as the call while checking (SW-321).
/// Its definition recurses on `k`, so unfolding it all gives
/// `x + (x + … + 0)` with `k` additions, each stuck on `x`: millions of
/// steps for `100000 * x`, deep enough to overflow the stack when dropped.
/// Folded, it's what dictionaries and theorems are (`value::is_folded`):
/// taking it apart or comparing it with anything but `mul k x'` unfolds one
/// step, to `add x (mul (k - 1) x)`, which is stuck on `x` too, so it's
/// never a number, a `Succ` or a constructor. What's equal doesn't change,
/// only when it's computed. Not while a program runs, nor with natives off.
pub fn folds_mul(g: &Ev, id: DefId, spine: &[Elim]) -> bool {
    match spine {
        [
            Elim::App(Value::Nat(k), _),
            Elim::App(Value::Neutral(Head::Var(..), _), _),
        ] => {
            !k.is_zero()
                && g.env.builtins().native(id) == Some(Native::Mul)
                && !g.machine.erasure.program_running()
        }
        _ => false,
    }
}

/// Whether `value` is built from numbers: a number, `k + x`, `Zero` or `Succ`.
pub fn nat_like(g: &Ev, value: &Value) -> bool {
    match value {
        Value::Nat(_) | Value::NatAdd(..) => true,
        Value::Ctor(d, _, _) => Some(*d) == g.env.builtins().nat,
        _ => false,
    }
}

/// Compares two numbers by their `k + base` forms, after taking off the
/// `Succ`s they share. Two bases are compared with `same`. A base on its own
/// against anything else is handed to `assign`: the unifier can solve a
/// metavariable there, and a folded call there (`Succ (f 0)` against `2`)
/// is unfolded and compared again; anything else is never equal.
pub fn compare(
    g: &Ev,
    a: &Value,
    b: &Value,
    same: impl FnOnce(&Value, &Value) -> budget::Result<bool>,
    assign: impl FnOnce(&Value, &Value) -> budget::Result<bool>,
) -> budget::Result<bool> {
    compare_with(g, a, b, same, assign, force)
}

/// [`compare`], forcing with `force`.
pub fn compare_with(
    g: &Ev,
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

/// [`compare`] for conversion, looking inside glued calls ([`Value::Call`])
/// only as far as it must (SW-1153).
///
/// [`view`] forces every `Succ`'s field, so a number whose `Succ`s are
/// glued calls is computed in full: `Succ (length xs)` against `length (Cons
/// 'a' xs)` (one unfolded a step, the other not) counted the whole of `xs`
/// on both sides, though once the other side is unfolded a step too, both
/// are `Succ` of the same call. This takes off `Succ`s up to a call on each
/// side and unfolds a call only while that leaves the two different: when
/// one side has more `Succ`s, or one has reached a number or a stuck value
/// and the other a call. Two bases left over with no `Succ`s on either side
/// are handed to `same`, a call included, which [`crate::value::conv`]
/// compares as it does any call: by its arguments first if the other is a
/// call of the same definition, and otherwise unfolded.
///
/// It answers as [`compare`] does with the same `assign`. Unfolding a call
/// gives its value, so the `Succ`s counted and the bases reached are
/// [`compare`]'s whenever this unfolds every call; it stops early only by
/// handing `same` two bases with no `Succ`s on either side, and those are
/// equal exactly when their values, the bases and counts [`compare`] would
/// reach, are (the same counts on both sides: none here, and then equal
/// bases, or equal numbers); or by handing `assign` a base that isn't a
/// call against the other side with its calls still in, which is equal
/// exactly when it is with them unfolded. Only the work differs: a call is
/// compared by its arguments, which only answers "equal" where unfolding
/// would too (`CallMemo` in value.rs).
pub fn compare_lazily(
    g: &Ev,
    a: &Value,
    b: &Value,
    same: impl FnOnce(&Value, &Value) -> budget::Result<bool>,
    assign: impl FnOnce(&Value, &Value) -> budget::Result<bool>,
) -> budget::Result<bool> {
    let (mut k1, mut b1) = view_to_call(g, a.clone(), BigUint::zero())?;
    let (mut k2, mut b2) = view_to_call(g, b.clone(), BigUint::zero())?;
    loop {
        let shared = k1.clone().min(k2.clone());
        k1 -= &shared;
        k2 -= &shared;
        let call = |b: &Option<Value>| matches!(b, Some(Value::Call(..)));
        // Which side to unfold a step: one with no `Succ`s left whose base
        // is a call, when the other has `Succ`s left or is a number. A
        // base that isn't a call, with no `Succ`s left, goes to `assign`
        // as in `compare`; a side with `Succ`s left against a number with
        // none can't be equal to it.
        let unfold_first = match (&b1, &b2) {
            (Some(x), Some(y)) if k1.is_zero() && k2.is_zero() => return same(x, y),
            (None, None) => return Ok(k1 == k2),
            _ if k1.is_zero() && call(&b1) => true,
            _ if k2.is_zero() && call(&b2) => false,
            (Some(x), other) if k1.is_zero() => {
                return assign(x, &from_view(k2.clone(), other.clone()));
            }
            (other, Some(y)) if k2.is_zero() => {
                return assign(y, &from_view(k1.clone(), other.clone()));
            }
            _ => return Ok(false),
        };
        if unfold_first {
            let x = force(g, b1.take().expect("a call"))?;
            (k1, b1) = view_to_call(g, x, k1)?;
        } else {
            let y = force(g, b2.take().expect("a call"))?;
            (k2, b2) = view_to_call(g, y, k2)?;
        }
    }
}

/// [`view`] from `k` `Succ`s on, stopping at a glued call rather than
/// unfolding it.
fn view_to_call(g: &Ev, value: Value, mut k: BigUint) -> budget::Result<(BigUint, Option<Value>)> {
    let mut value = value;
    loop {
        if !matches!(value, Value::Call(..)) {
            value = force(g, value)?;
        }
        match value {
            Value::Nat(n) => return Ok((k + &*n, None)),
            Value::NatAdd(n, base) => {
                k += &*n;
                value = (*base).clone();
            }
            Value::Ctor(d, 0, _) if Some(d) == g.env.builtins().nat => return Ok((k, None)),
            Value::Ctor(d, 1, fields) if Some(d) == g.env.builtins().nat && fields.len() == 1 => {
                k += 1u32;
                value = fields[0].clone();
            }
            other => return Ok((k, Some(other))),
        }
    }
}

/// The term for `k + base` shown to a person (SW-895): `base + k`, with the
/// number on the right as sums are usually written, `x + 1` included. Only
/// for printing ([`crate::value::quote_shown`],
/// [`crate::value::quote_unfolded_shown`]): the term is convertible with
/// [`nat_add_term`]'s but not the same, so it never goes into an elaborated
/// term, a hash or a comparison.
///
/// A `k + base` value comes from arithmetic: `+` (R2 or R4 of
/// docs/proposals/nat-add-recursion.md, on either side), `Succ` of such a
/// sum, or a native taking shared `Succ`s off one. `Succ x` written in the
/// source or a pattern, with `x` not a number or a sum, stays a constructor
/// value ([`ctor`] only compacts `Succ` of a number or a sum) and is shown
/// as `Succ x`.
pub fn nat_add_shown(g: &Ev, k: &BigUint, base: Term) -> Term {
    match native_def(g, Native::Add) {
        Some(add) => Term::app(
            Term::app(Term::Def(add), base),
            Term::Nat(Rc::new(k.clone())),
        ),
        None => nat_add_term(g, k, base),
    }
}

/// The term for `k + base`: `Succ base` when `k` is 1 (as proofs usually
/// write it), and otherwise an application of `add`.
pub fn nat_add_term(g: &Ev, k: &BigUint, base: Term) -> Term {
    if let Some(nat) = g.env.builtins().nat
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
            let nat = g.env.builtins().nat.expect("`k + x` values need `Nat`");
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
    /// A number of `Succ`s the result starts with (`k`), and the definition
    /// applied to these arguments for what is left. The result is `k` more
    /// than that: the evaluator adds them once it has it, so a rest that
    /// still computes is never left as a call that has to be unfolded.
    Succs(BigUint, Vec<Elim>),
}

/// Shortcuts for numbers with unknowns in them, each a number of steps of
/// the definition taken at once.
///
/// Never inlined, nor is [`run_numbers`]: [`run`] is on the Rust stack once
/// for each nested native call it forces an argument of (`Nat.pow 2 280` is
/// 280 of them), and only its loop over the arguments needs to be in that
/// frame. Inlined, these two made it 304 bytes of WebAssembly stack, and
/// the float gate's `Float.toInt 1e100` ran out of the playground's 256 KiB.
#[inline(never)]
fn run_partial(
    g: &Ev,
    id: DefId,
    native: Native,
    args: &[&Value],
    force: Force,
) -> budget::Result<Option<Outcome>> {
    let view = |v: &Value| view_with(g, v, force);
    let explicit = |v: Value| Elim::App(v, Icit::Explicit);
    match (native, args) {
        // `add (Succ m) n = Succ (add m n)`, so `add (k + m) n = k + add m n`;
        // and then `add m n`, stuck on `m`, is what R3 and R4 make of it
        // (`nat_add.rs`), if they're on.
        (Native::Add, [m, n]) => {
            let (k, base) = view(m)?;
            Ok(match base {
                None => {
                    let (k2, base2) = view(n)?;
                    Some(Outcome::Done(from_view(k + k2, base2)))
                }
                // The case tree gets stuck, and the evaluator applies R3
                // and R4 there.
                Some(_) if k.is_zero() => None,
                Some(base) => Some(Outcome::Done(
                    match crate::nat_add::stuck(g, id, &base, n, force)? {
                        Some((k2, rest)) => from_view(k + k2, Some(rest)),
                        None => from_view(k, Some(crate::nat_add::call(id, base, (*n).clone()))),
                    },
                )),
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
        // `mul (Succ m) n = n + mul m n`, so for a number `n`,
        // `mul (k + m) n = k·n + mul m n`, stuck on `m`: what `k` steps of the
        // case tree and `add`'s native make of it, in one step. One step at
        // a time, each would walk the rest of a chain of `k` `Succ`s to find
        // it isn't a number, which is quadratic in `k`: `(x + 16000) % 2`
        // multiplies a quotient of 8000 `Succ`s around a stuck step (SW-2572).
        // `m`'s head is looked at first: with no `Succ` there the case tree
        // is stuck on `m` and never looks at `n`, so neither may this. Then
        // `n`, so that a `y` that isn't a number leaves the chain unwalked
        // (the case tree then peels it one `Succ` a step).
        (Native::Mul, [m, n]) => {
            let starts_with_succ = match force(g, (*m).clone())? {
                Value::NatAdd(..) => true,
                Value::Ctor(d, 1, _) => Some(d) == g.env.builtins().nat,
                _ => false,
            };
            if !starts_with_succ {
                return Ok(None);
            }
            let Some(times) = as_nat_with(g, n, force)? else {
                return Ok(None);
            };
            let (k, base) = view_keeping(g, m, force)?;
            let Some(base) = base.filter(|_| !k.is_zero()) else {
                return Ok(None);
            };
            g.machine
                .budget
                .number_words(|| number_words(Native::Mul, &[k.clone(), times.clone()]))?;
            Ok(Some(Outcome::Done(from_view(
                k * times,
                Some(Value::Neutral(
                    Head::Def(id),
                    vec![explicit(base), explicit((*n).clone())].into(),
                )),
            ))))
        }
        // `divFuel (Succ f) n d = Succ (divFuel f (n - d) d)` while `d ≤ n`, so
        // for a number `d > 0`, `q = min(kf, k / d)` steps are all `Succ`s:
        // `divFuel (kf + f) (k + m) d = q + divFuel ((kf - q) + f) ((k - q·d) + m) d`.
        // One step at a time, `(x + 2^128) / 2` would take 2^127 of them.
        // As with `Mul`, the fuel's head is looked at first: with no `Succ`
        // the case tree is stuck on it and never looks at `n` or `d`.
        (Native::DivFuel, [fuel, n, d]) => {
            let (kf, fuel_base) = view(fuel)?;
            if kf.is_zero() {
                return Ok(None);
            }
            let Some(divisor) = as_nat_with(g, d, force)?.filter(|d| !d.is_zero()) else {
                return Ok(None);
            };
            let (k, n_base) = view(n)?;
            let q = (&k / &divisor).min(kf.clone());
            if q.is_zero() {
                return Ok(None);
            }
            Ok(Some(Outcome::Succs(
                q.clone(),
                vec![
                    explicit(from_view(&kf - &q, fuel_base)),
                    explicit(from_view(&k - &q * &divisor, n_base)),
                    explicit((*d).clone()),
                ],
            )))
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

/// Whether forced `value` may be a number: it's one, `Zero` or a `Succ`.
fn number_head(g: &Ev, value: &Value) -> bool {
    match value {
        Value::Nat(_) => true,
        Value::Ctor(d, c, _) => Some(*d) == g.env.builtins().nat && *c <= 1,
        _ => false,
    }
}

pub fn as_nat(g: &Ev, value: &Value) -> budget::Result<Option<BigUint>> {
    as_nat_with(g, value, force)
}

/// [`as_nat`], forcing with `force`.
pub fn as_nat_with(g: &Ev, value: &Value, force: Force) -> budget::Result<Option<BigUint>> {
    let mut succs = 0u64;
    let mut value = force(g, value.clone())?;
    loop {
        match value {
            Value::Nat(n) => return Ok(Some(&*n + succs)),
            Value::Ctor(d, 0, _) if Some(d) == g.env.builtins().nat => {
                return Ok(Some(BigUint::from(succs)));
            }
            Value::Ctor(d, 1, fields) if Some(d) == g.env.builtins().nat && fields.len() == 1 => {
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

fn bool_value(g: &Ev, b: bool) -> Option<Value> {
    Some(Value::Ctor(g.env.builtins().bool?, b as usize, [].into()))
}

/// Runs a native implementation of definition `id`, if all its arguments
/// are numbers, or takes a shortcut for some numbers with unknowns in them.
pub fn run(
    g: &Ev,
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
    // An argument whose head is plainly no number (neither a number nor
    // `Zero` or `Succ`) settles it before a chain of `Succ`s in another is
    // walked: a recursion peeling one `Succ` a step, as `(k + m) * y` does
    // for an unknown `y`, would otherwise walk the rest of the chain at
    // every step, which is quadratic in `k` (SW-2572). The forced heads
    // aren't kept, so this frame stays small (see `run_partial`): forcing
    // again finds a call's kept unfolding.
    for v in values.iter().take(native.numbers()) {
        if !number_head(g, &force(g, (*v).clone())?) {
            return run_partial(g, id, native, &values, force);
        }
    }
    let mut args = Vec::new();
    for v in values.iter().take(native.numbers()) {
        match as_nat_with(g, v, force)? {
            Some(n) => args.push(n),
            None => return run_partial(g, id, native, &values, force),
        }
    }
    // Charged before the work is done, when it counts.
    g.machine
        .budget
        .number_words(|| number_words(native, &args))?;
    Ok(run_numbers(g, native, &args).map(Outcome::Done))
}

/// The steps a native operation on numbers costs beyond its own when an
/// operation on big numbers counts their words
/// ([`crate::budget::Budget::count_number_words`]): none unless a number
/// is past a machine word; then the product of the operands' words for a
/// multiplication or a division (schoolbook's bound), and the sum of the
/// numbers' words for anything else. The fast runtime counts the same
/// (`stitchwort_rt::prims::number_cost`).
pub fn number_words(native: Native, args: &[BigUint]) -> u64 {
    if args.iter().all(|n| n.bits() <= 64) {
        return 0;
    }
    let words = |n: &BigUint| n.bits().div_ceil(64).max(1);
    match (native, args) {
        (Native::Mul, [m, n]) | (Native::DivFuel, [_, m, n]) => words(m).saturating_mul(words(n)),
        _ => args.iter().map(words).fold(0, u64::saturating_add),
    }
}

/// A native implementation on numbers. Never inlined (see [`run_partial`]).
#[inline(never)]
fn run_numbers(g: &Ev, native: Native, args: &[BigUint]) -> Option<Value> {
    let nat = |n: BigUint| Some(nat_value(n));
    match (native, args) {
        (Native::Add, [m, n]) => nat(m + n),
        (Native::Sub, [m, n]) => nat(if m >= n { m - n } else { BigUint::zero() }),
        (Native::Mul, [m, n]) => nat(m * n),
        (Native::Leq, [m, n]) => bool_value(g, m <= n),
        (Native::EqNat, [m, n]) => bool_value(g, m == n),
        (Native::DivFuel, [fuel, n, d]) => nat(if d.is_zero() {
            BigUint::zero()
        } else {
            fuel.min(&(n / d)).clone()
        }),
        (Native::EqNatRefl, [_]) => Some(Value::Refl),
        // When the numbers differ, the definition unfolds instead (to a proof
        // from `h`, which can only be a hypothesis).
        (Native::EqNatSound, [m, n]) => (m == n).then_some(Value::Refl),
        _ => None,
    }
}
