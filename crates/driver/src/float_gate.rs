//! The first gate of `Float`'s stage 1a (docs/proposals/float.md §3.4, D731):
//! the kernel's float natives agree with the definitions they replace as
//! whole terms, proofs included, and the primitives' results are the same
//! records the literal elaborator builds.
//!
//! Each check runs in a fresh session per mode of evaluation ([`Mode`]), and
//! compares normal forms (terms read back from values), never just `.bits`
//! or a `DecEq` answer, which would hide a difference in a proof field. The
//! same normal forms are then compared across the modes. It lives here,
//! rather than in a test, so the browser playground's WebAssembly build can
//! run it too (`stitchwort_web::float_gate`): the gate is to pass on both
//! kernels.

use stitchwort_core::float::{self, FloatNative};
use stitchwort_core::native::nat_value;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{apply, eval, quote};
use stitchwort_core::{DefId, Globals, Limits, Term, Value};

use crate::driver::Session;

/// Which natives the kernel uses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// Every native on: how programs are checked.
    NativesOn,
    /// The float natives off, the number natives on: the float definitions
    /// unfold, and compute on their bits with the number natives.
    FloatNativesOff,
    /// Every native off (the test cache's `n0` mode).
    AllNativesOff,
}

impl Mode {
    pub fn name(self) -> &'static str {
        match self {
            Mode::NativesOn => "natives on",
            Mode::FloatNativesOff => "float natives off",
            Mode::AllNativesOff => "all natives off",
        }
    }
}

/// The program the checks are about. Its theorems are §3.4's `rfl` rows,
/// checked by the kernel as the program loads; its definitions are the
/// terms whose normal forms are compared.
pub const PROGRAM: &str = r#"import Std (Float)

theorem sumHalves: 0.5 + 0.25 = 0.75 := rfl
theorem sumTenths: 0.1 + 0.2 = 0.30000000000000004 := rfl
theorem plusNegative: 0.0 + (-1.0) = -1.0 := rfl
theorem minusToNegative: 1.0 - 2.0 = -1.0 := rfl
theorem negNegLiteral: Float.neg (Float.neg 1.5) = 1.5 := rfl
theorem negNaN: Float.neg Float.nan = Float.nan := rfl
theorem negNegAny (x: Float): Float.neg (Float.neg x) = x := Float.negNeg x

def sumHalvesLeft: Float := 0.5 + 0.25
def sumHalvesRight: Float := 0.75
def sumTenthsLeft: Float := 0.1 + 0.2
def sumTenthsRight: Float := 0.30000000000000004
def plusNegativeLeft: Float := 0.0 + (-1.0)
def minusToNegativeLeft: Float := 1.0 - 2.0
def negativeOne: Float := -1.0
def negNegLeft: Float := Float.neg (Float.neg 1.5)
def negNegRight: Float := 1.5
def negNaNLeft: Float := Float.neg Float.nan
def nanItself: Float := Float.nan
def decSame: Decidable (1.5 = 1.5) := Float.decEq 1.5 1.5
def decDifferent: Decidable (1.5 = -1.5) := Float.decEq 1.5 (-1.5)
def decZeros: Decidable (0.0 = -0.0) := Float.decEq 0.0 (-0.0)
def decNaN: Decidable (Float.nan = Float.nan) := Float.decEq Float.nan Float.nan
def isNaNOfNaN: Bool := Float.isNaN Float.nan
def isNaNOfOne: Bool := Float.isNaN 1.0

theorem product: 0.1 * 3.0 = 0.30000000000000004 := rfl
theorem quotient: 1.0 / 0.0 = Float.infinity := rfl
theorem negQuotient: 1.0 / -0.0 = -Float.infinity := rfl
theorem nanQuotient: 0.0 / 0.0 = Float.nan := rfl
theorem remainder: -5.5 % 2.0 = -1.5 := rfl
theorem roundBelowHalf: Float.round 0.49999999999999994 = 0.0 := rfl
theorem roundMinusHalf: Float.round (-0.5) = -0.0 := rfl
theorem roundMinusZero: Float.round (-0.0) = -0.0 := rfl
theorem roundLarge: Float.round 4503599627370497 = 4503599627370497 := rfl
theorem roundTie: Float.round (-2.5) = -2.0 := rfl
theorem floorHalf: Float.floor (-0.5) = -1.0 := rfl
theorem ceilHalf: Float.ceil (-0.5) = -0.0 := rfl
theorem truncHalf: Float.trunc (-1.5) = -1.0 := rfl
theorem ofIntNegative: Float.ofInt (-3) = -3.0 := rfl
theorem ofIntZero: Float.ofInt 0 = 0.0 := rfl
theorem ofNatTie: Float.ofNat 9007199254740993 = 9007199254740992 := rfl
theorem toIntNegZero: Float.toInt (-0.0) = Some 0 := rfl
theorem toIntBig: Float.toInt 1e100 = Some 10000000000000000159028911097599180468360808563945281389781327557747838772170381060813469985856815104 := rfl
theorem toIntHalf: Float.toInt 0.5 = None := rfl
theorem zerosOrdered: -0.0 < 0.0 := rfl
theorem nanGreatest: Float.compare Float.nan Float.infinity = Greater := rfl
theorem ieeeZeros: Float.ieeeLt (-0.0) 0.0 = False := rfl
theorem ieeeZerosLe: Float.ieeeLe 0.0 (-0.0) = True := rfl
theorem sourceNaN: Float.toSource Float.nan = "Float.nan" := rfl
theorem sourceNegZero: Float.toSource (-0.0) = "-0.0" := rfl

def productLeft: Float := 0.1 * 3.0
def productRight: Float := 0.30000000000000004
def quotientLeft: Float := 1.0 / 0.0
def infinityItself: Float := Float.infinity
def negQuotientLeft: Float := 1.0 / -0.0
def negInfinity: Float := -Float.infinity
def remLeft: Float := -5.5 % 2.0
def remRight: Float := -1.5
def roundMinusHalfLeft: Float := Float.round (-0.5)
def negZero: Float := -0.0
def ofIntLeft: Float := Float.ofInt (-3)
def ofIntRight: Float := -3.0
def ofNatTieLeft: Float := Float.ofNat 9007199254740993
def ofNatTieRight: Float := 9007199254740992
def toIntBigLeft: Option Int := Float.toInt 1e100
def toIntNegZeroLeft: Option Int := Float.toInt (-0.0)
def toIntNegLeft: Option Int := Float.toInt (-3.0)
def toIntHalfLeft: Option Int := Float.toInt (-0.5)
def toIntNaNLeft: Option Int := Float.toInt Float.nan
def ieeeLtZeros: Bool := Float.ieeeLt (-0.0) 0.0
def ieeeLeZeros: Bool := Float.ieeeLe 0.0 (-0.0)
def ieeeLtNaN: Bool := Float.ieeeLt Float.nan 1.0
def ieeeLtOrdered: Bool := Float.ieeeLt (-1.0) 0.5
def isFiniteOfInfinity: Bool := Float.isFinite Float.infinity
def isFiniteOfOne: Bool := Float.isFinite (-1.0)
def compareZeros: Ordering := Float.compare (-0.0) 0.0
def sourceOfInfinity: Text := Float.toSource (-Float.infinity)
"#;

/// Pairs of the program's definitions whose normal forms must be the same
/// term.
const SAME: &[(&str, &str)] = &[
    ("sumHalvesLeft", "sumHalvesRight"),
    ("sumTenthsLeft", "sumTenthsRight"),
    ("plusNegativeLeft", "negativeOne"),
    ("minusToNegativeLeft", "negativeOne"),
    ("negNegLeft", "negNegRight"),
    ("negNaNLeft", "nanItself"),
    ("productLeft", "productRight"),
    ("quotientLeft", "infinityItself"),
    ("negQuotientLeft", "negInfinity"),
    ("remLeft", "remRight"),
    ("roundMinusHalfLeft", "negZero"),
    ("ofIntLeft", "ofIntRight"),
    ("ofNatTieLeft", "ofNatTieRight"),
];

/// The program's definitions whose normal forms are compared across modes.
const COMPARED: &[&str] = &[
    "sumHalvesLeft",
    "sumTenthsLeft",
    "plusNegativeLeft",
    "minusToNegativeLeft",
    "negativeOne",
    "negNegLeft",
    "negNaNLeft",
    "decSame",
    "decDifferent",
    "decZeros",
    "decNaN",
    "isNaNOfNaN",
    "isNaNOfOne",
    "productLeft",
    "quotientLeft",
    "negQuotientLeft",
    "remLeft",
    "roundMinusHalfLeft",
    "ofIntLeft",
    "ofNatTieLeft",
    "toIntBigLeft",
    "toIntNegZeroLeft",
    "toIntNegLeft",
    "toIntHalfLeft",
    "toIntNaNLeft",
    "ieeeLtZeros",
    "ieeeLeZeros",
    "ieeeLtNaN",
    "ieeeLtOrdered",
    "isFiniteOfInfinity",
    "isFiniteOfOne",
    "compareZeros",
    "sourceOfInfinity",
];

/// Bit patterns for the checks with a neutral witness: zeros, ones,
/// infinities, the NaN, the smallest subnormal, the largest finite.
pub const PATTERNS: &[u64] = &[
    0,
    float::SIGN,
    0x3FF0_0000_0000_0000,
    0xBFF0_0000_0000_0000,
    0x3FF8_0000_0000_0000,
    float::INFINITY,
    float::NEG_INFINITY,
    float::NAN,
    1,
    float::SIGN | 1,
    0x7FEF_FFFF_FFFF_FFFF,
    0xFFEF_FFFF_FFFF_FFFF,
];

/// One check's result.
#[derive(Clone, Debug)]
pub struct Check {
    pub name: String,
    pub mode: Mode,
    pub passed: bool,
    pub detail: String,
}

/// What a mode's session found: its checks, and the normal forms to compare
/// with the other modes'.
struct Run {
    checks: Vec<Check>,
    forms: Vec<(String, String)>,
}

/// Runs every check in each of `modes`, then compares the normal forms
/// across them. `limits` bound each session (a mode that runs out fails its
/// checks, saying so).
pub fn run(modes: &[Mode], limits: Limits) -> Vec<Check> {
    let mut out = Vec::new();
    let mut runs = Vec::new();
    for &mode in modes {
        let run = run_mode(mode, limits);
        out.extend(run.checks.iter().cloned());
        runs.push((mode, run));
    }
    if let Some(((first, base), rest)) = runs.split_first() {
        for (mode, run) in rest {
            for (name, form) in &run.forms {
                let Some((_, expected)) = base.forms.iter().find(|(n, _)| n == name) else {
                    continue;
                };
                out.push(Check {
                    name: format!("`{name}` is the same term as with {}", first.name()),
                    mode: *mode,
                    passed: form == expected,
                    detail: if form == expected {
                        String::new()
                    } else {
                        format!("{form} vs {expected}")
                    },
                });
            }
        }
    }
    out
}

fn check(out: &mut Vec<Check>, mode: Mode, name: String, result: Result<(), String>) {
    let (passed, detail) = match result {
        Ok(()) => (true, String::new()),
        Err(e) => (false, e),
    };
    out.push(Check {
        name,
        mode,
        passed,
        detail,
    });
}

fn def(g: &Globals, name: &str) -> Result<DefId, String> {
    g.defs
        .iter()
        .position(|d| &*d.name == name)
        .map(DefId)
        .ok_or_else(|| format!("no `{name}`"))
}

/// The normal form of `value`, with `level` variables in scope, as text.
fn normal(g: &Globals, level: usize, value: &Value) -> Result<String, String> {
    quote(g, level, value)
        .map(|t| format!("{t:?}"))
        .map_err(|e| format!("{e:?}"))
}

fn run_mode(mode: Mode, limits: Limits) -> Run {
    let mut checks = Vec::new();
    let mut forms = Vec::new();
    let mut session = Session::new();
    session.elab.limits = limits;
    {
        let b = &mut session.elab.globals.builtins;
        b.disable_natives = mode == Mode::AllNativesOff;
        b.disable_float_natives = mode == Mode::FloatNativesOff;
    }
    if let Err(errors) = session.load("float-gate.sw", PROGRAM) {
        let detail = errors
            .iter()
            .map(|e| format!("{}: {}", e.code, e.message))
            .collect::<Vec<_>>()
            .join("; ");
        check(&mut checks, mode, "the program checks".into(), Err(detail));
        return Run { checks, forms };
    }
    check(
        &mut checks,
        mode,
        "the program checks: every `rfl` row, and `neg (neg x) = x`".into(),
        Ok(()),
    );
    // The natives are bound, never used while checking, and used while a
    // program runs exactly when the mode says.
    {
        let g = &session.elab.globals;
        for native in FloatNative::ALL {
            let result = def(g, native.name()).and_then(|id| {
                let bound = g.builtins.float_native(id) == Some(native);
                let checking = g.builtins.float_def(id, false).is_some();
                let running = g.builtins.float_def(id, true).is_some();
                match (bound, checking, running, mode == Mode::NativesOn) {
                    (true, false, true, true) | (true, false, false, false) => Ok(()),
                    _ => Err(format!(
                        "bound {bound}, used while checking {checking}, while running {running}"
                    )),
                }
            });
            check(
                &mut checks,
                mode,
                format!(
                    "`{}` has its native, used only while running with natives on",
                    native.name()
                ),
                result,
            );
        }
    }
    // From here on the natives fire in evaluation, as in a run, so that the
    // normal forms below compare them with their definitions.
    session.elab.globals.builtins.float_natives_outside_runs = mode == Mode::NativesOn;
    let g = &session.elab.globals;
    let _op = g.budget.operation(limits);
    let value_of = |name: &str| -> Result<Value, String> {
        eval(g, &[], &Term::Def(def(g, name)?)).map_err(|e| format!("{e:?}"))
    };
    for (left, right) in SAME {
        let result = (|| {
            let l = normal(g, 0, &value_of(left)?)?;
            let r = normal(g, 0, &value_of(right)?)?;
            if l == r {
                Ok(())
            } else {
                Err(format!("{l} vs {r}"))
            }
        })();
        check(
            &mut checks,
            mode,
            format!("`{left}` and `{right}` normalise to the same term"),
            result,
        );
    }
    for name in COMPARED {
        if let Ok(form) = value_of(name).and_then(|v| normal(g, 0, &v)) {
            forms.push(((*name).to_string(), form));
        }
    }
    // A record with known bits and a variable for its witness.
    let Some(data) = g.registry.loaded_data(Builtin::Float) else {
        check(
            &mut checks,
            mode,
            "`Float` is loaded".into(),
            Err("it isn't".into()),
        );
        return Run { checks, forms };
    };
    for native in [FloatNative::Neg, FloatNative::Abs] {
        for &bits in PATTERNS {
            let name = format!(
                "`{}` of `{{ bits = {bits:#x}, valid = p }}` normalises to the record with `Eq.refl True`",
                native.name()
            );
            let result = (|| {
                let id = def(g, native.name())?;
                let x = Value::Ctor(data, 0, [nat_value(bits.into()), Value::var(0)].into());
                let f = eval(g, &[], &Term::Def(id)).map_err(|e| format!("{e:?}"))?;
                let got = apply(g, f, x).map_err(|e| format!("{e:?}"))?;
                let expected = eval(g, &[], &float::literal_term(data, native.on_bits(bits)))
                    .map_err(|e| format!("{e:?}"))?;
                let (got, expected) = (normal(g, 1, &got)?, normal(g, 1, &expected)?);
                if got == expected {
                    Ok(got)
                } else {
                    Err(format!("{got} vs {expected}"))
                }
            })();
            if let Ok(form) = &result {
                forms.push((format!("{} {bits:#x}", native.name()), form.clone()));
            }
            check(&mut checks, mode, name, result.map(|_| ()));
        }
    }
    // The natives returning a `Bool` or an `Option Int`, on records with a
    // neutral witness: they compute, to what they give on the literal (the
    // witness doesn't matter), and the same term in every mode.
    let with_witness = |bits: u64, level: usize| {
        Value::Ctor(data, 0, [nat_value(bits.into()), Value::var(level)].into())
    };
    let literal =
        |bits: u64| eval(g, &[], &float::literal_term(data, bits)).map_err(|e| format!("{e:?}"));
    for native in [
        FloatNative::IsNaN,
        FloatNative::IsFinite,
        FloatNative::ToInt,
    ] {
        for &bits in PATTERNS {
            let name = format!(
                "`{}` of `{{ bits = {bits:#x}, valid = p }}` is what it is of the literal",
                native.name()
            );
            let result = (|| {
                let f = eval(g, &[], &Term::Def(def(g, native.name())?))
                    .map_err(|e| format!("{e:?}"))?;
                let got =
                    apply(g, f.clone(), with_witness(bits, 0)).map_err(|e| format!("{e:?}"))?;
                let expected = apply(g, f, literal(bits)?).map_err(|e| format!("{e:?}"))?;
                let (got, expected) = (normal(g, 1, &got)?, normal(g, 1, &expected)?);
                if got == expected && !got.contains("Def(") {
                    Ok(got)
                } else {
                    Err(format!("{got} vs {expected}"))
                }
            })();
            if let Ok(form) = &result {
                forms.push((format!("{} {bits:#x}", native.name()), form.clone()));
            }
            check(&mut checks, mode, name, result.map(|_| ()));
        }
    }
    for native in [FloatNative::IeeeLt, FloatNative::IeeeLe] {
        for &a in PATTERNS {
            for &b in PATTERNS {
                let name = format!(
                    "`{}` of `{{ bits = {a:#x}, valid = p }}` and `{{ bits = {b:#x}, valid = q }}` is what it is of the literals",
                    native.name()
                );
                let result = (|| {
                    let f = eval(g, &[], &Term::Def(def(g, native.name())?))
                        .map_err(|e| format!("{e:?}"))?;
                    let partial =
                        apply(g, f.clone(), with_witness(a, 0)).map_err(|e| format!("{e:?}"))?;
                    let got =
                        apply(g, partial, with_witness(b, 1)).map_err(|e| format!("{e:?}"))?;
                    let partial = apply(g, f, literal(a)?).map_err(|e| format!("{e:?}"))?;
                    let expected = apply(g, partial, literal(b)?).map_err(|e| format!("{e:?}"))?;
                    let (got, expected) = (normal(g, 2, &got)?, normal(g, 2, &expected)?);
                    if got == expected && !got.contains("Def(") {
                        Ok(got)
                    } else {
                        Err(format!("{got} vs {expected}"))
                    }
                })();
                if let Ok(form) = &result {
                    forms.push((format!("{} {a:#x} {b:#x}", native.name()), form.clone()));
                }
                check(&mut checks, mode, name, result.map(|_| ()));
            }
        }
    }
    // `add` and `sub` on records with neutral witnesses: the record with
    // `Eq.refl True` and the machine's bits, in every mode.
    for native in [FloatNative::Add, FloatNative::Sub] {
        for &a in PATTERNS {
            for &b in PATTERNS {
                let name = format!(
                    "`{}` of `{{ bits = {a:#x}, valid = p }}` and `{{ bits = {b:#x}, valid = q }}` normalises to the record with `Eq.refl True`",
                    native.name()
                );
                let result = (|| {
                    let f = eval(g, &[], &Term::Def(def(g, native.name())?))
                        .map_err(|e| format!("{e:?}"))?;
                    let partial = apply(g, f, with_witness(a, 0)).map_err(|e| format!("{e:?}"))?;
                    let got =
                        apply(g, partial, with_witness(b, 1)).map_err(|e| format!("{e:?}"))?;
                    let expected = literal(native.on_pair(a, b))?;
                    let (got, expected) = (normal(g, 2, &got)?, normal(g, 2, &expected)?);
                    if got == expected {
                        Ok(got)
                    } else {
                        Err(format!("{got} vs {expected}"))
                    }
                })();
                if let Ok(form) = &result {
                    forms.push((format!("{} {a:#x} {b:#x}", native.name()), form.clone()));
                }
                check(&mut checks, mode, name, result.map(|_| ()));
            }
        }
    }
    Run { checks, forms }
}
