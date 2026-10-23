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
    let g = &session.elab.globals;
    let _op = g.budget.operation(limits);
    // The natives are bound, and used exactly when the mode says.
    for native in FloatNative::ALL {
        let result = def(g, native.name()).and_then(|id| {
            let bound = g.builtins.float_native(id) == Some(native);
            let used = g.builtins.float_def(id).is_some();
            match (bound, used, mode == Mode::NativesOn) {
                (true, true, true) | (true, false, false) => Ok(()),
                _ => Err(format!("bound {bound}, used {used}")),
            }
        });
        check(
            &mut checks,
            mode,
            format!(
                "`{}` has its native, used only with natives on",
                native.name()
            ),
            result,
        );
    }
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
    Run { checks, forms }
}
