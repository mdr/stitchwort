//! The kernel's comparison with proof positions skipped, over every term of
//! one type up to depth 2 built from a fixed signature
//! (docs/proposals/proof-irrelevance.md §8, "Equivalence and gluing,
//! enumerated"). For every pair it must give one answer with gluing on,
//! with the shortcuts disabled, with gluing off, in the kernel's own glued mode and from the
//! reference evaluator, and that answer must be the *plain* evaluator's: the
//! reference with every fold off ([`reference::set_plain`]), which computes
//! every value as written
//! (docs/proposals/equality-in-the-round.md, T1); the answers must form an equivalence relation; and a pair
//! found equal with `n` unknown stays equal once `n` is `0` or `1` (§7.10:
//! the shortcuts never equate what an unfolding tells apart).
//!
//! The terms are of type `Nat`, in the context `p q: 0 = 0`, `t: Tok`,
//! `n: Nat`, built from `n` and `0` by the operations of [`OPS`]: a
//! definition with an inert proof parameter (`modP`), one taking a proof
//! apart (`tokNat`), one using the proof inside a box (`unboxK`), one
//! storing its proof in a field (`keepK`), two definitions with the same
//! case tree (`pickA`, `pickB`), and `applyAt` with a partially applied
//! definition and its eta expansion.
//!
//! A second, smaller matrix does the same for fields of calls
//! (docs/proposals/match-call-field.md): a field of a call stuck in its own
//! case tree, of a call whose leaf is another call, and of a call with a
//! `Quot.lift` leaf, applied; a field of a `decreasing` definition's call,
//! which the elaborator keeps as `(f x).i`; and such a call returned by a
//! definition that isn't `decreasing`, past a proof or through `J` (D3030:
//! glued and unglued evaluation agree on what's equal).

use std::rc::Rc;

use stitchwort_core::chars::Chars;
use stitchwort_core::term::Term;
use stitchwort_core::value::{Head, Value, conv, eval, set_shortcuts_disabled};
use stitchwort_core::{DataId, DefId, Ev, Icit, reference};
use stitchwort_driver::driver::Session;

const PROGRAM: &str = r#"
import Std (Nat)

type Tok: Prop =
  | MkTok

type PB: Type =
  | MkPB (h: 0 = 0)

def modP (x: Nat) (h: 0 = 0): Nat :=
  match x with
    | Zero => 0
    | Succ m => m

def tokNat (t: Tok) (k: Nat): Nat :=
  match t with
    | MkTok => k

def unboxK (b: PB) (k: Nat): Nat :=
  match b with
    | MkPB h => J (y e => Nat) k h

def keepK (x: Nat) (h: 0 = 0): Nat := unboxK (MkPB h) x

def pickA (x: Nat): Nat :=
  match x with
    | Zero => 0
    | Succ m => m

def pickB (x: Nat): Nat :=
  match x with
    | Zero => 0
    | Succ m => m

def applyAt (f: Nat → Nat) (x: Nat): Nat := f x
"#;

/// The context's variables, by level.
const P: usize = 0;
const Q: usize = 1;
const T: usize = 2;
const N: usize = 3;
const LEVEL: usize = 4;

struct Sig {
    datas: Vec<(&'static str, DataId)>,
    defs: Vec<(&'static str, DefId)>,
}

impl Sig {
    fn def(&self, name: &str) -> Term {
        Term::Def(self.defs.iter().find(|(n, _)| *n == name).expect(name).1)
    }

    fn data(&self, name: &str) -> DataId {
        self.datas.iter().find(|(n, _)| *n == name).expect(name).1
    }
}

/// A variable at `level`, as a term under the context's binders, `depth`
/// binders further in.
fn var(level: usize, depth: usize) -> Term {
    Term::Var(LEVEL + depth - 1 - level)
}

fn app(f: Term, args: Vec<Term>) -> Term {
    args.into_iter()
        .fold(f, |f, a| Term::App(f.into(), a.into(), Icit::Explicit))
}

/// The operations, each building a `Nat` from one.
const OPS: &[&str] = &[
    "Succ",
    "modP p",
    "modP q",
    "tokNat t",
    "tokNat MkTok",
    "unboxK p",
    "unboxK q",
    "keepK p",
    "keepK q",
    "pickA",
    "pickB",
    "applyAt pickA",
    "applyAt eta",
];

fn op(sig: &Sig, name: &str, x: Term) -> Term {
    let pb = |v| Term::ctor(sig.data("PB"), 0, vec![var(v, 0)]);
    match name {
        "Succ" => Term::ctor(sig.data("Nat"), 1, vec![x]),
        "modP p" => app(sig.def("modP"), vec![x, var(P, 0)]),
        "modP q" => app(sig.def("modP"), vec![x, var(Q, 0)]),
        "tokNat t" => app(sig.def("tokNat"), vec![var(T, 0), x]),
        "tokNat MkTok" => app(
            sig.def("tokNat"),
            vec![Term::ctor(sig.data("Tok"), 0, vec![]), x],
        ),
        "unboxK p" => app(sig.def("unboxK"), vec![pb(P), x]),
        "unboxK q" => app(sig.def("unboxK"), vec![pb(Q), x]),
        "keepK p" => app(sig.def("keepK"), vec![x, var(P, 0)]),
        "keepK q" => app(sig.def("keepK"), vec![x, var(Q, 0)]),
        "pickA" => app(sig.def("pickA"), vec![x]),
        "pickB" => app(sig.def("pickB"), vec![x]),
        "applyAt pickA" => app(sig.def("applyAt"), vec![sig.def("pickA"), x]),
        "applyAt eta" => {
            let eta = Term::Lam(
                "y".into(),
                Icit::Explicit,
                app(sig.def("pickA"), vec![Term::Var(0)]).into(),
            );
            app(sig.def("applyAt"), vec![eta, x])
        }
        _ => unreachable!("{name}"),
    }
}

/// Every term up to depth 2 built by `ops` (each made by `op`), with a
/// name for messages.
fn terms(sig: &Sig, ops: &[&str], op: fn(&Sig, &str, Term) -> Term) -> Vec<(String, Term)> {
    let atoms = vec![
        ("n".to_string(), var(N, 0)),
        ("0".to_string(), Term::ctor(sig.data("Nat"), 0, vec![])),
    ];
    let mut level = atoms.clone();
    for _ in 0..2 {
        let mut next = atoms.clone();
        for (name, term) in &level {
            for o in ops {
                next.push((format!("{o} ({name})"), op(sig, o, term.clone())));
            }
        }
        level = next;
    }
    level
}

fn signature(g: &Ev, datas: &[&'static str], defs: &[&'static str]) -> Sig {
    let datas = datas
        .iter()
        .map(|name| {
            let id = g.env.datas().iter().position(|d| &**d.name() == *name);
            (*name, DataId(id.unwrap_or_else(|| panic!("no `{name}`"))))
        })
        .collect();
    let defs = defs
        .iter()
        .map(|name| {
            let id = g.env.defs().iter().position(|d| &**d.name() == *name);
            (*name, DefId(id.unwrap_or_else(|| panic!("no `{name}`"))))
        })
        .collect();
    Sig { datas, defs }
}

/// The equality matrix, by `value::conv` with gluing `glue` and the
/// shortcuts on or off, or by the reference evaluator.
fn matrix(g: &Ev, env: &[Value], terms: &[(String, Term)], how: How) -> Vec<Vec<bool>> {
    in_mode(g, how, || {
        let values: Vec<Value> = terms
            .iter()
            .map(|(_, t)| eval_how(g, env, t, how))
            .collect();
        values
            .iter()
            .map(|a| values.iter().map(|b| conv_how(g, a, b, how)).collect())
            .collect()
    })
}

#[derive(Clone, Copy, Debug)]
struct How {
    glue: bool,
    /// The kernel's own mode, as admission runs in (`in_kernel_modes`).
    kernel: bool,
    shortcuts: bool,
    reference: bool,
    /// The reference evaluator with every fold off; implies `reference`.
    plain: bool,
}

const GLUED: How = How {
    glue: true,
    kernel: false,
    shortcuts: true,
    reference: false,
    plain: false,
};

/// The answer every mode is held to: nothing folded, nothing compact.
const PLAIN: How = How {
    reference: true,
    plain: true,
    ..GLUED
};

/// Every mode but the plain one.
const MODES: [How; 5] = [
    GLUED,
    How {
        kernel: true,
        ..GLUED
    },
    How {
        shortcuts: false,
        ..GLUED
    },
    How {
        glue: false,
        ..GLUED
    },
    How {
        reference: true,
        ..GLUED
    },
];

impl How {
    fn name(self) -> &'static str {
        match self {
            How { plain: true, .. } => "plain",
            How {
                reference: true, ..
            } => "reference",
            How { kernel: true, .. } => "kernel glued",
            How {
                shortcuts: false, ..
            } => "shortcuts disabled",
            How { glue: false, .. } => "unglued",
            _ => "glued",
        }
    }
}

/// Steps the plain evaluator may take in one [`in_mode`]: far more than any
/// matrix here needs, so a runaway fails the test instead of hanging it.
const PLAIN_STEPS: u64 = 400_000_000;

/// Runs `f` with the evaluators set to `how`, and back to the defaults after.
fn in_mode<T>(g: &Ev, how: How, f: impl FnOnce() -> T) -> T {
    let was = g.machine.glue.replace(how.glue);
    let was_kernel = g.machine.kernel.replace(how.kernel);
    set_shortcuts_disabled(!how.shortcuts);
    reference::set_plain(how.plain);
    reference::set_plain_budget(PLAIN_STEPS);
    let out = f();
    reference::set_plain(false);
    set_shortcuts_disabled(false);
    g.machine.glue.set(was);
    g.machine.kernel.set(was_kernel);
    out
}

fn eval_how(g: &Ev, env: &[Value], term: &Term, how: How) -> Value {
    if how.reference {
        let value = reference::eval(g, env, term).unwrap();
        if how.plain
            && let Some(what) = reference::compact_or_lazy(g, &value)
        {
            panic!("the plain evaluator made {what} of {term:?}");
        }
        value
    } else {
        eval(g, env, term).unwrap()
    }
}

fn conv_how(g: &Ev, a: &Value, b: &Value, how: How) -> bool {
    if how.reference {
        reference::conv(g, LEVEL, a, b).unwrap()
    } else {
        conv(g, LEVEL, a, b).unwrap()
    }
}

#[test]
fn every_pair_is_compared_alike_and_the_relation_is_an_equivalence() {
    let mut session = Session::eager();
    session.load("equivalence.sw", PROGRAM).expect("loads");
    let g = &session.elab.ev();
    let sig = signature(
        g,
        &["Nat", "Tok", "PB"],
        &[
            "modP", "tokNat", "unboxK", "keepK", "pickA", "pickB", "applyAt",
        ],
    );
    let terms = terms(&sig, OPS, op);
    let count = compared_alike(g, &sig, &terms);
    // The relation isn't trivial: some pairs differ only in proofs and are
    // equal, others differ.
    assert!(count > terms.len() && count < terms.len() * terms.len());
}

const FIELDS_PROGRAM: &str = r#"
import Std (Nat)

type Fn = { at: Nat → Nat }

def NatEq (a: Nat) (b: Nat): Prop := a = b

def liftFn (q: Quot Nat NatEq): Fn := Quot.lift (b => { at = y => b }) (x y h => rewrite h in rfl) q

type Box = { value: Nat }

def fieldOf (x: Nat): Fn :=
  match x with
    | Zero => { at = y => y }
    | Succ m => { at = y => m }

def viaCall (x: Nat): Fn := fieldOf x

def countDown (x: Nat): Box
  decreasing x
:=
  match x with
    | Zero => { value = 0 }
    | Succ m => countDown m [decreasing := omega]

def valueOf (x: Nat): Nat := (countDown x).value

def leafOf (x: Nat): Nat
  decreasing x
:=
  match x with
    | Zero => (countDown x).value
    | Succ m => leafOf m [decreasing := omega]

def inner (x: Nat): Box
  decreasing x
:=
  match x with
    | Zero => { value = 1 }
    | Succ m => inner m [decreasing := omega]

def outer (x: Nat): Box
  decreasing x
:=
  match x with
    | Zero => inner x
    | Succ m => outer m [decreasing := omega]

def onOuter (x: Nat): Nat :=
  match (outer x).value with
    | Zero => 0
    | Succ m => m

def innerN (x: Nat): Nat
  decreasing x
:=
  match x with
    | Zero => 1
    | Succ m => innerN m [decreasing := omega]

def outerN (x: Nat): Nat
  decreasing x
:=
  match x with
    | Zero => innerN x
    | Succ m => outerN m [decreasing := omega]

def onOuterN (x: Nat): Nat :=
  match outerN x with
    | Zero => 0
    | Succ m => m

def keepProof (x: Nat) (h: x = x): Nat := x

theorem reflInner (x: Nat): x = x
  decreasing x
:=
  match x with
    | Zero => rfl
    | Succ m => rewrite reflInner m [decreasing := omega] in rfl

theorem reflOuter (x: Nat): x = x
  decreasing x
:=
  match x with
    | Zero => reflInner x
    | Succ m => rewrite reflOuter m [decreasing := omega] in rfl

def withProof (x: Nat): Nat := keepProof x (reflOuter x)

def jOuter (x: Nat): Nat := J (y e => Nat) (outerN x) (rfl: x = x)

def jRefl (x: Nat): Nat := J (y e => Nat) x (reflOuter x)

type Dict = { size: Nat → Nat }

def dictInner (x: Nat): Dict
  decreasing x
:=
  match x with
    | Zero => { size = y => y }
    | Succ m => dictInner m [decreasing := omega]

def dictOuter (x: Nat): Dict
  decreasing x
:=
  match x with
    | Zero => dictInner x
    | Succ m => dictOuter m [decreasing := omega]

def dict: Dict := dictOuter 2

def liftLeaf (q: Quot Nat NatEq) (x: Nat): Fn
  decreasing x
:=
  match x with
    | Zero => liftFn q
    | Succ m => liftLeaf q m [decreasing := omega]
"#;

/// The operations on fields of calls. `liftFn` takes the context's `t` as
/// its quotient: evaluation doesn't look at types, and a variable is what
/// leaves the lift stuck.
const FIELD_OPS: &[&str] = &[
    "Succ",
    "fieldOf.at",
    "viaCall.at",
    "liftFn.at",
    "countDown.value",
    "valueOf",
    "leafOf",
    "outer.value",
    "onOuter",
    "outerN",
    "onOuterN",
    "withProof",
    "jOuter",
    "jRefl",
    "dictOuter.size",
    "dict.size",
    "liftLeaf.at",
];

fn field_op(sig: &Sig, name: &str, x: Term) -> Term {
    let field = |d: &str, def: &str, arg: Term| {
        Term::Proj(sig.data(d), 0, app(sig.def(def), vec![arg]).into())
    };
    match name {
        "Succ" => Term::ctor(sig.data("Nat"), 1, vec![x]),
        "fieldOf.at" => app(field("Fn", "fieldOf", x.clone()), vec![x]),
        "viaCall.at" => app(field("Fn", "viaCall", x.clone()), vec![x]),
        "liftFn.at" => app(field("Fn", "liftFn", var(T, 0)), vec![x]),
        "countDown.value" => field("Box", "countDown", x),
        "valueOf" => app(sig.def("valueOf"), vec![x]),
        "leafOf" => app(sig.def("leafOf"), vec![x]),
        "outer.value" => field("Box", "outer", x),
        "onOuter" => app(sig.def("onOuter"), vec![x]),
        "outerN" => app(sig.def("outerN"), vec![x]),
        "onOuterN" => app(sig.def("onOuterN"), vec![x]),
        "withProof" => app(sig.def("withProof"), vec![x]),
        "jOuter" => app(sig.def("jOuter"), vec![x]),
        "jRefl" => app(sig.def("jRefl"), vec![x]),
        "dictOuter.size" => app(field("Dict", "dictOuter", x.clone()), vec![x]),
        "dict.size" => app(
            Term::Proj(sig.data("Dict"), 0, sig.def("dict").into()),
            vec![x],
        ),
        "liftLeaf.at" => app(
            Term::Proj(
                sig.data("Fn"),
                0,
                app(sig.def("liftLeaf"), vec![var(T, 0), x.clone()]).into(),
            ),
            vec![x],
        ),
        _ => unreachable!("{name}"),
    }
}

#[test]
fn fields_of_calls_are_compared_alike() {
    let mut session = Session::eager();
    session.load("fields.sw", FIELDS_PROGRAM).expect("loads");
    let g = &session.elab.ev();
    let sig = signature(
        g,
        &["Nat", "Fn", "Box", "Dict"],
        &[
            "fieldOf",
            "viaCall",
            "liftFn",
            "countDown",
            "valueOf",
            "leafOf",
            "outer",
            "onOuter",
            "outerN",
            "onOuterN",
            "withProof",
            "jOuter",
            "jRefl",
            "innerN",
            "dictOuter",
            "dict",
            "liftLeaf",
        ],
    );
    let mut terms = terms(&sig, FIELD_OPS, field_op);
    // Deeper terms around a folded call under `Succ`, each `2` (SW-2157):
    // the number comparison has to unfold the call to see it.
    let nat = |k: usize| {
        (0..k).fold(Term::ctor(sig.data("Nat"), 0, vec![]), |t, _| {
            Term::ctor(sig.data("Nat"), 1, vec![t])
        })
    };
    let succ = |t: Term| Term::ctor(sig.data("Nat"), 1, vec![t]);
    let call = |def: &str, t: Term| app(sig.def(def), vec![t]);
    let twos = [
        ("Succ (innerN (0))", succ(call("innerN", nat(0)))),
        (
            "Succ (withProof (outerN (0)))",
            succ(call("withProof", call("outerN", nat(0)))),
        ),
        (
            "Succ (withProof (Succ (0)))",
            succ(call("withProof", nat(1))),
        ),
        // The base isn't a call, but a glued call is still inside it.
        (
            "Succ (Succ (withProof (0)))",
            succ(succ(call("withProof", nat(0)))),
        ),
    ];
    // `countDown` always returns 0, past a plain or a `decreasing` wrapper.
    let zeros = [
        ("valueOf (Succ (Succ (0)))", call("valueOf", nat(2))),
        ("leafOf (Succ (Succ (0)))", call("leafOf", nat(2))),
        (
            "Succ (valueOf (leafOf (0)))",
            succ(call("valueOf", call("leafOf", nat(0)))),
        ),
    ];
    terms.extend(zeros.into_iter().map(|(name, t)| (name.to_string(), t)));
    terms.extend(twos.into_iter().map(|(name, t)| (name.to_string(), t)));
    let count = compared_alike(g, &sig, &terms);
    assert!(count > terms.len() && count < terms.len() * terms.len());
    let env: Vec<Value> = (0..LEVEL).map(Value::var).collect();
    let glued = matrix(g, &env, &terms, GLUED);
    let at = |name: &str| terms.iter().position(|(n, _)| n == name).expect(name);
    let two = at("Succ (Succ (0))");
    for name in [
        "Succ (outerN (0))",
        "Succ (innerN (0))",
        "Succ (withProof (outerN (0)))",
        "Succ (withProof (Succ (0)))",
        "Succ (Succ (withProof (0)))",
    ] {
        assert!(glued[at(name)][two], "{name} isn't 2");
    }
    let zero = at("0");
    for name in [
        "valueOf (Succ (Succ (0)))",
        "leafOf (Succ (Succ (0)))",
        "valueOf (0)",
        "leafOf (0)",
    ] {
        assert!(glued[at(name)][zero], "{name} isn't 0");
    }
    assert!(glued[at("Succ (Succ (withProof (0)))")][at("Succ (Succ (0))")]);
    assert!(glued[at("Succ (Succ (withProof (0)))")][at("Succ (innerN (0))")]);
    assert!(glued[at("valueOf (Succ (Succ (0)))")][at("leafOf (Succ (Succ (0)))")]);
    assert!(glued[at("Succ (valueOf (leafOf (0)))")][at("Succ (0)")]);
}

/// Checks that every pair of `terms` gets the plain evaluator's answer
/// glued, in the kernel's glued mode, with the shortcuts disabled, unglued
/// and from the reference evaluator; that the answers form an equivalence;
/// and that equal stays equal once `n` is `0` or `1`. Returns how many pairs
/// are equal.
fn compared_alike(g: &Ev, sig: &Sig, terms: &[(String, Term)]) -> usize {
    let env: Vec<Value> = (0..LEVEL).map(Value::var).collect();
    let plain = matrix(g, &env, terms, PLAIN);
    let glued = matrix(g, &env, terms, GLUED);
    let name = |i: usize| &terms[i].0;
    for how in MODES {
        let other = if how.name() == GLUED.name() {
            glued.clone()
        } else {
            matrix(g, &env, terms, how)
        };
        for i in 0..terms.len() {
            for j in 0..terms.len() {
                assert_eq!(
                    plain[i][j],
                    other[i][j],
                    "{} against {}: plain says {}, {how:?} says {}",
                    name(i),
                    name(j),
                    plain[i][j],
                    other[i][j]
                );
            }
        }
    }
    // Reflexive and symmetric; transitive: equal terms are equal to the
    // same terms.
    for i in 0..terms.len() {
        assert!(glued[i][i], "{} against itself", name(i));
        for j in 0..terms.len() {
            assert_eq!(glued[i][j], glued[j][i], "{} and {}", name(i), name(j));
            if glued[i][j]
                && let Some(k) = (0..terms.len()).find(|&k| glued[i][k] != glued[j][k])
            {
                panic!(
                    "{} = {}, but against {} they differ",
                    name(i),
                    name(j),
                    name(k)
                );
            }
        }
    }
    // Stable under substitution: equal stays equal with `n` known.
    let nat = |k: usize| {
        let nat = sig.data("Nat");
        (0..k).fold(Value::Ctor(nat, 0, Vec::new().into()), |v, _| {
            Value::Ctor(nat, 1, [v].into())
        })
    };
    for k in [0, 1] {
        let mut known = env.clone();
        known[N] = nat(k);
        let after = matrix(g, &known, terms, GLUED);
        for i in 0..terms.len() {
            for j in 0..terms.len() {
                assert!(
                    !glued[i][j] || after[i][j],
                    "{} = {} with `n` unknown, but not with `n := {k}`",
                    name(i),
                    name(j)
                );
            }
        }
    }
    glued.iter().flatten().filter(|b| **b).count()
}

// ---------------------------------------------------------------------------
// Wrapping a subterm in an identity (equality-in-the-round.md, T2)
// ---------------------------------------------------------------------------

const WRAP_PROGRAM: &str = r#"
import Std (Nat, Float, List, Char)

type Box = { value: Nat }

interface Id (a: Type) =
  { it: a → a }

def NatEq (a: Nat) (b: Nat): Prop := a = b

def idG (x: Nat): Nat := x

def idD (x: Nat) (k: Nat): Nat
  decreasing k
:=
  match k with
    | Zero => x
    | Succ m => idD x m [decreasing := omega]

def idDict: Id Nat := { it = x => x }

def liftId (q: Quot Nat NatEq) (x: Nat): Nat := Quot.lift (b => x) (a b h => rfl) q

def q0: Quot Nat NatEq := Quot.mk 0

def boxId (x: Nat) (k: Nat): Box
  decreasing k
:=
  match k with
    | Zero => { value = x }
    | Succ m => boxId x m [decreasing := omega]

def numMatch (n: Nat): Nat :=
  match n with
    | 3 => 10
    | _ => 20

def pickA (n: Nat) (x: Nat): Nat :=
  match n with
    | Zero => 1
    | Succ k => (match x with
      | Zero => 0
      | Succ m => m)

def pickB (n: Nat) (x: Nat): Nat :=
  match n with
    | Zero => 1
    | Succ k => (match x with
      | Zero => 0
      | Succ m => m)

def ignoresFirst (a: Nat) (x: Nat): Nat :=
  match x with
    | Zero => 0
    | Succ m => m

def alsoIgnores (a: Nat) (x: Nat): Nat :=
  match x with
    | Zero => 0
    | Succ m => m

def textTag (s: List Char): Nat :=
  match s with
    | Nil => 0
    | Cons c rest => 1
"#;

fn wrap_sig(g: &Ev) -> Sig {
    signature(
        g,
        &["Nat", "Box", "Id"],
        &[
            "idG",
            "idD",
            "idDict",
            "liftId",
            "q0",
            "boxId",
            "numMatch",
            "pickA",
            "pickB",
            "ignoresFirst",
            "alsoIgnores",
            "textTag",
            "Nat.add",
            "Nat.mul",
            "Float.ofNat",
        ],
    )
}

fn nat_term(sig: &Sig, k: usize) -> Term {
    (0..k).fold(Term::ctor(sig.data("Nat"), 0, vec![]), |t, _| {
        Term::ctor(sig.data("Nat"), 1, vec![t])
    })
}

fn succ_term(sig: &Sig, t: Term) -> Term {
    Term::ctor(sig.data("Nat"), 1, vec![t])
}

/// The same value spelled the other way: a closed chain of `Succ`s as a
/// number literal and a literal as the chain; a compact list as cons cells.
fn respell(g: &Ev, sig: &Sig, t: &Term) -> Term {
    fn closed_chain(t: &Term) -> Option<usize> {
        match t {
            Term::Ctor(_, 0, xs) if xs.is_empty() => Some(0),
            Term::Ctor(_, 1, xs) if xs.len() == 1 => closed_chain(&xs[0]).map(|k| k + 1),
            _ => None,
        }
    }
    match t {
        Term::Nat(k) => nat_term(sig, usize::try_from(&**k).unwrap()),
        Term::Chars(_) => reference::expand_term(g, t),
        Term::Ctor(_, 1, xs) if xs.len() == 1 => match closed_chain(t) {
            Some(k) => Term::Nat(Rc::new(k.into())),
            None => succ_term(sig, respell(g, sig, &xs[0])),
        },
        _ => t.clone(),
    }
}

/// The devices: each computes to its argument, in a different lazy form.
const DEVICES: &[&str] = &[
    "none",
    "glued",
    "decreasing",
    "dictionary",
    "lift",
    "field of a call",
    "k * x",
    "spelled",
];

fn device(g: &Ev, sig: &Sig, name: &str, x: Term) -> Term {
    match name {
        "none" => x,
        "glued" => app(sig.def("idG"), vec![x]),
        "decreasing" => app(sig.def("idD"), vec![x, nat_term(sig, 0)]),
        "dictionary" => app(
            Term::Proj(sig.data("Id"), 0, sig.def("idDict").into()),
            vec![x],
        ),
        "lift" => app(sig.def("liftId"), vec![sig.def("q0"), x]),
        "field of a call" => Term::Proj(
            sig.data("Box"),
            0,
            app(sig.def("boxId"), vec![x, nat_term(sig, 0)]).into(),
        ),
        "k * x" => app(sig.def("Nat.mul"), vec![Term::Nat(Rc::new(1u32.into())), x]),
        "spelled" => respell(g, sig, &x),
        _ => unreachable!("{name}"),
    }
}

/// A subterm to wrap. `inner` is what it's a `Succ` of, if it is, so the
/// device can sit under the `Succ` as well as over it.
struct Base {
    name: &'static str,
    term: Term,
    /// Its value, if it's a closed number.
    k: Option<usize>,
    inner: Option<Term>,
}

fn bases(sig: &Sig) -> Vec<Base> {
    let n = var(N, 0);
    let mut out: Vec<Base> = (0..4)
        .map(|k| Base {
            name: ["0", "1", "2", "3"][k],
            term: nat_term(sig, k),
            k: Some(k),
            inner: (k > 0).then(|| nat_term(sig, k - 1)),
        })
        .collect();
    out.push(Base {
        name: "n",
        term: n.clone(),
        k: None,
        inner: None,
    });
    out.push(Base {
        name: "Succ n",
        term: succ_term(sig, n.clone()),
        k: None,
        inner: Some(n),
    });
    out
}

/// The part of a term a context holds fixed or wraps: `base` is the plain
/// subterm and `hole` is the same subterm wrapped.
struct Ctx {
    name: &'static str,
    closed_only: bool,
    build: fn(&Sig, base: &Term, k: Option<usize>, hole: Term) -> (Term, Term),
}

fn float_of(sig: &Sig, t: Term) -> Term {
    app(sig.def("Float.ofNat"), vec![t])
}

fn contexts() -> Vec<Ctx> {
    vec![
        Ctx {
            name: "Succ",
            closed_only: false,
            build: |sig, b, _, h| (succ_term(sig, b.clone()), succ_term(sig, h)),
        },
        Ctx {
            name: "n + hole",
            closed_only: false,
            build: |sig, b, _, h| {
                (
                    app(sig.def("Nat.add"), vec![var(N, 0), b.clone()]),
                    app(sig.def("Nat.add"), vec![var(N, 0), h]),
                )
            },
        },
        Ctx {
            name: "n + hole, against Succ^k n",
            closed_only: true,
            build: |sig, _, k, h| {
                let expected = (0..k.unwrap()).fold(var(N, 0), |t, _| succ_term(sig, t));
                (expected, app(sig.def("Nat.add"), vec![var(N, 0), h]))
            },
        },
        Ctx {
            name: "hole + n",
            closed_only: false,
            build: |sig, b, _, h| {
                (
                    app(sig.def("Nat.add"), vec![b.clone(), var(N, 0)]),
                    app(sig.def("Nat.add"), vec![h, var(N, 0)]),
                )
            },
        },
        Ctx {
            name: "hole + n, against Succ^k n",
            closed_only: true,
            build: |sig, _, k, h| {
                let expected = (0..k.unwrap()).fold(var(N, 0), |t, _| succ_term(sig, t));
                (expected, app(sig.def("Nat.add"), vec![h, var(N, 0)]))
            },
        },
        Ctx {
            name: "number match",
            closed_only: false,
            build: |sig, b, _, h| {
                (
                    app(sig.def("numMatch"), vec![b.clone()]),
                    app(sig.def("numMatch"), vec![h]),
                )
            },
        },
        Ctx {
            name: "alike helpers, hole scrutinised",
            closed_only: false,
            build: |sig, b, _, h| {
                (
                    app(sig.def("pickA"), vec![b.clone(), var(N, 0)]),
                    app(sig.def("pickB"), vec![h, var(N, 0)]),
                )
            },
        },
        Ctx {
            name: "alike helpers, hole in the second place",
            closed_only: false,
            build: |sig, b, _, h| {
                (
                    app(sig.def("pickA"), vec![nat_term(sig, 1), b.clone()]),
                    app(sig.def("pickB"), vec![nat_term(sig, 1), h]),
                )
            },
        },
        Ctx {
            name: "alike helpers, hole unused",
            closed_only: false,
            build: |sig, b, _, h| {
                (
                    app(sig.def("ignoresFirst"), vec![b.clone(), var(N, 0)]),
                    app(sig.def("alsoIgnores"), vec![h, var(N, 0)]),
                )
            },
        },
        Ctx {
            name: "J base",
            closed_only: false,
            build: |_, b, _, h| {
                let motive = Term::Lam(
                    "y".into(),
                    Icit::Explicit,
                    Term::Lam("e".into(), Icit::Explicit, Term::Var(2).into()).into(),
                );
                (
                    b.clone(),
                    Term::J(motive.into(), h.into(), Term::Refl.into()),
                )
            },
        },
        Ctx {
            name: "projection of a record",
            closed_only: false,
            build: |sig, b, _, h| {
                (
                    b.clone(),
                    Term::Proj(
                        sig.data("Box"),
                        0,
                        Term::ctor(sig.data("Box"), 0, vec![h]).into(),
                    ),
                )
            },
        },
        Ctx {
            name: "Float.ofNat",
            closed_only: false,
            build: |sig, b, _, h| (float_of(sig, b.clone()), float_of(sig, h)),
        },
    ]
}

/// One pair that must be equal: the term, and the same with a device in it.
struct Wrapped {
    context: &'static str,
    device: &'static str,
    place: &'static str,
    base: String,
    left: Term,
    right: Term,
}

impl Wrapped {
    fn label(&self) -> String {
        format!(
            "{} with {} {} {}",
            self.context, self.device, self.place, self.base
        )
    }
}

fn wrapped_pairs(g: &Ev, sig: &Sig) -> Vec<Wrapped> {
    let mut out = Vec::new();
    for ctx in contexts() {
        for base in bases(sig) {
            if ctx.closed_only && base.k.is_none() {
                continue;
            }
            for dev in DEVICES {
                let mut holes = vec![("over", device(g, sig, dev, base.term.clone()))];
                if let Some(inner) = &base.inner {
                    holes.push((
                        "under Succ",
                        succ_term(sig, device(g, sig, dev, inner.clone())),
                    ));
                }
                for (place, hole) in holes {
                    let (left, right) = (ctx.build)(sig, &base.term, base.k, hole);
                    out.push(Wrapped {
                        context: ctx.name,
                        device: dev,
                        place,
                        base: base.name.to_string(),
                        left,
                        right,
                    });
                }
            }
        }
    }
    // Compact text and its cons cells, in a `match`. (`k * x` is a number's.)
    let chars = |s: &str| Term::Chars(Chars::whole(s.chars().collect::<Rc<[char]>>()));
    for (name, text) in [("\"ab\"", chars("ab")), ("\"\"", chars(""))] {
        let spelled = reference::expand_term(g, &text);
        let tag = |t: Term| app(sig.def("textTag"), vec![t]);
        for dev in DEVICES.iter().filter(|d| **d != "k * x") {
            for (place, plain, wrapped) in [
                ("over compact", &spelled, &text),
                ("over cons cells", &text, &spelled),
            ] {
                out.push(Wrapped {
                    context: "text match",
                    device: dev,
                    place,
                    base: name.to_string(),
                    left: tag(plain.clone()),
                    right: tag(device(g, sig, dev, wrapped.clone())),
                });
            }
        }
    }
    out
}

/// The gap a pair that fails today belongs to, and the ticket whose lane
/// fixes it (docs/proposals/equality-in-the-round.md §3.1). A lane that
/// fixes its gap makes its pairs pass: `wrapping_known_failures` shows
/// which, and the lane removes its `#[ignore]`.
fn known_gap(p: &Wrapped) -> Option<(&'static str, &'static str)> {
    let closed = ["1", "2", "3"].contains(&p.base.as_str());
    let folded = ["decreasing", "k * x"].contains(&p.device);
    let over = p.place == "over";
    match p.context {
        // The scrutinee is a folded call, or a number: the tree comparison
        // of two alike helpers doesn't take its branch.
        "alike helpers, hole scrutinised"
            if folded && over && ["n", "Succ n"].contains(&p.base.as_str()) =>
        {
            Some(("G1", "SW-2243"))
        }
        "alike helpers, hole scrutinised" if closed => Some(("G3", "SW-2243")),
        "alike helpers, hole in the second place" if p.base == "n" && over => {
            Some(("G3", "SW-2243"))
        }
        // `+` on a folded second argument.
        "n + hole" | "n + hole, against Succ^k n"
            if p.device == "decreasing"
                && (closed || p.base == "0" && over || p.base == "Succ n" && over) =>
        {
            Some(("G2", "SW-2244"))
        }
        // (With `n` a number, the pairs over `n` are these too.)
        "Float.ofNat" if p.device == "decreasing" => Some(("G4", "SW-2244")),
        // A number `match` on `Succ` of a folded call.
        "number match" if p.device == "decreasing" && !over && closed => Some(("G5", "SW-2244")),
        // New: a number's partial `+` on `Succ` of a folded call.
        "hole + n" | "hole + n, against Succ^k n"
            if p.device == "decreasing" && !over && closed =>
        {
            Some(("G9", "SW-2244"))
        }
        _ => None,
    }
}

/// The pairs among `pairs` that some mode (or the plain evaluator) calls
/// different, each with the modes that did.
fn unequal(g: &Ev, pairs: &[&Wrapped]) -> Vec<String> {
    let env: Vec<Value> = (0..LEVEL).map(Value::var).collect();
    let mut bad = Vec::new();
    for pair in pairs {
        let who: Vec<&str> = MODES
            .into_iter()
            .chain([PLAIN])
            .filter(|&how| {
                !in_mode(g, how, || {
                    let a = eval_how(g, &env, &pair.left, how);
                    let b = eval_how(g, &env, &pair.right, how);
                    conv_how(g, &a, &b, how)
                })
            })
            .map(How::name)
            .collect();
        if !who.is_empty() {
            bad.push(format!("{}: different in {}", pair.label(), who.join(", ")));
        }
    }
    bad
}

fn with_wrapped<T>(f: impl FnOnce(&Ev, Vec<Wrapped>) -> T) -> T {
    let mut session = Session::eager();
    session.load("wrap.sw", WRAP_PROGRAM).expect("loads");
    let g = &session.elab.ev();
    let sig = wrap_sig(g);
    f(g, wrapped_pairs(g, &sig))
}

#[test]
fn wrapping_a_subterm_in_an_identity_keeps_it_equal() {
    with_wrapped(|g, all| {
        let pairs: Vec<&Wrapped> = all.iter().filter(|p| known_gap(p).is_none()).collect();
        let bad = unequal(g, &pairs);
        assert!(
            bad.is_empty(),
            "{} of {} pairs differ:\n{}",
            bad.len(),
            pairs.len(),
            bad.join("\n")
        );
    })
}

/// The pairs of a known gap are equal in the plain evaluator: what the
/// lazy modes get wrong is not a matter of opinion.
#[test]
fn the_known_gaps_hold_in_the_plain_evaluator() {
    with_wrapped(|g, all| {
        let env: Vec<Value> = (0..LEVEL).map(Value::var).collect();
        let known: Vec<&Wrapped> = all.iter().filter(|p| known_gap(p).is_some()).collect();
        assert!(!known.is_empty());
        for pair in known {
            let same = in_mode(g, PLAIN, || {
                let a = eval_how(g, &env, &pair.left, PLAIN);
                let b = eval_how(g, &env, &pair.right, PLAIN);
                conv_how(g, &a, &b, PLAIN)
            });
            assert!(same, "{}: the plain evaluator says different", pair.label());
        }
    })
}

/// Every pair of gap `gap` must be equal in every mode.
fn known_wrapping(gap: &str) {
    with_wrapped(|g, all| {
        let pairs: Vec<&Wrapped> = all
            .iter()
            .filter(|p| known_gap(p).is_some_and(|(id, _)| id == gap))
            .collect();
        assert!(!pairs.is_empty(), "no pairs for {gap}");
        let bad = unequal(g, &pairs);
        assert!(
            bad.is_empty(),
            "{gap}: {} of {} pairs differ:\n{}",
            bad.len(),
            pairs.len(),
            bad.join("\n")
        );
    })
}

#[test]
#[ignore = "known failure G1 (folded scrutinee of alike helpers), fixed by SW-2243"]
fn wrapping_known_failure_g1() {
    known_wrapping("G1")
}

#[test]
#[ignore = "known failure G2 (`+` on a folded number), fixed by SW-2244"]
fn wrapping_known_failure_g2() {
    known_wrapping("G2")
}

#[test]
#[ignore = "known failure G3 (a number scrutinee of alike helpers), fixed by SW-2243"]
fn wrapping_known_failure_g3() {
    known_wrapping("G3")
}

#[test]
#[ignore = "known failure G4 (a float primitive on a folded number), fixed by SW-2244"]
fn wrapping_known_failure_g4() {
    known_wrapping("G4")
}

#[test]
#[ignore = "known failure G5 (a number `match` on `Succ` of a folded call), fixed by SW-2244"]
fn wrapping_known_failure_g5() {
    known_wrapping("G5")
}

#[test]
#[ignore = "known failure G9 (found by SW-2242: native `+` on `Succ` of a folded call), fixed by SW-2244"]
fn wrapping_known_failure_g9() {
    known_wrapping("G9")
}

// ---------------------------------------------------------------------------
// The six probes of docs/proposals/equality-in-the-round.md §3
// ---------------------------------------------------------------------------

/// Loads one of the probe files (`docs/repros/sw-2236/`, kept as found):
/// each has theorems true by computation and rejected today, next to
/// the same shape without the lazy form, which passes.
fn load_probe(name: &str, source: &str) {
    let mut session = Session::eager();
    if let Err(diagnostics) = session.load(name, source) {
        let shown: Vec<String> = diagnostics
            .iter()
            .map(|d| stitchwort_driver::render::render(&session.sources, d, false))
            .collect();
        panic!("{name} is rejected:\n{}", shown.join("\n"));
    }
}

#[test]
#[ignore = "known failure G1 (a folded call as the scrutinee of alike helpers), fixed by SW-2243"]
fn probe_g1_folded_scrutinee() {
    load_probe(
        "g1.sw",
        include_str!("../../../../docs/repros/sw-2236/g1.sw"),
    );
}

#[test]
#[ignore = "known failure G2 (`+` on a folded number), fixed by SW-2244"]
fn probe_g2_sum_with_a_folded_number() {
    load_probe(
        "g2.sw",
        include_str!("../../../../docs/repros/sw-2236/g2.sw"),
    );
}

#[test]
#[ignore = "known failure G3 (a number as the scrutinee of alike helpers), fixed by SW-2243"]
fn probe_g3_number_scrutinee() {
    load_probe(
        "g3.sw",
        include_str!("../../../../docs/repros/sw-2236/g3.sw"),
    );
}

/// Run glued only: with `STITCHWORT_GLUE=0` std's `Float` file fails its
/// pins (SW-2254), so the probe can't load unglued. (The wrapping pairs of
/// G4 do run unglued: they switch gluing off after loading.)
#[test]
#[ignore = "known failure G4 (a float primitive on a folded number), fixed by SW-2244"]
fn probe_g4_float_of_a_folded_number() {
    load_probe(
        "g4.sw",
        include_str!("../../../../docs/repros/sw-2236/g4.sw"),
    );
}

#[test]
#[ignore = "known failure G5 (a number `match` on `Succ` of a folded call), fixed by SW-2244"]
fn probe_g5_number_match_under_succ() {
    load_probe(
        "g5.sw",
        include_str!("../../../../docs/repros/sw-2236/g5.sw"),
    );
}

#[test]
fn probe_g6_same_definition_stuck_calls() {
    load_probe(
        "g6.sw",
        include_str!("../../../../docs/repros/sw-2236/g6.sw"),
    );
}

#[test]
#[ignore = "known failure G7 (a tree's leaf against the other tree's stuck `case`), fixed by SW-2243"]
fn probe_g7_leaf_against_a_stuck_case() {
    load_probe(
        "g7.sw",
        include_str!("../../../../docs/repros/sw-2236/g7.sw"),
    );
}

#[test]
#[ignore = "known failure G8 (two alike number-literal `match`es), fixed by SW-2243"]
fn probe_g8_alike_number_matches() {
    load_probe(
        "g8.sw",
        include_str!("../../../../docs/repros/sw-2236/g8.sw"),
    );
}

/// G6 as the equivalence the matrix requires: `ignoresFirst 1 n` and
/// `ignoresFirst 2 n` are both equal to `alsoIgnores 2 n`, so they must be
/// equal to each other.
#[test]
fn the_relation_is_transitive_over_an_unused_argument() {
    let mut session = Session::eager();
    session.load("wrap.sw", WRAP_PROGRAM).expect("loads");
    let g = &session.elab.ev();
    let sig = wrap_sig(g);
    let call = |def: &str, k: usize| {
        (
            format!("{def} {k} n"),
            app(sig.def(def), vec![nat_term(&sig, k), var(N, 0)]),
        )
    };
    let terms = vec![
        call("ignoresFirst", 1),
        call("ignoresFirst", 2),
        call("alsoIgnores", 2),
    ];
    compared_alike(g, &sig, &terms);
}

/// Closed ground truth: with `n` a number, every pair of the same context
/// (the wrapped pair itself, and the plain subterm of one base against the
/// plain subterm of another) is compared by every mode, and the answer must
/// be that of the *normal forms* of the two sides, which for closed first-order
/// values is syntactic equality (no policy about stuck calls shared with the
/// evaluators under test; the normal forms come from the plain evaluator).
#[test]
fn closed_terms_agree_with_their_normal_forms() {
    with_wrapped(|g, all| {
        let mut bad = Vec::new();
        let mut checked = 0;
        for k in [0, 1, 3, 4] {
            let mut env: Vec<Value> = (0..LEVEL).map(Value::var).collect();
            env[N] = (0..k).fold(Value::Ctor(g_nat(g), 0, Vec::new().into()), |v, _| {
                Value::Ctor(g_nat(g), 1, [v].into())
            });
            let normal = |t: &Term| {
                in_mode(g, PLAIN, || {
                    let v = reference::eval(g, &env, t).unwrap();
                    format!("{:?}", reference::quote(g, LEVEL, &v).unwrap())
                })
            };
            let mut pairs: Vec<(String, &Term, &Term)> = all
                .iter()
                .filter(|p| p.base != "Succ n" && known_gap(p).is_none())
                .map(|p| (p.label(), &p.left, &p.right))
                .collect();
            // Plain subterms of different bases in one context.
            for (i, a) in all.iter().enumerate() {
                for b in all[i + 1..].iter().take(12) {
                    if a.context == b.context && a.device == "none" && b.device == "none" {
                        pairs.push((
                            format!("{} against {}", a.label(), b.label()),
                            &a.left,
                            &b.left,
                        ));
                    }
                }
            }
            for (label, a, b) in pairs {
                let expected = normal(a) == normal(b);
                for how in MODES {
                    let got = in_mode(g, how, || {
                        let (x, y) = (eval_how(g, &env, a, how), eval_how(g, &env, b, how));
                        conv_how(g, &x, &y, how)
                    });
                    checked += 1;
                    if got != expected {
                        bad.push(format!(
                            "n = {k}: {label}: normal forms say {expected}, {} says {got}",
                            how.name()
                        ));
                    }
                }
            }
        }
        assert!(checked > 1000);
        assert!(
            bad.is_empty(),
            "{} of {checked} differ:\n{}",
            bad.len(),
            bad.join("\n")
        );
    })
}

fn g_nat(g: &Ev) -> DataId {
    g.env.builtins().nat.expect("Nat")
}

/// The plain evaluator folds nothing: a `decreasing` call, a dictionary
/// field, a field of a call, a number literal and `1 * x` come out as their
/// values, where the ordinary reference evaluator leaves each compact or
/// folded.
#[test]
fn the_plain_evaluator_folds_nothing() {
    let mut session = Session::eager();
    session.load("wrap.sw", WRAP_PROGRAM).expect("loads");
    let g = &session.elab.ev();
    let sig = wrap_sig(g);
    let env: Vec<Value> = (0..LEVEL).map(Value::var).collect();
    let three = nat_term(&sig, 3);
    let terms = [
        (
            "decreasing call",
            device(g, &sig, "decreasing", three.clone()),
        ),
        (
            "dictionary field",
            device(g, &sig, "dictionary", three.clone()),
        ),
        (
            "field of a call",
            device(g, &sig, "field of a call", three.clone()),
        ),
        ("1 * n", device(g, &sig, "k * x", var(N, 0))),
        ("a number literal", Term::Nat(Rc::new(3u32.into()))),
    ];
    for (name, term) in &terms {
        let plain = in_mode(g, PLAIN, || reference::eval(g, &env, term).unwrap());
        assert_eq!(reference::compact_or_lazy(g, &plain), None, "{name}");
        // Computed: a chain of constructors or the variable itself, never a
        // call left standing.
        let computed = match &plain {
            Value::Ctor(..) => true,
            Value::Neutral(Head::Var(..), spine) => spine.is_empty(),
            _ => false,
        };
        assert!(computed, "{name}: {plain:?}");
        // The same term in the ordinary reference evaluator is compact or
        // folded: the switch is what made the difference.
        let ordinary = reference::eval(g, &env, term).unwrap();
        let lazy = matches!(&ordinary, Value::Nat(_) | Value::Neutral(Head::Def(_), _));
        assert!(lazy, "{name}: {ordinary:?}");
    }
}
