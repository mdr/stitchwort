//! The kernel's comparison with proof positions skipped, over every term of
//! one type up to depth 2 built from a fixed signature
//! (docs/proposals/proof-irrelevance.md §8, "Equivalence and gluing,
//! enumerated"). For every pair it must give one answer with gluing on,
//! with the shortcuts disabled, with gluing off and from the reference
//! evaluator; the answers must form an equivalence relation; and a pair
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

use stitchwort_core::term::Term;
use stitchwort_core::value::{Value, conv, eval, set_shortcuts_disabled};
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
    nat: DataId,
    tok: DataId,
    pb: DataId,
    defs: Vec<(&'static str, DefId)>,
}

impl Sig {
    fn def(&self, name: &str) -> Term {
        Term::Def(self.defs.iter().find(|(n, _)| *n == name).expect(name).1)
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
    let pb = |v| Term::ctor(sig.pb, 0, vec![var(v, 0)]);
    match name {
        "Succ" => Term::ctor(sig.nat, 1, vec![x]),
        "modP p" => app(sig.def("modP"), vec![x, var(P, 0)]),
        "modP q" => app(sig.def("modP"), vec![x, var(Q, 0)]),
        "tokNat t" => app(sig.def("tokNat"), vec![var(T, 0), x]),
        "tokNat MkTok" => app(sig.def("tokNat"), vec![Term::ctor(sig.tok, 0, vec![]), x]),
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

/// Every term up to depth 2, with a name for messages.
fn terms(sig: &Sig) -> Vec<(String, Term)> {
    let atoms = vec![
        ("n".to_string(), var(N, 0)),
        ("0".to_string(), Term::ctor(sig.nat, 0, vec![])),
    ];
    let mut level = atoms.clone();
    for _ in 0..2 {
        let mut next = atoms.clone();
        for (name, term) in &level {
            for o in OPS {
                next.push((format!("{o} ({name})"), op(sig, o, term.clone())));
            }
        }
        level = next;
    }
    level
}

fn signature(g: &Ev) -> Sig {
    let data = |name: &str| {
        DataId(
            g.env
                .datas()
                .iter()
                .position(|d| &**d.name() == name)
                .unwrap_or_else(|| panic!("no `{name}`")),
        )
    };
    let names = [
        "modP", "tokNat", "unboxK", "keepK", "pickA", "pickB", "applyAt",
    ];
    let defs = names
        .iter()
        .map(|name| {
            let id = g.env.defs().iter().position(|d| &**d.name() == *name);
            (*name, DefId(id.unwrap_or_else(|| panic!("no `{name}`"))))
        })
        .collect();
    Sig {
        nat: data("Nat"),
        tok: data("Tok"),
        pb: data("PB"),
        defs,
    }
}

/// The equality matrix, by `value::conv` with gluing `glue` and the
/// shortcuts on or off, or by the reference evaluator.
fn matrix(g: &Ev, env: &[Value], terms: &[(String, Term)], how: How) -> Vec<Vec<bool>> {
    let was = g.machine.glue.replace(how.glue);
    set_shortcuts_disabled(!how.shortcuts);
    let values: Vec<Value> = terms
        .iter()
        .map(|(_, t)| {
            if how.reference {
                reference::eval(g, env, t).unwrap()
            } else {
                eval(g, env, t).unwrap()
            }
        })
        .collect();
    let rows = values
        .iter()
        .map(|a| {
            values
                .iter()
                .map(|b| {
                    if how.reference {
                        reference::conv(g, LEVEL, a, b).unwrap()
                    } else {
                        conv(g, LEVEL, a, b).unwrap()
                    }
                })
                .collect()
        })
        .collect();
    set_shortcuts_disabled(false);
    g.machine.glue.set(was);
    rows
}

#[derive(Clone, Copy, Debug)]
struct How {
    glue: bool,
    shortcuts: bool,
    reference: bool,
}

const GLUED: How = How {
    glue: true,
    shortcuts: true,
    reference: false,
};

#[test]
fn every_pair_is_compared_alike_and_the_relation_is_an_equivalence() {
    let mut session = Session::eager();
    session.load("equivalence.sw", PROGRAM).expect("loads");
    let g = &session.elab.ev();
    let sig = signature(g);
    let terms = terms(&sig);
    let env: Vec<Value> = (0..LEVEL).map(Value::var).collect();
    let glued = matrix(g, &env, &terms, GLUED);
    let others = [
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
    let name = |i: usize| &terms[i].0;
    for how in others {
        let other = matrix(g, &env, &terms, how);
        for i in 0..terms.len() {
            for j in 0..terms.len() {
                assert_eq!(
                    glued[i][j],
                    other[i][j],
                    "{} against {}: glued says {}, {how:?} says {}",
                    name(i),
                    name(j),
                    glued[i][j],
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
        (0..k).fold(Value::Ctor(sig.nat, 0, Vec::new().into()), |v, _| {
            Value::Ctor(sig.nat, 1, [v].into())
        })
    };
    for k in [0, 1] {
        let mut known = env.clone();
        known[N] = nat(k);
        let after = matrix(g, &known, &terms, GLUED);
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
    // The relation isn't trivial: some pairs differ only in proofs and are
    // equal, others differ.
    let count = glued.iter().flatten().filter(|b| **b).count();
    assert!(count > terms.len() && count < terms.len() * terms.len());
}
