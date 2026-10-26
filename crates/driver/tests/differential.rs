//! The evaluator (an abstract machine, `value.rs`) against the recursive
//! reference evaluator it was derived from (`reference.rs`): on the same
//! programs they must give the same normal forms. Both results are turned
//! back into terms by the reference's own `quote`, so a quoting bug can't hide
//! a disagreement (docs/proposals/stack-safe-evaluation.md).
//!
//! These use small inputs; deep ones are in `resources.rs`. The reference
//! recurses on the Rust stack, so they run on a thread with a large one.

use std::path::Path;

use stitchwort_core::reference;
use stitchwort_core::term::Term;
use stitchwort_core::value::{self, Elim, Head, Spine, Value, machine_runs};
use stitchwort_core::{DefId, Globals, Icit};
use stitchwort_driver::driver::{Session, par_map, tier_sample, with_stack};
use stitchwort_syntax::{SourceMap, Span};

// The deepest example is io.sw's 5,000 prints through `IO.simulate`, which the
// reference evaluates recursively, a few frames per print. Since partial
// handlers lane D (2404ada2) a handler folds with `foldCompD` and forwards with
// `callD`/`translateD`, one more layer of definitions per operation: in a
// release build it needs between 80 and 96 MiB (it needed 56 to 64 before), so
// 128 MiB. Debug builds use much more stack per frame.
const STACK: usize = if cfg!(debug_assertions) { 512 } else { 128 } * 1024 * 1024;

/// The normal form of `value`, as printed by the reference.
fn normal(g: &Globals, level: usize, value: &Value) -> String {
    format!(
        "{:?}",
        reference::quote(g, level, value).expect("no limits")
    )
}

/// The icits of a definition's parameters, from its body's lambdas.
fn param_icits(g: &Globals, id: DefId) -> Vec<Icit> {
    let def = g.def(id);
    let mut icits = Vec::new();
    let Some(mut term) = def.body().map(|b| &**b) else {
        return icits;
    };
    for _ in 0..def.arity {
        let Term::Lam(_, icit, body) = term.strip_loc() else {
            break;
        };
        icits.push(*icit);
        term = body;
    }
    icits
}

/// Definitions whose normal form on fresh variables is exponentially large,
/// so neither evaluator's result can be quoted. std `Random`'s xor halves its
/// arguments 64 times, and on a variable `a` the term for `a / 2` is
/// `Nat.divFuel a a 2`, which mentions `a` twice: each bit multiplies the
/// normal form's size by 4 (`Random.xorBits k a b` printed: 7,363 characters
/// at k = 2, 30 million at 8, 485 million at 10), and `Random.xor64` is
/// k = 64. Everything that calls it on an unknown number is as big: `main` in
/// random-seed.sw rolls with the seed `IO.randomSeed` gives, a variable in its
/// normal form. An entry is a name, or `example: name` for one example's
/// definition. Their closed uses (the module's and the example's tests) are
/// still compared.
const NORMAL_FORM_TOO_BIG: &[&str] = &[
    "Random.xor64",
    "Random.next",
    "Random.below",
    "Random.between",
    "Random.chance",
    "accept/random-seed.sw: main",
];

/// Compares the two evaluators on everything `g` defines: each definition
/// applied to fresh variables (open terms, stuck case trees, partial
/// application), and each definition's type.
fn compare_definitions(g: &Globals, what: &str) -> usize {
    let mut compared = 0;
    for i in 0..g.defs.len() {
        let id = DefId(i);
        let def = g.def(id);
        if def.body().is_none() {
            continue;
        }
        let icits = param_icits(g, id);
        // Applied to every prefix of its parameters, so partial
        // applications are covered too; none for a definition whose normal
        // form on variables is too big to build (its type is still compared).
        let too_big = NORMAL_FORM_TOO_BIG
            .iter()
            .any(|entry| *entry == &*def.name || *entry == format!("{what}: {}", def.name));
        let prefixes = if too_big { 0..0 } else { 0..icits.len() + 1 };
        for n in prefixes {
            let mut fast = value::eval(g, &[], &Term::Def(id)).expect("no limits");
            let mut slow = reference::eval(g, &[], &Term::Def(id)).expect("no limits");
            for (level, icit) in icits.iter().take(n).enumerate() {
                fast = value::apply_icit(g, fast, Value::var(level), *icit).expect("no limits");
                slow = reference::apply_icit(g, slow, Value::var(level), *icit).expect("no limits");
            }
            assert_eq!(
                normal(g, n, &fast),
                normal(g, n, &slow),
                "{what}: `{}` applied to {n} variable(s)",
                def.name
            );
            // The machine's quote (a work list) against the reference's,
            // which expands compact lists: quotation commutes with expansion.
            assert_eq!(
                format!(
                    "{:?}",
                    reference::expand_term(g, &value::quote(g, n, &fast).expect("no limits"))
                ),
                normal(g, n, &fast),
                "{what}: quoting `{}` applied to {n} variable(s)",
                def.name
            );
            assert!(
                value::conv(g, n, &fast, &slow).expect("no limits"),
                "{what}: `{}` applied to {n} variable(s) isn't convertible with itself",
                def.name
            );
            compared += 1;
        }
        let ty = reference::eval(g, &[], &def.ty).expect("no limits");
        assert!(value::conv(g, 0, &def.ty_value, &ty).expect("no limits"));
        assert_eq!(
            normal(g, 0, &def.ty_value),
            normal(g, 0, &ty),
            "{what}: the type of `{}`",
            def.name
        );
    }
    compared
}

/// The machine's `conv` (a work list) against the reference's. Conversion is
/// only meaningful between values of the same type, so it compares each
/// definition's value (unapplied, so partially applied definitions and eta
/// are covered) with every other definition's whose type is convertible
/// with its own, and each definition's type with the next few types.
fn compare_conversion(g: &Globals, what: &str) -> usize {
    let defs: Vec<(String, Value, Value)> = (0..g.defs.len())
        .filter(|&i| g.defs[i].body().is_some())
        .map(|i| {
            let def = &g.defs[i];
            let value = value::eval(g, &[], &Term::Def(DefId(i))).expect("no limits");
            (def.name.to_string(), value, def.ty_value.clone())
        })
        .collect();
    let agree = |x: &Value, y: &Value, what: &str| {
        let fast = value::conv(g, 0, x, y).expect("no limits");
        let slow = reference::conv(g, 0, x, y).expect("no limits");
        assert_eq!(fast, slow, "{what}");
        fast
    };
    let mut compared = 0;
    for (i, (x_name, x, x_ty)) in defs.iter().enumerate() {
        for (y_name, y, y_ty) in defs.iter().skip(i) {
            if agree(
                x_ty,
                y_ty,
                &format!("{what}: the types of `{x_name}` and `{y_name}`"),
            ) {
                agree(x, y, &format!("{what}: `{x_name}` and `{y_name}`"));
                compared += 1;
            }
        }
    }
    compared
}

fn examples() -> Vec<(String, String)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut found = Vec::new();
    for dir in ["accept", "extract"] {
        let mut paths: Vec<_> = std::fs::read_dir(root.join(dir))
            .expect("examples directory")
            .map(|e| e.expect("entry").path())
            .filter(|p| p.extension().is_some_and(|e| e == "sw"))
            .collect();
        paths.sort();
        for path in paths {
            let name = format!("{dir}/{}", path.file_name().unwrap().to_string_lossy());
            let source = std::fs::read_to_string(&path).expect("readable");
            // An example can opt out with a `-- differential: skip (reason)`
            // line, e.g. when it is too deep for the recursive reference
            // evaluator.
            if source
                .lines()
                .any(|l| l.starts_with("-- differential: skip"))
            {
                continue;
            }
            found.push((name, source));
        }
    }
    found
}

#[test]
fn the_evaluators_agree_on_the_prelude_and_every_example() {
    with_stack(STACK, || {
        let session = Session::for_stack(STACK);
        let prelude = compare_definitions(&session.elab.globals, "prelude");
        assert!(prelude > 200, "only {prelude} comparisons in the prelude");
        let conversions = compare_conversion(&session.elab.globals, "prelude");
        assert!(
            conversions > 100,
            "only {conversions} conversions in the prelude"
        );
        // Each example in its own session, on the thread pool. A corpus sweep:
        // a fixed sample below the full tier.
        par_map(STACK, &tier_sample(examples(), 4), |(name, text)| {
            let mut session = Session::for_stack(STACK);
            session.load(name, text).expect("examples check");
            let g = &session.elab.globals;
            compare_definitions(g, name);
            compare_conversion(g, name);
            for test in &session.elab.tests {
                let term = Term::Def(test.def);
                let fast = value::eval(g, &[], &term).expect("no limits");
                let slow = reference::eval(g, &[], &term).expect("no limits");
                assert_eq!(
                    normal(g, 0, &fast),
                    normal(g, 0, &slow),
                    "{name}: test \"{}\"",
                    test.name
                );
            }
        });
    });
}

fn span() -> Span {
    Span::point(SourceMap::new().add("test", ""), 0)
}

fn def(g: &Globals, name: &str) -> DefId {
    DefId(
        g.defs
            .iter()
            .position(|d| &*d.name == name)
            .unwrap_or_else(|| panic!("no `{name}`")),
    )
}

/// Both evaluators on `value` forced, and on `f` applied to it.
fn agree_after_forcing(g: &Globals, f: DefId, value: &Value) -> String {
    let fast = value::force(g, value.clone()).expect("no limits");
    let slow = reference::force(g, value.clone()).expect("no limits");
    assert_eq!(normal(g, 0, &fast), normal(g, 0, &slow));
    let fast = value::apply(g, Value::Neutral(Head::Def(f), Spine::new()), value.clone())
        .expect("no limits");
    let slow = reference::apply_icit(
        g,
        Value::Neutral(Head::Def(f), Spine::new()),
        value.clone(),
        Icit::Explicit,
    )
    .expect("no limits");
    let (fast, slow) = (normal(g, 0, &fast), normal(g, 0, &slow));
    assert_eq!(fast, slow);
    fast
}

/// A case stuck on a metavariable takes a step once it's solved: the machine
/// forces the scrutinee, replaying the metavariable's spine.
#[test]
fn a_stuck_case_unblocks_when_its_metavariable_is_solved() {
    let session = Session::new();
    let g = &session.elab.globals;
    let pred = def(g, "Nat.pred");
    // `?m 3`, with `?m` unsolved: `pred (?m 3)` is stuck.
    let m = g.new_meta(span());
    let stuck = Value::Neutral(
        Head::Meta(m),
        vec![Elim::App(
            stitchwort_core::native::nat_value(3u32.into()),
            Icit::Explicit,
        )]
        .into(),
    );
    assert_eq!(
        agree_after_forcing(g, pred, &stuck),
        format!(
            "{:?}",
            Term::app(
                Term::Def(pred),
                Term::app(Term::Meta(m), Term::Nat(std::rc::Rc::new(3u32.into())))
            )
        )
    );
    // `?m := x => Succ (Succ x)`: now `pred (?m 3)` is 4.
    let nat = g.builtins.nat.unwrap();
    let solution = value::eval(
        g,
        &[],
        &Term::Lam(
            "x".into(),
            Icit::Explicit,
            std::rc::Rc::new(Term::ctor(
                nat,
                1,
                vec![Term::ctor(nat, 1, vec![Term::Var(0)])],
            )),
        ),
    )
    .unwrap();
    g.solve_meta(m, solution);
    assert_eq!(agree_after_forcing(g, pred, &stuck), "Nat(4)");
}

/// `J` on a neutral proof stays stuck, keeping its motive and base; on a
/// solved metavariable standing for `rfl`, it reduces to the base, including
/// when the `J` is in the metavariable's spine.
#[test]
fn j_with_reflexive_and_stuck_proofs() {
    let session = Session::new();
    let g = &session.elab.globals;
    let nat = g.builtins.nat.unwrap();
    let zero = Term::ctor(nat, 0, vec![]);
    let motive = Term::Lam(
        "y".into(),
        Icit::Explicit,
        std::rc::Rc::new(Term::Lam(
            "p".into(),
            Icit::Explicit,
            std::rc::Rc::new(Term::data(nat, vec![])),
        )),
    );
    let j = |proof: Term| Term::J(motive.clone().into(), zero.clone().into(), proof.into());
    // Stuck on a variable.
    let env = [Value::var(0)];
    let fast = value::eval(g, &env, &j(Term::Var(0))).unwrap();
    let slow = reference::eval(g, &env, &j(Term::Var(0))).unwrap();
    assert_eq!(normal(g, 1, &fast), normal(g, 1, &slow));
    assert!(
        matches!(fast, Value::Neutral(Head::Var(0), ref s) if matches!(s[..], [Elim::J { .. }]))
    );
    // Stuck on an unsolved metavariable, then solved with `rfl`.
    let m = g.new_meta(span());
    let fast = value::eval(g, &[], &j(Term::Meta(m))).unwrap();
    let slow = reference::eval(g, &[], &j(Term::Meta(m))).unwrap();
    assert_eq!(normal(g, 0, &fast), normal(g, 0, &slow));
    g.solve_meta(m, Value::Refl);
    let forced = value::force(g, fast.clone()).unwrap();
    let forced_ref = reference::force(g, slow).unwrap();
    assert_eq!(normal(g, 0, &forced), normal(g, 0, &forced_ref));
    assert_eq!(normal(g, 0, &forced), "Nat(0)");
}

/// A deep evaluation runs in one machine, not one per level; and the
/// reference never starts the machine.
#[test]
fn deep_evaluation_runs_in_one_machine_and_the_reference_in_none() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load(
                "deep.sw",
                "import Std (List)\n\n\
                 def replicate : Nat -> a -> List a\n  \
                 | Zero,   x => Nil\n  \
                 | Succ n, x => Cons x (replicate n x)\n\n\
                 def total (n : Nat) : Nat := List.length (replicate n 1) + List.length (replicate n 2)\n",
            )
            .unwrap();
        let g = &session.elab.globals;
        let term = Term::app(
            Term::Def(def(g, "total")),
            Term::Nat(std::rc::Rc::new(1000u32.into())),
        );
        let before = machine_runs();
        let fast = value::eval(g, &[], &term).unwrap();
        assert_eq!(machine_runs() - before, 1);
        let before = machine_runs();
        let slow = reference::eval(g, &[], &term).unwrap();
        assert_eq!(machine_runs(), before, "the reference started the machine");
        assert_eq!(normal(g, 0, &fast), normal(g, 0, &slow));
    });
}

/// Quotients (docs/proposals/map-equality.md §7.2): both evaluators apply
/// the one rule, `Quot.lift f h (Quot.mk a)` to `f a`, through definitions
/// and folded theorems, leave `Quot.ind`, `Quot.sound` and `J` on them
/// stuck, and keep a definition that lifts a variable folded; and conversion
/// agrees on all of it. Every definition is compared applied to variables
/// (`compare_definitions`), so the folded and stuck forms are covered.
#[test]
fn the_evaluators_agree_on_quotients() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load(
                "quotients.sw",
                "import Std (Eq)\n\n\
                 def AllTrue (x: Bool) (y: Bool): Prop := Unit\n\
                 def Q: Type := Quot Bool AllTrue\n\
                 theorem same: (Quot.mk False: Q) = Quot.mk True := Quot.sound Trivial\n\
                 def stuck: Nat := J (y p => Nat) 0 same\n\
                 def byInd: 0 = 0 := Quot.ind [p := q => 0 = 0] (b => rfl) (Quot.mk False: Q)\n\
                 def stuckToo: Nat := J (y p => Nat) 0 byInd\n\
                 def BoolEq (x: Bool) (y: Bool): Prop := x = y\n\
                 def QE: Type := Quot Bool BoolEq\n\
                 def toNat (b: Bool): Nat := if b then 1 else 0\n\
                 def toNatRespects (x: Bool) (y: Bool) (same: BoolEq x y): toNat x = toNat y :=\n  \
                 rewrite same in rfl\n\
                 def observe (q: QE): Nat := Quot.lift toNat toNatRespects q\n\
                 def mkTrue: QE := Quot.mk True\n\
                 def one: Nat := observe mkTrue\n\
                 def oneDirectly: Nat := Quot.lift toNat toNatRespects mkTrue\n\
                 def viaMatch (b: Bool) (q: QE): Nat :=\n  \
                 match b with\n    \
                 | True => Quot.lift toNat toNatRespects q\n    \
                 | False => 0\n\
                 def twice (q: QE): Nat := observe q + observe q\n\
                 def proofLift (q: Q): 0 = 0 := Quot.lift (b => rfl) (x y r => rfl) q\n\
                 def propLift (q: Q): Prop := Quot.lift (b => Unit) (x y r => rfl) q\n",
            )
            .unwrap();
        let g = &session.elab.globals;
        assert!(compare_definitions(g, "quotients.sw") > 20);
        assert!(compare_conversion(g, "quotients.sw") > 20);
        let closed = |name: &str| {
            let term = Term::Def(def(g, name));
            let fast = value::eval(g, &[], &term).expect("no limits");
            let slow = reference::eval(g, &[], &term).expect("no limits");
            assert_eq!(normal(g, 0, &fast), normal(g, 0, &slow), "{name}");
            normal(g, 0, &fast)
        };
        assert_eq!(closed("one"), "Nat(1)");
        assert_eq!(closed("oneDirectly"), "Nat(1)");
        // `J` on `Quot.sound`, and on a proof by `Quot.ind`, is stuck: a
        // closed `Nat` that isn't a number (§9.1, A3 and A6's kernel side).
        for name in ["stuck", "stuckToo"] {
            let shown = closed(name);
            assert!(shown.starts_with("J("), "{name}: {shown}");
        }
        // A lift of a variable, folded by name; unfolded, the lift itself.
        let observe = def(g, "observe");
        let applied = |f: DefId| {
            let fast = value::apply(
                g,
                value::eval(g, &[], &Term::Def(f)).unwrap(),
                Value::var(0),
            )
            .unwrap();
            let slow = reference::apply_icit(
                g,
                reference::eval(g, &[], &Term::Def(f)).unwrap(),
                Value::var(0),
                Icit::Explicit,
            )
            .unwrap();
            assert_eq!(normal(g, 1, &fast), normal(g, 1, &slow));
            normal(g, 1, &fast)
        };
        assert_eq!(
            applied(observe),
            format!("App(Def(DefId({})), Var(0), Explicit)", observe.0)
        );
    });
}

/// `let` (docs/proposals/let.md stage 2): both evaluators put the value in
/// the environment, once, before the body, on closed and open terms, with the
/// value or the body a function, nested, and under binders. The elaborator
/// doesn't produce `Let` yet, so the terms are built here.
#[test]
fn the_evaluators_agree_on_let() {
    with_stack(STACK, || {
        let session = Session::eager_for_stack(STACK);
        let g = &session.elab.globals;
        let nat = g.builtins.nat.unwrap();
        let nat_ty = || Term::data(nat, vec![]);
        let num = |n: u32| Term::Nat(std::rc::Rc::new(n.into()));
        let add = |a: Term, b: Term| Term::app(Term::app(Term::Def(def(g, "Nat.add")), a), b);
        let range = |n: Term| Term::app(Term::Def(def(g, "List.range")), n);
        let length = |xs: Term| {
            Term::app(
                Term::app_icit(Term::Def(def(g, "List.length")), nat_ty(), Icit::Implicit),
                xs,
            )
        };
        let let_ = |x: &str, value: Term, body: Term| {
            Term::Let(
                x.into(),
                std::rc::Rc::new(nat_ty()),
                std::rc::Rc::new(value),
                std::rc::Rc::new(body),
                false,
            )
        };
        let lam = |x: &str, body: Term| Term::Lam(x.into(), Icit::Explicit, std::rc::Rc::new(body));
        let v = Term::Var;
        let cases: Vec<(&str, usize, Term)> = vec![
            ("a quick value", 0, let_("x", num(3), add(v(0), v(0)))),
            (
                "a value that needs a frame",
                0,
                let_("x", add(num(2), num(3)), add(v(0), num(1))),
            ),
            (
                "a list used twice",
                0,
                let_("n", length(range(num(50))), add(v(0), v(0))),
            ),
            (
                "nested, each using the last",
                0,
                let_(
                    "a",
                    num(1),
                    let_(
                        "b",
                        add(v(0), v(0)),
                        let_("c", add(v(0), v(1)), add(v(0), v(2))),
                    ),
                ),
            ),
            (
                "a function in the body, applied",
                0,
                Term::app(let_("x", num(5), lam("y", add(v(1), v(0)))), num(1)),
            ),
            (
                "a function in the body, unapplied",
                0,
                let_("x", num(5), lam("y", add(v(0), v(1)))),
            ),
            (
                "under a binder",
                0,
                lam(
                    "z",
                    let_(
                        "x",
                        add(v(0), num(1)),
                        lam("w", let_("y", add(v(1), v(0)), add(v(0), v(3)))),
                    ),
                ),
            ),
            (
                "open: stuck on a variable",
                1,
                let_("x", add(v(0), num(1)), add(v(0), v(0))),
            ),
            (
                "open: the value unused",
                1,
                let_("x", add(v(0), v(0)), v(1)),
            ),
            (
                "in an argument",
                1,
                add(let_("x", num(4), add(v(0), v(1))), v(0)),
            ),
        ];
        for (what, level, term) in cases {
            let env: Vec<Value> = (0..level).map(Value::var).collect();
            let fast = value::eval(g, &env, &term).expect("no limits");
            let slow = reference::eval(g, &env, &term).expect("no limits");
            assert_eq!(normal(g, level, &fast), normal(g, level, &slow), "{what}");
            assert!(
                value::conv(g, level, &fast, &slow).expect("no limits"),
                "{what}"
            );
        }
        // The machine evaluates a long chain of `let`s in one run.
        let mut chain = v(0);
        for _ in 0..10_000 {
            chain = let_("x", add(v(0), num(1)), chain);
        }
        let chain = let_("x", num(0), chain);
        let before = machine_runs();
        let fast = value::eval(g, &[], &chain).expect("no limits");
        assert_eq!(machine_runs() - before, 1);
        assert_eq!(normal(g, 0, &fast), "Nat(10000)");
    });
}
