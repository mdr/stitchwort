//! The evaluator (an abstract machine, `value.rs`) against the recursive
//! reference evaluator it was derived from (`reference.rs`): on the same
//! programs they must give the same normal forms. Both results are turned
//! back into terms by the reference's own `quote`, so a quoting bug can't hide
//! a disagreement (docs/proposals/stack-safe-evaluation.md).
//!
//! These use small inputs; deep ones are in `resources.rs`. The reference
//! recurses on the Rust stack, so they run on a thread with a large one.

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use stitchwort_core::budget::{ResourceError, Result};
use stitchwort_core::reference;
use stitchwort_core::term::Term;
use stitchwort_core::value::{self, Elim, Head, Spine, Value, machine_runs};
use stitchwort_core::{DefId, Icit};
use stitchwort_driver::driver::{Session, par_map, tier, tier_sample, with_stack};
use stitchwort_syntax::{SourceMap, Span};

// The deepest example is io.sw's 5,000 prints through `IO.simulate`, which the
// reference evaluates recursively, a few frames per print. Since partial
// handlers lane D (2404ada2) a handler folds with `foldCompD` and forwards with
// `callD`/`translateD`, one more layer of definitions per operation: in a
// release build it needs between 80 and 96 MiB (it needed 56 to 64 before), so
// 128 MiB. Debug builds use much more stack per frame.
const STACK: usize = if cfg!(debug_assertions) { 512 } else { 128 } * 1024 * 1024;

/// The normal form of `value`, as printed by the reference.
fn normal(g: &stitchwort_core::Ev, level: usize, value: &Value) -> String {
    try_normal(g, level, value).expect("no limits")
}

/// [`normal`], failing if the reference runs out of its budget.
fn try_normal(g: &stitchwort_core::Ev, level: usize, value: &Value) -> Result<String> {
    Ok(format!("{:?}", reference::quote(g, level, value)?))
}

/// Definition `id`'s type, evaluated by the machine with gluing off. Its
/// kept type (`Def::ty_value`) is glued (D3680), and the reference never
/// glues, so it can't read one back: [`compare_definitions`] compares the
/// kept type with the reference's by the machine's `conv`, and this with
/// the reference's normal form.
fn unglued_type(g: &stitchwort_core::Ev, id: DefId) -> Value {
    let was = g.machine.glue.replace(false);
    let ty = value::eval(g, &[], g.def(id).ty()).expect("no limits");
    g.machine.glue.set(was);
    ty
}

/// The icits of a definition's parameters, from its body's lambdas.
fn param_icits(g: &stitchwort_core::Ev, id: DefId) -> Vec<Icit> {
    let def = g.def(id);
    let mut icits = Vec::new();
    let Some(mut term) = def.body().map(|b| &**b) else {
        return icits;
    };
    for _ in 0..def.arity() {
        let Term::Lam(_, icit, body) = term.strip_loc() else {
            break;
        };
        icits.push(*icit);
        term = body;
    }
    icits
}

/// Steps the reference evaluator may take on one comparison: one normal
/// form's evaluation and read-back, or one conversion check (see
/// [`within_budget`]). The reference shares nothing, so a normal form with
/// sharing the machine keeps, exponentially large written out, takes as many
/// steps: std `Random`'s xor halves its arguments 64 times, and `a / 2`
/// mentions `a` twice, so its normal form on a variable grows by 4 per bit;
/// as-written-unconfirmed.sw's thousand nested `if`s stuck on `x`, or
/// let-chain-match.sw's 40 `let`s each used twice, are the same. Read back,
/// they took gigabytes (SW-1052, SW-1181, SW-2583); over the budget they
/// are reported as too big to compare and skipped. The most any definition
/// in the broad sample needs is 1.9 million steps (std's
/// `Float.Model.addBits` on two variables, SW-2613); a step keeps about
/// 150 bytes, so a comparison that runs out has taken under a gigabyte.
/// `STITCHWORT_DIFFERENTIAL_STEPS` overrides it, to measure.
const REFERENCE_STEPS: u64 = 5_000_000;

/// Comparisons skipped as too big, across the sweep, each counted once: a
/// comparison of std's definitions alone is the same in every example that
/// imports them, so it is kept under `std`, and any other under its example
/// (see [`place`]). Skipping hides nothing from a passing run only if someone
/// looks, so the test reports the count and fails above [`MAX_SKIPPED`].
static SKIPPED: Mutex<BTreeSet<String>> = Mutex::new(BTreeSet::new());

/// Skips across the sweep counting repeats, for the report only.
static SKIPPED_REPEATS: AtomicUsize = AtomicUsize::new(0);

/// The most distinct skips the sweep tolerates. Counted with repeats, a
/// sample's skips rose and fell with how many examples importing `Float` it
/// happened to take, about 23 each for `Float.Model`'s `isqrt`, `sqrtBits`
/// and the four arithmetic `...Bits` (SW-4255): the broad sample is every
/// fourth example, so a new example early in the list moved it from about 50
/// skips to 104 with no change to either evaluator. Counted once, std's
/// skips are the same whichever examples import them, and what remains
/// varies with the sample only through examples' own definitions
/// (random-seed.sw, kernel-same-call-arguments.sw, as-written-unconfirmed.sw,
/// match-bounded-search.sw, ...). A new skip is an oracle that compares
/// less than before: look at which (`--no-capture` lists them) before
/// raising this. Slices (`STITCHWORT_DIFFERENTIAL_SKIP` or `_LIMIT`) and
/// another step budget skip other amounts, so they are not checked.
///
/// The all tier on 22 Nov 2026 found 90: 53 from the thirteen
/// `large-hypothesis-*.sw` examples (added 19 and 20 Nov to hold large
/// hypotheses, whose types the shared-nothing reference can't write out
/// within the budget, by design), and the 37 that remained. So the limit is
/// the old 60 plus what those examples add, rounded up.
const MAX_SKIPPED: usize = 95;

/// Where a skipped comparison is counted: `std` when it involves only std's
/// definitions, otherwise the example (or `prelude`) being swept.
fn place<'a>(g: &stitchwort_core::Ev, example: &'a str, ids: &[DefId]) -> &'a str {
    if ids.iter().all(|&id| g.def(id).path().starts_with("Std.")) {
        "std"
    } else {
        example
    }
}

/// How deeply the reference evaluator may nest on the sweep's thread: what
/// [`STACK`] holds with room to spare. The release limit is above the deepest
/// comparison that must run (io.sw's 5,000 prints reach 30,029, in 80 to
/// 96 MiB of the 128); the debug one is a guess at a quarter of it, as debug
/// frames are several times bigger, and skips io.sw's test. Measured with
/// `STITCHWORT_DIFFERENTIAL_DEPTH` (which overrides it) and
/// `reference::take_max_depth`; a comparison past it is skipped like one past
/// its step budget, instead of overflowing the stack and aborting the test
/// process (SW-4546).
const REFERENCE_DEPTH: usize = if cfg!(debug_assertions) {
    10_000
} else {
    35_000
};

fn reference_depth() -> usize {
    static DEPTH: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *DEPTH.get_or_init(|| {
        std::env::var("STITCHWORT_DIFFERENTIAL_DEPTH")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(REFERENCE_DEPTH)
    })
}

fn reference_steps() -> u64 {
    static STEPS: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *STEPS.get_or_init(|| {
        std::env::var("STITCHWORT_DIFFERENTIAL_STEPS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(REFERENCE_STEPS)
    })
}

/// Definitions the sweep leaves out on purpose, so [`MAX_SKIPPED`] counts only
/// comparisons that were meant to happen (SW-3855).
///
/// - `Float.Theory.*` are theorems about the float model: their proofs and
///   statements unfold `Float.Model` and have no run-time meaning, and the
///   model is compared through its own definitions. Their types alone are
///   over the budget (hundreds of skips in every example that imports `Float`).
/// - `Float.Model.floorBits`, `ceilBits` and `roundBits` rebuild a float from
///   its bits with the shared-nothing reference: over 5 million steps even
///   applied to one variable. The rest of `Float.Model` (`addBits`, `mulBits`,
///   ...) stays in, and `Float.floor` and friends are checked by the
///   examples' own tests.
fn left_out(name: &str) -> bool {
    name.starts_with("Float.Theory.")
        || matches!(
            name,
            "Float.Model.floorBits" | "Float.Model.ceilBits" | "Float.Model.roundBits"
        )
}

/// `f`, with the reference evaluator on this thread limited to
/// [`REFERENCE_STEPS`] and [`REFERENCE_DEPTH`]; `None` if it ran out, after saying what was too big
/// to compare. `comparison` is counted in [`SKIPPED`] under `place`.
fn within_budget<T>(
    example: &str,
    place: &str,
    comparison: &str,
    f: impl FnOnce() -> Result<T>,
) -> Option<T> {
    reference::set_budget(Some(reference_steps()));
    reference::set_depth_limit(Some(reference_depth()));
    let out = f();
    reference::set_budget(None);
    reference::set_depth_limit(None);
    if std::env::var("STITCHWORT_DIFFERENTIAL_SHOW_DEPTH").is_ok() {
        eprintln!(
            "depth {}: {example}: {comparison}",
            reference::take_max_depth()
        );
    }
    match out {
        Ok(out) => Some(out),
        Err(ResourceError::Work | ResourceError::Depth) => {
            eprintln!("too big to compare: {example}: {comparison}");
            SKIPPED
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(format!("{place}: {comparison}"));
            SKIPPED_REPEATS.fetch_add(1, Ordering::Relaxed);
            None
        }
        Err(e) => panic!("{example}: {comparison}: {e}"),
    }
}

/// Compares the two evaluators on everything `g` defines: each definition
/// applied to fresh variables (open terms, stuck case trees, partial
/// application), and each definition's type. A normal form over the
/// reference's budget is skipped, with the longer applications of the same
/// definition, which are as big.
fn compare_definitions(g: &stitchwort_core::Ev, what: &str) -> usize {
    let mut compared = 0;
    for i in 0..g.env.defs().len() {
        let id = DefId(i);
        let def = g.def(id);
        if def.body().is_none() || left_out(def.name()) {
            continue;
        }
        let icits = param_icits(g, id);
        let place = place(g, what, &[id]);
        // Applied to every prefix of its parameters, so partial
        // applications are covered too.
        for n in 0..icits.len() + 1 {
            let comparison = format!("`{}` applied to {n} variable(s)", def.name());
            let applied = format!("{what}: {comparison}");
            // The reference first, so the machine never builds a value whose
            // read-back is over the budget.
            let Some(slow) = within_budget(what, place, &comparison, || {
                let mut slow = reference::eval(g, &[], &Term::Def(id))?;
                for (level, icit) in icits.iter().take(n).enumerate() {
                    slow = reference::apply_icit(g, slow, Value::var(level), *icit)?;
                }
                Ok(slow)
            }) else {
                break;
            };
            let Some(slow_normal) =
                within_budget(what, place, &comparison, || try_normal(g, n, &slow))
            else {
                break;
            };
            let mut fast = value::eval(g, &[], &Term::Def(id)).expect("no limits");
            for (level, icit) in icits.iter().take(n).enumerate() {
                fast = value::apply_icit(g, fast, Value::var(level), *icit).expect("no limits");
            }
            let Some(fast_normal) =
                within_budget(what, place, &comparison, || try_normal(g, n, &fast))
            else {
                break;
            };
            assert_eq!(fast_normal, slow_normal, "{applied}");
            // The machine's quote (a work list) against the reference's,
            // which expands compact lists: quotation commutes with expansion.
            assert_eq!(
                format!(
                    "{:?}",
                    reference::expand_term(g, &value::quote(g, n, &fast).expect("no limits"))
                ),
                fast_normal,
                "quoting {applied}"
            );
            assert!(
                value::conv(g, n, &fast, &slow).expect("no limits"),
                "{applied} isn't convertible with itself"
            );
            compared += 1;
        }
        let comparison = format!("the type of `{}`", def.name());
        let the_type = format!("{what}: {comparison}");
        let Some(ty) = within_budget(what, place, &comparison, || {
            reference::eval(g, &[], def.ty())
        }) else {
            continue;
        };
        assert!(value::conv(g, 0, def.ty_value(), &ty).expect("no limits"));
        let Some(slow) = within_budget(what, place, &comparison, || try_normal(g, 0, &ty)) else {
            continue;
        };
        let Some(fast) = within_budget(what, place, &comparison, || {
            try_normal(g, 0, &unglued_type(g, id))
        }) else {
            continue;
        };
        assert_eq!(fast, slow, "{the_type}");
    }
    compared
}

/// The machine's `conv` (a work list) against the reference's. Conversion is
/// only meaningful between values of the same type, so it compares each
/// definition's value (unapplied, so partially applied definitions and eta
/// are covered) with every other definition's whose type is convertible
/// with its own, and each definition's type with the next few types. A
/// pair the reference can't decide within its budget is skipped.
fn compare_conversion(g: &stitchwort_core::Ev, what: &str) -> usize {
    let defs: Vec<(DefId, String, Value, Value)> = (0..g.env.defs().len())
        .filter(|&i| g.env.defs()[i].body().is_some() && !left_out(g.env.defs()[i].name()))
        .map(|i| {
            let def = &g.env.defs()[i];
            let value = value::eval(g, &[], &Term::Def(DefId(i))).expect("no limits");
            (
                DefId(i),
                def.name().to_string(),
                value,
                unglued_type(g, DefId(i)),
            )
        })
        .collect();
    let agree = |x: &Value, y: &Value, place: &str, comparison: &str| {
        let slow = within_budget(what, place, comparison, || reference::conv(g, 0, x, y))?;
        let fast = value::conv(g, 0, x, y).expect("no limits");
        assert_eq!(fast, slow, "{what}: {comparison}");
        Some(fast)
    };
    let mut compared = 0;
    for (i, (x_id, x_name, x, x_ty)) in defs.iter().enumerate() {
        for (y_id, y_name, y, y_ty) in defs.iter().skip(i) {
            let place = place(g, what, &[*x_id, *y_id]);
            if agree(
                x_ty,
                y_ty,
                place,
                &format!("the types of `{x_name}` and `{y_name}`"),
            ) == Some(true)
                && agree(x, y, place, &format!("`{x_name}` and `{y_name}`")).is_some()
            {
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
        let prelude = compare_definitions(&session.elab.ev(), "prelude");
        assert!(prelude > 200, "only {prelude} comparisons in the prelude");
        let conversions = compare_conversion(&session.elab.ev(), "prelude");
        assert!(
            conversions > 100,
            "only {conversions} conversions in the prelude"
        );
        // Each example in its own session, on the thread pool. A corpus sweep:
        // a fixed sample below the all tier.
        // `STITCHWORT_DIFFERENTIAL_SKIP` and `_LIMIT` narrow the sweep to a
        // slice of the sample, to measure or bisect (docs/testing.md).
        // `STITCHWORT_DIFFERENTIAL_ONLY` instead picks examples by name from
        // every example, not just the tier's sample, so any one can run alone.
        let all = examples();
        let mut sample = match std::env::var("STITCHWORT_DIFFERENTIAL_ONLY") {
            Ok(only) => all
                .into_iter()
                .filter(|(name, _)| name.contains(&only))
                .collect(),
            Err(_) => tier_sample(all, 4),
        };
        if let Some(n) = std::env::var("STITCHWORT_DIFFERENTIAL_SKIP")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
        {
            sample.drain(..n.min(sample.len()));
        }
        if let Some(n) = std::env::var("STITCHWORT_DIFFERENTIAL_LIMIT")
            .ok()
            .and_then(|v| v.parse().ok())
        {
            sample.truncate(n);
        }
        par_map(STACK, &sample, |(name, text)| {
            let mut session = Session::for_stack(STACK);
            session.load(name, text).expect("examples check");
            let g = &session.elab.ev();
            compare_definitions(g, name);
            compare_conversion(g, name);
            for test in session.elab.tests() {
                let comparison = format!("test \"{}\"", test.name);
                let what = format!("{name}: {comparison}");
                let term = Term::Def(test.def);
                let Some(slow) = within_budget(name, name, &comparison, || {
                    let slow = reference::eval(g, &[], &term)?;
                    try_normal(g, 0, &slow)
                }) else {
                    continue;
                };
                let fast = value::eval(g, &[], &term).expect("no limits");
                let Some(fast) = within_budget(name, name, &comparison, || try_normal(g, 0, &fast))
                else {
                    continue;
                };
                assert_eq!(fast, slow, "{what}");
            }
        });
        report_skips();
    });
}

/// Says how many comparisons were skipped: on stderr, and in
/// `differential-skips.txt` in the cargo target folder with each distinct
/// skip (nextest shows a passing test's output only with `--success-output`),
/// and fails the test above [`MAX_SKIPPED`].
fn report_skips() {
    let distinct = SKIPPED.lock().unwrap_or_else(|e| e.into_inner()).clone();
    let skipped = distinct.len();
    let repeats = SKIPPED_REPEATS.load(Ordering::Relaxed);
    let tier = tier();
    let line = format!(
        "differential: {skipped} comparisons too big to compare ({repeats} counting repeats \
         across examples; tier {tier:?}, budget {} steps)",
        reference_steps()
    );
    eprintln!("{line}");
    let file = Path::new(env!("CARGO_TARGET_TMPDIR")).join("differential-skips.txt");
    let listed: String = distinct.iter().map(|s| format!("{s}\n")).collect();
    let _ = std::fs::write(file, format!("{line}\n{listed}"));
    let sliced = [
        "STITCHWORT_DIFFERENTIAL_SKIP",
        "STITCHWORT_DIFFERENTIAL_LIMIT",
        "STITCHWORT_DIFFERENTIAL_ONLY",
        "STITCHWORT_DIFFERENTIAL_STEPS",
    ]
    .iter()
    .any(|v| std::env::var(v).is_ok());
    assert!(
        sliced || skipped <= MAX_SKIPPED,
        "{line}; the most expected is {}. The oracle compares less than it did: \
         look at the new `too big to compare` skips (--no-capture, or \
         differential-skips.txt in the target's tmp folder, lists them) before \
         raising `MAX_SKIPPED`",
        MAX_SKIPPED
    );
}

fn span() -> Span {
    Span::point(SourceMap::new().add("test", ""), 0)
}

fn def(g: &stitchwort_core::Ev, name: &str) -> DefId {
    DefId(
        g.env
            .defs()
            .iter()
            .position(|d| &**d.name() == name)
            .unwrap_or_else(|| panic!("no `{name}`")),
    )
}

/// Both evaluators on `value` forced, and on `f` applied to it.
fn agree_after_forcing(g: &stitchwort_core::Ev, f: DefId, value: &Value) -> String {
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
    let g = &session.elab.ev();
    let pred = def(g, "Nat.pred");
    // `?m 3`, with `?m` unsolved: `pred (?m 3)` is stuck.
    let m = session.elab.metas().new_meta(span());
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
    let nat = g.env.builtins().nat.unwrap();
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
    session.elab.metas().solve_meta(m, solution);
    assert_eq!(agree_after_forcing(g, pred, &stuck), "Nat(4)");
}

/// `J` on a neutral proof stays stuck, keeping its motive and base; on a
/// solved metavariable standing for `byComputing`, it reduces to the base, including
/// when the `J` is in the metavariable's spine.
#[test]
fn j_with_reflexive_and_stuck_proofs() {
    let session = Session::new();
    let g = &session.elab.ev();
    let nat = g.env.builtins().nat.unwrap();
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
        matches!(fast, Value::Neutral(Head::Var(0, _), ref s) if matches!(s[..], [Elim::J { .. }]))
    );
    // Stuck on an unsolved metavariable, then solved with `byComputing`.
    let m = session.elab.metas().new_meta(span());
    let fast = value::eval(g, &[], &j(Term::Meta(m))).unwrap();
    let slow = reference::eval(g, &[], &j(Term::Meta(m))).unwrap();
    assert_eq!(normal(g, 0, &fast), normal(g, 0, &slow));
    session.elab.metas().solve_meta(m, Value::Refl);
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
        let g = &session.elab.ev();
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

/// A term nested deeper than the reference evaluator's depth limit fails with
/// `Depth` instead of overflowing the stack, and the limit leaves nothing
/// behind for the next evaluation (SW-4546).
#[test]
fn the_reference_evaluator_stops_at_its_depth_limit() {
    with_stack(STACK, || {
        let session = Session::for_stack(STACK);
        let g = &session.elab.ev();
        let nested = |n: usize| {
            let mut term = Term::Nat(std::rc::Rc::new(7u32.into()));
            for _ in 0..n {
                term = Term::Ann(
                    term.into(),
                    Term::Sort(stitchwort_core::term::Sort::Type(0)).into(),
                );
            }
            term
        };
        reference::set_depth_limit(Some(100));
        let too_deep = reference::eval(g, &[], &nested(1_000));
        assert!(
            matches!(too_deep, Err(ResourceError::Depth)),
            "{too_deep:?}"
        );
        assert!(reference::eval(g, &[], &nested(50)).is_ok());
        reference::set_depth_limit(None);
        assert!(reference::eval(g, &[], &nested(1_000)).is_ok());
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
                 def byInd: 0 = 0 := Quot.ind [p := q => 0 = 0] (b => byComputing) (Quot.mk False: Q)\n\
                 def stuckToo: Nat := J (y p => Nat) 0 byInd\n\
                 def BoolEq (x: Bool) (y: Bool): Prop := x = y\n\
                 def QE: Type := Quot Bool BoolEq\n\
                 def toNat (b: Bool): Nat := if b then 1 else 0\n\
                 def toNatRespects (x: Bool) (y: Bool) (same: BoolEq x y): toNat x = toNat y :=\n  \
                 rewrite same then byComputing\n\
                 def observe (q: QE): Nat := Quot.lift toNat toNatRespects q\n\
                 def mkTrue: QE := Quot.mk True\n\
                 def one: Nat := observe mkTrue\n\
                 def oneDirectly: Nat := Quot.lift toNat toNatRespects mkTrue\n\
                 def viaMatch (b: Bool) (q: QE): Nat :=\n  \
                 match b with\n    \
                 | True => Quot.lift toNat toNatRespects q\n    \
                 | False => 0\n\
                 def twice (q: QE): Nat := observe q + observe q\n\
                 def proofLift (q: Q): 0 = 0 := Quot.lift (b => byComputing) (x y r => byComputing) q\n\
                 def propLift (q: Q): Prop := Quot.lift (b => Unit) (x y r => byComputing) q\n",
            )
            .unwrap();
        let g = &session.elab.ev();
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
        let g = &session.elab.ev();
        let nat = g.env.builtins().nat.unwrap();
        let nat_ty = || Term::data(nat, vec![]);
        let num = |n: u32| Term::Nat(std::rc::Rc::new(n.into()));
        let add = |a: Term, b: Term| Term::app(Term::app(Term::Def(def(g, "Nat.add")), a), b);
        let range = |n: Term| Term::app(Term::app(Term::Def(def(g, "List.range")), num(0)), n);
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

/// Two stuck calls are compared by their case trees, and looked up by their
/// printed normal forms. `Float.Model.isqrt`'s is a tree of about 4^64 nodes
/// (a Newton step uses the last guess four times, 64 steps unrolled), so
/// printing it to look the pair up took over the budget and the comparison
/// was skipped; it is now compared without a record (SW-4265).
#[test]
fn a_pair_of_calls_with_an_enormous_normal_form_compares_without_printing_it() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("isqrt", "import Std (Float)\ndef probe (n: Nat): Nat := Float.Model.isqrt n + Float.Model.pow2 n\n")
            .expect("checks");
        let g = &session.elab.ev();
        let value = |name: &str| value::eval(g, &[], &Term::Def(def(g, name))).expect("no limits");
        let (isqrt, pow2) = (value("Float.Model.isqrt"), value("Float.Model.pow2"));
        reference::set_budget(Some(1_000_000));
        let slow = reference::conv(g, 0, &isqrt, &pow2);
        reference::set_budget(None);
        assert!(!slow.expect("within the budget"));
        assert!(!value::conv(g, 0, &isqrt, &pow2).expect("no limits"));
    });
}
