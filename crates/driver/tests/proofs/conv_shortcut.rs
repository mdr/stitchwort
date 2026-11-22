//! The kernel's conversion check, and the elaborator's unification,
//! recognise identical closures without running them (`value.rs`,
//! `same_closure`), and, comparing two definitions by their case trees,
//! answer a pair of calls already found equal from a record
//! (`same_stuck_trees`, SW-395; `reject/case-tree-chains-*.sw` exercise it,
//! one with a metavariable solved and then taken back); and the kernel
//! compares two glued calls of the same definition by their arguments
//! before their unfoldings, answering a pair already found equal or
//! different from a record (`conv`, `CallMemo`; D483, SW-4647). All are
//! turned off together. That may only skip work, never change a verdict. The
//! shortcuts can only answer "equal", so the risk is a program wrongly
//! accepted: every rejected example (the soundness suite included) must get
//! exactly the same diagnostics with the shortcut turned off. Accepted
//! examples are left out to keep the gate fast (D74, 20 Oct 2026): the
//! shortcut can't turn an acceptance into a rejection.
//!
//! Below the all tier each run compares a sample that moves on daily
//! (`CONV_SHORTCUT_SEED`); `EXAMPLES=name` compares just the examples named
//! (SW-3660: the whole broad sample had grown past 800 s).

use std::path::Path;
use std::time::{Duration, Instant};

use stitchwort_core::value::set_shortcuts_disabled;
use stitchwort_driver::driver::{Session, daily_tier_sample, par_map, with_stack};

const STACK: usize = 64 * 1024 * 1024;

/// An example whose two checks together take longer is reported.
const SLOW: Duration = Duration::from_secs(20);

/// Examples whose check only ends in reasonable time because of a shortcut,
/// left out of the comparison (they are still checked by the other example
/// tests). `parser-count-differs-from-lemma-with-unknown.sw` is answered by
/// the unifier's record of pairs of calls found different (SW-1521), which
/// answers "different", not "equal": without it the comparison takes about
/// 2³⁵ steps (SW-1702). `as-written-unconfirmed-other-rounds.sw` compares
/// closures holding large shared values: the same-closure shortcut compares
/// each shared part once, and without it the walk runs out of steps first
/// (SW-2730, SW-2995).
const NEEDS_THE_SHORTCUT: &[&str] = &[
    "reject/parser-count-differs-from-lemma-with-unknown.sw",
    "reject/as-written-unconfirmed-other-rounds.sw",
];

fn examples() -> Vec<(String, String)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut found = Vec::new();
    for dir in ["reject", "soundness"] {
        let mut paths: Vec<_> = std::fs::read_dir(root.join(dir))
            .expect("examples directory")
            .map(|e| e.expect("entry").path())
            .filter(|p| p.extension().is_some_and(|e| e == "sw"))
            .collect();
        paths.sort();
        for path in paths {
            let name = format!("{dir}/{}", path.file_name().unwrap().to_string_lossy());
            if NEEDS_THE_SHORTCUT.contains(&name.as_str()) {
                continue;
            }
            found.push((name, std::fs::read_to_string(&path).expect("readable")));
        }
    }
    found
}

/// The outcome of checking `text`, prelude included, with the shortcut on or
/// off: every diagnostic, in full. The switch is per thread, so examples can
/// be checked side by side (`par_map`).
fn verdict(name: &str, text: &str, shortcuts: bool) -> String {
    set_shortcuts_disabled(!shortcuts);
    let mut session = Session::for_stack(STACK);
    let result = session.load(name, text).map(|_| ());
    set_shortcuts_disabled(false);
    format!("{result:?}")
}

/// How many examples a sweep in the broad tier skips between two it
/// compares (four times as many in quick and lane, none in all): one in
/// eight, about 150 of them.
const BROAD_STRIDE: usize = 8;

/// The examples `EXAMPLES` names (comma-separated parts of their names, as
/// in the other example sweeps), all of them, or `None` when it is unset or
/// empty.
fn named(examples: &[(String, String)]) -> Option<Vec<(String, String)>> {
    let filter = std::env::var("EXAMPLES")
        .ok()
        .filter(|f| !f.trim().is_empty())?;
    let parts: Vec<_> = filter
        .split(',')
        .map(str::trim)
        .filter(|p| !p.is_empty())
        .collect();
    let chosen: Vec<_> = (examples.iter())
        .filter(|(name, _)| parts.iter().any(|part| name.contains(part)))
        .cloned()
        .collect();
    assert!(
        !chosen.is_empty(),
        "EXAMPLES={filter} matches no rejected or soundness example"
    );
    Some(chosen)
}

#[test]
fn every_rejected_example_gets_the_same_verdict_without_the_shortcut() {
    with_stack(STACK, || {
        let examples = examples();
        assert!(examples.len() > 250, "only {} examples", examples.len());
        let all = examples.len();
        let named = named(&examples);
        let filtered = named.is_some();
        let examples = match named {
            Some(chosen) => chosen,
            None => {
                // A corpus sweep: a sample below the all tier, starting at
                // the seed's place, and the count of rejections expected in
                // proportion.
                daily_tier_sample(examples, BROAD_STRIDE, "CONV_SHORTCUT_SEED")
            }
        };
        let verdicts = par_map(STACK, &examples, |(name, text)| {
            let started = Instant::now();
            let with = verdict(name, text, true);
            let with_took = started.elapsed();
            let without = verdict(name, text, false);
            let without_took = started.elapsed() - with_took;
            // A slow example is where the sweep's time goes: named, so that
            // a run near its cap says which.
            if with_took + without_took > SLOW {
                eprintln!(
                    "slow: {name}: {with_took:.1?} with the shortcut, {without_took:.1?} without"
                );
            }
            assert_eq!(with, without, "{name}: the verdict depends on the shortcut");
            with.starts_with("Err")
        });
        let rejected = verdicts.iter().filter(|rejected| **rejected).count();
        assert!(
            filtered || rejected > 200 * examples.len() / all,
            "only {rejected} rejections compared"
        );
    });
}

/// SW-920: unification's identity shortcut sees through a solved unknown.
/// Here `_` is solved with `seed`, and comparing the two sides of `%`
/// meets two closures that differ only in holding `?x` (solved with `seed`)
/// where the other holds `seed`. Without the shortcut seeing that, the
/// comparison ran both bodies, unfolding `Nat.divFuel` once per `Succ` of
/// `+ 12345`: about 154 million steps, 25 s.
#[test]
fn a_solved_unknown_is_seen_through_by_the_identity_shortcut() {
    let work = |hole: &str| {
        with_stack(STACK, || {
            let mut session = Session::for_stack(STACK);
            let text = format!(
                "def body (seed: Nat): Nat := (seed * 1103515245 + 12345) % 2147483648\n\n\
                 theorem metaSeed (seed: Nat): body seed < 2147483648 :=\n  \
                 Std.Nat.modLt ({hole} * 1103515245 + 12345) 2147483648\n"
            );
            let before = session.elab.kernel.machine.budget.total_work();
            let loaded = session.load("sw920.sw", &text);
            assert!(loaded.is_ok(), "{hole}: {loaded:?}");
            session.elab.kernel.machine.budget.total_work() - before
        })
    };
    let written = work("seed");
    let solved = work("_");
    eprintln!("work: `seed` {written}, `_` {solved}");
    assert!(
        solved < written + written / 10,
        "`_`: {solved} steps, `seed`: {written}"
    );
}
