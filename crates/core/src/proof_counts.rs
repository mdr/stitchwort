//! `STITCHWORT_PROOF_COUNTS=1`: how often today's rules treat two proofs, or
//! a computation on a proof, in a way full proof irrelevance would change
//! (docs/proposals/full-proof-irrelevance.md §9, stage 3), read off the
//! proof marks (`value::is_proof`). Nothing is changed by counting: the
//! counters only measure what stages 4 and 5 (rules K, S and I) would
//! touch. The timings report prints the tables. Counted over the whole
//! process, every thread together. Off, a count costs one relaxed load.

use crate::collections::HashMap;
use std::fmt::Write;
use std::panic::Location;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU8, Ordering::Relaxed};

use crate::ev::Ev;

/// What was counted.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Kind {
    /// A comparison of two values both marked proofs answered "different"
    /// (rule I would say "equal"): the innermost pair of a failed
    /// conversion. Counted where it fails, so a comparison retried after
    /// unfolding counts each failure.
    DifferentProofs,
    /// The same in the elaborator's unifier.
    UnifyDifferentProofs,
    /// The unifier solved unknowns while comparing two values both marked
    /// proofs, neither of them an unknown itself: the inference rule I
    /// gives up (§7). Counted once per pair; [`Kind::SolvedUnknowns`]
    /// counts the unknowns.
    SolvedInsideProofs,
    /// The unknowns solved in those pairs.
    SolvedUnknowns,
    /// A `J` whose result is data, stuck because its proof isn't
    /// `byComputing`: what rule K would compute.
    StuckCastIntoData,
    /// A `case` on a proof of a proposition with one constructor, producing
    /// data, stuck because the proof isn't a constructor: what rule S would
    /// compute.
    StuckOneShapeIntoData,
    /// A `case` the kernel checked on a proof of an indexed proposition
    /// (other than `=`, which is `J`) producing data (§4.4, Q2).
    IndexedPropIntoData,
    /// A cast into data on a proof that isn't `byComputing` took its base
    /// because its ends were equal (rule K).
    CastFired,
    /// A `case` on a proof that isn't a constructor took its only branch
    /// (rule S).
    OneShapeFired,
    /// Two values both marked proofs were found equal without being looked
    /// at (rule I).
    RuleI,
}

impl Kind {
    fn label(self) -> &'static str {
        match self {
            Kind::DifferentProofs => "two proofs compared different (conversion, innermost pair)",
            Kind::UnifyDifferentProofs => "two proofs compared different (unifier, innermost pair)",
            Kind::SolvedInsideProofs => "unifier pairs of proofs that solved unknowns inside",
            Kind::SolvedUnknowns => "  unknowns solved in them",
            Kind::StuckCastIntoData => "J into data stuck on a proof that isn't byComputing",
            Kind::StuckOneShapeIntoData => "one-constructor match into data stuck on a proof",
            Kind::IndexedPropIntoData => "indexed proposition matched into data (kernel check)",
            Kind::CastFired => "J into data took its base by rule K (ends equal)",
            Kind::OneShapeFired => "one-constructor match on a proof took its branch by rule S",
            Kind::RuleI => "two proofs found equal by rule I",
        }
    }
}

#[derive(Default)]
struct Counts {
    by_kind: HashMap<(bool, Kind), u64>,
    by_decl: HashMap<(Kind, String), u64>,
    /// Top-level comparisons with both sides marked proofs, by what and
    /// where they were called from: (proof pairs, of which different).
    by_caller: HashMap<(&'static str, bool, String), [u64; 2]>,
}

static COUNTS: Mutex<Option<Counts>> = Mutex::new(None);

/// 0 before the variable is read, then 1 for off and 2 for on.
static STATE: AtomicU8 = AtomicU8::new(0);

/// Turns counting on for a test that can't set the environment before the
/// first read of [`on`].
#[doc(hidden)]
pub fn force_on_for_tests() {
    STATE.store(2, Relaxed);
}

/// Whether `STITCHWORT_PROOF_COUNTS=1`.
#[inline]
pub fn on() -> bool {
    match STATE.load(Relaxed) {
        0 => read_variable(),
        state => state == 2,
    }
}

#[cold]
fn read_variable() -> bool {
    let on = std::env::var("STITCHWORT_PROOF_COUNTS").is_ok_and(|v| v == "1");
    STATE.store(if on { 2 } else { 1 }, Relaxed);
    on
}

fn declaration() -> String {
    crate::budget::with_current_declaration(|d| d.map(str::to_owned))
        .unwrap_or_else(|| "(outside a declaration)".to_owned())
}

/// Counts `n` of `kind`, if the counters are on.
#[inline]
pub fn record(g: &Ev, kind: Kind, n: u64) {
    if on() {
        record_now(g.machine.kernel.get(), kind, n);
    }
}

#[inline(never)]
fn record_now(kernel: bool, kind: Kind, n: u64) {
    let decl = declaration();
    let mut guard = COUNTS.lock().unwrap();
    let counts = guard.get_or_insert_with(Counts::default);
    *counts.by_kind.entry((kernel, kind)).or_default() += n;
    *counts.by_decl.entry((kind, decl)).or_default() += n;
}

/// Counts a top-level comparison (`what`: "conv" or "unify") of two values
/// both marked proofs, called from `caller`, and whether it answered
/// "different".
#[inline(never)]
pub fn record_caller(g: &Ev, what: &'static str, caller: &Location, different: bool) {
    let mut guard = COUNTS.lock().unwrap();
    let counts = guard.get_or_insert_with(Counts::default);
    let at = format!("{}:{}", caller.file(), caller.line());
    let entry = counts
        .by_caller
        .entry((what, g.machine.kernel.get(), at))
        .or_default();
    entry[0] += 1;
    entry[1] += u64::from(different);
}

/// The count of `kind` so far, kernel and elaborator together: for tests.
pub fn total(kind: Kind) -> u64 {
    let guard = COUNTS.lock().unwrap();
    guard.as_ref().map_or(0, |c| {
        c.by_kind
            .iter()
            .filter(|((_, k), _)| *k == kind)
            .map(|(_, n)| n)
            .sum()
    })
}

const TOP: usize = 10;

/// The report's lines, if the counters are on.
pub fn report() -> Option<String> {
    if !on() {
        return None;
    }
    let guard = COUNTS.lock().unwrap();
    let empty = Counts::default();
    let counts = guard.as_ref().unwrap_or(&empty);
    let mut out = String::new();
    let _ = writeln!(
        out,
        "proof counts (what full proof irrelevance would change; docs/proposals/\
         full-proof-irrelevance.md §9 stage 3)"
    );
    let _ = writeln!(out, "{:>12}  {:>12}  what", "elaborator", "kernel");
    let mut kinds: Vec<Kind> = counts.by_kind.keys().map(|k| k.1).collect();
    kinds.sort();
    kinds.dedup();
    for kind in &kinds {
        let get = |k: bool| counts.by_kind.get(&(k, *kind)).copied().unwrap_or(0);
        let _ = writeln!(
            out,
            "{:>12}  {:>12}  {}",
            get(false),
            get(true),
            kind.label()
        );
    }
    for kind in kinds {
        let mut decls: Vec<(&String, u64)> = counts
            .by_decl
            .iter()
            .filter(|((k, _), _)| *k == kind)
            .map(|((_, d), n)| (d, *n))
            .collect();
        decls.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        let _ = writeln!(out, "most, {}:", kind.label().trim());
        for (decl, n) in decls.into_iter().take(TOP) {
            let _ = writeln!(out, "{n:>12}  {decl}");
        }
    }
    let mut callers: Vec<_> = counts.by_caller.iter().collect();
    callers.sort_by(|a, b| b.1[0].cmp(&a.1[0]).then(a.0.cmp(b.0)));
    let _ = writeln!(
        out,
        "top-level comparisons of two proofs, by caller: {:>8} {:>10}  what  mode  where",
        "pairs", "different"
    );
    for ((what, kernel, at), [pairs, different]) in callers {
        let mode = if *kernel { "kernel" } else { "elab" };
        let _ = writeln!(out, "{pairs:>12} {different:>10}  {what}  {mode}  {at}");
    }
    Some(out)
}
