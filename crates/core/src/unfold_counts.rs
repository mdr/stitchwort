//! `STITCHWORT_THEOREM_UNFOLDS=1`: how often a theorem's proof is unfolded
//! from a call of it elsewhere, by site (what looked inside the proof), by
//! mode (kernel or elaborator), by theorem and by the declaration being
//! checked (docs/proposals/parallel-checking.md §2.2; the question is how
//! much would change if theorems were sealed). A theorem's own body being
//! checked isn't counted. The timings report prints the tables. Counted over
//! the whole process, every thread together; nothing reads them but the
//! report. Off, a count costs one relaxed load.

use crate::collections::HashMap;
use std::fmt::Write;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU8, Ordering::Relaxed};

use crate::ev::Ev;
use crate::term::DefId;

/// What looked inside a theorem's proof.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Site {
    /// A `case` on a proof (the machine's `Frame::Scrutinee`).
    Case,
    /// A `case` in a case tree walked outside the machine (`tree_scrutinee`).
    TreeCase,
    /// `J` on a proof, or on a field of a folded call.
    J,
    /// A `Quot.lift` on a proof.
    Lift,
    /// A projection of a proof, or of a stuck field of a call.
    Project,
    /// What a folded call's body returned was itself a folded call
    /// (`Frame::Unfolding`).
    Chain,
    /// A stuck field of a call applied to an argument.
    FieldApply,
    /// A metavariable's solution or a conversion's remainder replayed
    /// (`Frame::ReplayElim`).
    Replay,
    /// The kernel's conversion: a folded call against something else.
    Conversion,
    /// Conversion of a folded call with a `J` or application after it
    /// (`unfold_folded_head`: SW-4642's over-applied calls).
    OverApplied,
    /// The unifier's comparison, or its over-applied one.
    Unify,
    /// The unifier's over-applied comparison.
    UnifyOverApplied,
    /// A `case` split in the elaborator (`cases.rs`).
    CaseSplit,
    /// The fields of an unfolded call's result.
    Field,
    /// Any other caller of `unfold_folded` in the elaborator.
    Other,
    /// `unfold_once`: a glued call stepped.
    Once,
}

impl Site {
    fn label(self) -> &'static str {
        match self {
            Site::Case => "case on a proof (machine)",
            Site::TreeCase => "case on a proof (tree walk)",
            Site::J => "J",
            Site::Lift => "Quot.lift",
            Site::Project => "projection",
            Site::Chain => "call returned by a body",
            Site::FieldApply => "stuck field applied",
            Site::Replay => "replayed elimination",
            Site::Conversion => "conversion",
            Site::OverApplied => "conversion, over-applied",
            Site::Unify => "unify",
            Site::UnifyOverApplied => "unify, over-applied",
            Site::CaseSplit => "elaborator case split",
            Site::Field => "field of an unfolding",
            Site::Other => "other elaborator caller",
            Site::Once => "unfold_once",
        }
    }
}

#[derive(Default)]
struct Counts {
    by_site: HashMap<(bool, Site), u64>,
    by_theorem: HashMap<String, [u64; 2]>,
    by_decl: HashMap<String, [u64; 2]>,
    by_pair: HashMap<(String, String), u64>,
    by_theorem_site: HashMap<(String, Site), u64>,
}

static COUNTS: Mutex<Option<Counts>> = Mutex::new(None);

/// 0 before the variable is read, then 1 for off and 2 for on.
static STATE: AtomicU8 = AtomicU8::new(0);

/// Whether `STITCHWORT_THEOREM_UNFOLDS=1`.
#[inline]
pub fn on() -> bool {
    match STATE.load(Relaxed) {
        0 => read_variable(),
        state => state == 2,
    }
}

#[cold]
fn read_variable() -> bool {
    let on = std::env::var("STITCHWORT_THEOREM_UNFOLDS").is_ok_and(|v| v == "1");
    STATE.store(if on { 2 } else { 1 }, Relaxed);
    on
}

/// Counts an unfolding of definition `id`'s body at `site`, if it is a
/// theorem.
#[inline]
pub fn record(g: &Ev, id: DefId, site: Site) {
    if on() {
        record_now(g, id, site);
    }
}

#[inline(never)]
fn record_now(g: &Ev, id: DefId, site: Site) {
    let def = g.def(id);
    if !def.theorem {
        return;
    }
    let kernel = g.machine.kernel.get();
    let theorem = def.path.to_string();
    let decl = crate::budget::with_current_declaration(|d| d.map(str::to_owned))
        .unwrap_or_else(|| "(outside a declaration)".to_owned());
    add(kernel, site, theorem, decl);
}

fn add(kernel: bool, site: Site, theorem: String, decl: String) {
    let mut guard = COUNTS.lock().unwrap();
    let counts = guard.get_or_insert_with(Counts::default);
    let side = usize::from(kernel);
    *counts.by_site.entry((kernel, site)).or_default() += 1;
    counts.by_theorem.entry(theorem.clone()).or_default()[side] += 1;
    counts.by_decl.entry(decl.clone()).or_default()[side] += 1;
    *counts
        .by_theorem_site
        .entry((theorem.clone(), site))
        .or_default() += 1;
    *counts.by_pair.entry((decl, theorem)).or_default() += 1;
}

/// How many theorem unfoldings were counted so far, by `(kernel, site)`:
/// for the unit test.
pub fn total() -> u64 {
    let guard = COUNTS.lock().unwrap();
    guard.as_ref().map_or(0, |c| c.by_site.values().sum())
}

const TOP: usize = 25;

/// The report's lines, if the counters are on: totals by site and mode, then
/// the theorems unfolded most, the declarations that unfolded most, and the
/// pairs.
pub fn report() -> Option<String> {
    if !on() {
        return None;
    }
    let guard = COUNTS.lock().unwrap();
    let empty = Counts::default();
    let counts = guard.as_ref().unwrap_or(&empty);
    let mut out = String::new();
    let sum = |kernel: bool| -> u64 {
        counts
            .by_site
            .iter()
            .filter(|((k, _), _)| *k == kernel)
            .map(|(_, n)| n)
            .sum()
    };
    let (elab, kernel) = (sum(false), sum(true));
    let _ = writeln!(
        out,
        "theorem unfoldings (a call of a theorem unfolded, not its own body checked): \
         {} in all, {elab} elaborator, {kernel} kernel; {} theorems, {} declarations",
        elab + kernel,
        counts.by_theorem.len(),
        counts.by_decl.len()
    );
    let _ = writeln!(out, "{:>12}  {:>12}  site", "elaborator", "kernel");
    let mut sites: Vec<Site> = counts.by_site.keys().map(|k| k.1).collect();
    sites.sort();
    sites.dedup();
    for site in sites {
        let get = |k: bool| counts.by_site.get(&(k, site)).copied().unwrap_or(0);
        let _ = writeln!(
            out,
            "{:>12}  {:>12}  {}",
            get(false),
            get(true),
            site.label()
        );
    }
    // The first segment of each declaration's name: `Std`, `Aoc`, `Syntax`:
    // what part of the program did the unfolding.
    let mut roots: HashMap<&str, [u64; 2]> = HashMap::default();
    for (decl, n) in &counts.by_decl {
        let root = decl.split(['.', ',']).next().unwrap_or(decl);
        let slot = roots.entry(root).or_default();
        slot[0] += n[0];
        slot[1] += n[1];
    }
    let mut roots: Vec<_> = roots.into_iter().collect();
    roots.sort_by(|a, b| (b.1[0] + b.1[1]).cmp(&(a.1[0] + a.1[1])).then(a.0.cmp(b.0)));
    let _ = writeln!(out, "by the first name of the declaration unfolding:");
    for (root, n) in roots.into_iter().take(TOP) {
        let _ = writeln!(out, "{:>12}  {:>12}  {root}", n[0], n[1]);
    }
    let table = |out: &mut String, title: &str, rows: Vec<(String, [u64; 2])>| {
        let _ = writeln!(out, "{title} (top {TOP}):");
        let _ = writeln!(out, "{:>12}  {:>12}  name", "elaborator", "kernel");
        for (name, n) in rows.into_iter().take(TOP) {
            let _ = writeln!(out, "{:>12}  {:>12}  {name}", n[0], n[1]);
        }
    };
    let ranked = |m: &HashMap<String, [u64; 2]>| {
        let mut rows: Vec<(String, [u64; 2])> = m.iter().map(|(k, v)| (k.clone(), *v)).collect();
        rows.sort_by(|a, b| {
            (b.1[0] + b.1[1])
                .cmp(&(a.1[0] + a.1[1]))
                .then(a.0.cmp(&b.0))
        });
        rows
    };
    let top = ranked(&counts.by_theorem);
    let _ = writeln!(out, "sites of the theorems unfolded most (top 10):");
    for (name, _) in top.iter().take(10) {
        let mut by: Vec<(Site, u64)> = counts
            .by_theorem_site
            .iter()
            .filter(|((t, _), _)| t == name)
            .map(|((_, s), n)| (*s, *n))
            .collect();
        by.sort_by_key(|x| std::cmp::Reverse(x.1));
        let by: Vec<String> = by
            .iter()
            .map(|(s, n)| format!("{n} {}", s.label()))
            .collect();
        let _ = writeln!(out, "  {name}: {}", by.join(", "));
    }
    table(&mut out, "theorems unfolded most", top);
    table(
        &mut out,
        "declarations that unfolded most",
        ranked(&counts.by_decl),
    );
    let mut pairs: Vec<(&(String, String), &u64)> = counts.by_pair.iter().collect();
    pairs.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    let _ = writeln!(out, "declaration unfolding a theorem (top {TOP}):");
    for ((decl, theorem), n) in pairs.into_iter().take(TOP) {
        let _ = writeln!(out, "{n:>12}  {decl}  <-  {theorem}");
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_by_site_mode_theorem_and_declaration() {
        let before = total();
        add(false, Site::J, "T.a".into(), "D.one".into());
        add(true, Site::J, "T.a".into(), "D.one".into());
        add(false, Site::Case, "T.b".into(), "D.two".into());
        assert_eq!(total(), before + 3);
        let guard = COUNTS.lock().unwrap();
        let counts = guard.as_ref().unwrap();
        assert!(counts.by_site[&(false, Site::J)] >= 1);
        assert!(counts.by_site[&(true, Site::J)] >= 1);
        assert!(counts.by_theorem["T.a"][0] >= 1 && counts.by_theorem["T.a"][1] >= 1);
        assert!(counts.by_pair[&("D.two".to_owned(), "T.b".to_owned())] >= 1);
    }
}
