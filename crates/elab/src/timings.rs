//! `STITCHWORT_TIMINGS`: where a run's time goes, per project namespace and
//! per standard library file (docs/proposals/check-cache.md, stage 0), and
//! per declaration (docs/proposals/proof-check-speed.md).
//!
//! Set the variable (to anything) and the CLI prints a table to stderr at
//! the end: elaboration time, time inside the kernel's declare and define
//! calls, and the size of the core terms each unit produced. Times are
//! exclusive: a library file loads in the middle of the namespace that needs
//! it, and its time and terms count against the file, not the namespace.
//!
//! `stitchwort check --timings[=all|N]` turns the tables on too, and says
//! how many declarations to list (20 by default). A namespace the check
//! cache answered for is a row marked `(cached)`.
//!
//! A second table lists declarations, slowest first (elaboration plus kernel
//! time), with their full names: a component of mutually recursive
//! declarations is one row. Besides the times it shows the evaluation steps
//! the declaration took (`Budget::total_work`) and the core term nodes it
//! made. The 20 slowest by default; `STITCHWORT_TIMINGS=decls` lists every
//! one. The table also has the largest single read-back (nodes, counted as
//! `Limits::size` counts them) and the most frames pending at once; a third
//! table lists the declarations with the largest read-backs, and the run's
//! maximum of each, for choosing the size limit (SW-2681). These are
//! exclusive too: a library file that loads while a declaration is checked
//! counts against the file.
//!
//! The timing code lives here, around the elaborator's calls into the
//! kernel, not in the kernel. When the variable is unset, every hook is one
//! read of a cached flag.

use std::cell::RefCell;
use std::fmt::Write as _;
use std::io::Write as _;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use stitchwort_core::budget::{PHASES, Peaks, step_phases};
use stitchwort_core::{Ev, Term};

/// How many declarations `check --timings` asked the tables to list; 0 if
/// it wasn't given.
static REQUESTED: AtomicUsize = AtomicUsize::new(0);

/// Turns the tables on for a run, listing `shown` declarations
/// (`check --timings`). Call it before any checking starts.
pub fn request(shown: usize) {
    REQUESTED.store(shown.max(1), Ordering::Relaxed);
}

/// Whether the tables are on: `check --timings`, or `STITCHWORT_TIMINGS`
/// set (read once).
#[inline]
pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("STITCHWORT_TIMINGS").is_some())
        || REQUESTED.load(Ordering::Relaxed) != 0
}

/// How many declarations the second table lists: what `--timings` asked
/// for, else the variable's count (`decls` is all), else 20.
fn decls_shown() -> usize {
    match REQUESTED.load(Ordering::Relaxed) {
        0 => match std::env::var("STITCHWORT_TIMINGS") {
            Ok(v) if v == "decls" => usize::MAX,
            _ => 20,
        },
        n => n,
    }
}

struct Row {
    label: String,
    elab: Duration,
    kernel: Duration,
    nodes: usize,
    decls: usize,
}

struct DeclRow {
    label: String,
    elab: Duration,
    kernel: Duration,
    steps: u64,
    /// The steps charged to each [`Phase`], when `STITCHWORT_STEP_PHASES=1`;
    /// `Phase::Other` is what the rest of `steps` was, so they sum to it.
    phases: Option<[u64; PHASES]>,
    nodes: usize,
    /// The largest read-back and the most frames pending at once.
    peaks: Peaks,
    /// The applications its `byFacts` calls tried, and the most one call
    /// tried, against `facts::ATTEMPTS`.
    facts: (usize, usize),
}

/// A unit, or a declaration, being elaborated: what has been spent in it
/// and in the units loaded inside it.
struct Frame {
    start: Instant,
    kernel: Duration,
    children: Duration,
    child_nodes: usize,
    child_decls: usize,
    child_steps: u64,
    steps_before: u64,
    /// Steps per [`Phase`] (`STITCHWORT_STEP_PHASES`) when it began, and
    /// those of the units loaded inside it.
    phases_before: [u64; PHASES],
    child_phases: [u64; PHASES],
    defs_before: usize,
    datas_before: usize,
    /// For a unit: how many declarations were being checked when it began.
    decl_depth: usize,
    /// For a declaration: the budget's peaks when it began, which it takes
    /// back when it ends, so that a declaration's peaks don't include those
    /// of a library file loaded inside it.
    outer_peaks: Peaks,
    /// For a declaration: its `byFacts` attempts, in all and in one call.
    facts: (usize, usize),
}

impl Frame {
    fn new(g: &Ev) -> Frame {
        Frame {
            start: Instant::now(),
            kernel: Duration::ZERO,
            children: Duration::ZERO,
            child_nodes: 0,
            child_decls: 0,
            child_steps: 0,
            steps_before: g.machine.budget.total_work(),
            phases_before: g.machine.budget.phase_steps(),
            child_phases: [0; PHASES],
            defs_before: g.env.defs().len(),
            datas_before: g.env.datas().len(),
            decl_depth: DECLS.with(|d| d.borrow().len()),
            outer_peaks: Peaks::default(),
            facts: (0, 0),
        }
    }
}

thread_local! {
    static STACK: RefCell<Vec<Frame>> = const { RefCell::new(Vec::new()) };
    static DECLS: RefCell<Vec<Frame>> = const { RefCell::new(Vec::new()) };
}
static ROWS: Mutex<Vec<Row>> = Mutex::new(Vec::new());
static DECL_ROWS: Mutex<Vec<DeclRow>> = Mutex::new(Vec::new());
static START: OnceLock<Instant> = OnceLock::new();

/// Marks the start of the run, for the time outside the units.
pub fn start() {
    if enabled() {
        START.get_or_init(Instant::now);
    }
}

/// Runs a kernel declare or define call, charging its time to the unit
/// and the declaration being elaborated.
#[inline]
pub fn kernel_call<T>(f: impl FnOnce() -> T) -> T {
    if !enabled() {
        return f();
    }
    let t = Instant::now();
    let out = f();
    let spent = t.elapsed();
    let decl_depth = STACK.with(|s| {
        let mut s = s.borrow_mut();
        let top = s.last_mut()?;
        top.kernel += spent;
        Some(top.decl_depth)
    });
    DECLS.with(|d| {
        let mut d = d.borrow_mut();
        // A declaration of the innermost unit, not one checked before a
        // library file began loading.
        if d.len() > decl_depth.unwrap_or(0)
            && let Some(top) = d.last_mut()
        {
            top.kernel += spent;
        }
    });
    out
}

/// Starts a unit.
pub(crate) fn begin(g: &Ev) {
    let frame = Frame::new(g);
    STACK.with(|s| s.borrow_mut().push(frame));
}

/// Ends the innermost unit and records its row.
pub(crate) fn end(g: &Ev, label: String) {
    let Some(frame) = STACK.with(|s| s.borrow_mut().pop()) else {
        return;
    };
    let total = frame.start.elapsed();
    let (nodes, decls) = made(g, &frame);
    let steps = g
        .machine
        .budget
        .total_work()
        .saturating_sub(frame.steps_before);
    STACK.with(|s| {
        if let Some(parent) = s.borrow_mut().last_mut() {
            parent.children += total;
            parent.child_nodes += nodes;
            parent.child_decls += decls;
        }
    });
    // A library file loaded while a declaration was being checked.
    DECLS.with(|d| {
        let mut d = d.borrow_mut();
        if d.len() == frame.decl_depth
            && let Some(top) = d.last_mut()
        {
            top.children += total;
            top.child_nodes += nodes;
            top.child_steps += steps;
            let now = g.machine.budget.phase_steps();
            for (child, (now, before)) in top
                .child_phases
                .iter_mut()
                .zip(now.iter().zip(&frame.phases_before))
            {
                *child += now.saturating_sub(*before);
            }
        }
    });
    ROWS.lock().unwrap().push(Row {
        label,
        elab: total.saturating_sub(frame.kernel + frame.children),
        kernel: frame.kernel,
        nodes: nodes - frame.child_nodes,
        decls: decls - frame.child_decls,
    });
}

/// Records namespace `ns`, which the check cache answered for without
/// elaborating anything: a row marked `(cached)`, with no time to show.
pub fn cached_namespace(ns: &str) {
    if enabled() {
        ROWS.lock().unwrap().push(Row {
            label: format!("{ns} (cached)"),
            elab: Duration::ZERO,
            kernel: Duration::ZERO,
            nodes: 0,
            decls: 0,
        });
    }
}

/// Starts checking a declaration (a component of them).
pub(crate) fn decl_begin(g: &Ev) {
    let mut frame = Frame::new(g);
    frame.outer_peaks = g.machine.budget.take_peaks();
    DECLS.with(|d| d.borrow_mut().push(frame));
}

/// Counts one `byFacts` call's attempts against the declaration being
/// checked.
pub(crate) fn facts_attempts(attempts: usize) {
    if !enabled() {
        return;
    }
    DECLS.with(|d| {
        if let Some(frame) = d.borrow_mut().last_mut() {
            frame.facts.0 += attempts;
            frame.facts.1 = frame.facts.1.max(attempts);
        }
    });
}

/// Ends the innermost declaration and records its row. Called after its
/// operation has ended, so that its steps are counted.
pub(crate) fn decl_end(g: &Ev, label: String) {
    let Some(frame) = DECLS.with(|d| d.borrow_mut().pop()) else {
        return;
    };
    let total = frame.start.elapsed();
    let peaks = g.machine.budget.take_peaks();
    g.machine.budget.restore_peaks(frame.outer_peaks);
    let (nodes, _) = made(g, &frame);
    let steps = g
        .machine
        .budget
        .total_work()
        .saturating_sub(frame.steps_before);
    let steps = steps.saturating_sub(frame.child_steps);
    let phases = step_phases().then(|| {
        let now = g.machine.budget.phase_steps();
        let mut phases: [u64; PHASES] = std::array::from_fn(|i| {
            now[i]
                .saturating_sub(frame.phases_before[i])
                .saturating_sub(frame.child_phases[i])
        });
        // Charging is by phase boundaries, so what is left of `steps` after
        // the named phases is `Other`; it also absorbs any rounding where an
        // operation's steps were set aside.
        let named: u64 = phases[1..].iter().sum();
        phases[0] = steps.saturating_sub(named);
        if named > steps {
            phases[1..].fill(0);
            phases[0] = steps;
        }
        phases
    });
    DECL_ROWS.lock().unwrap().push(DeclRow {
        label,
        elab: total.saturating_sub(frame.kernel + frame.children),
        kernel: frame.kernel,
        steps,
        phases,
        nodes: nodes.saturating_sub(frame.child_nodes),
        peaks,
        facts: frame.facts,
    });
}

/// The core term nodes of the definitions and types made since `frame`
/// began, and how many there are.
fn made(g: &Ev, frame: &Frame) -> (usize, usize) {
    let (mut nodes, mut decls) = (0, 0);
    for def in &g.env.defs()[frame.defs_before..] {
        nodes += size(def.ty());
        if let Some(body) = def.body() {
            nodes += size(body);
        }
        decls += 1;
    }
    for data in &g.env.datas()[frame.datas_before..] {
        for (_, t) in data.params().iter().chain(data.indices()) {
            nodes += size(t);
        }
        for c in data.ctors() {
            for (_, t) in &c.fields {
                nodes += size(t);
            }
            for t in &c.result {
                nodes += size(t);
            }
        }
        decls += 1;
    }
    (nodes, decls)
}

/// Tree size of a term, not counting source-location wrappers.
fn size(t: &Term) -> usize {
    t.subterms()
        .filter(|(t, _)| !matches!(t, Term::Loc(..)))
        .count()
}

fn ms(d: Duration) -> String {
    format!("{:.1}", d.as_secs_f64() * 1000.0)
}

/// The sessions' postponement queue counters (`state::Stats`), those of
/// elaborators made while `STITCHWORT_TIMINGS` is set.
static SESSION_STATS: Mutex<Vec<std::sync::Arc<crate::state::Stats>>> = Mutex::new(Vec::new());

/// Counts `stats` in the report.
pub(crate) fn register_stats(stats: std::sync::Arc<crate::state::Stats>) {
    SESSION_STATS.lock().unwrap().push(stats);
}

/// Each counter's name, with its sum over the sessions.
fn queue_counts() -> Vec<(&'static str, usize)> {
    let mut total = crate::state::Stats::default().counts().to_vec();
    for stats in SESSION_STATS.lock().unwrap().iter() {
        for (sum, (_, n)) in total.iter_mut().zip(stats.counts()) {
            sum.1 += n;
        }
    }
    total
}

/// The widest a name column pads to. One row names a whole mutual group,
/// which can be thousands of characters long; padding every row to that
/// width wrote tens of megabytes of spaces (SW-4610). A longer label is
/// printed in full, pushing that one row's numbers right, so its name can
/// still be read and grepped.
const MAX_NAME: usize = 60;

/// The width of a name column's padding: its longest label, up to
/// [`MAX_NAME`], but at least `least` (the header's own width).
fn name_width<'a>(labels: impl Iterator<Item = &'a str>, least: usize) -> usize {
    labels
        .map(|label| label.chars().count())
        .max()
        .unwrap_or(0)
        .min(MAX_NAME)
        .max(least)
}

/// Prints the tables to stderr, in one buffered write.
pub fn report() {
    if !enabled() {
        return;
    }
    let wall = START.get().map(Instant::elapsed).unwrap_or_default();
    let rows = ROWS.lock().unwrap();
    let width = name_width(rows.iter().map(|r| r.label.as_str()), 5);
    let mut out = String::new();
    let _ = writeln!(
        out,
        "{:<width$}  {:>10}  {:>10}  {:>10}  {:>8}",
        "unit", "elab ms", "kernel ms", "nodes", "decls"
    );
    let (mut elab, mut kernel, mut nodes, mut decls) = (Duration::ZERO, Duration::ZERO, 0, 0);
    let (mut lib_elab, mut lib_kernel, mut lib_nodes, mut lib_decls) =
        (Duration::ZERO, Duration::ZERO, 0, 0);
    for r in rows.iter() {
        let _ = writeln!(
            out,
            "{:<width$}  {:>10}  {:>10}  {:>10}  {:>8}",
            r.label,
            ms(r.elab),
            ms(r.kernel),
            r.nodes,
            r.decls
        );
        elab += r.elab;
        kernel += r.kernel;
        nodes += r.nodes;
        decls += r.decls;
        if r.label.starts_with("std/") {
            lib_elab += r.elab;
            lib_kernel += r.kernel;
            lib_nodes += r.nodes;
            lib_decls += r.decls;
        }
    }
    let line = |out: &mut String, name: &str, e: Duration, k: Duration, n: usize, d: usize| {
        let _ = writeln!(
            out,
            "{:<width$}  {:>10}  {:>10}  {:>10}  {:>8}",
            name,
            ms(e),
            ms(k),
            n,
            d
        );
    };
    let _ = writeln!(out, "{}", "-".repeat(width + 46));
    line(
        &mut out,
        "library files",
        lib_elab,
        lib_kernel,
        lib_nodes,
        lib_decls,
    );
    line(&mut out, "total", elab, kernel, nodes, decls);
    let _ = writeln!(
        out,
        "wall {} ms; outside the units (parsing, core load, printing) {} ms",
        ms(wall),
        ms(wall.saturating_sub(elab + kernel))
    );
    let queue: Vec<String> = queue_counts()
        .into_iter()
        .map(|(name, n)| format!("{n} {name}"))
        .collect();
    let _ = writeln!(out, "postponement queue: {}", queue.join(", "));
    report_decls(&mut out);
    if let Some(metrics) = stitchwort_core::env_metrics::report() {
        out.push_str(&metrics);
    }
    // Standard error is unbuffered: one write for the whole tables, then one
    // flush, rather than an `eprintln!` (and often several writes) a row.
    let stderr = std::io::stderr();
    let mut stderr = stderr.lock();
    let _ = stderr.write_all(out.as_bytes());
    let _ = stderr.flush();
}

/// Prints the declarations, slowest first.
fn report_decls(out: &mut String) {
    let mut rows = DECL_ROWS.lock().unwrap();
    if rows.is_empty() {
        let _ = writeln!(out);
        let _ = writeln!(out, "no declarations were checked");
        return;
    }
    rows.sort_by(|a, b| {
        (b.elab + b.kernel)
            .cmp(&(a.elab + a.kernel))
            .then_with(|| a.label.cmp(&b.label))
    });
    let shown = decls_shown().min(rows.len());
    let _ = writeln!(out);
    write_decls(out, &rows, shown);
    if shown < rows.len() {
        let _ = writeln!(
            out,
            "({} more; --timings=all lists every declaration)",
            rows.len() - shown
        );
    }
    let width = name_width(rows[..shown].iter().map(|r| r.label.as_str()), 11);
    report_phases(out, &rows[..shown], width);
    report_readbacks(out, &mut rows);
    report_facts(out, &mut rows);
}

/// The declaration table's header and its first `shown` rows.
fn write_decls(out: &mut String, rows: &[DeclRow], shown: usize) {
    let width = name_width(rows[..shown].iter().map(|r| r.label.as_str()), 11);
    let _ = writeln!(
        out,
        "{:<width$}  {:>10}  {:>10}  {:>10}  {:>12}  {:>10}  {:>10}  {:>10}",
        "declaration", "elab ms", "kernel ms", "total ms", "steps", "nodes", "read-back", "frames"
    );
    for r in &rows[..shown] {
        let _ = writeln!(
            out,
            "{:<width$}  {:>10}  {:>10}  {:>10}  {:>12}  {:>10}  {:>10}  {:>10}",
            r.label,
            ms(r.elab),
            ms(r.kernel),
            ms(r.elab + r.kernel),
            r.steps,
            r.nodes,
            r.peaks.readback,
            r.peaks.frames
        );
    }
}

/// With `STITCHWORT_STEP_PHASES=1`, prints the steps each of `rows` took in
/// each elaborator phase, in the order of the table above: the phases sum to
/// `steps`.
fn report_phases(out: &mut String, rows: &[DeclRow], width: usize) {
    if !step_phases() {
        return;
    }
    let _ = writeln!(out);
    let _ = writeln!(
        out,
        "{:<width$}  {:>12}  {:>12}  {:>12}  {:>12}  {:>12}  {:>12}",
        "steps by phase", "steps", "walk", "unify", "apply", "read-back", "other"
    );
    for r in rows {
        let [other, walk, unify, apply, readback] = r.phases.unwrap_or([r.steps, 0, 0, 0, 0]);
        let _ = writeln!(
            out,
            "{:<width$}  {:>12}  {:>12}  {:>12}  {:>12}  {:>12}  {:>12}",
            r.label, r.steps, walk, unify, apply, readback, other
        );
    }
}

/// Prints the declarations whose `byFacts` calls tried the most
/// applications: the proofs nearest the attempt limit.
fn report_facts(out: &mut String, rows: &mut [DeclRow]) {
    rows.sort_by(|a, b| {
        (b.facts.1, b.facts.0)
            .cmp(&(a.facts.1, a.facts.0))
            .then_with(|| a.label.cmp(&b.label))
    });
    let used = rows.iter().take_while(|r| r.facts.0 > 0).count();
    if used == 0 {
        return;
    }
    let shown = decls_shown().min(used);
    let width = name_width(rows[..shown].iter().map(|r| r.label.as_str()), 16);
    let _ = writeln!(out);
    let _ = writeln!(
        out,
        "{:<width$}  {:>12}  {:>12}",
        "byFacts attempts", "most in one", "in all"
    );
    for r in &rows[..shown] {
        let _ = writeln!(
            out,
            "{:<width$}  {:>12}  {:>12}",
            r.label, r.facts.1, r.facts.0
        );
    }
    let _ = writeln!(
        out,
        "the limit is {} attempts a call",
        crate::facts::ATTEMPTS
    );
}

/// Prints the declarations with the largest single read-back, largest first:
/// what a lower `Limits::size` would break first (SW-2681).
fn report_readbacks(out: &mut String, rows: &mut [DeclRow]) {
    rows.sort_by(|a, b| {
        (b.peaks.readback, b.peaks.frames)
            .cmp(&(a.peaks.readback, a.peaks.frames))
            .then_with(|| a.label.cmp(&b.label))
    });
    let shown = decls_shown().min(rows.len());
    let width = name_width(rows[..shown].iter().map(|r| r.label.as_str()), 11);
    let _ = writeln!(out);
    let _ = writeln!(
        out,
        "{:<width$}  {:>12}  {:>12}",
        "largest read-backs", "nodes", "max frames"
    );
    for r in &rows[..shown] {
        let _ = writeln!(
            out,
            "{:<width$}  {:>12}  {:>12}",
            r.label, r.peaks.readback, r.peaks.frames
        );
    }
    let deepest = rows.iter().map(|r| r.peaks.frames).max().unwrap_or(0);
    let _ = writeln!(
        out,
        "over {} declarations: largest read-back {} nodes, deepest {} frames",
        rows.len(),
        rows.first().map_or(0, |r| r.peaks.readback),
        deepest
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decl_row(label: &str) -> DeclRow {
        DeclRow {
            label: label.to_owned(),
            elab: Duration::ZERO,
            kernel: Duration::ZERO,
            steps: 0,
            phases: None,
            nodes: 0,
            peaks: Peaks::default(),
            facts: (0, 0),
        }
    }

    /// A mutual group's name can be thousands of characters long; it is
    /// printed in full, while every other row pads only to [`MAX_NAME`]
    /// (SW-4610).
    #[test]
    fn a_very_long_name_does_not_widen_the_other_rows() {
        let long_name = format!("Main.{}", "a".repeat(500));
        let rows = [decl_row("Main.short"), decl_row(&long_name)];
        let mut out = String::new();
        write_decls(&mut out, &rows, rows.len());
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines.len(), 3, "{out}");
        let (header, short, long) = (lines[0], lines[1], lines[2]);
        // The long name is printed in full: nothing is lost to an ellipsis.
        assert!(
            long.starts_with(&format!("{long_name}  ")),
            "long row: {long}"
        );
        // The short row is padded only to the cap, not to the long name's
        // width, so it lines up with the header.
        assert!(short.starts_with(&format!("{:<MAX_NAME$}  ", "Main.short")));
        assert_eq!(short.chars().count(), header.chars().count(), "{out}");
        // Only the long row's own numbers are pushed right.
        assert!(long.chars().count() > header.chars().count(), "{out}");
        let numbers = |line: &str| line.chars().skip(MAX_NAME + 2).collect::<String>();
        assert!(long.ends_with(&numbers(short)), "long row: {long}");
    }
}
