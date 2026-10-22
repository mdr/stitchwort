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
//! A second table lists declarations, slowest first (elaboration plus kernel
//! time), with their full names: a component of mutually recursive
//! declarations is one row. Besides the times it shows the evaluation steps
//! the declaration took (`Budget::total_work`) and the core term nodes it
//! made. The 20 slowest by default; `STITCHWORT_TIMINGS=decls` lists every
//! one. These are exclusive too: a library file that loads while a
//! declaration is checked counts against the file.
//!
//! The timing code lives here, around the elaborator's calls into the
//! kernel, not in the kernel. When the variable is unset, every hook is one
//! read of a cached flag.

use std::cell::RefCell;
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use stitchwort_core::{Globals, Term};

/// Whether `STITCHWORT_TIMINGS` is set. Read once.
#[inline]
pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("STITCHWORT_TIMINGS").is_some())
}

/// How many declarations the second table lists.
fn decls_shown() -> usize {
    match std::env::var("STITCHWORT_TIMINGS") {
        Ok(v) if v == "decls" => usize::MAX,
        _ => 20,
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
    nodes: usize,
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
    defs_before: usize,
    datas_before: usize,
    /// For a unit: how many declarations were being checked when it began.
    decl_depth: usize,
}

impl Frame {
    fn new(g: &Globals) -> Frame {
        Frame {
            start: Instant::now(),
            kernel: Duration::ZERO,
            children: Duration::ZERO,
            child_nodes: 0,
            child_decls: 0,
            child_steps: 0,
            steps_before: g.budget.total_work(),
            defs_before: g.defs.len(),
            datas_before: g.datas.len(),
            decl_depth: DECLS.with(|d| d.borrow().len()),
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
pub(crate) fn begin(g: &Globals) {
    let frame = Frame::new(g);
    STACK.with(|s| s.borrow_mut().push(frame));
}

/// Ends the innermost unit and records its row.
pub(crate) fn end(g: &Globals, label: String) {
    let Some(frame) = STACK.with(|s| s.borrow_mut().pop()) else {
        return;
    };
    let total = frame.start.elapsed();
    let (nodes, decls) = made(g, &frame);
    let steps = g.budget.total_work().saturating_sub(frame.steps_before);
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

/// Starts checking a declaration (a component of them).
pub(crate) fn decl_begin(g: &Globals) {
    let frame = Frame::new(g);
    DECLS.with(|d| d.borrow_mut().push(frame));
}

/// Ends the innermost declaration and records its row. Called after its
/// operation has ended, so that its steps are counted.
pub(crate) fn decl_end(g: &Globals, label: String) {
    let Some(frame) = DECLS.with(|d| d.borrow_mut().pop()) else {
        return;
    };
    let total = frame.start.elapsed();
    let (nodes, _) = made(g, &frame);
    let steps = g.budget.total_work().saturating_sub(frame.steps_before);
    DECL_ROWS.lock().unwrap().push(DeclRow {
        label,
        elab: total.saturating_sub(frame.kernel + frame.children),
        kernel: frame.kernel,
        steps: steps.saturating_sub(frame.child_steps),
        nodes: nodes.saturating_sub(frame.child_nodes),
    });
}

/// The core term nodes of the definitions and types made since `frame`
/// began, and how many there are.
fn made(g: &Globals, frame: &Frame) -> (usize, usize) {
    let (mut nodes, mut decls) = (0, 0);
    for def in &g.defs[frame.defs_before..] {
        nodes += size(&def.ty);
        if let Some(body) = def.body() {
            nodes += size(body);
        }
        decls += 1;
    }
    for data in &g.datas[frame.datas_before..] {
        for (_, t) in data.params.iter().chain(&data.indices) {
            nodes += size(t);
        }
        for c in &data.ctors {
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

/// Prints the tables to stderr.
pub fn report() {
    if !enabled() {
        return;
    }
    let wall = START.get().map(Instant::elapsed).unwrap_or_default();
    let rows = ROWS.lock().unwrap();
    let width = rows.iter().map(|r| r.label.len()).max().unwrap_or(0).max(5);
    eprintln!(
        "{:<width$}  {:>10}  {:>10}  {:>10}  {:>8}",
        "unit", "elab ms", "kernel ms", "nodes", "decls"
    );
    let (mut elab, mut kernel, mut nodes, mut decls) = (Duration::ZERO, Duration::ZERO, 0, 0);
    let (mut lib_elab, mut lib_kernel, mut lib_nodes, mut lib_decls) =
        (Duration::ZERO, Duration::ZERO, 0, 0);
    for r in rows.iter() {
        eprintln!(
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
    let line = |name: &str, e: Duration, k: Duration, n: usize, d: usize| {
        eprintln!(
            "{:<width$}  {:>10}  {:>10}  {:>10}  {:>8}",
            name,
            ms(e),
            ms(k),
            n,
            d
        );
    };
    eprintln!("{}", "-".repeat(width + 46));
    line("library files", lib_elab, lib_kernel, lib_nodes, lib_decls);
    line("total", elab, kernel, nodes, decls);
    eprintln!(
        "wall {} ms; outside the units (parsing, core load, printing) {} ms",
        ms(wall),
        ms(wall.saturating_sub(elab + kernel))
    );
    report_decls();
}

/// Prints the declarations, slowest first.
fn report_decls() {
    let mut rows = DECL_ROWS.lock().unwrap();
    if rows.is_empty() {
        return;
    }
    rows.sort_by(|a, b| {
        (b.elab + b.kernel)
            .cmp(&(a.elab + a.kernel))
            .then_with(|| a.label.cmp(&b.label))
    });
    let shown = decls_shown().min(rows.len());
    let width = rows[..shown]
        .iter()
        .map(|r| r.label.len())
        .max()
        .unwrap_or(0)
        .max(11);
    eprintln!();
    eprintln!(
        "{:<width$}  {:>10}  {:>10}  {:>12}  {:>10}",
        "declaration", "elab ms", "kernel ms", "steps", "nodes"
    );
    for r in &rows[..shown] {
        eprintln!(
            "{:<width$}  {:>10}  {:>10}  {:>12}  {:>10}",
            r.label,
            ms(r.elab),
            ms(r.kernel),
            r.steps,
            r.nodes
        );
    }
    if shown < rows.len() {
        eprintln!(
            "({} more; STITCHWORT_TIMINGS=decls lists every declaration)",
            rows.len() - shown
        );
    }
}
