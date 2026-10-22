//! `STITCHWORT_TIMINGS`: where a run's time goes, per project namespace and
//! per standard library file (docs/proposals/check-cache.md, stage 0).
//!
//! Set the variable (to anything) and the CLI prints a table to stderr at
//! the end: elaboration time, time inside the kernel's declare and define
//! calls, and the size of the core terms each unit produced. Times are
//! exclusive: a library file loads in the middle of the namespace that needs
//! it, and its time and terms count against the file, not the namespace.
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

struct Row {
    label: String,
    elab: Duration,
    kernel: Duration,
    nodes: usize,
    decls: usize,
}

/// A unit being elaborated: what has been spent in it and in the units
/// loaded inside it.
struct Frame {
    start: Instant,
    kernel: Duration,
    children: Duration,
    child_nodes: usize,
    child_decls: usize,
    defs_before: usize,
    datas_before: usize,
}

thread_local! {
    static STACK: RefCell<Vec<Frame>> = const { RefCell::new(Vec::new()) };
}
static ROWS: Mutex<Vec<Row>> = Mutex::new(Vec::new());
static START: OnceLock<Instant> = OnceLock::new();

/// Marks the start of the run, for the time outside the units.
pub fn start() {
    if enabled() {
        START.get_or_init(Instant::now);
    }
}

/// Runs a kernel declare or define call, charging its time to the unit
/// being elaborated.
#[inline]
pub fn kernel_call<T>(f: impl FnOnce() -> T) -> T {
    if !enabled() {
        return f();
    }
    let t = Instant::now();
    let out = f();
    let spent = t.elapsed();
    STACK.with(|s| {
        if let Some(top) = s.borrow_mut().last_mut() {
            top.kernel += spent;
        }
    });
    out
}

/// Starts a unit.
pub(crate) fn begin(g: &Globals) {
    STACK.with(|s| {
        s.borrow_mut().push(Frame {
            start: Instant::now(),
            kernel: Duration::ZERO,
            children: Duration::ZERO,
            child_nodes: 0,
            child_decls: 0,
            defs_before: g.defs.len(),
            datas_before: g.datas.len(),
        })
    });
}

/// Ends the innermost unit and records its row.
pub(crate) fn end(g: &Globals, label: String) {
    let Some(frame) = STACK.with(|s| s.borrow_mut().pop()) else {
        return;
    };
    let total = frame.start.elapsed();
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
    let (own_nodes, own_decls) = (nodes - frame.child_nodes, decls - frame.child_decls);
    STACK.with(|s| {
        if let Some(parent) = s.borrow_mut().last_mut() {
            parent.children += total;
            parent.child_nodes += nodes;
            parent.child_decls += decls;
        }
    });
    ROWS.lock().unwrap().push(Row {
        label,
        elab: total - frame.kernel - frame.children,
        kernel: frame.kernel,
        nodes: own_nodes,
        decls: own_decls,
    });
}

/// Tree size of a term, not counting source-location wrappers.
fn size(t: &Term) -> usize {
    t.subterms()
        .filter(|(t, _)| !matches!(t, Term::Loc(..)))
        .count()
}

/// Prints the table to stderr.
pub fn report() {
    if !enabled() {
        return;
    }
    let wall = START.get().map(Instant::elapsed).unwrap_or_default();
    let rows = ROWS.lock().unwrap();
    let ms = |d: Duration| format!("{:.1}", d.as_secs_f64() * 1000.0);
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
}
