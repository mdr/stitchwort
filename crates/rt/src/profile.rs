//! The machine's profiler, for `stitchwort run --profile`
//! (docs/proposals/run-profiler.md): exact calls per definition, and
//! sampled self and total time.
//!
//! - **Rows.** Every code of the [`Image`] belongs to a row, named in
//!   source terms: a global's code by the global (the optimiser's copies,
//!   `Std.Map.insertWith[2]`, by the function they copy), a lambda's by the
//!   definition that makes it with `.λ` after, the entry as `(entry)`.
//! - **Calls** are counted at every frame entry, a tail call included.
//! - **Time** is sampled: a timer thread raises a flag every interval, and
//!   at the next frame entry the machine charges the real time since the
//!   last sample to the stack it has then: to the top frame's row as self
//!   time, and once (however deep the recursion) to every row on the stack
//!   as total time.
//! - **Tail calls.** A tail call replaces its caller's frame, which would
//!   drop the caller from the stack. Each frame depth keeps the rows that
//!   have run in it since its frame was pushed (up to [`CHAIN`]), and a
//!   sample counts them all as on the stack.
//!
//! The counters are relaxed atomics in a [`Profile`] shared with the
//! caller, written only by the machine's thread, so a signal handler on
//! another thread can report the profile of an interrupted run.

use std::fmt::Write as _;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};
use std::time::{Duration, Instant};

use smallvec::SmallVec;
use stitchwort_core::collections::HashMap;

use crate::code::{Image, Instr};
use crate::ir::Program;

/// The most rows a frame depth remembers having run in it, through tail
/// calls; past this the middle of a tail-call chain is lost.
const CHAIN: usize = 8;

/// When the profiler samples.
#[derive(Clone, Copy, Debug)]
pub enum Sampling {
    /// Every so often, by a timer thread: what `--profile` uses.
    Every(Duration),
    /// At every frame entry, each sample weighing one: deterministic, for
    /// tests of the accounting.
    EachEntry,
}

/// What a run's profile has counted: per row, the calls and the time.
/// Shared between the machine's thread, which writes it, and whoever
/// reports it.
pub struct Profile {
    names: Vec<Box<str>>,
    calls: Vec<AtomicU64>,
    /// Nanoseconds, or samples with [`Sampling::EachEntry`].
    self_time: Vec<AtomicU64>,
    total_time: Vec<AtomicU64>,
    samples: AtomicU64,
    sampling: Sampling,
}

/// One row of a profile, for tests and reports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row {
    pub name: String,
    pub calls: u64,
    /// Nanoseconds, or samples with [`Sampling::EachEntry`].
    pub self_time: u64,
    pub total_time: u64,
}

impl Profile {
    /// The rows with anything counted, most self time first (then most
    /// calls, then by name).
    pub fn rows(&self) -> Vec<Row> {
        let mut rows: Vec<Row> = (0..self.names.len())
            .map(|i| Row {
                name: self.names[i].to_string(),
                calls: self.calls[i].load(Relaxed),
                self_time: self.self_time[i].load(Relaxed),
                total_time: self.total_time[i].load(Relaxed),
            })
            .filter(|row| row.calls > 0 || row.total_time > 0)
            .collect();
        rows.sort_by(|a, b| (b.self_time, b.calls, &a.name).cmp(&(a.self_time, a.calls, &b.name)));
        rows
    }

    /// The samples taken.
    pub fn samples(&self) -> u64 {
        self.samples.load(Relaxed)
    }

    /// The table `--profile` prints: a heading, then the first `top` rows
    /// (all of them if `top` is 0).
    pub fn report(&self, top: usize) -> String {
        let rows = self.rows();
        let all: u64 = rows.iter().map(|row| row.self_time).sum();
        let mut out = String::new();
        let timed = matches!(self.sampling, Sampling::Every(_));
        match self.sampling {
            Sampling::Every(every) => {
                let _ = writeln!(
                    out,
                    "profile: {} s in the program, {} samples every {} ms",
                    seconds(all),
                    grouped(self.samples()),
                    every.as_secs_f64() * 1000.0
                );
            }
            Sampling::EachEntry => {
                let _ = writeln!(out, "profile: {} samples, one per call", self.samples());
            }
        }
        let unit = if timed { "s" } else { "n" };
        let _ = writeln!(
            out,
            "  self %    self {unit}   total %   total {unit}          calls  definition"
        );
        let shown = if top == 0 { rows.len() } else { top };
        for row in rows.iter().take(shown) {
            let (own, total) = if timed {
                (seconds(row.self_time), seconds(row.total_time))
            } else {
                (row.self_time.to_string(), row.total_time.to_string())
            };
            let _ = writeln!(
                out,
                "{:>7.1}%  {:>8}  {:>7.1}%  {:>8}  {:>13}  {}",
                percent(row.self_time, all),
                own,
                percent(row.total_time, all),
                total,
                grouped(row.calls),
                row.name
            );
        }
        if rows.len() > shown {
            let _ = writeln!(
                out,
                "  ({} more; --profile-top 0 shows them all)",
                rows.len() - shown
            );
        }
        out
    }
}

fn percent(part: u64, all: u64) -> f64 {
    if all == 0 {
        0.0
    } else {
        part as f64 * 100.0 / all as f64
    }
}

fn seconds(ns: u64) -> String {
    format!("{:.3}", ns as f64 / 1e9)
}

/// `n` with commas between thousands.
fn grouped(n: u64) -> String {
    let digits = n.to_string();
    let mut out = String::new();
    for (i, c) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    out
}

/// The machine's side of a profile: what it needs at each frame entry.
pub(crate) struct Profiler {
    shared: Arc<Profile>,
    /// Each code's row.
    row_of: Vec<u32>,
    /// Per frame depth, the rows that have run in that frame, the current
    /// one last.
    chains: Vec<SmallVec<[u32; 4]>>,
    /// Per row, the last sample that counted it in its total.
    stamp: Vec<u64>,
    /// Raised by the timer thread; `None` samples at every entry.
    due: Option<Arc<AtomicBool>>,
    last: Instant,
}

impl Profiler {
    pub(crate) fn new(program: &Program, image: &Image, sampling: Sampling) -> Profiler {
        let (names, row_of) = rows(program, image);
        let n = names.len();
        let counters = || (0..n).map(|_| AtomicU64::new(0)).collect::<Vec<_>>();
        let shared = Arc::new(Profile {
            names,
            calls: counters(),
            self_time: counters(),
            total_time: counters(),
            samples: AtomicU64::new(0),
            sampling,
        });
        let due = match sampling {
            Sampling::Every(every) => Some(timer(every)),
            Sampling::EachEntry => None,
        };
        Profiler {
            shared,
            row_of,
            chains: Vec::new(),
            stamp: vec![0; n],
            due,
            last: Instant::now(),
        }
    }

    pub(crate) fn profile(&self) -> Arc<Profile> {
        self.shared.clone()
    }

    /// A frame for `code` has just been pushed at `depth` (0 for the
    /// bottom frame), or (`tail`) has replaced the frame there.
    #[inline(never)]
    pub(crate) fn entered(&mut self, code: u32, depth: usize, tail: bool) {
        let row = self.row_of[code as usize];
        let calls = &self.shared.calls[row as usize];
        calls.store(calls.load(Relaxed) + 1, Relaxed);
        if self.chains.len() <= depth {
            self.chains.resize_with(depth + 1, SmallVec::new);
        }
        let chain = &mut self.chains[depth];
        if !tail {
            chain.clear();
            chain.push(row);
        } else if let Some(at) = chain.iter().position(|r| *r == row) {
            // Current again (a loop): last, without growing the chain.
            chain.remove(at);
            chain.push(row);
        } else {
            if chain.len() == CHAIN {
                // The middle goes: the frame's first row stays.
                chain.remove(1);
            }
            chain.push(row);
        }
        let weight = match &self.due {
            None => 1,
            Some(due) => {
                if !due.load(Relaxed) {
                    return;
                }
                due.store(false, Relaxed);
                let now = Instant::now();
                let ns = now.duration_since(self.last).as_nanos();
                self.last = now;
                u64::try_from(ns).unwrap_or(u64::MAX)
            }
        };
        self.sample(depth, weight);
    }

    /// Charges `weight` to the stack of frames `0..=depth`. Each depth's
    /// chain is its current frame's: set when that frame was pushed, and
    /// added to only by tail calls in it.
    fn sample(&mut self, depth: usize, weight: u64) {
        let p = &self.shared;
        let id = p.samples.load(Relaxed) + 1;
        p.samples.store(id, Relaxed);
        let add = |counter: &AtomicU64| counter.store(counter.load(Relaxed) + weight, Relaxed);
        let top = *self.chains[depth].last().expect("the new frame's row");
        add(&p.self_time[top as usize]);
        for chain in &self.chains[..=depth] {
            for &row in chain {
                if self.stamp[row as usize] != id {
                    self.stamp[row as usize] = id;
                    add(&p.total_time[row as usize]);
                }
            }
        }
    }
}

/// A flag raised every `every`, by a thread that ends once only it holds
/// the flag.
fn timer(every: Duration) -> Arc<AtomicBool> {
    let due = Arc::new(AtomicBool::new(false));
    let theirs = due.clone();
    let spawned = std::thread::Builder::new()
        .name("profile timer".into())
        .spawn(move || {
            while Arc::strong_count(&theirs) > 1 {
                std::thread::sleep(every);
                theirs.store(true, Relaxed);
            }
        });
    if spawned.is_err() {
        // No timer: sample at every entry rather than never.
        due.store(true, Relaxed);
    }
    due
}

/// The rows' names and each code's row (see the module's doc).
fn rows(program: &Program, image: &Image) -> (Vec<Box<str>>, Vec<u32>) {
    let codes = image.codes.len();
    // The globals' and the entry's codes: the names lambdas are charged to.
    let mut owner: Vec<Option<Rc<str>>> = vec![None; codes];
    for (g, code) in image.global_code.iter().enumerate() {
        if let Some(code) = code {
            owner[*code as usize] = Some(source_name(&program.globals[g].name).into());
        }
    }
    owner[image.entry_code as usize] = Some("(entry)".into());
    // Which code makes each lambda's closure.
    let mut maker: Vec<Option<u32>> = vec![None; codes];
    for (code, body) in image.codes.iter().enumerate() {
        for instr in &body.instrs {
            if let Instr::Closure { lambda, .. } = instr {
                let made = image.lambda_code[*lambda as usize] as usize;
                maker[made].get_or_insert(u32::try_from(code).expect("codes fit"));
            }
        }
    }
    let mut code_name = owner.clone();
    for &code in &image.lambda_code {
        // Up through the makers (lambdas in lambdas) to a definition.
        let mut at = code;
        let mut hops = 0;
        let made_in = loop {
            match maker[at as usize] {
                Some(up) if hops < codes => {
                    if let Some(name) = &owner[up as usize] {
                        break Some(name.clone());
                    }
                    at = up;
                    hops += 1;
                }
                _ => break None,
            }
        };
        let name = match made_in {
            Some(owner) => format!("{owner}.λ"),
            None => "(a lambda)".to_string(),
        };
        code_name[code as usize] = Some(name.into());
    }
    let mut index: HashMap<Rc<str>, u32> = HashMap::default();
    let mut names: Vec<Box<str>> = Vec::new();
    let row_of = code_name
        .into_iter()
        .map(|name| {
            let name = name.unwrap_or_else(|| "(unnamed code)".into());
            *index.entry(name.clone()).or_insert_with(|| {
                names.push((*name).into());
                u32::try_from(names.len() - 1).expect("rows fit")
            })
        })
        .collect();
    (names, row_of)
}

/// A global's name as its source has it: without the optimiser's suffix
/// for a copy (`Std.Map.insertWith[2]`, `go[cells]`), and with a `match`
/// the elaborator made a function of (`Std.Map.Tree.get.%match1`) charged
/// to the definition it's in.
fn source_name(name: &str) -> &str {
    let name = match name.find('[') {
        Some(at) if at > 0 => &name[..at],
        _ => name,
    };
    match name.rfind(".%match") {
        Some(at)
            if at > 0
                && name[at + ".%match".len()..]
                    .chars()
                    .all(|c| c.is_ascii_digit()) =>
        {
            source_name(&name[..at])
        }
        _ => name,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn copies_are_named_as_what_they_copy() {
        assert_eq!(source_name("Std.Map.insertWith[2]"), "Std.Map.insertWith");
        assert_eq!(source_name("go[cells#1]"), "go");
        assert_eq!(source_name("Day11.step"), "Day11.step");
        assert_eq!(source_name("Std.Map.Tree.get.%match1"), "Std.Map.Tree.get");
        assert_eq!(source_name("f.%match2.%match1[3]"), "f");
        assert_eq!(source_name("Day11.Seat.%decEq"), "Day11.Seat.%decEq");
    }

    #[test]
    fn numbers_are_grouped_by_thousands() {
        assert_eq!(grouped(0), "0");
        assert_eq!(grouped(999), "999");
        assert_eq!(grouped(1000), "1,000");
        assert_eq!(grouped(21_816_000), "21,816,000");
    }
}
