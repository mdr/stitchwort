//! `check --jobs N` (docs/proposals/parallel-checking.md §9, and
//! parallel-checking-stage-3.md): a parallel fill of the check cache, after
//! which the ordinary sequential check runs over the same store and
//! reports.
//!
//! Workers are threads, each with its own session. A worker given a
//! namespace replays what its session lacks of the namespace's
//! dependencies from the cache, then checks the namespace; the entry is
//! written by the code that writes it in a sequential check. When nothing
//! more can be filled, [`fill`] returns, and the caller runs its usual
//! check, which finds an entry for every namespace that was clean and
//! checks for itself whatever has none (an error, an open goal, a syntax
//! error, and everything that uses one). So every message, its order, the
//! summary and the exit code come from the sequential check: the fill only
//! decides which entries exist when it starts (§9.4).
//!
//! - **Two jobs per namespace** (stage 3, D3735). The *proof job* is the
//!   namespace's whole check, which writes its entry. The *interface job*
//!   is an interface pass (`Elaborator::set_interface_pass`): the
//!   namespace's definitions and the statements of its theorems, with the
//!   proofs it may defer left out, giving an interface entry that the
//!   namespaces above it are checked against while its proofs are still
//!   being checked. Interface entries live in this run's memory only
//!   ([`WorkerStore`]), are read only by workers, and are never written to
//!   a store; the check after the fill can't see them. A namespace gets an
//!   interface job only if something in the fill uses it and it has a
//!   theorem whose proof may be deferred (`cache::may_defer`); without
//!   (`STITCHWORT_STATEMENTS_FIRST=0`, [`Jobs::statements_first`]) the
//!   fill is stage 1's.
//! - **The key chain is the join** (stage 3 §5). An entry written by a
//!   proof job checked against an interface entry is keyed by the digest
//!   that interface claimed, so the check after the fill finds it only
//!   once the namespace below has its own whole entry with that digest.
//!   A whole entry is written as soon as its own namespace's check passes
//!   (D3737), which is what an entry already means (invariant W′).
//! - **What a worker holds.** Its session keeps every namespace it loaded,
//!   for the whole run, so it loads each at most once. A namespace it
//!   checked without writing an entry is rewound away, so no later job runs
//!   beside a failed namespace. With interface jobs, a mark is kept before
//!   each namespace it holds, so that it can rewind to before a namespace
//!   it holds the interface of and check it whole.
//! - **Ready, and left.** A job is ready when every namespace its namespace
//!   uses has an interface: a whole entry (found before the fill, or
//!   written in it), or an interface entry. A namespace is left to the
//!   check after the fill if it has a syntax error, or its proof job wrote
//!   nothing, or its interface pass failed, or it uses one that is left;
//!   no new job is started above it, and the rest of the graph is still
//!   filled. Jobs above it already running finish, and their entries are
//!   harmless by the key chain.
//! - **Which first.** An interface job (they unlock work), by stage 1's
//!   rule: the longest chain of namespaces above, then the one the worker
//!   holds most of the closure of, then the first in canonical order.
//!   Then a proof job the worker's session doesn't hold: first one whose
//!   dependants wait for it (it has no interface), by the same rule, then
//!   the lowest in canonical order. Then a proof job of a namespace the
//!   session holds the interface of, the one nearest the top of the
//!   session, after rewinding to before it. Given a seed, a random ready
//!   job, for the test that the order doesn't change an entry.
//! - **Digests must agree.** A proof job's interface digest must be its
//!   interface pass's; a namespace where they differ is counted
//!   ([`Fill::mismatches`]), and what is above it left to the check after
//!   the fill. Never expected: it would be a bug in the deferral rule or
//!   the digest, and costs time, not correctness.
//! - **Library files** are claimed ([`ClaimStore`]) so two workers don't
//!   elaborate the same one.
//! - **A panic** in a worker stops the fill (a shared flag, also each
//!   worker's cancellation flag); the check after it meets the same
//!   problem on the caller's thread and reports it as without `--jobs`.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

use stitchwort_elab::cache::{Key, Stats, Store, may_defer};
use stitchwort_syntax::{Severity, SourceMap};

use crate::check_cache::{ClaimStore, Claims};
use crate::driver::Session;
use crate::project::{
    Analysis, CONFIG, Files, Load, Target, analyse, dependencies, project_sources,
};
use crate::rewind::Mark;

/// How a parallel fill runs.
pub struct Jobs<'a> {
    /// How many workers, the caller's thread among them.
    pub count: usize,
    /// The stack each worker thread gets, which the sessions `make_session`
    /// makes must be for; the caller's thread must have it too.
    pub stack: usize,
    /// A session as the check after the fill uses, without a check cache.
    pub make_session: &'a (dyn Fn(usize) -> Session + Sync),
    /// A worker's handle on the store the check after the fill uses.
    pub make_store: &'a (dyn Fn() -> Rc<dyn Store> + Sync),
    /// Pick ready jobs at random, from this seed (`STITCHWORT_JOBS_SEED`),
    /// rather than by the rule above.
    pub seed: Option<u64>,
    /// Whether namespaces get interface jobs (stage 3); off with
    /// `STITCHWORT_STATEMENTS_FIRST=0`, for comparison.
    pub statements_first: bool,
    /// A flag that stops the fill when set from outside (the language
    /// server's shutdown): it becomes every worker's cancellation flag, so
    /// the namespaces being checked stop part-way and aren't written, and
    /// no more jobs are given out. A panic in a worker sets it too.
    pub cancel: Option<Arc<AtomicBool>>,
    /// Whether the workers' sessions are freed when they finish. The
    /// command line leaves them, since freeing takes longer than the
    /// process has left; a server that lives on frees them.
    pub free_sessions: bool,
    /// Told which namespaces the fill may still write, for a caller that
    /// checks beside it (the language server, [`Watch`]).
    pub watch: Option<&'a Watch>,
}

/// Which namespaces a running fill may still write an entry for, so that
/// a check running beside it (the language server's, SW-4760) can wait
/// for an entry rather than check the namespace itself. Until the fill has
/// planned, every namespace counts; once it has ended (finished, stopped
/// or given up), none does.
#[derive(Debug, Default)]
pub struct Watch(Mutex<WatchState>);

#[derive(Debug, Default)]
struct WatchState {
    planned: bool,
    over: bool,
    /// The namespaces whose proof job is waiting or running.
    pending: std::collections::BTreeSet<String>,
}

impl Watch {
    fn state(&self) -> std::sync::MutexGuard<'_, WatchState> {
        self.0.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Whether the fill may yet write the entry of `namespace`.
    pub fn pending(&self, namespace: &str) -> bool {
        let state = self.state();
        !state.over && (!state.planned || state.pending.contains(namespace))
    }

    /// Whether the fill has ended.
    pub fn over(&self) -> bool {
        self.state().over
    }

    fn update(&self, pending: std::collections::BTreeSet<String>) {
        let mut state = self.state();
        state.planned = true;
        state.pending = pending;
    }

    fn end(&self) {
        let mut state = self.state();
        state.over = true;
        state.pending.clear();
    }
}

/// Ends a fill's [`Watch`] however the fill returns.
struct EndWatch<'a>(Option<&'a Watch>);

impl Drop for EndWatch<'_> {
    fn drop(&mut self) {
        if let Some(watch) = self.0 {
            watch.end();
        }
    }
}

/// The number of workers `auto` means: the cores, but at most 8 and at
/// most one per 2 GB of memory (a worker on `tools/fmt` holds about
/// 0.6 GB, and the machine runs other things); at least 1.
pub fn auto_jobs() -> usize {
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
    let by_memory = physical_memory().map_or(usize::MAX, |bytes| (bytes >> 31) as usize);
    cores.min(8).min(by_memory).max(1)
}

/// The machine's memory in bytes, where it can be asked.
#[cfg(unix)]
#[allow(unsafe_code)]
fn physical_memory() -> Option<u64> {
    // SAFETY: `sysconf` reads a system constant; it has no preconditions
    // and returns -1 for a name it doesn't know.
    let (pages, size) = unsafe {
        (
            libc::sysconf(libc::_SC_PHYS_PAGES),
            libc::sysconf(libc::_SC_PAGESIZE),
        )
    };
    (pages > 0 && size > 0).then(|| pages as u64 * size as u64)
}

#[cfg(not(unix))]
fn physical_memory() -> Option<u64> {
    None
}

/// A hook for the tests of the panic path (SW-4726): the next job of the
/// given worker, in a fill of the project of the given name, panics. Always
/// compiled, since integration tests link the library without `cfg(test)`
/// and the verifier builds in release; it can't be set from outside the
/// process (no environment variable), and a fill of any other project name
/// never reads it as set.
pub mod panic_hook {
    use std::sync::Mutex;

    /// (project, worker, whether it has fired).
    static HOOK: Mutex<Option<(String, usize, bool)>> = Mutex::new(None);

    /// Makes `worker`'s next job in a fill of `project` panic.
    pub fn arm(project: &str, worker: usize) {
        *HOOK.lock().unwrap_or_else(|e| e.into_inner()) =
            Some((project.to_string(), worker, false));
    }

    /// Whether the armed panic happened, and disarms.
    pub fn take_fired() -> bool {
        let hook = HOOK.lock().unwrap_or_else(|e| e.into_inner()).take();
        hook.is_some_and(|(_, _, fired)| fired)
    }

    pub(super) fn maybe_panic(project: &str, worker: usize) {
        let mut hook = HOOK.lock().unwrap_or_else(|e| e.into_inner());
        if let Some((p, w, fired)) = hook.as_mut()
            && p == project
            && *w == worker
            && !*fired
        {
            *fired = true;
            drop(hook);
            panic!("panic hook: worker {worker} of {project}");
        }
    }
}

/// A hook for the test of the mismatch rule: in a fill of the project of
/// the given name, the given namespace's two digests are taken to differ,
/// as they would if the deferral rule or the digest had a bug. Compiled
/// and keyed as [`panic_hook`] is.
pub mod mismatch_hook {
    use std::sync::Mutex;

    /// (project, namespace).
    static HOOK: Mutex<Option<(String, String)>> = Mutex::new(None);

    /// Makes `namespace`'s digests differ in fills of `project`, until
    /// [`disarm`].
    pub fn arm(project: &str, namespace: &str) {
        *HOOK.lock().unwrap_or_else(|e| e.into_inner()) =
            Some((project.to_string(), namespace.to_string()));
    }

    pub fn disarm() {
        *HOOK.lock().unwrap_or_else(|e| e.into_inner()) = None;
    }

    pub(super) fn armed(project: &str, namespace: &str) -> bool {
        let hook = HOOK.lock().unwrap_or_else(|e| e.into_inner());
        hook.as_ref()
            .is_some_and(|(p, n)| p == project && n == namespace)
    }
}

/// What a fill did.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Fill {
    /// Whether any worker started: not when fewer than two namespaces
    /// lacked an entry, or the project couldn't be read.
    pub ran: bool,
    /// The workers that ran.
    pub workers: usize,
    /// Namespaces that had an entry before the fill.
    pub found: usize,
    /// Namespaces given an entry by the fill: checked or replayed by the
    /// worker given them.
    pub filled: usize,
    /// Namespaces left to the check after the fill: with no entry, or with
    /// one it can't find, since something below has none.
    pub left: usize,
    /// Dependencies a worker had to elaborate, finding no entry it could
    /// replay: never expected, since a job is given out only once what its
    /// namespace uses has an entry or an interface entry.
    pub twice: usize,
    /// Namespaces whose proof job's interface digest wasn't their interface
    /// pass's: never expected (each costs checking what is above it again).
    pub mismatches: usize,
    /// Proof jobs of a namespace the worker held the interface of, which it
    /// rewound to before; and the namespaces those rewinds dropped.
    pub rewinds: usize,
    pub rewound: usize,
    /// Proof jobs checked in a session holding a theorem whose proof hadn't
    /// been checked (from an interface): the ones stage 3 started early.
    pub against_promises: usize,
    /// The workers' cache counts, added up: `interface_passes`,
    /// `interface_made`, `deferred` and `interface_hits` say what the
    /// interface jobs did.
    pub stats: Stats,
    /// Waits for another worker's library file that ran out of patience.
    pub claims_gave_up: u64,
    /// Panics in workers other than the first, each of which stopped the
    /// fill and left the rest to the check after it: right answer, one
    /// job's speed, so only this count shows it (worker 0's panic is
    /// raised instead). Never expected.
    pub panics: usize,
}

impl Fill {
    /// How the check after the fill should load what a command asked to
    /// `load`: with nothing left out unloaded if the fill left a
    /// namespace. A left namespace may fail, and one that fails after a
    /// namespace left out unloaded makes the check start again with
    /// everything loaded, which would check it a third time (once in the
    /// fill, twice after); loading everything from the start checks it once
    /// after the fill. What is reported is the same either way.
    pub fn load_after(&self, load: Load) -> Load {
        if self.left > 0 {
            Load::Everything
        } else {
            load
        }
    }
}

/// How long a worker waits for a library file another is elaborating
/// before elaborating it itself (a belt: the claims can't deadlock).
const CLAIM_PATIENCE: Duration = Duration::from_secs(60);

/// A namespace's proof job: stage 1's job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Status {
    Waiting,
    Running,
    /// It has an entry.
    Done,
    Left,
}

/// A namespace's interface job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Interface {
    /// None to run: nothing in the fill waits for it, it has nothing to
    /// defer, its proof job finished first, or it was left.
    Unwanted,
    Waiting,
    Running,
    /// Its interface entry is in the run's memory.
    Made,
    /// It made no entry, and had no error: what uses it waits for its
    /// proof job.
    Missing,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Job {
    Interface(usize),
    Proof(usize),
}

/// What a job ended with.
enum Outcome {
    /// Whether it wrote (or found) the namespace's entry, and the interface
    /// digest the session then has for it.
    Proof { written: bool, digest: Option<Key> },
    /// The interface entry's digest, if it made one; whether the pass had
    /// an error or a goal.
    Interface { digest: Option<Key>, broken: bool },
}

/// The namespaces of a fill, by their position in canonical order.
struct Graph {
    names: Vec<String>,
    /// The ones each uses directly.
    uses: Vec<Vec<usize>>,
    /// The ones each uses directly or not, in canonical order.
    closure: Vec<Vec<usize>>,
    /// The longest chain of namespaces above each, itself included.
    height: Vec<usize>,
}

impl Graph {
    fn new(analysis: &Analysis, order: &[String]) -> Graph {
        let index = |name: &str| order.iter().position(|n| n == name);
        let uses: Vec<Vec<usize>> = order
            .iter()
            .map(|name| {
                let ns = analysis.namespace(name).expect("a namespace");
                let mut uses: Vec<usize> = (ns.edges.iter())
                    .filter(|e| e.target != *name)
                    .filter_map(|e| index(&e.target))
                    .collect();
                uses.sort_unstable();
                uses.dedup();
                uses
            })
            .collect();
        let closure = order
            .iter()
            .map(|name| {
                (dependencies(analysis, name).iter())
                    .filter_map(|n| index(n))
                    .collect()
            })
            .collect();
        // Canonical order puts what a namespace uses before it, so the
        // namespaces above one come after it.
        let mut height = vec![1; order.len()];
        for i in (0..order.len()).rev() {
            for &used in &uses[i] {
                height[used] = height[used].max(height[i] + 1);
            }
        }
        Graph {
            names: order.to_vec(),
            uses,
            closure,
            height,
        }
    }

    /// Whether `j` uses `i`, directly or not.
    fn above(&self, j: usize, i: usize) -> bool {
        self.closure[j].binary_search(&i).is_ok()
    }
}

/// The scheduler's state, behind one lock.
struct Board {
    status: Vec<Status>,
    interface: Vec<Interface>,
    /// The digest each namespace's interface entry claimed, and the one its
    /// proof job's entry has.
    claimed: Vec<Option<Key>>,
    proved: Vec<Option<Key>>,
    /// Namespaces whose digests differed.
    mismatched: Vec<bool>,
    /// What each worker's session holds, in the order it loaded them.
    held: Vec<Vec<usize>>,
    running: usize,
    stopped: bool,
    rng: Option<u64>,
}

impl Board {
    /// Whether what uses `i` may be checked against it: it has an entry or
    /// an interface entry.
    fn available(&self, i: usize) -> bool {
        self.status[i] == Status::Done || self.interface[i] == Interface::Made
    }

    fn uses_available(&self, graph: &Graph, i: usize) -> bool {
        graph.uses[i].iter().all(|&u| self.available(u))
    }

    fn draw(&mut self, n: usize) -> Option<usize> {
        let state = self.rng.as_mut()?;
        // xorshift64*: a reproducible schedule per seed.
        *state ^= *state >> 12;
        *state ^= *state << 25;
        *state ^= *state >> 27;
        let draw = state.wrapping_mul(0x2545_f491_4f6c_dd1d);
        Some((draw % n as u64) as usize)
    }

    fn pick(&mut self, graph: &Graph, worker: usize) -> Option<Job> {
        let n = graph.names.len();
        let held = &self.held[worker];
        let mut mask = vec![false; n];
        for &h in held {
            mask[h] = true;
        }
        let holds = |i: usize| mask[i];
        let interfaces: Vec<usize> = (0..n)
            .filter(|&i| {
                self.interface[i] == Interface::Waiting
                    && self.status[i] == Status::Waiting
                    && !holds(i)
                    && self.uses_available(graph, i)
            })
            .collect();
        let proofs: Vec<usize> = (0..n)
            .filter(|&i| self.status[i] == Status::Waiting && self.uses_available(graph, i))
            .collect();
        if interfaces.is_empty() && proofs.is_empty() {
            return None;
        }
        if self.rng.is_some() {
            let jobs: Vec<Job> = (interfaces.iter().map(|&i| Job::Interface(i)))
                .chain(proofs.iter().map(|&i| Job::Proof(i)))
                .collect();
            let at = self.draw(jobs.len()).expect("a seed");
            return Some(jobs[at]);
        }
        let have = |i: usize| graph.closure[i].iter().filter(|&&d| holds(d)).count();
        // Rule 1: an interface job, by stage 1's rule.
        if let Some(i) = (interfaces.iter().copied())
            .max_by_key(|&i| (graph.height[i], have(i), std::cmp::Reverse(i)))
        {
            return Some(Job::Interface(i));
        }
        // Rule 2: a proof job the session doesn't hold. One whose dependants
        // wait for its entry (it has no interface) by stage 1's rule, as
        // stage 1 picks every job; then the lowest in canonical order, so
        // that a worker that only proves never holds what it is given.
        let unblocks = |i: usize| self.interface[i] != Interface::Made;
        if let Some(i) = (proofs.iter().copied().filter(|&i| !holds(i))).max_by_key(|&i| {
            let first = unblocks(i);
            (
                first,
                if first { graph.height[i] } else { 0 },
                if first { have(i) } else { 0 },
                std::cmp::Reverse(i),
            )
        }) {
            return Some(Job::Proof(i));
        }
        // Rule 3: the held one nearest the top of the session, which the
        // worker rewinds to before.
        (proofs.iter().copied())
            .max_by_key(|&i| held.iter().position(|&h| h == i))
            .map(Job::Proof)
    }

    /// `i` and everything above it that hasn't been given out are left.
    fn leave(&mut self, graph: &Graph, i: usize) {
        if self.status[i] != Status::Done {
            self.status[i] = Status::Left;
        }
        if self.interface[i] == Interface::Waiting {
            self.interface[i] = Interface::Unwanted;
        }
        self.leave_above(graph, i);
    }

    /// Nothing above `i` that hasn't been given out is: those jobs are left
    /// to the check after the fill. What is running finishes.
    fn leave_above(&mut self, graph: &Graph, i: usize) {
        for j in i + 1..graph.names.len() {
            if !graph.above(j, i) {
                continue;
            }
            if self.status[j] == Status::Waiting {
                self.status[j] = Status::Left;
            }
            if self.interface[j] == Interface::Waiting {
                self.interface[j] = Interface::Unwanted;
            }
        }
    }

    /// The two digests of `i`, once both are known: unequal is a mismatch,
    /// and what is above `i` was checked against an interface its whole
    /// entry doesn't have.
    fn compare(&mut self, graph: &Graph, project: &str, i: usize) {
        let (Some(claimed), Some(proved)) = (self.claimed[i], self.proved[i]) else {
            return;
        };
        if claimed == proved && !mismatch_hook::armed(project, &graph.names[i]) {
            return;
        }
        if std::env::var_os("STITCHWORT_CACHE_DEBUG").is_some() {
            eprintln!(
                "check cache: {}: its interface pass's digest isn't its proof job's",
                graph.names[i]
            );
        }
        self.mismatched[i] = true;
        self.leave_above(graph, i);
    }

    /// Namespaces the check after the fill has no usable entry for: left,
    /// or with an entry keyed by something below that is left or whose
    /// digests differed.
    fn left(&self, graph: &Graph) -> usize {
        let unsound = |d: usize| self.status[d] == Status::Left || self.mismatched[d];
        (0..graph.names.len())
            .filter(|&j| {
                self.status[j] == Status::Left
                    || (self.status[j] == Status::Done
                        && graph.closure[j].iter().any(|&d| unsound(d)))
            })
            .count()
    }
}

/// A worker's own counts.
#[derive(Default)]
struct Tally {
    filled: usize,
    twice: usize,
    rewinds: usize,
    rewound: usize,
    against_promises: usize,
    stats: Stats,
    /// Panics the worker caught (at most one: it stops after it).
    panics: usize,
    /// The panic the worker caught, which stopped the fill.
    panic: Option<Box<dyn std::any::Any + Send>>,
}

/// Fills the check cache for checking `target` of the project in `files`
/// (`project` is its name for display) with `jobs.count` workers. Call it
/// on a thread with `jobs.stack` bytes of stack, before the check that
/// reports, which then finds the entries. With one job, or with fewer than
/// two namespaces lacking an entry, it does nothing.
pub fn fill(files: &(dyn Files + Sync), project: &str, target: &Target, jobs: &Jobs) -> Fill {
    let _end = EndWatch(jobs.watch);
    let stop = jobs.cancel.clone().unwrap_or_default();
    if jobs.count < 2 || matches!(target, Target::Theorems { .. }) || stop.load(Ordering::Relaxed) {
        return Fill::default();
    }
    // Read once, so every worker sees the same text.
    let Ok(config) = files.read(CONFIG) else {
        return Fill::default();
    };
    let Ok(texts) = project_sources(files, project, &mut SourceMap::new()) else {
        return Fill::default();
    };
    let read = Read {
        files,
        project,
        config: &config,
        texts: &texts,
    };
    let claims = Arc::new(Claims::new(CLAIM_PATIENCE));
    let interfaces = Arc::new(Interfaces::default());
    // Worker 0 is the caller's thread, whose session also plans the fill.
    let Some(mut first) = Worker::new(0, &read, jobs, &claims, &interfaces) else {
        return Fill::default();
    };
    let Ok(prepared) = first
        .session
        .prepare_analysis(project, &first.analysis, target)
    else {
        return Fill::default();
    };
    let order = prepared.order;
    let graph = Graph::new(&first.analysis, &order);
    let mut status = vec![Status::Waiting; order.len()];
    let mut board_left = Vec::new();
    for (i, name) in order.iter().enumerate() {
        let ns = first.analysis.namespace(name).expect("a namespace");
        if !ns.parse_errors.is_empty() {
            board_left.push(i);
            continue;
        }
        let deps: Vec<String> = graph.closure[i].iter().map(|&d| order[d].clone()).collect();
        if first.session.elab.plan_namespace(name, &deps).is_some() {
            status[i] = Status::Done;
        }
    }
    // An interface job for a namespace something waits on, and whose
    // interface pass would leave a proof out: otherwise it would be its
    // whole check, and its entry serves.
    let interface = (0..order.len())
        .map(|i| {
            let wanted = jobs.statements_first
                && status[i] == Status::Waiting
                && (0..order.len())
                    .any(|j| status[j] == Status::Waiting && graph.uses[j].contains(&i))
                && (first
                    .analysis
                    .namespace(&order[i])
                    .expect("a namespace")
                    .modules
                    .iter())
                .flat_map(|m| &m.decls)
                .any(may_defer);
            if wanted {
                Interface::Waiting
            } else {
                Interface::Unwanted
            }
        })
        .collect();
    let mut board = Board {
        status,
        interface,
        claimed: vec![None; order.len()],
        proved: vec![None; order.len()],
        mismatched: vec![false; order.len()],
        held: vec![Vec::new(); jobs.count],
        running: 0,
        stopped: false,
        rng: jobs
            .seed
            .map(|seed| seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1),
    };
    for i in board_left {
        board.leave(&graph, i);
    }
    let found = board.status.iter().filter(|s| **s == Status::Done).count();
    let lacking = board
        .status
        .iter()
        .filter(|s| **s == Status::Waiting)
        .count();
    if lacking < 2 {
        first.release(jobs);
        return Fill::default();
    }
    let workers = jobs.count.min(lacking);
    board.held.truncate(workers);
    let board = Mutex::new(board);
    let changed = Condvar::new();
    let shared = Shared {
        project,
        graph: &graph,
        board: &board,
        changed: &changed,
        stop: &stop,
        watch: jobs.watch,
    };
    shared.tell_watch(&shared.board());
    let mut tallies: Vec<Tally> = std::thread::scope(|scope| {
        let handles: Vec<_> = (1..workers)
            .map(|w| {
                let (shared, claims, read, interfaces) = (&shared, &claims, &read, &interfaces);
                std::thread::Builder::new()
                    .stack_size(jobs.stack)
                    .spawn_scoped(scope, move || {
                        // Worker 0 read the same texts, so this can't fail
                        // where it didn't; if it does, the others carry on.
                        let Some(mut worker) = Worker::new(w, read, jobs, claims, interfaces)
                        else {
                            return Tally::default();
                        };
                        let analysis = &worker.analysis;
                        if worker
                            .session
                            .prepare_analysis(project, analysis, target)
                            .is_err()
                        {
                            worker.release(jobs);
                            return Tally::default();
                        }
                        worker.run(shared, jobs)
                    })
                    .expect("can't start a thread")
            })
            .collect();
        let mut tallies = vec![first.run(&shared, jobs)];
        tallies.extend(handles.into_iter().map(|h| {
            h.join().unwrap_or_else(|_| Tally {
                panics: 1,
                ..Tally::default()
            })
        }));
        tallies
    });
    // Worker 0 is the caller's thread, which the check after the fill runs
    // on: a panic there may have left its thread-local state half-changed,
    // so the run fails as one job meeting the panic would, rather than
    // checking on over that state.
    if let Some(panic) = tallies.first_mut().and_then(|t| t.panic.take()) {
        std::panic::resume_unwind(panic);
    }
    let board = board.into_inner().unwrap_or_else(|e| e.into_inner());
    let mut fill = Fill {
        ran: true,
        workers,
        found,
        left: board.left(&graph),
        mismatches: board.mismatched.iter().filter(|m| **m).count(),
        claims_gave_up: claims.gave_up(),
        ..Fill::default()
    };
    for tally in tallies {
        fill.filled += tally.filled;
        fill.twice += tally.twice;
        fill.rewinds += tally.rewinds;
        fill.rewound += tally.rewound;
        fill.against_promises += tally.against_promises;
        fill.panics += tally.panics;
        add_stats(&mut fill.stats, &tally.stats);
    }
    fill
}

/// The project as read once, before the workers start.
struct Read<'a> {
    files: &'a (dyn Files + Sync),
    project: &'a str,
    /// The text of `stitchwort.yaml`.
    config: &'a str,
    /// (path within the project, text) of its `.sw` files.
    texts: &'a [(String, String)],
}

/// What the workers share.
struct Shared<'a> {
    project: &'a str,
    graph: &'a Graph,
    board: &'a Mutex<Board>,
    changed: &'a Condvar,
    stop: &'a Arc<AtomicBool>,
    watch: Option<&'a Watch>,
}

/// How often a worker waiting for a job looks at the stop flag, which can
/// be set from outside the fill ([`Jobs::cancel`]) without waking it.
const STOP_POLL: Duration = Duration::from_millis(50);

impl Shared<'_> {
    fn board(&self) -> std::sync::MutexGuard<'_, Board> {
        self.board.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Tells the watch, if any, which namespaces may still be written.
    fn tell_watch(&self, board: &Board) {
        if let Some(watch) = self.watch {
            let pending = (board.status.iter().zip(&self.graph.names))
                .filter(|(s, _)| matches!(s, Status::Waiting | Status::Running))
                .map(|(_, name)| name.clone())
                .collect();
            watch.update(pending);
        }
    }

    /// Stops the fill: no more jobs are given out, and the namespaces being
    /// checked are cancelled (and so not written).
    fn halt(&self) {
        self.stop.store(true, Ordering::Relaxed);
        self.board().stopped = true;
        self.changed.notify_all();
    }

    /// The next job for `worker`, waiting while others run; `None` when
    /// nothing more can be filled.
    fn next(&self, worker: usize) -> Option<Job> {
        let mut board = self.board();
        loop {
            if board.stopped || self.stop.load(Ordering::Relaxed) {
                return None;
            }
            if let Some(job) = board.pick(self.graph, worker) {
                match job {
                    Job::Interface(i) => board.interface[i] = Interface::Running,
                    Job::Proof(i) => board.status[i] = Status::Running,
                }
                board.running += 1;
                return Some(job);
            }
            if board.running == 0 {
                drop(board);
                self.changed.notify_all();
                return None;
            }
            board = (self.changed.wait_timeout(board, STOP_POLL))
                .unwrap_or_else(|e| e.into_inner())
                .0;
        }
    }

    /// `job` ended with `outcome`; the worker's session now holds `held`,
    /// in the order it loaded them.
    fn finish(&self, worker: usize, job: Job, outcome: Outcome, held: Vec<usize>) {
        let mut board = self.board();
        board.running -= 1;
        board.held[worker] = held;
        match (job, outcome) {
            (Job::Proof(i), Outcome::Proof { written, digest }) => {
                if written {
                    board.status[i] = Status::Done;
                    board.proved[i] = digest;
                    if board.interface[i] == Interface::Waiting {
                        board.interface[i] = Interface::Unwanted;
                    }
                    board.compare(self.graph, self.project, i);
                } else {
                    board.leave(self.graph, i);
                }
            }
            (Job::Interface(i), Outcome::Interface { digest, broken }) => {
                if let Some(digest) = digest {
                    board.interface[i] = Interface::Made;
                    board.claimed[i] = Some(digest);
                    board.compare(self.graph, self.project, i);
                } else if broken {
                    // An error in a definition or a statement: the proof
                    // job would fail too.
                    board.interface[i] = Interface::Missing;
                    board.leave(self.graph, i);
                } else {
                    board.interface[i] = Interface::Missing;
                }
            }
            _ => unreachable!("an outcome of the other kind of job"),
        }
        self.tell_watch(&board);
        drop(board);
        self.changed.notify_all();
    }
}

/// The interface entries of one fill, by unit and key: in memory, for the
/// run, read only through the workers' [`WorkerStore`]s (stage 3 §3,
/// decision C: never written to disk).
#[derive(Default)]
struct Interfaces(Mutex<InterfaceEntries>);

/// Each interface entry's bytes, by unit and key.
type InterfaceEntries = BTreeMap<(String, Key), Arc<[u8]>>;

impl Interfaces {
    fn entries(&self) -> std::sync::MutexGuard<'_, InterfaceEntries> {
        self.0.lock().unwrap_or_else(|e| e.into_inner())
    }
}

/// A worker's store: its [`ClaimStore`], and the fill's interface entries,
/// which this is the only store to serve ([`Store::read_interface`]). Only
/// [`fill`] makes one, so only a worker's session can load an interface
/// entry; the check after the fill uses the store without it.
struct WorkerStore {
    claims: Rc<ClaimStore>,
    interfaces: Arc<Interfaces>,
    /// Off while a proof job checks its own namespace, which must be
    /// checked whole, never loaded from its interface entry.
    serve: Cell<bool>,
}

impl Store for WorkerStore {
    fn compiler(&self) -> &str {
        self.claims.compiler()
    }

    fn kernel(&self) -> &str {
        self.claims.kernel()
    }

    fn salt(&self) -> [u8; 16] {
        self.claims.salt()
    }

    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        self.claims.read(unit, key)
    }

    fn read_others(&self, unit: &str, key: &Key) -> Vec<Vec<u8>> {
        self.claims.read_others(unit, key)
    }

    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        self.claims.write(unit, key, entry)
    }

    fn abandon(&self, unit: &str, key: &Key) {
        self.claims.abandon(unit, key)
    }

    fn read_interface(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        if !self.serve.get() {
            return None;
        }
        (self.interfaces.entries())
            .get(&(unit.to_string(), *key))
            .map(|bytes| bytes.to_vec())
    }
}

struct Worker {
    id: usize,
    project: String,
    session: Session,
    analysis: Analysis,
    claims: Rc<ClaimStore>,
    store: Rc<WorkerStore>,
    /// What the session holds, by position in canonical order.
    loaded: Vec<bool>,
    /// Of those, the ones it holds as an interface (its own interface pass,
    /// or an interface entry), whose theorems' proofs may not be checked.
    promised: Vec<bool>,
    /// What the session holds, in the order loaded, each with the mark
    /// taken before it was loaded (with interface jobs), to rewind to.
    stack: Vec<(usize, Option<Mark>)>,
    /// Whether marks are kept: only with interface jobs, the only way a
    /// worker comes to hold a namespace it must then check whole.
    keep_marks: bool,
}

impl Worker {
    /// A worker's session, with the project's files analysed in it as the
    /// check after the fill will analyse them.
    fn new(
        id: usize,
        read: &Read,
        jobs: &Jobs,
        claims: &Arc<Claims>,
        interfaces: &Arc<Interfaces>,
    ) -> Option<Worker> {
        let mut session = (jobs.make_session)(jobs.stack);
        let claim_store = Rc::new(ClaimStore::new((jobs.make_store)(), claims.clone(), id));
        let store = Rc::new(WorkerStore {
            claims: claim_store.clone(),
            interfaces: interfaces.clone(),
            serve: Cell::new(true),
        });
        session.elab.set_check_cache(store.clone());
        // Nothing a worker writes depends on a proof below it (§10.3), and
        // what is reported comes from the check after the fill, which loads
        // them.
        session.elab.set_load_without_proofs(true);
        if let Some(include) = read.files.include_files() {
            session.include_from(include);
        }
        // As `project_sources` adds it: the namespaces' keys hash its text.
        let display = format!("{}/{CONFIG}", read.project);
        (read.files)
            .config(read.config, &display, &mut session.sources)
            .ok()?;
        let analysis = analyse(&mut session, read.project, read.texts.to_vec());
        if !analysis.diagnostics.is_empty() {
            return None;
        }
        Some(Worker {
            id,
            project: read.project.to_string(),
            session,
            analysis,
            claims: claim_store,
            store,
            loaded: Vec::new(),
            promised: Vec::new(),
            stack: Vec::new(),
            keep_marks: jobs.statements_first,
        })
    }

    /// Frees the worker's session if `jobs` says so, else leaves it.
    fn release(self, jobs: &Jobs) {
        if jobs.free_sessions {
            drop(self);
        } else {
            std::mem::forget(self);
        }
    }

    fn run(mut self, shared: &Shared, jobs: &Jobs) -> Tally {
        let mut tally = Tally::default();
        self.loaded = vec![false; shared.graph.names.len()];
        self.promised = vec![false; shared.graph.names.len()];
        self.session.share_cancel_flag(shared.stop.clone());
        let budget = &self.session.elab.kernel.machine.budget;
        budget.watch_cancel(true);
        while let Some(job) = shared.next(self.id) {
            let ran = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                self.claims.begin_job();
                panic_hook::maybe_panic(&self.project, self.id);
                let outcome = match job {
                    Job::Interface(i) => self.interface(shared.graph, i, &mut tally),
                    Job::Proof(i) => self.prove(shared.graph, i, &mut tally),
                };
                self.claims.end_job();
                outcome
            }));
            match ran {
                Ok(outcome) => {
                    if let Outcome::Proof { written: true, .. } = outcome {
                        tally.filled += 1;
                    }
                    shared.finish(self.id, job, outcome, self.held());
                }
                Err(panic) => {
                    // On a worker thread, the check after the fill meets
                    // the same panic and reports it; worker 0's is raised
                    // again once the others stop (`fill`).
                    tally.panics += 1;
                    tally.panic = Some(panic);
                    self.claims.end_job();
                    let failed = match job {
                        Job::Interface(_) => Outcome::Interface {
                            digest: None,
                            broken: true,
                        },
                        Job::Proof(_) => Outcome::Proof {
                            written: false,
                            digest: None,
                        },
                    };
                    shared.finish(self.id, job, failed, Vec::new());
                    shared.halt();
                    break;
                }
            }
        }
        self.session.elab.kernel.machine.budget.watch_cancel(false);
        tally.stats = self.session.elab.check_cache_stats();
        self.release(jobs);
        tally
    }

    fn held(&self) -> Vec<usize> {
        self.stack.iter().map(|(d, _)| *d).collect()
    }

    /// Loads what namespace `i` uses that the session lacks: each from its
    /// entry, or, lacking one, its interface entry.
    fn load_closure(&mut self, graph: &Graph, i: usize, tally: &mut Tally) {
        stitchwort_elab::timings::loading(Some(self.id));
        for &d in &graph.closure[i] {
            if self.loaded[d] {
                continue;
            }
            let ns = self
                .analysis
                .namespace(&graph.names[d])
                .expect("a namespace");
            let mark = self.keep_marks.then(|| self.session.mark());
            let before = self.session.elab.check_cache_stats();
            let _ = self.session.check_project_namespace(&self.analysis, ns);
            let after = self.session.elab.check_cache_stats();
            if after.namespace_misses > before.namespace_misses {
                tally.twice += 1;
            }
            self.promised[d] = after.interface_hits > before.interface_hits;
            self.loaded[d] = true;
            self.stack.push((d, mark));
        }
        stitchwort_elab::timings::loading(None);
    }

    /// Rewinds the session to before namespace `i`, which it holds: `i` and
    /// everything loaded after it are gone.
    fn unload_from(&mut self, i: usize, tally: &mut Tally) {
        let at = (self.stack.iter())
            .position(|(d, _)| *d == i)
            .expect("the namespace is held");
        let dropped = self.stack.split_off(at);
        tally.rewinds += 1;
        tally.rewound += dropped.len();
        for (d, _) in &dropped {
            self.loaded[*d] = false;
            self.promised[*d] = false;
        }
        // Rewinding to the oldest lets go of those after it.
        let (_, mark) = dropped.into_iter().next().expect("one at least");
        let mark = mark.expect("a held interface has a mark (interface jobs keep them)");
        self.session.rewind(&mark);
        self.session.release(mark);
    }

    /// Checks namespace `i` as an interface pass, its closure loaded first;
    /// keeps it if that makes an interface entry, which it publishes.
    fn interface(&mut self, graph: &Graph, i: usize, tally: &mut Tally) -> Outcome {
        assert!(!self.loaded[i], "an interface job for a namespace held");
        self.load_closure(graph, i, tally);
        let name = &graph.names[i];
        let ns = self.analysis.namespace(name).expect("a namespace");
        let mark = self.session.mark();
        self.session.elab.set_interface_pass(Some(name));
        let (found, _) = self.session.check_project_namespace(&self.analysis, ns);
        self.session.elab.set_interface_pass(None);
        match self.session.elab.take_interface_entry() {
            Some(entry) => {
                (self.store.interfaces.entries())
                    .insert((entry.unit, entry.key), Arc::from(entry.bytes));
                self.loaded[i] = true;
                self.promised[i] = true;
                self.stack.push((i, Some(mark)));
                Outcome::Interface {
                    digest: Some(entry.digest),
                    broken: false,
                }
            }
            None => {
                self.session.rewind(&mark);
                self.session.release(mark);
                let broken =
                    (found.iter()).any(|d| matches!(d.severity, Severity::Error | Severity::Goal));
                Outcome::Interface {
                    digest: None,
                    broken,
                }
            }
        }
    }

    /// Checks namespace `i` whole, its closure loaded first (rewinding to
    /// before `i` if the session holds its interface); whether `i` now has
    /// an entry, and the digest the session has for it.
    fn prove(&mut self, graph: &Graph, i: usize, tally: &mut Tally) -> Outcome {
        if self.loaded[i] {
            self.unload_from(i, tally);
        }
        self.load_closure(graph, i, tally);
        if graph.closure[i].iter().any(|&d| self.promised[d]) {
            tally.against_promises += 1;
        }
        let name = &graph.names[i];
        let ns = self.analysis.namespace(name).expect("a namespace");
        let mark = self.session.mark();
        let before = self.session.elab.check_cache_stats();
        self.store.serve.set(false);
        let _ = self.session.check_project_namespace(&self.analysis, ns);
        self.store.serve.set(true);
        let after = self.session.elab.check_cache_stats();
        let written = after.namespace_written > before.namespace_written
            || after.namespace_hits > before.namespace_hits;
        let digest = written
            .then(|| self.session.elab.namespace_digest(name))
            .flatten();
        if written {
            self.loaded[i] = true;
            self.promised[i] = false;
            if self.keep_marks {
                self.stack.push((i, Some(mark)));
            } else {
                self.session.release(mark);
                self.stack.push((i, None));
            }
        } else {
            self.session.rewind(&mark);
            self.session.release(mark);
        }
        Outcome::Proof { written, digest }
    }
}

fn add_stats(sum: &mut Stats, s: &Stats) {
    sum.hits += s.hits;
    sum.misses += s.misses;
    sum.written += s.written;
    sum.uncacheable += s.uncacheable;
    sum.namespace_hits += s.namespace_hits;
    sum.namespace_misses += s.namespace_misses;
    sum.namespace_written += s.namespace_written;
    sum.namespace_uncacheable += s.namespace_uncacheable;
    sum.namespace_waiting_on_error += s.namespace_waiting_on_error;
    sum.late_misses += s.late_misses;
    sum.refused += s.refused;
    sum.digest_mismatches += s.digest_mismatches;
    sum.stated += s.stated;
    sum.interface_passes += s.interface_passes;
    sum.interface_made += s.interface_made;
    sum.deferred += s.deferred;
    sum.interface_hits += s.interface_hits;
    sum.unproved += s.unproved;
}
