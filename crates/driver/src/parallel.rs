//! `check --jobs N` (docs/proposals/parallel-checking.md §9): a parallel
//! fill of the check cache, after which the ordinary sequential check runs
//! over the same store and reports.
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
//! - **What a worker holds.** Its session keeps every namespace it loaded,
//!   for the whole run, so it loads each at most once. A namespace it
//!   checked without writing an entry is rewound away, so no later job runs
//!   beside a failed namespace.
//! - **Ready, and left.** A namespace is ready when every namespace it uses
//!   has an entry (found before the fill, or written in it). It is left to
//!   the check after the fill if it has a syntax error, or a worker checked
//!   it and wrote nothing, or it uses one that is left. The rest of the
//!   graph is still filled.
//! - **Which first.** The ready namespace with the longest chain of
//!   namespaces above it, then the one the worker holds most of the
//!   closure of, then the first in canonical order; or, given a seed, a
//!   random one, for the test that the order doesn't change an entry.
//! - **Library files** are claimed ([`ClaimStore`]) so two workers don't
//!   elaborate the same one.
//! - **A panic** in a worker stops the fill (a shared flag, also each
//!   worker's cancellation flag); the check after it meets the same
//!   problem on the caller's thread and reports it as without `--jobs`.

use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

use stitchwort_elab::cache::{Stats, Store};
use stitchwort_syntax::SourceMap;

use crate::check_cache::{ClaimStore, Claims};
use crate::driver::Session;
use crate::project::{
    Analysis, CONFIG, Files, Load, Target, analyse, dependencies, project_sources,
};

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
    /// Pick ready namespaces at random, from this seed
    /// (`STITCHWORT_JOBS_SEED`), rather than by the rule above.
    pub seed: Option<u64>,
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
    /// Namespaces left to the check after the fill.
    pub left: usize,
    /// Dependencies a worker had to elaborate, finding no entry it could
    /// replay: never expected, since a namespace is given out only once
    /// what it uses has an entry.
    pub twice: usize,
    /// The workers' cache counts, added up.
    pub stats: Stats,
    /// Waits for another worker's library file that ran out of patience.
    pub claims_gave_up: u64,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Status {
    Waiting,
    Running,
    /// It has an entry.
    Done,
    Left,
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
}

/// The scheduler's state, behind one lock.
struct Board {
    status: Vec<Status>,
    /// What each worker's session holds.
    held: Vec<Vec<bool>>,
    running: usize,
    stopped: bool,
    rng: Option<u64>,
}

impl Board {
    fn ready(&self, graph: &Graph, i: usize) -> bool {
        self.status[i] == Status::Waiting
            && graph.uses[i]
                .iter()
                .all(|&u| self.status[u] == Status::Done)
    }

    fn pick(&mut self, graph: &Graph, worker: usize) -> Option<usize> {
        let ready: Vec<usize> = (0..graph.names.len())
            .filter(|&i| self.ready(graph, i))
            .collect();
        if ready.is_empty() {
            return None;
        }
        if let Some(state) = &mut self.rng {
            // xorshift64*: a reproducible schedule per seed.
            *state ^= *state >> 12;
            *state ^= *state << 25;
            *state ^= *state >> 27;
            let draw = state.wrapping_mul(0x2545_f491_4f6c_dd1d);
            return Some(ready[(draw % ready.len() as u64) as usize]);
        }
        let held = &self.held[worker];
        ready.into_iter().max_by_key(|&i| {
            let have = graph.closure[i].iter().filter(|&&d| held[d]).count();
            (graph.height[i], have, std::cmp::Reverse(i))
        })
    }

    /// `i` and everything above it that hasn't been given out are left.
    fn leave(&mut self, graph: &Graph, i: usize) {
        self.status[i] = Status::Left;
        for j in i + 1..graph.names.len() {
            if self.status[j] == Status::Waiting
                && graph.closure[j]
                    .iter()
                    .any(|&d| self.status[d] == Status::Left)
            {
                self.status[j] = Status::Left;
            }
        }
    }
}

/// A worker's own counts.
#[derive(Default)]
struct Tally {
    filled: usize,
    twice: usize,
    stats: Stats,
    /// The panic the worker caught, which stopped the fill.
    panic: Option<Box<dyn std::any::Any + Send>>,
}

/// Fills the check cache for checking `target` of the project in `files`
/// (`project` is its name for display) with `jobs.count` workers. Call it
/// on a thread with `jobs.stack` bytes of stack, before the check that
/// reports, which then finds the entries. With one job, or with fewer than
/// two namespaces lacking an entry, it does nothing.
pub fn fill(files: &(dyn Files + Sync), project: &str, target: &Target, jobs: &Jobs) -> Fill {
    if jobs.count < 2 || matches!(target, Target::Theorems { .. }) {
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
    // Worker 0 is the caller's thread, whose session also plans the fill.
    let Some(mut first) = Worker::new(0, &read, jobs, &claims) else {
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
    let mut board = Board {
        status,
        held: vec![vec![false; order.len()]; jobs.count],
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
        std::mem::forget(first);
        return Fill::default();
    }
    let workers = jobs.count.min(lacking);
    board.held.truncate(workers);
    let board = Mutex::new(board);
    let changed = Condvar::new();
    let stop = Arc::new(AtomicBool::new(false));
    let shared = Shared {
        graph: &graph,
        board: &board,
        changed: &changed,
        stop: &stop,
    };
    let mut tallies: Vec<Tally> = std::thread::scope(|scope| {
        let handles: Vec<_> = (1..workers)
            .map(|w| {
                let (shared, claims, read) = (&shared, &claims, &read);
                std::thread::Builder::new()
                    .stack_size(jobs.stack)
                    .spawn_scoped(scope, move || {
                        // Worker 0 read the same texts, so this can't fail
                        // where it didn't; if it does, the others carry on.
                        let Some(mut worker) = Worker::new(w, read, jobs, claims) else {
                            return Tally::default();
                        };
                        let analysis = &worker.analysis;
                        if worker
                            .session
                            .prepare_analysis(project, analysis, target)
                            .is_err()
                        {
                            std::mem::forget(worker);
                            return Tally::default();
                        }
                        worker.run(shared)
                    })
                    .expect("can't start a thread")
            })
            .collect();
        let mut tallies = vec![first.run(&shared)];
        tallies.extend(handles.into_iter().map(|h| h.join().unwrap_or_default()));
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
        left: board.status.iter().filter(|s| **s == Status::Left).count(),
        claims_gave_up: claims.gave_up(),
        ..Fill::default()
    };
    for tally in tallies {
        fill.filled += tally.filled;
        fill.twice += tally.twice;
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
    graph: &'a Graph,
    board: &'a Mutex<Board>,
    changed: &'a Condvar,
    stop: &'a Arc<AtomicBool>,
}

impl Shared<'_> {
    fn board(&self) -> std::sync::MutexGuard<'_, Board> {
        self.board.lock().unwrap_or_else(|e| e.into_inner())
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
    fn next(&self, worker: usize) -> Option<usize> {
        let mut board = self.board();
        loop {
            if board.stopped {
                return None;
            }
            if let Some(i) = board.pick(self.graph, worker) {
                board.status[i] = Status::Running;
                board.running += 1;
                return Some(i);
            }
            if board.running == 0 {
                drop(board);
                self.changed.notify_all();
                return None;
            }
            board = self.changed.wait(board).unwrap_or_else(|e| e.into_inner());
        }
    }

    fn finish(&self, worker: usize, i: usize, written: bool, loaded: &[usize]) {
        let mut board = self.board();
        board.running -= 1;
        for &d in loaded {
            board.held[worker][d] = true;
        }
        if written {
            board.status[i] = Status::Done;
            board.held[worker][i] = true;
        } else {
            board.leave(self.graph, i);
        }
        drop(board);
        self.changed.notify_all();
    }
}

struct Worker {
    id: usize,
    session: Session,
    analysis: Analysis,
    store: Rc<ClaimStore>,
    /// What the session holds, by position in canonical order.
    loaded: Vec<bool>,
}

impl Worker {
    /// A worker's session, with the project's files analysed in it as the
    /// check after the fill will analyse them.
    fn new(id: usize, read: &Read, jobs: &Jobs, claims: &Arc<Claims>) -> Option<Worker> {
        let mut session = (jobs.make_session)(jobs.stack);
        let store = Rc::new(ClaimStore::new((jobs.make_store)(), claims.clone(), id));
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
            session,
            analysis,
            store,
            loaded: Vec::new(),
        })
    }

    fn run(mut self, shared: &Shared) -> Tally {
        let mut tally = Tally::default();
        self.loaded = vec![false; shared.graph.names.len()];
        self.session.share_cancel_flag(shared.stop.clone());
        let budget = &self.session.elab.kernel.machine.budget;
        budget.watch_cancel(true);
        while let Some(i) = shared.next(self.id) {
            let job = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                self.job(shared.graph, i, &mut tally)
            }));
            match job {
                Ok((written, loaded)) => {
                    if written {
                        tally.filled += 1;
                    }
                    shared.finish(self.id, i, written, &loaded);
                }
                Err(panic) => {
                    // On a worker thread, the check after the fill meets
                    // the same panic and reports it; worker 0's is raised
                    // again once the others stop (`fill`).
                    tally.panic = Some(panic);
                    self.store.end_job();
                    shared.finish(self.id, i, false, &[]);
                    shared.halt();
                    break;
                }
            }
        }
        self.session.elab.kernel.machine.budget.watch_cancel(false);
        tally.stats = self.session.elab.check_cache_stats();
        // As the CLI does with its session: freeing it all takes longer
        // than the process has left.
        std::mem::forget(self);
        tally
    }

    /// Loads what namespace `i` uses that the session lacks, then checks
    /// `i`; whether `i` now has an entry, and what was loaded for it.
    fn job(&mut self, graph: &Graph, i: usize, tally: &mut Tally) -> (bool, Vec<usize>) {
        self.store.begin_job();
        let mut loaded = Vec::new();
        stitchwort_elab::timings::loading(Some(self.id));
        for &d in &graph.closure[i] {
            if self.loaded[d] {
                continue;
            }
            let ns = self
                .analysis
                .namespace(&graph.names[d])
                .expect("a namespace");
            let before = self.session.elab.check_cache_stats().namespace_misses;
            let _ = self.session.check_project_namespace(&self.analysis, ns);
            if self.session.elab.check_cache_stats().namespace_misses > before {
                tally.twice += 1;
            }
            self.loaded[d] = true;
            loaded.push(d);
        }
        stitchwort_elab::timings::loading(None);
        let ns = self
            .analysis
            .namespace(&graph.names[i])
            .expect("a namespace");
        let mark = self.session.mark();
        let before = self.session.elab.check_cache_stats();
        let _ = self.session.check_project_namespace(&self.analysis, ns);
        let after = self.session.elab.check_cache_stats();
        let written = after.namespace_written > before.namespace_written
            || after.namespace_hits > before.namespace_hits;
        if written {
            self.session.release(mark);
            self.loaded[i] = true;
        } else {
            self.session.rewind(&mark);
            self.session.release(mark);
        }
        self.store.end_job();
        (written, loaded)
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
}
