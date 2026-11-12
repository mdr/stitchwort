//! Runs source files through the compiler pipeline.

use std::cell::RefCell;
use std::path::PathBuf;
use std::sync::Arc;

use stitchwort_core::collections::HashMap;
use stitchwort_core::hash::ContentHash;
use stitchwort_core::value::{eval, force};
use stitchwort_core::{Limits, ResourceError, Term, Value};
use stitchwort_elab::project::{FileModeContext, SourceUnit};
use stitchwort_elab::shown::{SHOWN_SIDE, SHOWN_SIDE_NODES, cut_to, first_difference, text_lines};
use stitchwort_elab::{Elaborator, LibraryIndex, prelude};
use stitchwort_syntax::ast::Expr;
use stitchwort_syntax::{
    Diagnostic, FileId, Severity, SourceMap, parse_expression_within, parse_module_recovering,
    parse_module_within,
};

/// Which library files a session knows.
#[derive(Clone, Copy)]
enum Library<'a> {
    /// The standard library, `std/`.
    Standard,
    /// None: the core alone.
    None,
    /// These instead, for tests.
    Files(&'a [(&'a str, &'a str)]),
}

/// A compiler session: the prelude plus whatever has been loaded since.
pub struct Session {
    pub sources: SourceMap,
    pub elab: Elaborator,
    /// Warnings from files loaded without errors. (A file with errors
    /// returns its warnings with them.)
    pub warnings: Vec<Diagnostic>,
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

/// Runs `f` on a new thread with `stack` bytes of stack, for a session whose
/// limits are [`Limits::for_stack`] of the same size.
pub fn with_stack<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> T {
    stitchwort_host::with_stack(stack, f)
}

/// Runs `f` on a new thread with `stack` bytes of stack, with a session made
/// there by `make` for that same stack (`Session::for_stack`,
/// `Session::navigable_for_stack` or `Session::eager_for_stack`): the
/// thread and the session's limits come from one number, so they can't
/// disagree. A session told it has more stack than its thread does can't
/// stop with E-RESOURCE before the thread overflows, which aborts the
/// process (docs/testing.md, "Stack").
pub fn with_session<T: Send>(
    stack: usize,
    make: fn(usize) -> Session,
    f: impl FnOnce(&mut Session) -> T + Send,
) -> T {
    with_stack(stack, || f(&mut make(stack)))
}

/// How many worker threads the tests' per-file loops use: the machine's
/// parallelism capped at 8 (each session holds tens of MB), or
/// `STITCHWORT_TEST_THREADS` if set.
#[doc(hidden)]
pub fn test_threads() -> usize {
    std::env::var("STITCHWORT_TEST_THREADS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|n| *n > 0)
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get().min(8)))
}

/// Maps `f` over `items` on up to [`test_threads`] threads, each with `stack`
/// bytes of stack, and returns the results in the order of `items`. A panic
/// in `f` is held until every item has run, then the one for the earliest
/// item is re-raised, so failures are reported deterministically.
#[doc(hidden)]
pub fn par_map<T: Sync, R: Send>(stack: usize, items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    par_map_with(stack, items, || (), |(), item| f(item))
}

/// [`par_map`], where each worker thread first makes its own state with
/// `init` (once, however many items it takes), and `f` gets it with each
/// item: for a sweep that would otherwise build the same expensive thing,
/// such as an eager session, for every item.
#[doc(hidden)]
pub fn par_map_with<S, T: Sync, R: Send>(
    stack: usize,
    items: &[T],
    init: impl Fn() -> S + Sync,
    f: impl Fn(&mut S, &T) -> R + Sync,
) -> Vec<R> {
    par_map_with_at_most(stack, usize::MAX, items, init, f)
}

/// [`par_map_with`] on at most `max_workers` threads: for a sweep whose
/// `init` costs far more than an item (an eager session loads for seconds,
/// a hash snapshot takes milliseconds), where each extra worker repeats the
/// load and the merge tier's other tests already keep every core busy.
#[doc(hidden)]
pub fn par_map_with_at_most<S, T: Sync, R: Send>(
    stack: usize,
    max_workers: usize,
    items: &[T],
    init: impl Fn() -> S + Sync,
    f: impl Fn(&mut S, &T) -> R + Sync,
) -> Vec<R> {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};
    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<Option<std::thread::Result<R>>>> =
        Mutex::new((0..items.len()).map(|_| None).collect());
    let workers = test_threads().min(max_workers).min(items.len()).max(1);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            std::thread::Builder::new()
                .stack_size(stack)
                .spawn_scoped(scope, || {
                    let mut state = None;
                    loop {
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        let Some(item) = items.get(i) else { break };
                        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            f(state.get_or_insert_with(&init), item)
                        }));
                        if r.is_err() {
                            // A panic may leave the state half-updated.
                            state = None;
                        }
                        results.lock().unwrap_or_else(|e| e.into_inner())[i] = Some(r);
                    }
                })
                .expect("can't start a thread");
        }
    });
    results
        .into_inner()
        .unwrap_or_else(|e| e.into_inner())
        .into_iter()
        .map(|r| match r.expect("every item ran") {
            Ok(v) => v,
            Err(panic) => std::panic::resume_unwind(panic),
        })
        .collect()
}

/// The test tier being run (docs/testing.md, "Tiers"): `STITCHWORT_TIER`
/// is `lane`, `merge`, `daily` or `full`; when it is unset, the nextest
/// profile of the same name (`.config/nextest.toml`) says which tier, and
/// no profile at all means `daily` ([`tier`]). The tier decides how much of
/// a corpus a sweep covers ([`tier_sample`]) and whether a full-only part of
/// a test runs ([`full_tier`]).
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Tier {
    Lane,
    Merge,
    Daily,
    Full,
}

/// The tier from `STITCHWORT_TIER`; when that is unset, from the nextest
/// profile, which nextest puts in each test's `NEXTEST_PROFILE` and
/// `.config/nextest.toml` names after the tier (`full`, `merge`, `daily`, and
/// `lane-AREA` for a lane): so `cargo nextest run --profile full` runs the
/// full-only tests without the variable having to be set. `default` (and no
/// profile at all) means `daily`. A set `STITCHWORT_TIER` wins. Panics on an
/// unknown name, so a typo doesn't quietly run the wrong amount.
#[doc(hidden)]
pub fn tier() -> Tier {
    let named = std::env::var("STITCHWORT_TIER").ok();
    let profile = std::env::var("NEXTEST_PROFILE").ok();
    tier_from(named.as_deref(), profile.as_deref())
}

/// [`tier`] from the two names it reads, so that its fallback is testable
/// without changing the process environment that other tests see.
fn tier_from(named: Option<&str>, profile: Option<&str>) -> Tier {
    if let Some(name) = named {
        return match name {
            "" | "daily" => Tier::Daily,
            "lane" => Tier::Lane,
            "merge" => Tier::Merge,
            "full" => Tier::Full,
            other => panic!("STITCHWORT_TIER={other}: expected lane, merge, daily or full"),
        };
    }
    match profile {
        None | Some("" | "default" | "daily") => Tier::Daily,
        Some("merge") => Tier::Merge,
        Some("full") => Tier::Full,
        Some(name) if name == "lane" || name.starts_with("lane-") => Tier::Lane,
        Some(other) => {
            panic!("NEXTEST_PROFILE={other}: expected default, lane-AREA, merge, daily or full")
        }
    }
}

/// Whether the full tier is on, for a test or part of one that runs only
/// there; when it is off, says what was skipped.
#[doc(hidden)]
pub fn full_tier(test: &str) -> bool {
    let on = tier() == Tier::Full;
    if !on {
        eprintln!("skipped {test}: full tier only (`task test:full`)");
    }
    on
}

/// A corpus sweep's share of `items` in this tier, a fixed sample (every
/// n-th item, from the first, in the order given): every item in the full
/// tier, every `daily_stride`-th in `daily`, and every
/// `4 * daily_stride`-th in `merge` and `lane`. A stride of 1 means the
/// whole corpus in `daily`.
#[doc(hidden)]
pub fn tier_sample<T>(items: Vec<T>, daily_stride: usize) -> Vec<T> {
    let stride = match tier() {
        Tier::Full => 1,
        Tier::Daily => daily_stride.max(1),
        Tier::Merge | Tier::Lane => 4 * daily_stride.max(1),
    };
    items.into_iter().step_by(stride).collect()
}

/// Where an eager session gets the standard library's files.
enum StdCache {
    /// Checked from source.
    Source,
    /// Replayed from the test cache under `target/` where it has them, and
    /// checked (and cached) where not.
    Test,
}

/// How long the test std cache keeps entries of other builds: a few
/// minutes, because every edit-and-test cycle is a new build, and an entry
/// is a few hundred KB.
const TEST_STD_CACHE_GRACE: std::time::Duration = std::time::Duration::from_secs(10 * 60);

/// The test std cache's folder for sessions with `stack` bytes of stack:
/// `test-std-cache/{stack}` in the cargo target folder the running test
/// binary is in (`target/release/deps/x` gives `target/`), or in the
/// temporary folder if that is not found. The stack is part of the cache's
/// key, and a unit's entries for other keys are evicted when it is
/// written, so each stack has a folder of its own.
#[doc(hidden)]
pub fn test_std_cache_dir(stack: usize) -> std::path::PathBuf {
    let target = std::env::current_exe().ok().and_then(|exe| {
        exe.ancestors()
            .find(|a| a.file_name().is_some_and(|n| n == "target"))
            .map(std::path::Path::to_path_buf)
    });
    target
        .unwrap_or_else(std::env::temp_dir)
        .join("test-std-cache")
        .join(stack.to_string())
}

/// What a filled test std cache's marker holds: the build's fingerprint (the
/// Rust sources) and the library's text. A change to a library file alone
/// leaves the fingerprint as it was but makes the entries of every file
/// after it miss, so a marker of the fingerprint alone called the cache full
/// and let every process check those files from source at once (about
/// 1.3 GB each, SW-3000).
fn cache_stamp() -> &'static str {
    static STAMP: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    STAMP.get_or_init(|| {
        let mut hasher = blake3::Hasher::new();
        hasher.update(stitchwort_elab::prelude().as_bytes());
        for (path, text) in stitchwort_elab::library_files() {
            hasher.update(path.as_bytes());
            hasher.update(text.as_bytes());
        }
        format!("{FINGERPRINT}-{}", &hasher.finalize().to_hex()[..16])
    })
}

/// Lets one process at a time load the library into an empty test std cache.
///
/// After a compiler change every test process finds the cache empty and would
/// check the whole library itself, all at once (a sweep's eight workers
/// included): ten times the work, on the cores that the other tests need.
/// The first process takes an advisory lock beside the cache directory and
/// loads; the others wait for it, then replay what it wrote. A marker beside
/// the cache, holding the build's fingerprint, tells later processes (and
/// the holder's own next sessions) that the cache is full, so replays don't
/// queue for the lock.
#[doc(hidden)]
pub struct TestCacheTurn {
    file: Option<std::fs::File>,
    marker: std::path::PathBuf,
}

impl TestCacheTurn {
    pub fn take(cache_dir: &std::path::Path) -> Self {
        let marker = cache_dir.with_extension("done");
        let none = |marker| TestCacheTurn { file: None, marker };
        let full = |marker: &std::path::Path| {
            std::fs::read_to_string(marker).is_ok_and(|text| text == cache_stamp())
        };
        if full(&marker) {
            return none(marker);
        }
        let lock = cache_dir.with_extension("lock");
        let file = lock
            .parent()
            .and_then(|parent| std::fs::create_dir_all(parent).ok())
            .and_then(|()| {
                std::fs::OpenOptions::new()
                    .create(true)
                    .write(true)
                    .truncate(false)
                    .open(&lock)
                    .ok()
            });
        let Some(file) = file else {
            return none(marker);
        };
        if file.lock().is_err() {
            return none(marker);
        }
        if full(&marker) {
            let _ = file.unlock();
            return none(marker);
        }
        TestCacheTurn {
            file: Some(file),
            marker,
        }
    }

    /// Whether this process is the one to fill the cache (the others waited
    /// for it, or found it full).
    pub fn is_filling(&self) -> bool {
        self.file.is_some()
    }

    /// The library loaded through the cache: it is full.
    pub fn finish(&self) {
        if self.file.is_some() {
            let _ = std::fs::write(&self.marker, cache_stamp());
        }
    }
}

impl Drop for TestCacheTurn {
    fn drop(&mut self) {
        if let Some(file) = &self.file {
            let _ = file.unlock();
        }
    }
}

impl Session {
    /// A session for a thread with `stack` bytes of stack.
    pub fn for_stack(stack: usize) -> Self {
        let mut session = Session::new();
        session.elab.options.limits = Limits::for_stack(stack);
        session
    }

    /// [`Session::navigable`], for a thread with `stack` bytes of stack.
    pub fn navigable_for_stack(stack: usize) -> Self {
        let mut session = Session::navigable();
        session.elab.options.limits = Limits::for_stack(stack);
        session
    }

    /// [`Session::eager`], for a thread with `stack` bytes of stack.
    #[doc(hidden)]
    pub fn eager_for_stack(stack: usize) -> Self {
        // The library loads now, so under these limits, not the defaults.
        Self::start(
            prelude(),
            Library::Standard,
            true,
            false,
            false,
            Limits::for_stack(stack),
            StdCache::Test,
        )
        .unwrap_or_else(|report| panic!("{report}"))
    }

    /// A session with the whole library loaded from source (the library
    /// this process reads, `--std-dir` included), under limits for a thread
    /// with `stack` bytes; the report of what failed to load if it doesn't.
    pub fn try_eager_library_for_stack(stack: usize) -> Result<Self, String> {
        Self::start(
            prelude(),
            Library::Standard,
            true,
            false,
            false,
            Limits::for_stack(stack),
            StdCache::Source,
        )
    }

    /// [`Session::eager_for_stack`], checking the whole library from source
    /// (the test cache is not used): for the tests whose point is that
    /// check (docs/testing.md, "The test std cache").
    #[doc(hidden)]
    pub fn eager_from_source_for_stack(stack: usize) -> Self {
        Self::start(
            prelude(),
            Library::Standard,
            true,
            false,
            false,
            Limits::for_stack(stack),
            StdCache::Source,
        )
        .unwrap_or_else(|report| panic!("{report}"))
    }

    pub fn new() -> Self {
        Session::with_prelude(prelude())
    }

    /// A session recording what code navigation needs (the index of
    /// `nav::index_json`), from the core on: recording turned on after the
    /// session was made would miss the names in the core (`std/core/`).
    pub fn navigable() -> Self {
        Self::start(
            prelude(),
            Library::Standard,
            false,
            false,
            true,
            Limits::default(),
            StdCache::Source,
        )
        .unwrap_or_else(|report| panic!("{report}"))
    }

    /// A session whose prelude is the given text: for tests that change a
    /// prelude definition.
    #[doc(hidden)]
    pub fn with_prelude(prelude: &str) -> Self {
        Self::try_with_prelude(prelude).unwrap_or_else(|report| panic!("{report}"))
    }

    /// Like [`Session::with_prelude`], but a prelude that doesn't check gives
    /// its diagnostics rendered with file, line and labels (what an author of
    /// the prelude needs), not a panic.
    #[doc(hidden)]
    pub fn try_with_prelude(prelude: &str) -> Result<Self, String> {
        Self::start(
            prelude,
            Library::Standard,
            false,
            false,
            false,
            Limits::default(),
            StdCache::Source,
        )
    }

    /// A session with every library file loaded up front, in canonical
    /// order, instead of on demand: for tests that compare it with the lazy
    /// one (docs/proposals/std-library.md §4.0).
    #[doc(hidden)]
    pub fn eager() -> Self {
        Self::start(
            prelude(),
            Library::Standard,
            true,
            false,
            false,
            Limits::default(),
            StdCache::Test,
        )
        .unwrap_or_else(|report| panic!("{report}"))
    }

    /// [`Session::eager`], checking the whole library from source.
    #[doc(hidden)]
    pub fn eager_from_source() -> Self {
        Self::start(
            prelude(),
            Library::Standard,
            true,
            false,
            false,
            Limits::default(),
            StdCache::Source,
        )
        .unwrap_or_else(|report| panic!("{report}"))
    }

    /// A session with the core only: the library's names aren't known, and
    /// nothing loads. For a test that the core stands on its own.
    #[doc(hidden)]
    pub fn core_alone() -> Self {
        Self::start(
            prelude(),
            Library::None,
            false,
            false,
            false,
            Limits::default(),
            StdCache::Source,
        )
        .unwrap_or_else(|report| panic!("{report}"))
    }

    /// A session whose library is the given files `(path, text)`, after the
    /// real core: for tests of the loader. The files load on demand, or all
    /// of them now with `eager`; with `library_tests` their `test`s are
    /// checked too.
    #[doc(hidden)]
    pub fn with_library_files(
        files: &[(&str, &str)],
        eager: bool,
        library_tests: bool,
    ) -> Result<Self, String> {
        Self::start(
            prelude(),
            Library::Files(files),
            eager,
            library_tests,
            false,
            Limits::default(),
            StdCache::Source,
        )
    }

    /// A session with every library file loaded, and the `test`s of the core
    /// and the library files checked: what [`Session::run_library_tests`]
    /// runs.
    #[doc(hidden)]
    pub fn with_library_tests() -> Self {
        Self::start(
            prelude(),
            Library::Standard,
            true,
            true,
            false,
            Limits::default(),
            StdCache::Source,
        )
        .unwrap_or_else(|report| panic!("{report}"))
    }

    /// [`Session::with_prelude`], except that a pinned declaration the
    /// prelude changed (`stitchwort_core::pins`) runs as written, without
    /// its native, instead of refusing the prelude: for the tests that
    /// check what a changed declaration falls back to.
    #[doc(hidden)]
    #[cfg(feature = "test-bypass")]
    pub fn with_prelude_falling_back(prelude: &str) -> Self {
        Self::try_with_prelude_falling_back(prelude).unwrap_or_else(|report| panic!("{report}"))
    }

    /// [`Session::with_prelude_falling_back`], giving a prelude that
    /// doesn't check as its rendered diagnostics.
    #[doc(hidden)]
    #[cfg(feature = "test-bypass")]
    pub fn try_with_prelude_falling_back(prelude: &str) -> Result<Self, String> {
        let mut elab = Elaborator::new();
        elab.options.stale_pins_fall_back = true;
        Self::start_in(
            elab,
            prelude,
            Library::Standard,
            false,
            false,
            false,
            Limits::default(),
            StdCache::Source,
        )
    }

    /// Loads the core (the prelude text given), then makes the library's
    /// names known, and loads its files too if `eager`.
    fn start(
        prelude: &str,
        library: Library,
        eager: bool,
        library_tests: bool,
        navigation: bool,
        limits: Limits,
        std_cache: StdCache,
    ) -> Result<Self, String> {
        Self::start_in(
            Elaborator::new(),
            prelude,
            library,
            eager,
            library_tests,
            navigation,
            limits,
            std_cache,
        )
    }

    /// [`Session::start`] with the elaborator given, before anything loads.
    #[allow(clippy::too_many_arguments)]
    fn start_in(
        elab: Elaborator,
        prelude: &str,
        library: Library,
        eager: bool,
        library_tests: bool,
        navigation: bool,
        limits: Limits,
        std_cache: StdCache,
    ) -> Result<Self, String> {
        let mut session = Session {
            sources: SourceMap::new(),
            elab,
            warnings: Vec::new(),
        };
        session.elab.options.limits = limits;
        if navigation {
            session.elab.enable_navigation();
        }
        // Counterexample searches run on the fast runtime (D1154).
        session.elab.options.counterexample_runner = Some(crate::counterexample::run_fast);
        let stack = session.elab.options.limits.stack;
        let index = match library {
            Library::Standard | Library::None => LibraryIndex::standard(stack),
            Library::Files(files) => {
                LibraryIndex::build(stitchwort_elab::prelude(), files, stack).map(Arc::new)
            }
        }
        .map_err(|e| format!("internal error: the standard library: {e}"))?;
        let report = |sources: &SourceMap, what: &str, diagnostics: &[Diagnostic]| {
            let mut report = format!("internal error: {what}:\n");
            for d in diagnostics {
                report.push_str(&crate::render::render(sources, d, false));
            }
            report
        };
        session.elab.set_loading_prelude(true);
        session.elab.options.library_tests = library_tests;
        let file = session.sources.add("<prelude>", prelude);
        // The library's files follow the core in the source map, in the
        // index's order, so the spans the index parsed are this session's.
        for lib in index.files.iter().skip(1) {
            let id = session.sources.add(format!("std/{}", lib.path), &lib.text);
            assert_eq!(
                id, lib.id,
                "the library's files are numbered as the index's"
            );
        }
        // The index has parsed the core, unless a test changed its text.
        let parsed;
        let module = if prelude == index.files[0].text {
            &index.files[0].module
        } else {
            parsed = parse_module_within(file, prelude, stack)
                .map_err(|ds| report(&session.sources, "the prelude doesn't parse", &ds))?;
            &parsed
        };
        session.elab.set_core_link_names(Some(index.clone()));
        let mut diagnostics = session.elab.elaborate_module(module);
        session.elab.set_core_link_names(None);
        // A broken doc link in the core fails the load, as in a library
        // file (SW-1046). A test's own library files don't have the names
        // the core's docs link to, so its links aren't checked.
        if matches!(library, Library::Files(_)) {
            diagnostics.retain(|d| d.code != "W-DOC-LINK");
        } else if diagnostics.iter().any(|d| d.code == "W-DOC-LINK") {
            return Err(report(
                &session.sources,
                "the prelude has a broken doc link",
                &diagnostics,
            ));
        }
        if let Err(diagnostics) = session.finish_load(0, diagnostics) {
            return Err(report(
                &session.sources,
                "the prelude doesn't check",
                &diagnostics,
            ));
        }
        if let Err(missing) = session.elab.finish_core() {
            return Err(format!("internal error: {}", missing.message));
        }
        if matches!(library, Library::Standard) {
            stitchwort_core::registry::check_library_declares_all(|n| {
                index.owner(&format!("Std.{n}"))
            })
            .map_err(|d| format!("internal error: {}", d.message))?;
        }
        if !matches!(library, Library::None) {
            session.elab.install_library(index);
        }
        if eager && let StdCache::Test = std_cache {
            let dir = test_std_cache_dir(session.elab.options.limits.stack);
            session.elab.set_check_cache(std::rc::Rc::new(
                crate::check_cache::CheckCache::with_grace(&dir, TEST_STD_CACHE_GRACE),
            ));
        }
        // One process checks the library into an empty test cache at a time
        // (see `TestCacheTurn`); with the cache empty after a compiler change,
        // every test in every process would otherwise check it at once.
        let _turn = (eager && matches!(std_cache, StdCache::Test))
            .then(|| TestCacheTurn::take(&test_std_cache_dir(session.elab.options.limits.stack)));
        if eager && let Err(diagnostics) = session.elab.load_all_libraries() {
            return Err(report(
                &session.sources,
                "the standard library doesn't check",
                &diagnostics,
            ));
        }
        if let Some(turn) = &_turn {
            turn.finish();
        }
        Ok(session)
    }

    /// For a test of what a program does, not of how the library checks:
    /// in every tier but the full one, library files load through the test
    /// std cache (the one [`Session::eager_for_stack`] fills), where they
    /// would each be checked from source in every session, which was most
    /// of the CPU of the tests that make many. The full tier still checks
    /// from source, as a second guard beside `hash_stability`'s `prelude`. `Session::eager_from_source_for_stack` is
    /// for the tests of that check.
    #[doc(hidden)]
    pub fn use_test_std_cache(&mut self) {
        if tier() == Tier::Full {
            return;
        }
        let dir = test_std_cache_dir(self.elab.options.limits.stack);
        self.elab.set_check_cache(std::rc::Rc::new(
            crate::check_cache::CheckCache::with_grace(&dir, TEST_STD_CACHE_GRACE),
        ));
    }

    /// Loads library files and project namespaces from, and keeps them in,
    /// the check cache in the cache directory `dir`
    /// (docs/proposals/check-cache.md). Off unless
    /// this is called: tests, snapshots and the benchmark never use it.
    pub fn use_check_cache(&mut self, dir: &std::path::Path) {
        self.elab
            .set_check_cache(std::rc::Rc::new(crate::check_cache::CheckCache::at(dir)));
    }

    /// Lets `include` read the files of a project: from `files`, where the
    /// project's files are found by their path in it.
    pub fn include_from(&mut self, files: std::rc::Rc<dyn stitchwort_elab::project::IncludeFiles>) {
        self.elab.set_include_files(files);
    }

    /// For the next [`Session::load_file`] of a file on its own: `include`
    /// reads from `files`, the file's own folder, and the file is called
    /// `name` in it.
    pub fn include_in_folder(
        &mut self,
        files: std::rc::Rc<dyn stitchwort_elab::project::IncludeFiles>,
        name: &str,
    ) {
        self.elab.set_include_files(files);
        self.elab.set_next_include_location(name.to_string());
    }

    /// Parses, elaborates and checks a file, and checks that its exports can
    /// cross the JS boundary.
    pub fn load(&mut self, name: &str, text: &str) -> Result<FileId, Vec<Diagnostic>> {
        self.load_file(name, text, None)
    }

    /// [`Session::load`] for a file named on its own that lives inside a
    /// project: with `context`, a use of one of the project's namespaces is
    /// `E-FILE-MODE`, which says what to do instead.
    pub fn load_file(
        &mut self,
        name: &str,
        text: &str,
        context: Option<FileModeContext>,
    ) -> Result<FileId, Vec<Diagnostic>> {
        let file = self.sources.add(name, text);
        if let Some(location) = self.elab.take_next_include_location() {
            self.elab.set_include_location(file, location);
        }
        // A syntax error doesn't stop the declarations that parsed from
        // being checked, so one run reports every error; the file never
        // loads as a success, though.
        let (module, parse_errors) =
            parse_module_recovering(file, text, self.elab.options.limits.stack);
        let first_new_def = self.elab.kernel.env.defs().len();
        self.elab.set_file_mode(context);
        let diagnostics =
            if module.namespace.is_none() && module.decls.is_empty() && !parse_errors.is_empty() {
                Vec::new()
            } else {
                self.elab.elaborate_module(&module)
            };
        self.elab.set_file_mode(None);
        if parse_errors.is_empty() {
            self.finish_load(first_new_def, diagnostics)?;
            Ok(file)
        } else {
            Err(merge_recovered(parse_errors, diagnostics))
        }
    }

    /// Loads several files of one namespace as one module: for tests, until
    /// projects load (`docs/proposals/multi-file.md` §4.4). Each file is
    /// `(name, text)`, and all must start with the same namespace line.
    #[doc(hidden)]
    pub fn load_namespace(&mut self, files: &[(&str, &str)]) -> Result<(), Vec<Diagnostic>> {
        let mut sorted: Vec<(&str, &str)> = files.to_vec();
        sorted.sort_by_key(|(name, _)| *name);
        let ids: Vec<FileId> = sorted
            .iter()
            .map(|&(name, text)| self.sources.add(name, text))
            .collect();
        let mut modules = Vec::new();
        let mut errors = Vec::new();
        for (id, (_, text)) in ids.iter().zip(&sorted) {
            match parse_module_within(*id, text, self.elab.options.limits.stack) {
                Ok(module) => modules.push(module),
                Err(parse_errors) => errors.extend(parse_errors),
            }
        }
        if !errors.is_empty() {
            return Err(errors);
        }
        let internal = |message: &str| vec![Diagnostic::error("E-INTERNAL", message)];
        let Some(first) = modules.first().and_then(|m| m.namespace.as_ref()) else {
            return Err(internal("every file of a namespace needs a namespace line"));
        };
        let namespace = first.path.text.clone();
        if modules
            .iter()
            .any(|m| m.namespace.as_ref().map(|n| &n.path.text) != Some(&namespace))
        {
            return Err(internal("the files must all be in the same namespace"));
        }
        if let Err(d) = self.elab.check_namespace_name(first) {
            return Err(vec![d]);
        }
        let units: Vec<SourceUnit> = sorted
            .iter()
            .zip(&ids)
            .zip(&modules)
            .map(|(((name, _), id), module)| SourceUnit {
                file: Some(*id),
                name,
                module,
            })
            .collect();
        let first_new_def = self.elab.kernel.env.defs().len();
        let diagnostics = self
            .elab
            .elaborate_namespace(Some(&namespace), &units, None);
        self.finish_load(first_new_def, diagnostics)
    }

    /// What `load` does once the elaborator is done: checks that the new
    /// definitions' exports can cross the JS boundary, keeps the warnings,
    /// and returns the errors if there are any.
    fn finish_load(
        &mut self,
        first_new_def: usize,
        mut diagnostics: Vec<Diagnostic>,
    ) -> Result<(), Vec<Diagnostic>> {
        self.check_exports(first_new_def, false, &mut diagnostics);
        if diagnostics.iter().any(|d| d.severity == Severity::Error) {
            Err(diagnostics)
        } else {
            self.warnings.extend(diagnostics);
            Ok(())
        }
    }

    /// If `diagnostics` has no errors, checks that the exports of the
    /// definitions from `first_new_def` on can cross the JS boundary, and
    /// can be named together: with every export of the session (a file), or
    /// with only these (`among`: one namespace of a project).
    pub(crate) fn check_exports(
        &self,
        first_new_def: usize,
        among: bool,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        let errors = |ds: &[Diagnostic]| ds.iter().any(|d| d.severity == Severity::Error);
        if errors(diagnostics) {
            return;
        }
        let view = self.elab.backend();
        let g = &view;
        let _op = g
            .machine
            .budget
            .operation(Limits::stack_only(self.elab.options.limits.stack));
        for id in first_new_def..g.env.defs().len() {
            let id = stitchwort_core::DefId(id);
            if g.def(id).export()
                && let Err(d) = stitchwort_js::exportable(g, id)
            {
                diagnostics.push(d);
            }
        }
        if errors(diagnostics) {
            return;
        }
        let fit = if among {
            stitchwort_js::exports_fit_together_among(
                g,
                (first_new_def..g.env.defs().len()).map(stitchwort_core::DefId),
            )
        } else {
            stitchwort_js::exports_fit_together(g)
        };
        if let Err(d) = fit {
            diagnostics.push(d);
        }
    }

    /// Parses an expression typed in (for `eval` or the REPL), within this
    /// session's stack limit.
    pub fn parse_expression(&mut self, name: &str, text: &str) -> Result<Expr, Diagnostic> {
        let file = self.sources.add(name, text);
        let expr = parse_expression_within(file, text, self.elab.options.limits.stack)?;
        // The library files it uses load now: checking it needs them.
        self.elab.prepare_expr(&expr)?;
        Ok(expr)
    }

    /// Adds `import` lines typed in (the REPL, the playground's Evaluate
    /// tab) to the imports that expressions see; they accumulate. Returns
    /// the errors and warnings, as a file's imports give.
    pub fn add_imports(&mut self, name: &str, text: &str) -> Vec<Diagnostic> {
        let file = self.sources.add(name, text);
        let module = match parse_module_within(file, text, self.elab.options.limits.stack) {
            Ok(module) => module,
            Err(diagnostics) => return diagnostics,
        };
        if !module.decls.is_empty() || module.namespace.is_some() {
            return vec![Diagnostic::error(
                "E-PARSE",
                "only `import` lines and expressions can be entered here, not declarations",
            )];
        }
        self.elab.add_session_imports(&module.imports)
    }

    /// Parses an expression the driver wrote itself.
    pub(crate) fn parse_internal(&mut self, name: &str, text: &str) -> Result<Expr, Diagnostic> {
        self.parse_expression(name, text)
    }

    /// Generates JavaScript for the exports loaded so far.
    pub fn extract(&self) -> Result<stitchwort_js::Output, Diagnostic> {
        let g = &self.elab.ev();
        self.refuse_unfinished((0..g.env.defs().len()).map(stitchwort_core::DefId))?;
        stitchwort_js::generate(&self.elab.backend(), self.elab.options.limits)
    }

    /// An error if any of the exports among `ids` is unfinished (it, or
    /// something it uses, has an open goal, `?`): it has no body to
    /// generate, and only checked code is built (D636).
    fn refuse_unfinished(
        &self,
        ids: impl Iterator<Item = stitchwort_core::DefId>,
    ) -> Result<(), Diagnostic> {
        let g = &self.elab.ev();
        for id in ids {
            let def = g.def(id);
            if def.export() && self.elab.is_unfinished(id) {
                return Err(Diagnostic::error(
                    "E-UNFINISHED",
                    format!(
                        "`{}` can't be built: it, or something it uses, has an open goal (`?`)",
                        def.name()
                    ),
                )
                .with_label(def.span(), "fill in every goal it needs first"));
            }
        }
        Ok(())
    }

    /// Generates JavaScript for the exports of namespace `namespace` of the
    /// project loaded, and no others'.
    pub fn extract_namespace(&self, namespace: &str) -> Result<stitchwort_js::Output, Diagnostic> {
        let g = &self.elab.ev();
        let ids: Vec<stitchwort_core::DefId> = self
            .elab
            .namespace_def_range(namespace)
            .map(stitchwort_core::DefId)
            .filter(|id| g.def(*id).export())
            .collect();
        self.refuse_unfinished(ids.iter().copied())?;
        stitchwort_js::generate_exports(
            &self.elab.backend(),
            self.elab.options.limits,
            stitchwort_js::Options::default(),
            &ids,
        )
    }

    /// Generates the JavaScript program that runs `main` under Node
    /// (`stitchwort run --js`).
    pub fn extract_program(
        &self,
        main: &crate::run::Main,
    ) -> Result<stitchwort_js::run::Program, Diagnostic> {
        stitchwort_js::run::generate_program(
            &self.elab.backend(),
            self.elab.options.limits,
            main.term(),
        )
    }
}

/// What a load that had syntax errors reports: those, then what checking
/// the declarations that did parse found, in file order. Uses of
/// declarations that failed to parse (`E-FAILED-DEPENDENCY`) go without
/// saying: the syntax error is the cause.
pub(crate) fn merge_recovered(
    parse_errors: Vec<Diagnostic>,
    checked: Vec<Diagnostic>,
) -> Vec<Diagnostic> {
    let mut all = parse_errors;
    let mut recovered = Vec::new();
    for d in checked {
        if d.code == "E-FAILED-DEPENDENCY" {
            continue;
        }
        // A body that didn't parse fails with its own error, which isn't
        // reported: the parser's error at the same place is. What the check
        // found about its statement, a counterexample, belongs on that one.
        if d.code == stitchwort_elab::UNPARSED_BODY {
            if let Some(at) = d.primary_span()
                && let Some(error) = all.iter_mut().find(|e| e.primary_span() == Some(at))
            {
                let counterexample = d.counterexample_data().cloned();
                error.notes.extend(d.notes);
                if let Some(counterexample) = counterexample {
                    error.detail_mut().counterexample = Some(counterexample);
                }
            }
            continue;
        }
        recovered.push(d);
    }
    all.extend(recovered);
    all.sort_by_key(|d| {
        d.labels.first().map_or((usize::MAX, u32::MAX), |l| {
            (l.span.file.index(), l.span.start)
        })
    });
    all
}

/// Whether a test's expression evaluated to `True`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Passed,
    Failed,
    /// It ran out of resources before finishing: neither passed nor failed.
    /// Never cached.
    OutOfResources(ResourceError),
}

pub struct TestResult {
    pub name: String,
    /// The namespace its module is in; empty if it has none.
    pub namespace: String,
    pub outcome: Outcome,
    /// Whether the outcome came from the cache, rather than running the test.
    pub cached: bool,
    /// `None` if hashing the test ran out of resources.
    pub hash: Option<ContentHash>,
    /// For a failed test, what can be said about why (D601).
    pub detail: Option<Failure>,
    /// For a test that wasn't run, why: its code reaches an open goal
    /// (`?`), naming the `?` and where it is, or it uses a declaration with
    /// an error, or has one of its own ([`Session::with_broken_tests`]). The test fails
    /// (`outcome` is [`Outcome::Failed`]). Never cached.
    pub unfinished: Option<String>,
    /// For a passing test, the gaps it relies on: open goals or
    /// declarations with an error that are proofs or types it passes
    /// around, which are erased when it runs, so it still runs (SW-2939,
    /// D3525). Empty for a test that relies on none, and for a test that
    /// didn't pass: a failure keeps its own reason.
    pub assuming: Vec<crate::reliance::GoalPlace>,
}

/// Why a test failed, as far as it can be told: the part of the test that is
/// false, and for a comparison, the values of its two sides. Found by running
/// parts of the test again when it fails, also for a cached failure: the
/// cache keeps only the outcome, so a passing test never pays for this. It's
/// only a presentation: the test failed because the kernel found `False`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure {
    /// Which part of the test is false, when it isn't the whole expression
    /// (the last of some `let`s, or the first false operand of `&&`).
    pub part: Option<Part>,
    /// If that part is a comparison, its two sides.
    pub comparison: Option<Comparison>,
}

/// `range` in `text`, widened over the round brackets the parser leaves out
/// of an expression's span (it has no node for a bracketed expression): an
/// unmatched closer in the range pulls the start back to its opener, and an
/// unmatched opener pushes the end on to its closer. Unchanged if the
/// brackets don't pair up.
fn balanced_range(text: &str, range: std::ops::Range<usize>) -> std::ops::Range<usize> {
    let Some(inside) = text.get(range.clone()) else {
        return range;
    };
    let (mut closers, mut openers) = (0usize, 0usize);
    for c in inside.chars() {
        match c {
            '(' => openers += 1,
            ')' if openers > 0 => openers -= 1,
            ')' => closers += 1,
            _ => {}
        }
    }
    let mut start = range.start;
    let mut need = closers;
    for (i, c) in text[..range.start].char_indices().rev() {
        if need == 0 {
            break;
        }
        match c {
            ')' => need += 1,
            '(' => {
                need -= 1;
                start = i;
            }
            _ => {}
        }
    }
    let mut end = range.end;
    let mut want = openers;
    for (i, c) in text[range.end..].char_indices() {
        if want == 0 {
            break;
        }
        match c {
            '(' => want += 1,
            ')' => {
                want -= 1;
                end = range.end + i + 1;
            }
            _ => {}
        }
    }
    if need > 0 || want > 0 {
        return range;
    }
    start..end
}

/// A part of a test's expression: its text (on one line, cut off with `…` if
/// long) and where it starts (`line` and `column` count from 1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Part {
    pub text: String,
    pub file: String,
    pub line: usize,
    pub column: usize,
}

/// The two sides of a failed comparison, printed (up to `SHOWN_SIDE` characters
/// each, then cut off with `…`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Comparison {
    /// The operator as written: `==`, `!=`, `=`, `<`, `<=`, `>` or `>=`.
    pub op: &'static str,
    pub left: String,
    pub right: String,
    /// A side that is a text of several lines, shown as its lines (see
    /// [`text_lines`]), for showing in place of the quoted text.
    pub left_lines: Option<String>,
    pub right_lines: Option<String>,
    /// For two lists or two texts that aren't equal, where they first differ.
    pub difference: Option<String>,
}

/// Test results, stored by the test's content hash (DESIGN.md §11). A test's
/// hash covers everything it depends on, so a cached result stays valid until
/// something the test uses changes. The local cache is trusted. Results live
/// in a directory, or in memory for hosts without a file system.
///
/// The key also has the compiler that ran it: its version, a fingerprint of
/// the Rust that evaluates tests ([`EVAL_FINGERPRINT`]), and the modes that change how programs are
/// evaluated ([`modes`]). So a result is never reused by a different build,
/// or by a run with natives or compact text switched off.
///
/// In a directory, each result is a file named by its key and the test it
/// is for ([`Cache::unit`]). Writing a result deletes that test's other
/// results from the same build and modes, and the first write of a run
/// deletes results of other builds more than a day old (D283, as for the
/// check cache).
pub struct Cache {
    dir: Option<PathBuf>,
    memory: Option<RefCell<Memory>>,
    /// Whether this run has written yet (the first write sweeps).
    written: std::cell::Cell<bool>,
    /// Set by [`Cache::verifying`]: what has been checked so far.
    verify: Option<RefCell<Verification>>,
}

/// What a verifying cache ([`Cache::verifying`]) has found.
#[derive(Default, Debug)]
pub struct Verification {
    /// Tests run fresh whose cached result was compared with it.
    pub compared: usize,
    /// Tests run fresh that the cache had no result for.
    pub missing: usize,
    /// Tests whose cached result differs from the fresh one.
    pub disagreements: Vec<Disagreement>,
}

/// A test whose cached result differs from a fresh run's: the cache's key
/// missed something that decides a result, or the test isn't deterministic.
#[derive(Debug)]
pub struct Disagreement {
    pub namespace: String,
    pub name: String,
    pub hash: ContentHash,
    pub cached: Outcome,
    pub fresh: Outcome,
}

/// A cache's results when it has no directory to keep them in: the ones it
/// started with, and the ones added since (which the host can save).
struct Memory {
    known: HashMap<String, Outcome>,
    added: Vec<(String, Outcome)>,
}

/// Part of every cache key, so results from another version of the compiler
/// aren't reused.
const COMPILER: &str = concat!("stitchwort-", env!("CARGO_PKG_VERSION"));

/// A hash of the source of this crate and every workspace crate it's built
/// with ([`FINGERPRINT_CRATES`]: the elaborator, the
/// runtime that runs the tests, …), made by `build.rs`: part of every cache
/// key, so results from another build of the compiler aren't reused, even
/// with the same version number.
pub const FINGERPRINT: &str = env!("STITCHWORT_FINGERPRINT");

/// The crates whose sources [`FINGERPRINT`] covers, as directories relative
/// to the workspace root, comma-separated
/// ([`crate::fingerprint::source_crates`]).
pub const FINGERPRINT_CRATES: &str = env!("STITCHWORT_FINGERPRINT_CRATES");

/// The fingerprint of what evaluates tests, made by `build.rs`
/// ([`crate::fingerprint::evaluation_fingerprint`]): the test cache's key has
/// this and not [`FINGERPRINT`], because a test's hash already covers
/// the program and the standard library it uses. Only a change to the Rust
/// that evaluates a term, or to the toolchain, starts a fresh cache.
pub const EVAL_FINGERPRINT: &str = env!("STITCHWORT_EVAL_FINGERPRINT");

/// The crates whose sources [`EVAL_FINGERPRINT`] covers (and the driver's
/// `test_run.rs` besides), as directories relative to the workspace root,
/// comma-separated.
pub const EVAL_FINGERPRINT_CRATES: &str = env!("STITCHWORT_EVAL_FINGERPRINT_CRATES");

/// [`FINGERPRINT`] without the toolchain and target: the same in a native
/// and a WebAssembly build of the same sources, so a test can tell whether
/// the playground's bundle is up to date (`stitchwort_web::source_fingerprint`).
/// It covers web's crate graph ([`SOURCE_FINGERPRINT_CRATES`]), so editing the
/// web crate itself marks `web/pkg` stale.
pub const SOURCE_FINGERPRINT: &str = env!("STITCHWORT_SOURCE_FINGERPRINT");

/// The crates whose sources [`SOURCE_FINGERPRINT`] covers, as directories
/// relative to the workspace root, comma-separated: web and every workspace
/// crate it's built with (which includes the driver's graph and the
/// formatter).
pub const SOURCE_FINGERPRINT_CRATES: &str = env!("STITCHWORT_SOURCE_FINGERPRINT_CRATES");

impl Cache {
    pub fn at(dir: impl Into<PathBuf>) -> Self {
        Cache {
            dir: Some(dir.into()),
            memory: None,
            written: std::cell::Cell::new(false),
            verify: None,
        }
    }

    /// A cache kept in memory, for hosts without a file system: it starts
    /// with `known`, and [`Cache::added`] gives the results added since.
    pub fn memory(known: impl IntoIterator<Item = (String, Outcome)>) -> Self {
        Cache {
            dir: None,
            memory: Some(RefCell::new(Memory {
                known: known.into_iter().collect(),
                added: Vec::new(),
            })),
            written: std::cell::Cell::new(false),
            verify: None,
        }
    }

    pub fn disabled() -> Self {
        Cache {
            dir: None,
            memory: None,
            written: std::cell::Cell::new(false),
            verify: None,
        }
    }

    /// This cache, used to check itself: tests are all run fresh, each
    /// result is compared with what the cache holds for it
    /// ([`Cache::verification`]), and nothing is written.
    pub fn verifying(mut self) -> Self {
        self.verify = Some(RefCell::new(Verification::default()));
        self
    }

    /// What a [`Cache::verifying`] cache has found so far; `None` for any
    /// other.
    pub fn verification(&self) -> Option<std::cell::Ref<'_, Verification>> {
        self.verify.as_ref().map(RefCell::borrow)
    }

    /// The test named `name` in namespace `namespace`, as a directory
    /// cache's file names have it: a short hash.
    pub fn unit(namespace: &str, name: &str) -> String {
        let mut h = blake3::Hasher::new();
        h.update(namespace.as_bytes());
        h.update(&[0]);
        h.update(name.as_bytes());
        h.finalize().as_bytes()[..8]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    }

    /// The key of the result of the test with `hash`, when run with `modes`:
    /// the file name in a directory cache.
    pub fn key(hash: &ContentHash, modes: &str) -> String {
        format!("{COMPILER}-{EVAL_FINGERPRINT}-{modes}-{}", hash.hex())
    }

    /// Where the result of test `unit` ([`Cache::unit`]) with `hash` is
    /// kept, when run with `modes`.
    pub fn path(&self, unit: &str, hash: &ContentHash, modes: &str) -> Option<PathBuf> {
        Some(self.dir.as_ref()?.join("tests").join(format!(
            "{}-{unit}-{}",
            Self::build(modes),
            hash.hex()
        )))
    }

    /// The start of the file names of this build's results with `modes`.
    fn build(modes: &str) -> String {
        format!("{COMPILER}-{EVAL_FINGERPRINT}-{modes}")
    }

    /// After writing `keep`, the result of test `unit`: deletes the test's
    /// other results for this build and modes, and on the first write of a
    /// run, other builds' results older than a day.
    fn evict(&self, unit: &str, modes: &str, keep: &std::path::Path) {
        let first = !self.written.replace(true);
        let Some(dir) = keep.parent() else {
            return;
        };
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        let own = format!("{}-{unit}-", Self::build(modes));
        let this_build = format!("{COMPILER}-{EVAL_FINGERPRINT}-");
        let now = std::time::SystemTime::now();
        for entry in entries.flatten() {
            let path = entry.path();
            let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                continue;
            };
            if path == keep {
                continue;
            }
            let stale = name.starts_with(&own)
                || (first
                    && !name.starts_with(&this_build)
                    && entry
                        .metadata()
                        .and_then(|m| m.modified())
                        .ok()
                        .and_then(|t| now.duration_since(t).ok())
                        .is_some_and(|age| age > crate::check_cache::GRACE));
            if stale {
                let _ = std::fs::remove_file(&path);
            }
        }
    }

    /// The results added by [`Cache::put`] during this run: only `Passed` and
    /// `Failed`, like the ones on disk. Empty for a cache without memory.
    pub fn added(&self) -> Vec<(String, Outcome)> {
        self.memory
            .as_ref()
            .map_or_else(Vec::new, |memory| memory.borrow().added.clone())
    }

    /// The cached result, unless verifying: then every test runs.
    pub(crate) fn get(&self, unit: &str, hash: &ContentHash, modes: &str) -> Option<Outcome> {
        if self.verify.is_some() {
            return None;
        }
        self.stored(unit, hash, modes)
    }

    /// In a [`Cache::verifying`] cache, compares the fresh `outcome` of the
    /// test with the one held; otherwise nothing. Out-of-resources isn't a
    /// result, so isn't compared.
    pub(crate) fn verify_result(
        &self,
        test: &stitchwort_elab::TestDecl,
        hash: &ContentHash,
        modes: &str,
        outcome: Outcome,
    ) {
        let Some(verify) = &self.verify else {
            return;
        };
        if matches!(outcome, Outcome::OutOfResources(_)) {
            return;
        }
        let unit = Self::unit(&test.namespace, &test.name);
        let mut verify = verify.borrow_mut();
        match self.stored(&unit, hash, modes) {
            None => verify.missing += 1,
            Some(cached) => {
                verify.compared += 1;
                if cached != outcome {
                    verify.disagreements.push(Disagreement {
                        namespace: test.namespace.clone(),
                        name: test.name.clone(),
                        hash: *hash,
                        cached,
                        fresh: outcome,
                    });
                }
            }
        }
    }

    /// What the cache holds for the test, whether or not this run reads it.
    fn stored(&self, unit: &str, hash: &ContentHash, modes: &str) -> Option<Outcome> {
        if let Some(memory) = &self.memory {
            return memory.borrow().known.get(&Self::key(hash, modes)).copied();
        }
        match std::fs::read_to_string(self.path(unit, hash, modes)?)
            .ok()?
            .trim()
        {
            "passed" => Some(Outcome::Passed),
            "failed" => Some(Outcome::Failed),
            _ => None,
        }
    }

    /// Best effort: a cache that can't be written just means re-running later.
    pub(crate) fn put(&self, unit: &str, hash: &ContentHash, modes: &str, outcome: Outcome) {
        if self.verify.is_some() {
            return;
        }
        // Not a result: running it again with other limits may finish.
        if matches!(outcome, Outcome::OutOfResources(_)) {
            return;
        }
        if let Some(memory) = &self.memory {
            let key = Self::key(hash, modes);
            let mut memory = memory.borrow_mut();
            memory.known.insert(key.clone(), outcome);
            memory.added.push((key, outcome));
            return;
        }
        let Some(path) = self.path(unit, hash, modes) else {
            return;
        };
        let text = match outcome {
            Outcome::Passed => "passed",
            Outcome::Failed => "failed",
            Outcome::OutOfResources(_) => unreachable!(),
        };
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        if std::fs::write(&path, text).is_ok() {
            self.evict(unit, modes, &path);
        }
    }
}

pub use crate::test_run::modes;

/// The most characters of a part of a test shown to say where it failed.
const SHOWN_PART: usize = 100;

impl Session {
    /// Why `test` failed, if it did and that can be told (D601): walks down
    /// its probe to the first false operand of each `&&`, then shows the sides
    /// of the comparison it ends at. Every step runs a closed term of its own,
    /// so what's wrong with one never changes the outcome.
    pub(crate) fn failure(
        &self,
        test: &stitchwort_elab::TestDecl,
        outcome: Outcome,
    ) -> Option<Failure> {
        use stitchwort_elab::ProbeKind;
        if outcome != Outcome::Failed {
            return None;
        }
        let mut probe = test.probe.as_ref()?;
        while let ProbeKind::And(a, b) = &probe.kind {
            // `a && b` is false when `a` is, and otherwise when `b` is.
            match self.holds(a) {
                Some(true) => probe = b,
                Some(false) => probe = a,
                None => break,
            }
        }
        let part = if probe.whole {
            None
        } else {
            self.part(probe.span)
        };
        let comparison = match &probe.kind {
            ProbeKind::Compare { op, left, right } => Some(self.compare(op, left, right)),
            _ => None,
        };
        if part.is_none() && comparison.is_none() {
            return None;
        }
        Some(Failure { part, comparison })
    }

    /// Whether the operand `probe` is `True`, if it can be told.
    fn holds(&self, probe: &stitchwort_elab::Probe) -> Option<bool> {
        let g = &self.elab.ev();
        let term = probe.truth.as_ref()?;
        let _op = g.machine.budget.operation(self.elab.options.limits);
        let _erasing = g.machine.erasure.running();
        match eval(g, &[], term).and_then(|v| force(g, v)) {
            Ok(Value::Ctor(_, c, _)) => Some(c == 1),
            _ => None,
        }
    }

    /// The text and place of the expression at `span`.
    /// Where the test `name` of `namespace` starts (its `test` keyword, or
    /// the attributes before it): `text` is empty, `line` and `column`
    /// count from 1.
    pub fn test_location(&self, namespace: &str, name: &str) -> Option<Part> {
        let span = self.test_span(namespace, name)?;
        let mut at = self.part(span)?;
        at.text.clear();
        Some(at)
    }

    /// Where the test `name` of `namespace` is declared, whether it could be
    /// checked or not.
    fn test_span(&self, namespace: &str, name: &str) -> Option<stitchwort_syntax::Span> {
        let same = |n: &str, ns: &str| n == name && ns == namespace;
        (self.elab.tests().iter())
            .find(|t| same(&t.name, &t.namespace))
            .map(|t| t.span)
            .or_else(|| {
                (self.elab.broken_tests().iter())
                    .find(|t| same(&t.name, &t.namespace))
                    .map(|t| t.span)
            })
    }

    /// `results` with the tests that couldn't be checked because they use a
    /// declaration with an error (`Elaborator::broken_tests`, D3523), those
    /// whose name `keep` keeps, each failed saying so: in `results` among
    /// the tests of its namespace, in source order.
    pub fn with_broken_tests(
        &self,
        mut results: Vec<TestResult>,
        keep: impl Fn(&str) -> bool,
    ) -> Vec<TestResult> {
        let order = |s: stitchwort_syntax::Span| (s.file.index(), s.start);
        for test in self.elab.broken_tests().iter().filter(|t| keep(&t.name)) {
            let place = |span: stitchwort_syntax::Span| {
                let file = self.sources.get(span.file);
                let end = (span.start as usize).min(file.text.len());
                let before = file.text.get(..end)?;
                let line = before.matches('\n').count() + 1;
                let column = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
                Some(format!("{}:{line}:{column}", file.name))
            };
            let at = (test
                .error_at
                .filter(|s| s.file.index() < self.sources.len()))
            .and_then(place)
            .map_or_else(String::new, |p| format!(" ({p})"));
            let how = if test.uses == test.broken {
                String::new()
            } else {
                format!(", which depends on `{}`", test.broken)
            };
            let why = if test.own {
                format!("it has an error{at}")
            } else {
                format!("it uses `{}`{how}, which has an error{at}", test.uses)
            };
            let result = TestResult {
                name: test.name.clone(),
                namespace: test.namespace.clone(),
                outcome: Outcome::Failed,
                cached: false,
                hash: None,
                detail: None,
                unfinished: Some(why),
                assuming: Vec::new(),
            };
            let span_of = |r: &TestResult| self.test_span(&r.namespace, &r.name).map(order);
            let same_namespace = |r: &TestResult| r.namespace == test.namespace;
            let index = (results.iter())
                .position(|r| same_namespace(r) && span_of(r).is_some_and(|o| o > order(test.span)))
                .or_else(|| {
                    (results.iter())
                        .rposition(same_namespace)
                        .map(|last| last + 1)
                })
                .unwrap_or(results.len());
            results.insert(index, result);
        }
        results
    }

    fn part(&self, span: stitchwort_syntax::Span) -> Option<Part> {
        if span.file.index() >= self.sources.len() {
            return None;
        }
        let file = self.sources.get(span.file);
        let range = balanced_range(&file.text, span.range());
        let text = file.text.get(range.clone())?;
        let before = file.text.get(..range.start)?;
        let line = before.matches('\n').count() + 1;
        let column = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
        let one_line = text.split_whitespace().collect::<Vec<_>>().join(" ");
        let shown: String = if one_line.chars().count() > SHOWN_PART {
            let mut cut: String = one_line.chars().take(SHOWN_PART).collect();
            cut.push('…');
            cut
        } else {
            one_line
        };
        Some(Part {
            text: shown,
            file: file.name.clone(),
            line,
            column,
        })
    }

    /// The values of the sides of a comparison.
    fn compare(&self, op: &'static str, left: &Term, right: &Term) -> Comparison {
        let g = &self.elab.ev();
        // Each side is shown in an operation of its own, with a small limit
        // on the size of the value: a value too big to show is a marker, and
        // never a crash (quoting a very long list nests as deep as it is
        // long, which overflows the WebAssembly stack).
        let limits = Limits {
            size: SHOWN_SIDE_NODES,
            ..self.elab.options.limits
        };
        let show = |term: &Term| -> (String, Option<Term>) {
            let _op = g.machine.budget.operation(limits);
            let _erasing = g.machine.erasure.running();
            let Ok(v) = eval(g, &[], term) else {
                return ("…".to_string(), None);
            };
            match stitchwort_core::value::quote(g, 0, &v) {
                Ok(t) => (
                    cut_to(&stitchwort_core::pretty::term(g, &[], &t), SHOWN_SIDE),
                    Some(t),
                ),
                Err(_) => ("… (too large to show)".to_string(), None),
            }
        };
        let (left, left_term) = show(left);
        let (right, right_term) = show(right);
        let difference = match (op, &left_term, &right_term) {
            ("==" | "=", Some(l), Some(r)) => first_difference(g, l, r),
            _ => None,
        };
        let lines = |term: &Option<Term>| term.as_ref().and_then(|t| text_lines(g, t, SHOWN_SIDE));
        Comparison {
            op,
            left,
            right,
            left_lines: lines(&left_term),
            right_lines: lines(&right_term),
            difference,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_nextest_profile_names_the_tier_when_the_variable_does_not() {
        assert_eq!(tier_from(None, Some("full")), Tier::Full);
        assert_eq!(tier_from(None, Some("merge")), Tier::Merge);
        assert_eq!(tier_from(None, Some("lane-syntax")), Tier::Lane);
        assert_eq!(tier_from(None, Some("lane-search")), Tier::Lane);
        assert_eq!(tier_from(None, Some("daily")), Tier::Daily);
        assert_eq!(tier_from(None, Some("default")), Tier::Daily);
        assert_eq!(tier_from(None, None), Tier::Daily);
    }

    #[test]
    fn a_set_variable_wins_over_the_nextest_profile() {
        assert_eq!(tier_from(Some("daily"), Some("full")), Tier::Daily);
        assert_eq!(tier_from(Some(""), Some("full")), Tier::Daily);
        assert_eq!(tier_from(Some("merge"), Some("full")), Tier::Merge);
        assert_eq!(tier_from(Some("full"), Some("default")), Tier::Full);
    }

    #[test]
    #[should_panic(expected = "NEXTEST_PROFILE=ful")]
    fn an_unknown_nextest_profile_panics() {
        tier_from(None, Some("ful"));
    }

    #[test]
    fn a_part_keeps_the_brackets_the_parser_left_out_of_its_span() {
        let text = "a && (f x).y == 2 && g (z) == 1";
        // `f x).y == 2` is the span the parser gives; `g (z` likewise.
        let first = text.find("f x").unwrap();
        let range = first..text.find(" &&").map(|_| 17).unwrap();
        assert_eq!(&text[balanced_range(text, range)], "(f x).y == 2");
        let second = text.find("g (z").unwrap();
        assert_eq!(&text[balanced_range(text, second..second + 4)], "g (z)");
        assert_eq!(&text[balanced_range(text, 0..4)], "a &&");
    }

    fn session() -> Session {
        let mut session = Session::new();
        session
            .load(
                "cache-test.sw",
                "test \"passes\" := True\ntest \"fails\" := False\n",
            )
            .expect("the tests check");
        session
    }

    #[test]
    fn a_memory_cache_starts_empty_and_records_what_it_adds() {
        let session = session();
        let cache = Cache::memory([]);
        let results = session.run_tests(&cache);
        assert_eq!(results.len(), 2);
        assert!(!results.iter().any(|r| r.cached));
        let added = cache.added();
        assert_eq!(added.len(), 2);
        let modes = modes(&session.elab.ev());
        for (result, (key, outcome)) in results.iter().zip(&added) {
            assert_eq!(key, &Cache::key(&result.hash.expect("a hash"), &modes));
            assert_eq!(*outcome, result.outcome);
        }
        assert_eq!(added[0].1, Outcome::Passed);
        assert_eq!(added[1].1, Outcome::Failed);
    }

    #[test]
    fn a_memory_cache_reuses_known_results() {
        let session = session();
        let first = Cache::memory([]);
        let ran = session.run_tests(&first);
        let second = Cache::memory(first.added());
        let cached = session.run_tests(&second);
        assert!(cached.iter().all(|r| r.cached));
        assert_eq!(cached[0].outcome, ran[0].outcome);
        assert_eq!(cached[1].outcome, ran[1].outcome);
        assert!(second.added().is_empty());
    }

    #[test]
    fn a_key_for_another_modes_string_is_not_used() {
        let session = session();
        let results = session.run_tests(&Cache::disabled());
        let other: Vec<_> = results
            .iter()
            .map(|r| {
                (
                    Cache::key(&r.hash.expect("a hash"), "n0c0-other"),
                    r.outcome,
                )
            })
            .collect();
        let cache = Cache::memory(other);
        let results = session.run_tests(&cache);
        assert!(!results.iter().any(|r| r.cached));
        assert_eq!(cache.added().len(), 2);
    }
}
