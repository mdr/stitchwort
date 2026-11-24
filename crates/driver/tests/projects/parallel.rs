//! `check --jobs N` (docs/proposals/parallel-checking.md §9.5): a parallel
//! fill of the check cache, then the sequential check over it, must report
//! what a sequential check reports, and leave the same entries.
//!
//! Each test checks a small project with one job into one cache, and with
//! several into another (on disk, given the first one's salt, or in
//! memory), and compares what was reported, what the session holds
//! (`canonical_dump`) and the entries byte for byte.

use std::path::{Path, PathBuf};
use std::rc::Rc;

use stitchwort_driver::check_cache::{CheckCache, MemoryStore};
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::nav::index_json;
use stitchwort_driver::parallel::{Fill, Jobs, fill};
use stitchwort_driver::project::{
    DiskFiles, Files, Load, MemoryFiles, Target, analyse, assert_holds_no_stated_theorem,
    project_sources,
};
use stitchwort_driver::render::render;
use stitchwort_elab::cache::{Stats, Store, canonical_dump, canonical_dump_without_proofs};
use stitchwort_elab::timings;

use crate::check_cache::STACK;

/// Where a check keeps its entries.
#[derive(Clone)]
enum Kept {
    Dir(PathBuf),
    Memory(MemoryStore),
}

impl Kept {
    fn store(&self) -> Rc<dyn Store> {
        match self {
            Kept::Dir(dir) => Rc::new(CheckCache::at(dir)),
            Kept::Memory(memory) => Rc::new(memory.clone()),
        }
    }
}

/// What a check reported and left.
struct Checked {
    /// Whether it passed, and every diagnostic, rendered.
    report: String,
    /// What the session holds afterwards.
    dump: String,
    fill: Fill,
    /// The check after the fill's cache counts.
    stats: Stats,
    /// The navigation index (`check --index`), for a navigable check.
    index: Option<String>,
}

/// Checks the project in `files` with `jobs` workers, keeping entries in
/// `kept`; `load` as `check` (`Diagnostics`) or a command that uses it all.
fn check(
    files: &(dyn Files + Sync),
    kept: &Kept,
    jobs: usize,
    seed: Option<u64>,
    load: Load,
) -> Checked {
    check_target(files, kept, jobs, seed, load, &Target::Everything)
}

/// [`check`] of `target` rather than the whole project.
fn check_target(
    files: &(dyn Files + Sync),
    kept: &Kept,
    jobs: usize,
    seed: Option<u64>,
    load: Load,
    target: &Target,
) -> Checked {
    check_as("par", files, kept, jobs, seed, load, target, false)
}

/// [`check_target`], with the sessions recording what code navigation needs
/// when `navigable`, and the index of what was loaded in the result, as
/// `check --index` writes it.
#[allow(clippy::too_many_arguments)]
fn check_as(
    project: &str,
    files: &(dyn Files + Sync),
    kept: &Kept,
    jobs: usize,
    seed: Option<u64>,
    load: Load,
    target: &Target,
    navigable: bool,
) -> Checked {
    let make: &(dyn Fn(usize) -> Session + Sync) = if navigable {
        &Session::navigable_for_stack
    } else {
        &Session::for_stack
    };
    with_stack(STACK, || {
        let mut session = make(STACK);
        session.elab.set_check_cache(kept.store());
        let make_store = || kept.store();
        let fill = fill(
            files,
            project,
            target,
            &Jobs {
                count: jobs,
                stack: STACK,
                make_session: make,
                make_store: &make_store,
                seed,
            },
        );
        // As `check` does: everything loaded if the fill left a namespace.
        let load = fill.load_after(load);
        let result = session.load_project_for(files, project, target, load);
        let diagnostics = match &result {
            Ok(_) => session.warnings.clone(),
            Err(ds) => ds.clone(),
        };
        let mut report = format!("accepted {}\n", result.is_ok());
        for d in &diagnostics {
            report.push_str(&render(&session.sources, d, false));
        }
        let checked = Checked {
            report,
            dump: canonical_dump(&session.elab),
            fill,
            stats: session.elab.check_cache_stats(),
            index: navigable.then(|| index_json(&session, result.is_err(), None, "", &diagnostics)),
        };
        std::mem::forget(session);
        checked
    })
}

/// A new, empty directory.
fn temp_dir(name: &str) -> PathBuf {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-parallel-{name}-{}-{n}-{nanos}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// A directory whose cache has `like`'s salt, so that the same entries are
/// the same bytes in both.
fn salted_like(like: &Path, name: &str) -> PathBuf {
    let dir = temp_dir(name);
    std::fs::create_dir_all(dir.join("check")).unwrap();
    std::fs::copy(like.join("check/header"), dir.join("check/header")).unwrap();
    dir
}

/// The entries in a cache directory: file name and bytes.
fn entries(dir: &Path) -> Vec<(String, Vec<u8>)> {
    let mut found: Vec<(String, Vec<u8>)> = std::fs::read_dir(dir.join("check"))
        .unwrap()
        .flatten()
        .map(|e| e.file_name().to_string_lossy().to_string())
        .filter(|name| name != "header" && !name.starts_with(".tmp-"))
        .map(|name| {
            let bytes = std::fs::read(dir.join("check").join(&name)).unwrap();
            (name, bytes)
        })
        .collect();
    found.sort();
    found
}

/// Whether `dir` holds an entry for project namespace `ns`.
fn has_entry(dir: &Path, ns: &str) -> bool {
    let unit = format!("-ns.{ns}");
    entries(dir).iter().any(|(name, _)| {
        name.find(&unit).is_some_and(|at| {
            let rest = &name[at + unit.len()..];
            rest.starts_with('-') || rest.starts_with('+')
        })
    })
}

/// A diamond (`Base` under `Left` and `Right`, both under `Top`) beside a
/// chain (`One` → `Two` → `Three`, over `Base`), with `left` as
/// `Par.Left`'s body.
fn diamond_and_chain(left: &str, config: &str) -> MemoryFiles {
    let file = |ns: &str, imports: &[&str], body: &str| {
        let mut text = format!("namespace Par.{ns}\nimport Std (Nat)\n");
        for import in imports {
            text.push_str(&format!("import Par.{import} (..)\n"));
        }
        text.push('\n');
        text.push_str(body);
        text.push('\n');
        (format!("src/Par/{ns}.sw"), text)
    };
    let files = [
        ("stitchwort.yaml".to_string(), config.to_string()),
        file("Base", &[], "def base: Nat := 3"),
        file("Left", &["Base"], left),
        file("Right", &["Base"], "def right: Nat := base + 2"),
        file("Top", &["Left", "Right"], "def top: Nat := left + right"),
        file("One", &["Base"], "def one: Nat := base + 1"),
        file("Two", &["One"], "def two: Nat := one + 1"),
        file("Three", &["Two"], "def three: Nat := two + 1"),
    ];
    MemoryFiles {
        files: files.into_iter().collect(),
        reversed: false,
    }
}

const CONFIG: &str = "sources: [src]\n";

/// Asserts that `parallel` reported and holds what `sequential` did, and
/// that its fill ran cleanly.
fn assert_same(sequential: &Checked, parallel: &Checked, what: &str) {
    assert_eq!(
        sequential.report, parallel.report,
        "{what}: the reports differ"
    );
    assert!(
        sequential.dump == parallel.dump,
        "{what}: the sessions differ"
    );
    let fill = &parallel.fill;
    assert!(
        fill.ran && fill.filled > 0,
        "{what}: nothing was filled: {fill:?}"
    );
    assert_eq!(fill.twice, 0, "{what}: a dependency was elaborated again");
    assert_eq!(fill.stats.refused, 0, "{what}: {fill:?}");
    assert_eq!(fill.stats.late_misses, 0, "{what}: {fill:?}");
    assert_eq!(parallel.stats.refused, 0, "{what}");
    assert_eq!(parallel.stats.late_misses, 0, "{what}");
    assert_eq!(fill.claims_gave_up, 0, "{what}");
}

/// The standing byte-compare: on the diamond and chain, the copied
/// par_check project and an example project, four jobs leave the bytes one
/// job leaves, on disk, and report and hold the same, on disk and in
/// memory.
#[test]
fn four_jobs_report_and_write_what_one_job_does() {
    let projects: Vec<(&str, Box<dyn Files + Sync>)> = vec![
        (
            "diamond and chain",
            Box::new(diamond_and_chain("def left: Nat := base + 1", CONFIG)),
        ),
        (
            "par_project",
            Box::new(DiskFiles {
                root: Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("tests/projects/parallel/par_project"),
            }),
        ),
        (
            "trip-journal",
            Box::new(DiskFiles {
                root: Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../../examples/projects/accept/trip-journal"),
            }),
        ),
    ];
    for (what, files) in &projects {
        let one = temp_dir("one");
        let sequential = check(&**files, &Kept::Dir(one.clone()), 1, None, Load::Everything);
        assert!(!sequential.fill.ran);
        let four = salted_like(&one, "four");
        let parallel = check(
            &**files,
            &Kept::Dir(four.clone()),
            4,
            None,
            Load::Everything,
        );
        assert_same(&sequential, &parallel, what);
        assert!(
            entries(&one) == entries(&four),
            "{what}: the entries differ"
        );
        let memory = MemoryStore::default();
        let in_memory = check(
            &**files,
            &Kept::Memory(memory.clone()),
            4,
            None,
            Load::Everything,
        );
        assert_same(&sequential, &in_memory, &format!("{what}, in memory"));
        assert_eq!(memory.len(), entries(&one).len(), "{what}: in memory");
        // A plain check over the cache the fill made reports the same.
        let plain = check(
            &**files,
            &Kept::Dir(four.clone()),
            4,
            None,
            Load::Diagnostics,
        );
        assert_eq!(sequential.report, plain.report, "{what}: a warm check");
        assert!(!plain.fill.ran, "{what}: a warm cache was filled again");
        let _ = std::fs::remove_dir_all(&one);
        let _ = std::fs::remove_dir_all(&four);
    }
}

/// Random schedules (`STITCHWORT_JOBS_SEED`): whatever order the workers
/// load and check namespaces in, the entries are the same bytes (the
/// invariant that load order doesn't reach an entry, §9.4 item 2).
#[test]
fn random_schedules_write_the_same_entries() {
    let files = diamond_and_chain("def left: Nat := base + 1", CONFIG);
    let one = temp_dir("seeds-one");
    let sequential = check(&files, &Kept::Dir(one.clone()), 1, None, Load::Everything);
    let expected = entries(&one);
    for seed in 0..20 {
        let dir = salted_like(&one, "seed");
        let parallel = check(
            &files,
            &Kept::Dir(dir.clone()),
            3,
            Some(seed),
            Load::Everything,
        );
        assert_same(&sequential, &parallel, &format!("seed {seed}"));
        assert!(entries(&dir) == expected, "seed {seed}: the entries differ");
        let _ = std::fs::remove_dir_all(&dir);
    }
    let _ = std::fs::remove_dir_all(&one);
}

/// A failure in the middle of the graph (an error, an open goal, a syntax
/// error in `Par.Left`): reported as with one job, everything not above it
/// filled, and what is above it left to the check after the fill.
#[test]
fn a_failure_is_reported_as_with_one_job_and_the_rest_is_filled() {
    let cases = [
        ("an error", "def left: Nat := base + true", CONFIG),
        (
            "an open goal",
            "def left: Nat := base + 1\n\ntheorem leftIsFour: left = 4 := ?",
            "sources: [src]\ncheck:\n  open-goals: warn\n",
        ),
        ("a syntax error", "def left: Nat := (base +", CONFIG),
    ];
    // The timings' rows count each elaboration of a namespace.
    timings::request(1);
    for (what, left, config) in cases {
        let files = diamond_and_chain(left, config);
        let one = temp_dir("fail-one");
        let sequential = check(&files, &Kept::Dir(one.clone()), 1, None, Load::Diagnostics);
        assert!(
            sequential.report.contains("Par/Left.sw"),
            "{what}: the fixture didn't fail in Par.Left: {}",
            sequential.report
        );
        let four = salted_like(&one, "fail-four");
        let before = timings::rows_labelled("Par.Left");
        let parallel = check(&files, &Kept::Dir(four.clone()), 4, None, Load::Diagnostics);
        assert_eq!(sequential.report, parallel.report, "{what}");
        assert!(parallel.fill.ran, "{what}: {:?}", parallel.fill);
        assert_eq!(
            parallel.fill.left, 2,
            "{what}: Left and Top: {:?}",
            parallel.fill
        );
        for ns in ["Par.Base", "Par.Right", "Par.One", "Par.Two", "Par.Three"] {
            assert!(has_entry(&four, ns), "{what}: no entry for {ns}");
        }
        assert!(
            !has_entry(&four, "Par.Left"),
            "{what}: an entry for Par.Left"
        );
        // Left to the check after the fill, which writes what one job
        // writes: nothing above an error, but a namespace above an open goal
        // has an entry (keyed to the unfinished namespace's source).
        assert_eq!(
            has_entry(&one, "Par.Top"),
            has_entry(&four, "Par.Top"),
            "{what}"
        );
        assert!(
            entries(&one) == entries(&four),
            "{what}: the entries differ"
        );
        // `Par.Left` is elaborated once by a worker (unless it has a syntax
        // error, which no worker is given) and once after the fill: not
        // twice after it, left out unloaded and then all again after the
        // error (SW-4719's review, F1).
        let elaborated = timings::rows_labelled("Par.Left") - before;
        let expected = if what == "a syntax error" { 1 } else { 2 };
        assert_eq!(elaborated, expected, "{what}: Par.Left elaborated");
        let _ = std::fs::remove_dir_all(&one);
        let _ = std::fs::remove_dir_all(&four);
    }
}

/// One job when there's nothing to share out: a warm cache, or `--only`.
#[test]
fn a_warm_cache_or_only_runs_no_fill() {
    let files = diamond_and_chain("def left: Nat := base + 1", CONFIG);
    let dir = temp_dir("warm");
    let cold = check(&files, &Kept::Dir(dir.clone()), 4, None, Load::Diagnostics);
    assert!(cold.fill.ran);
    let warm = check(&files, &Kept::Dir(dir.clone()), 4, None, Load::Diagnostics);
    assert!(!warm.fill.ran, "{:?}", warm.fill);
    assert_eq!(cold.report, warm.report);
    let only = with_stack(STACK, || {
        let make_store = || Kept::Dir(dir.clone()).store();
        fill(
            &files,
            "par",
            &Target::Theorems {
                namespaces: vec![],
                only: vec!["Par.Top.top".into()],
            },
            &Jobs {
                count: 4,
                stack: STACK,
                make_session: &Session::for_stack,
                make_store: &make_store,
                seed: None,
            },
        )
    });
    assert!(!only.ran);
    let _ = std::fs::remove_dir_all(&dir);
}

/// Workers needing the same uncached library file (`Ord/Ord.sw`, which
/// the prelude doesn't load) at once elaborate it once between them: the
/// others wait for its entry (`ClaimStore`).
#[test]
fn library_files_are_elaborated_once_between_workers() {
    let file = |ns: &str| {
        (
            format!("src/Par/{ns}.sw"),
            format!(
                "namespace Par.{ns}\nimport Std (Nat)\n\n\
                 def {}: Nat := Std.Ord.max 1 2\n",
                ns.to_lowercase()
            ),
        )
    };
    let files = MemoryFiles {
        files: [
            ("stitchwort.yaml".to_string(), CONFIG.to_string()),
            file("A"),
            file("B"),
            file("C"),
        ]
        .into_iter()
        .collect(),
        reversed: false,
    };
    let one = temp_dir("claims-one");
    let sequential = check(&files, &Kept::Dir(one.clone()), 1, None, Load::Diagnostics);
    assert!(
        sequential.stats.misses > 0,
        "no library file was elaborated"
    );
    let three = temp_dir("claims-three");
    let parallel = check(
        &files,
        &Kept::Dir(three.clone()),
        3,
        None,
        Load::Diagnostics,
    );
    assert_eq!(sequential.report, parallel.report);
    assert_eq!(
        parallel.fill.stats.misses + parallel.stats.misses,
        sequential.stats.misses,
        "a library file was elaborated twice: {:?}",
        parallel.fill
    );
    assert_eq!(parallel.fill.claims_gave_up, 0);
    let _ = std::fs::remove_dir_all(&one);
    let _ = std::fs::remove_dir_all(&three);
}

/// A worker that claimed a library file and finished elaborating it
/// without writing an entry (it failed) lets go of the claim at once, so
/// another waiting for it reads again and elaborates it, rather than
/// waiting out the claims' patience (SW-4723).
#[test]
fn an_abandoned_library_file_does_not_stall_a_waiting_worker() {
    use std::sync::Arc;
    use std::time::{Duration, Instant};
    use stitchwort_driver::check_cache::{ClaimStore, Claims};

    let claims = Arc::new(Claims::new(Duration::from_secs(60)));
    let memory = MemoryStore::default();
    let key = [7u8; 32];
    let unit = "std.Failing";
    let owner = ClaimStore::new(Rc::new(memory.clone()), claims.clone(), 0);
    owner.begin_job();
    assert_eq!(owner.read(unit, &key), None, "the owner claims the file");
    let started = Instant::now();
    let waited = std::thread::scope(|scope| {
        let waiter = scope.spawn(|| {
            let store = ClaimStore::new(Rc::new(memory.clone()), claims.clone(), 1);
            store.begin_job();
            store.read(unit, &key)
        });
        std::thread::sleep(Duration::from_millis(200));
        owner.abandon(unit, &key);
        waiter.join().unwrap()
    });
    assert_eq!(waited, None);
    assert!(
        started.elapsed() < Duration::from_secs(10),
        "the waiter waited for the patience to run out"
    );
    assert_eq!(claims.gave_up(), 0);
}

/// A namespace's entry doesn't depend on what else its session loaded
/// first: `Par.B`'s constructor `Floor` shares its short name with
/// `Par.A`'s, and B checked after A in one session (as one job checks
/// them, or a worker that took A first) writes the bytes B checked on its
/// own does (SW-4731: the names were ordered by their place among every
/// `Floor` in the session).
#[test]
fn an_entry_is_the_same_whatever_the_session_loaded_before() {
    let file = |ns: &str, body: &str| {
        (
            format!("src/Par/{ns}.sw"),
            format!("namespace Par.{ns}\nimport Std (Nat)\n\n{body}\n"),
        )
    };
    let files = MemoryFiles {
        files: [
            ("stitchwort.yaml".to_string(), CONFIG.to_string()),
            file("A", "type Tile = | Wall | Floor"),
            file(
                "B",
                "type Cell = | Roll | Floor\n\ntype Room = | Floor | Door",
            ),
        ]
        .into_iter()
        .collect(),
        reversed: false,
    };
    let both = temp_dir("order-both");
    check(&files, &Kept::Dir(both.clone()), 1, None, Load::Diagnostics);
    let alone = salted_like(&both, "order-alone");
    let only_b = Target::Namespaces(vec!["Par.B".to_string()]);
    check_target(
        &files,
        &Kept::Dir(alone.clone()),
        1,
        None,
        Load::Diagnostics,
        &only_b,
    );
    let b = |dir: &Path| {
        entries(dir)
            .into_iter()
            .find(|(name, _)| name.contains("-ns.Par.B-"))
    };
    let (from_both, from_alone) = (b(&both), b(&alone));
    assert!(from_both.is_some(), "no entry for Par.B");
    assert!(
        from_both == from_alone,
        "Par.B's entry depends on Par.A being loaded first"
    );
    let _ = std::fs::remove_dir_all(&both);
    let _ = std::fs::remove_dir_all(&alone);
}

/// Stage 2 (parallel-checking.md §10.4): theorems over four namespaces,
/// `Par.Uses` and `Par.Side` both over `Par.Facts`, so that a worker that
/// didn't check `Par.Facts` loads it from its entry without the proofs.
/// `bumpId` (recursive), `bumpFn`, `bumpTwo`, the `@[reading]` theorem and
/// the mutual pair `evenBump` and `oddBump` load as stated theorems;
/// `secretSucc`, with an `unfolding` list, loads whole, and so does
/// `bumpBack`, recursive through a lifted `match` helper. (No instance
/// theorem: an instance's type is an interface applied to a type, and no
/// source shape found makes that a proposition.)
fn theorems_project() -> MemoryFiles {
    let file = |ns: &str, body: &str| (format!("src/Par/{ns}.sw"), body.to_string());
    let files = [
        ("stitchwort.yaml".to_string(), CONFIG.to_string()),
        file(
            "Facts",
            "namespace Par.Facts\n\
             import Std (Nat, Eq, Bool, Iff)\n\n\
             def bump (n: Nat): Nat := match n with\n  \
               | Zero => Zero\n  \
               | Succ k => Succ (bump k)\n\n\
             theorem bumpId ∀ (n: Nat): bump n = n := match n with\n  \
               | Zero => byComputing\n  \
               | Succ n => Eq.cong Succ (bumpId n)\n\n\
             theorem bumpFn ∀ (n: Nat): bump n = n := bumpId n\n\n\
             theorem bumpTwo: bump 2 = 2 := byComputing\n\n\
             type InRange (lo x hi: Nat): Prop = { low: lo ≤ x, high: x ≤ hi }\n\n\
             def inRange (lo x hi: Nat): Bool := lo <= x && x <= hi\n\n\
             theorem fwd ∀ (lo x hi: Nat) (h: inRange lo x hi): InRange lo x hi :=\n  \
               { low = h.left, high = h.right }\n\n\
             @[reading]\n\
             theorem inRangeReads ∀ (lo x hi: Nat): inRange lo x hi ↔ InRange lo x hi :=\n  \
               { forward = fwd lo x hi, backward = r => Both r.low r.high }\n\n\
             opaque def secret (n: Nat): Nat := Succ n\n\n\
             theorem secretSucc ∀ (n: Nat): secret n = Succ n\n  \
               unfolding secret\n\
             := byComputing\n\n\
             theorem evenBump ∀ (n: Nat): bump n = n := match n with\n  \
               | Zero => byComputing\n  \
               | Succ k => Eq.cong Succ (oddBump k)\n\n\
             theorem oddBump ∀ (n: Nat): bump n = n := match n with\n  \
               | Zero => byComputing\n  \
               | Succ k => Eq.cong Succ (evenBump k)\n\n\
             theorem bumpBack ∀ (n: Nat): n = bump n := Eq.flipped (match n with\n  \
               | Zero => byComputing\n  \
               | Succ k => Eq.cong Succ (bumpBack k).flipped)\n",
        ),
        file(
            "Uses",
            "namespace Par.Uses\n\
             import Std (Nat, Eq)\n\
             import Par.Facts (..)\n\n\
             theorem bumpTwice ∀ (n: Nat): bump (bump n) = n :=\n  \
               Eq.trans (bumpId (bump n)) (bumpId n)\n\n\
             theorem below ∀ (lo x hi: Nat) (h: inRange lo x hi): x ≤ hi :=\n  \
               match h with | { low, high } => high\n\n\
             def partial: ∀ (n: Nat) => bump n = n := bumpFn\n",
        ),
        file(
            "Top",
            "namespace Par.Top\n\
             import Std (Nat, Eq)\n\
             import Par.Uses (..)\n\
             import Par.Facts (..)\n\n\
             theorem bumpThrice ∀ (n: Nat): bump (bump (bump n)) = n :=\n  \
               Eq.trans (bumpTwice (bump n)) (bumpId n)\n\n\
             def three: Nat := bump 3\n",
        ),
        file(
            "Side",
            "namespace Par.Side\n\
             import Std (Nat, Eq)\n\
             import Par.Facts (..)\n\n\
             theorem bumpFour: bump 4 = 4 := bumpFn 4\n",
        ),
    ];
    MemoryFiles {
        files: files.into_iter().collect(),
        reversed: false,
    }
}

/// Workers load the namespaces below the one they check without their
/// proofs, as stated theorems, and still write the bytes one job writes
/// and leave the check after them reporting and holding the same, for any
/// schedule.
#[test]
fn workers_loading_without_proofs_write_what_one_job_does() {
    let files = theorems_project();
    let one = temp_dir("stated-one");
    let sequential = check(&files, &Kept::Dir(one.clone()), 1, None, Load::Everything);
    assert!(
        sequential.report.starts_with("accepted true"),
        "{}",
        sequential.report
    );
    for seed in [None, Some(1), Some(2), Some(3), Some(4), Some(5)] {
        let dir = salted_like(&one, "stated-two");
        // `Par.Facts` has an entry before the fill, so whichever worker
        // checks `Par.Uses` or `Par.Side` loads it from there: a worker
        // that checked a namespace itself holds it whole, and on a project
        // this small one worker may take every job before another starts.
        let facts = Target::Namespaces(vec!["Par.Facts".to_string()]);
        let kept = Kept::Dir(dir.clone());
        check_target(&files, &kept, 1, None, Load::Diagnostics, &facts);
        let parallel = check(&files, &Kept::Dir(dir.clone()), 2, seed, Load::Everything);
        assert_same(&sequential, &parallel, &format!("seed {seed:?}"));
        assert!(
            parallel.fill.stats.stated > 0,
            "seed {seed:?}: no worker loaded a theorem without its proof: {:?}",
            parallel.fill
        );
        assert_eq!(parallel.stats.stated, 0, "the check after the fill");
        assert!(
            entries(&one) == entries(&dir),
            "seed {seed:?}: the entries differ"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
    let _ = std::fs::remove_dir_all(&one);
}

/// A session that loads each namespace of `files` from `kept` in turn, as
/// a worker does, with or without proofs.
fn load_each(files: &MemoryFiles, kept: &Kept, without_proofs: bool) -> Session {
    let mut session = Session::for_stack(STACK);
    session.elab.set_check_cache(kept.store());
    session.elab.set_load_without_proofs(without_proofs);
    let sources = project_sources(files, "par", &mut session.sources).unwrap();
    let analysis = analyse(&mut session, "par", sources);
    let prepared = session
        .prepare_analysis("par", &analysis, &Target::Everything)
        .unwrap();
    for name in &prepared.order {
        let ns = analysis.namespace(name).unwrap();
        let (found, _) = session.check_project_namespace(&analysis, ns);
        assert!(found.is_empty(), "{name}: {found:?}");
    }
    session
}

/// From a warm cache, a load without proofs holds everything a whole load
/// does but the theorems' proofs (`canonical_dump_without_proofs`), with
/// nothing refused or missed. And a session loaded for a command that uses
/// what it loads holds no stated theorem, even when asked to load without
/// proofs (C1 of docs/reviews/SW-4734-fable-review.md), where the same
/// session that only checks does.
#[test]
fn a_load_without_proofs_holds_all_but_the_proofs_and_never_reaches_a_command_that_reads_them() {
    let files = theorems_project();
    let memory = MemoryStore::default();
    let kept = Kept::Memory(memory);
    with_stack(STACK, || {
        let cold = load_each(&files, &kept, false);
        std::mem::forget(cold);
        let whole = load_each(&files, &kept, false);
        let without = load_each(&files, &kept, true);
        for session in [&whole, &without] {
            let stats = session.elab.check_cache_stats();
            assert_eq!(stats.namespace_hits, 4, "{stats:?}");
            assert_eq!((stats.refused, stats.late_misses), (0, 0), "{stats:?}");
        }
        assert_eq!(whole.elab.check_cache_stats().stated, 0);
        assert!(without.elab.check_cache_stats().stated >= 3);
        assert!(without.elab.holds_stated_theorems());
        assert!(
            canonical_dump_without_proofs(&whole.elab)
                == canonical_dump_without_proofs(&without.elab),
            "a load without proofs holds something else"
        );
        assert!(canonical_dump(&whole.elab) != canonical_dump(&without.elab));
        // The theorem with an `unfolding` list loads whole and prints whole
        // in both sessions; the recursive theorem and the mutual pair are
        // stated. `bumpId`'s `match` is its whole body, on a parameter, so
        // it becomes the theorem's own case tree, not a helper: a group of
        // one that refers to itself, which a stated theorem can stand for
        // (its body and `recursive` flag have no reader outside the
        // cache). `bumpBack`'s `match`, under `Eq.flipped`, is lifted and
        // calls the theorem, so joins its group; the helper is no theorem,
        // and the group's hash covers its body, so the group loads whole.
        let whole_dump = canonical_dump(&whole.elab);
        let group_of = |name: &str| {
            let line = (whole_dump.lines())
                .find(|l| l.starts_with("def ") && l.contains(&format!(" Par.Facts.{name} ")))
                .unwrap_or_else(|| panic!("no {name} in the dump"));
            let id = line.split(' ').nth(1).unwrap();
            let group = line
                .split(" group ")
                .nth(1)
                .unwrap()
                .split(" theorem ")
                .next();
            (id.to_string(), group.unwrap().to_string())
        };
        let (id, group) = group_of("bumpId");
        assert_eq!(group, format!("Some([{id}])"), "bumpId has a helper");
        let (id, group) = group_of("bumpBack");
        let helper = group_of("bumpBack.%match1").0;
        assert_eq!(group, format!("Some([{id}, {helper}])"));
        let dump = canonical_dump(&without.elab);
        for (name, stated) in [
            ("secretSucc", false),
            ("bumpId", true),
            ("evenBump", true),
            ("oddBump", true),
            ("bumpBack", false),
        ] {
            let line = dump
                .lines()
                .find(|l| l.starts_with("def ") && l.contains(&format!(" Par.Facts.{name} ")))
                .unwrap_or_else(|| panic!("no {name} in the dump"));
            assert!(
                line.contains(&format!("stated {stated} ")),
                "{name} loaded the wrong way: {line}"
            );
        }
        assert!(
            dump.lines()
                .any(|l| l.contains(" Par.Facts.secretSucc ") && !l.contains("unfolding []")),
            "secretSucc lost its unfolding list"
        );
        let reporting = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            assert_holds_no_stated_theorem(&without);
        }));
        assert!(reporting.is_err(), "the invariant's check let one through");
        std::mem::forget(whole);
        std::mem::forget(without);

        let mut session = Session::for_stack(STACK);
        session.elab.set_check_cache(kept.store());
        session.elab.set_load_without_proofs(true);
        let loaded = session.load_project_for(&files, "par", &Target::Everything, Load::Everything);
        assert!(loaded.is_ok());
        assert!(!session.elab.holds_stated_theorems());
        assert_eq!(session.elab.check_cache_stats().stated, 0);
        std::mem::forget(session);
    });
}

/// Instances in sibling namespaces (`Rich.Left`, `Rich.Right`, each its own
/// type over `Rich.Base`'s interface), a theorem whose `match` is lifted
/// into a `%match` helper (`bumpBack`, under `Eq.flipped`), different
/// uncached library files per branch (`Ord/Ord.sw` under `Left`,
/// `List/Toolkit.sw` under `Right`), and `Rich.Top` over both.
fn rich_project() -> MemoryFiles {
    let file = |ns: &str, body: &str| (format!("src/Rich/{ns}.sw"), body.to_string());
    let files = [
        ("stitchwort.yaml".to_string(), CONFIG.to_string()),
        file(
            "Base",
            "namespace Rich.Base\n\
             import Std (Nat, Eq)\n\n\
             interface Weigh (a: Type) = { weight: a → Nat }\n\n\
             def bump (n: Nat): Nat := match n with\n  \
               | Zero => Zero\n  \
               | Succ k => Succ (bump k)\n\n\
             theorem bumpBack ∀ (n: Nat): n = bump n := Eq.flipped (match n with\n  \
               | Zero => byComputing\n  \
               | Succ k => Eq.cong Succ (bumpBack k).flipped)\n",
        ),
        file(
            "Left",
            "namespace Rich.Left\n\
             import Std (Nat, Eq)\n\
             import Rich.Base (..)\n\n\
             type Box = | MkBox (size: Nat)\n\n\
             instance Box.instWeigh: Weigh Box := { weight = match | MkBox n => bump n }\n\n\
             def biggest: Nat := Std.Ord.max 1 2\n\n\
             theorem leftBack ∀ (n: Nat): n = bump n := bumpBack n\n",
        ),
        file(
            "Right",
            "namespace Rich.Right\n\
             import Std (Nat, List)\n\
             import Rich.Base (..)\n\n\
             type Crate = | MkCrate (width: Nat) (depth: Nat)\n\n\
             instance Crate.instWeigh: Weigh Crate := { weight = match | MkCrate a b => a + b }\n\n\
             def bumped: List Nat := [1, 2].map (n => bump n)\n",
        ),
        file(
            "Top",
            "namespace Rich.Top\n\
             import Std (Nat)\n\
             import Rich.Base (..)\n\
             import Rich.Left (..)\n\
             import Rich.Right (..)\n\n\
             def total: Nat := Weigh.weight (MkBox 1) + Weigh.weight (MkCrate 2 3)\n",
        ),
    ];
    MemoryFiles {
        files: files.into_iter().collect(),
        reversed: false,
    }
}

/// Over `rich_project`, whatever the schedule, `Rich.Base`'s entry already
/// there (so a worker loads it without proofs rather than checking it, on a
/// project this small where one worker may take every job): the report, the
/// session, the entries and the `--index` are what one job gives.
#[test]
fn random_schedules_over_instances_theorems_and_library_files_match_one_job() {
    let files = rich_project();
    let one = temp_dir("rich-one");
    let sequential = check_as(
        "rich",
        &files,
        &Kept::Dir(one.clone()),
        1,
        None,
        Load::Everything,
        &Target::Everything,
        true,
    );
    assert!(
        sequential.report.starts_with("accepted true"),
        "{}",
        sequential.report
    );
    let expected = entries(&one);
    for seed in 0..8 {
        let dir = salted_like(&one, "rich-seed");
        let base = Target::Namespaces(vec!["Rich.Base".to_string()]);
        check_as(
            "rich",
            &files,
            &Kept::Dir(dir.clone()),
            1,
            None,
            Load::Diagnostics,
            &base,
            true,
        );
        let parallel = check_as(
            "rich",
            &files,
            &Kept::Dir(dir.clone()),
            3,
            Some(seed),
            Load::Everything,
            &Target::Everything,
            true,
        );
        assert_same(&sequential, &parallel, &format!("seed {seed}"));
        assert!(
            sequential.index == parallel.index,
            "seed {seed}: the --index differs"
        );
        assert!(entries(&dir) == expected, "seed {seed}: the entries differ");
        assert!(
            parallel.fill.stats.stated > 0,
            "seed {seed}: no worker loaded a theorem without its proof: {:?}",
            parallel.fill
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
    let _ = std::fs::remove_dir_all(&one);
}
