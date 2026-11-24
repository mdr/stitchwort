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
use stitchwort_driver::parallel::{Fill, Jobs, fill};
use stitchwort_driver::project::{DiskFiles, Files, Load, MemoryFiles, Target};
use stitchwort_driver::render::render;
use stitchwort_elab::cache::{Stats, Store, canonical_dump};

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
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session.elab.set_check_cache(kept.store());
        let make_store = || kept.store();
        let fill = fill(
            files,
            "par",
            &Target::Everything,
            &Jobs {
                count: jobs,
                stack: STACK,
                make_session: &Session::for_stack,
                make_store: &make_store,
                seed,
            },
        );
        let result = session.load_project_for(files, "par", &Target::Everything, load);
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
