//! [`Options`]: the settings and test switches fixed when the session is
//! built. They say how to check, not what was checked: a rewind leaves them
//! as they are, and nothing the elaborator does changes them. The host (or
//! a test) sets them after [`crate::Elaborator::new`], before the first
//! load.
//!
//! The ones that change what elaborating a library file gives are part of
//! the check cache's key ([`Options::cache_key`]).

use std::rc::Rc;

use stitchwort_core::budget::Limits;

use crate::{cache, counterexample};

#[derive(Default)]
pub struct Options {
    /// Evaluation steps one `rewrite`'s comparisons may use between them;
    /// `None` is the default (`rewrite.rs`). Tests set it small.
    pub rewrite_budget: Option<u64>,
    /// Whether the `test`s of the core and the library files are checked
    /// (the library test target), instead of skipped.
    pub library_tests: bool,
    /// Resource limits for checking each declaration.
    pub limits: Limits,
    /// For tests only: compile number patterns the old way, as nested `Succ`
    /// patterns, even where a number case would do. Only usable with small
    /// numbers. Tests compare the two compilations.
    pub numbers_as_succ: bool,
    /// Whether declarations are elaborated with glued evaluation
    /// (`Kernel::glue`, docs/proposals/folded-calls.md): on unless
    /// `STITCHWORT_GLUE=0` (the library always glues, whatever this says:
    /// [`crate::Elaborator::gluing`]). The switch in the `Machine` is on only while a
    /// declaration or an expression typed in is elaborated
    /// ([`crate::Elaborator::glued`]), never while it is checked by the
    /// kernel or run.
    pub glue: bool,
    /// Whether a declaration that fails where a test fact is expected and
    /// a proof of its reading is given is checked again with the fact
    /// built there (`build.rs`, docs/proposals/bool-as-proposition-building.md):
    /// on unless `STITCHWORT_BUILD=0`, which gives the behaviour from
    /// before, for comparison.
    pub build: bool,
    /// For tests: the instance step budget, instead of the default.
    pub instance_budget: Option<usize>,
    /// For tests: `+ * < <=` on `Nat` and `Int` always find their
    /// dictionary and project its field, instead of building the term the
    /// projection would give directly when no dictionary of the interface is
    /// in scope (docs/proposals/interfaces.md §5.13, D187: the two must be
    /// the same).
    pub uniform_operators: bool,
    /// Where library files' results are kept between runs, if anywhere
    /// (`cache`). Installed by the host before anything loads.
    pub(crate) check_cache: Option<Rc<dyn cache::Store>>,
    /// For tests: every namespace replay fails part way
    /// (`fail_namespace_replays_late`).
    pub(crate) fail_replays_late: bool,
    /// For tests: a replayed entry is refused right after the group with
    /// the declaration of this full path is admitted and bound
    /// (`refuse_replays_after`).
    pub(crate) refuse_replays_after: Option<String>,
    /// For tests: generating the plain form of `f.unfold` for the
    /// `decreasing` definition with this name fails, as a compiler bug in
    /// it would (`decreasing.rs`, `plain_view_or_not`).
    #[doc(hidden)]
    pub refuse_plain_view: Option<String>,
    /// For the rewind test: a project's driver checks each namespace, rewinds
    /// to just before it, and checks it again (`rewind.rs`).
    #[doc(hidden)]
    pub recheck_namespaces: bool,
    /// Theorems of project namespaces that are not checked, by namespace
    /// and the name as written there: a `check` of only some theorems
    /// (`project::plan_theorems`, which says which are safe to leave out).
    /// A namespace with any is never read from or written to the check
    /// cache.
    pub skip_theorems: std::collections::BTreeMap<String, std::collections::BTreeSet<String>>,
    /// For the rewind test: every cache is emptied before every declaration
    /// (`Caches::clear`), which must change nothing.
    #[doc(hidden)]
    pub clear_caches_per_declaration: bool,
    /// Runs counterexample searches on the fast runtime (the driver's);
    /// without one they run on the reference evaluator
    /// (`counterexample.rs`).
    pub counterexample_runner: Option<counterexample::FastRunner>,
    /// For tests: no counterexample search when a theorem fails.
    pub no_counterexamples: bool,
    /// For tests: keep each failure-time search's log in
    /// `Presentation::counterexample_log`. Off otherwise, since a kept
    /// session would grow it with every request (SW-1818).
    pub log_counterexamples: bool,
    /// Searches stop at their count of inputs, never at their wall-time
    /// limit: for the benchmarks, whose counts must be the same on every
    /// run (a timed search tries as many inputs as the machine manages), and
    /// for tests, whose snapshots would lose a counterexample note under
    /// load. `Elaborator::new` starts it from
    /// `STITCHWORT_UNTIMED_COUNTEREXAMPLES=1`.
    pub untimed_counterexamples: bool,
    /// For tests that change the prelude: a pinned declaration
    /// (`stitchwort_core::pins`) that isn't the pinned one is bound without
    /// its native, and runs as written, instead of refusing the library.
    #[doc(hidden)]
    #[cfg(feature = "test-bypass")]
    pub stale_pins_fall_back: bool,
}

impl Options {
    /// The options a new elaborator starts with: glued evaluation
    /// (docs/proposals/folded-calls.md) is on while elaborating, and
    /// `STITCHWORT_GLUE=0` turns it off, for comparison; building test
    /// facts is on unless `STITCHWORT_BUILD=0`;
    /// `STITCHWORT_UNTIMED_COUNTEREXAMPLES=1` (set for the workspace's
    /// tests by `.cargo/config.toml`) is `untimed_counterexamples`.
    pub(crate) fn from_env() -> Options {
        Options {
            glue: std::env::var("STITCHWORT_GLUE").map_or(true, |v| v != "0"),
            build: std::env::var("STITCHWORT_BUILD").map_or(true, |v| v != "0"),
            untimed_counterexamples: std::env::var("STITCHWORT_UNTIMED_COUNTEREXAMPLES")
                .is_ok_and(|v| v == "1"),
            ..Options::default()
        }
    }

    /// The settings that change what elaborating a library file gives, as
    /// part of the check cache's key (`cache::Elaborator::modes`). The
    /// text is part of the cache's format: changing it makes every entry
    /// miss.
    pub(crate) fn cache_key(&self) -> String {
        let Options {
            rewrite_budget,
            limits,
            numbers_as_succ,
            instance_budget,
            uniform_operators,
            glue,
            build,
            // Not usable with the library test target (`cache_usable`).
            library_tests: _,
            // Where entries are kept, and a test's way of making replays fail.
            check_cache: _,
            fail_replays_late: _,
            refuse_replays_after: _,
            // Names a test's own definition.
            refuse_plain_view: _,
            // Drives the rewind test.
            recheck_namespaces: _,
            // Namespaces with theorems skipped bypass the cache.
            skip_theorems: _,
            // Caches only save work.
            clear_caches_per_declaration: _,
            // Counterexample searches only run when a theorem fails, and
            // a library file's don't.
            counterexample_runner: _,
            no_counterexamples: _,
            log_counterexamples: _,
            untimed_counterexamples: _,
            // Only for a changed prelude, which is checked from source.
            #[cfg(feature = "test-bypass")]
                stale_pins_fall_back: _,
        } = self;
        format!(
            "succ {} limits {} {} {} {} rewrite {:?} instances {:?} uniform {} glue {} build {}",
            numbers_as_succ,
            limits.work,
            limits.stack,
            limits.size,
            limits.frames,
            rewrite_budget,
            instance_budget,
            uniform_operators,
            glue,
            build,
        )
    }
}
