//! Running tests: the code that decides what a test computes once its term
//! is fixed, and so the only part of this crate in the test cache's key
//! (`build.rs`, [`crate::driver::EVAL_FINGERPRINT`]). Anything that changes
//! which outcome a test gets belongs in this file; explaining a failure
//! ([`Session::failure`]) and the cache's file layout don't decide it.

use stitchwort_core::hash::def_hash;
use stitchwort_core::step::{Machine, Obs};
use stitchwort_core::value::{eval, force};
use stitchwort_core::{Ev, ResourceError, Term, Value};

use crate::driver::{Cache, Outcome, Session, TestResult};

/// The effective modes of evaluation, for the cache key: whether the native
/// implementations are used (`n1`) or not (`n0`), and whether text literals
/// are compact (`c1`) or constructors (`c0`).
pub fn modes(g: &Ev) -> String {
    format!(
        "n{}c{}",
        u8::from(!g.env.builtins().disable_natives),
        u8::from(g.env.builtins().compact_literals().is_some())
    )
}

/// Which evaluator runs a test.
#[derive(Clone, Copy)]
enum Runner {
    /// The reference evaluator, the type checker's own.
    Reference,
    /// The machine of `stitchwort-rt`, falling back to the reference
    /// evaluator.
    Machine,
}

/// Which of the session's tests to run.
type Selection<'a> = dyn Fn(&stitchwort_elab::TestDecl) -> bool + 'a;

/// Tests lowered for the machine.
struct TestMachine {
    program: stitchwort_rt::Program,
}

impl TestMachine {
    /// The outcome of the test `def` on `machine`, if it was lowered and
    /// finished there: running out of resources is left to the reference
    /// evaluator, whose limits a test's result is reported against.
    fn run(
        &self,
        machine: &mut stitchwort_rt::Machine,
        def: stitchwort_core::DefId,
        partial: Option<stitchwort_rt::Limits>,
    ) -> Option<Outcome> {
        let global = self.program.globals.iter().position(|g| g.def == def)?;
        let global = stitchwort_rt::ir::GlobalId(u32::try_from(global).ok()?);
        machine.reset_steps();
        let value = match partial {
            // A test that runs partial code (D1183) is a `Delay`, stepped
            // as `stitchwort run` steps a partial `main`, on a machine of
            // its own.
            Some(limits) => {
                let mut own = stitchwort_rt::Machine::new(&self.program, limits);
                own.global(global)
                    .map_err(stitchwort_rt::host::RunError::from)
                    .and_then(|delay| stitchwort_rt::run_partial(own, limits, delay))
            }
            None => machine.global(global).map_err(Into::into),
        };
        match value {
            Ok(stitchwort_rt::value::Value::Tag(tag)) => {
                Some(if tag == self.program.shapes.true_ {
                    Outcome::Passed
                } else {
                    Outcome::Failed
                })
            }
            _ => None,
        }
    }
}

impl Session {
    /// Runs every test of the program loaded so far, using cached results
    /// where possible. The core's and the library's tests aren't the
    /// program's (docs/proposals/std-library.md §4.7): see
    /// [`Session::run_library_tests`].
    pub fn run_tests(&self, cache: &Cache) -> Vec<TestResult> {
        self.run_selected(cache, &|test| !test.library, Runner::Reference)
    }

    /// [`Session::run_tests`], for only the tests `keep` keeps.
    pub fn run_tests_where(
        &self,
        cache: &Cache,
        keep: impl Fn(&stitchwort_elab::TestDecl) -> bool,
    ) -> Vec<TestResult> {
        self.run_selected(
            cache,
            &|test| !test.library && keep(test),
            Runner::Reference,
        )
    }

    /// [`Session::run_tests`], on the machine of `stitchwort-rt`
    /// (docs/proposals/fast-runtime.md) where it can: a test it can't lower
    /// or finish runs on the reference evaluator, which also still explains
    /// a failure (SW-412).
    pub fn run_tests_fast(&self, cache: &Cache) -> Vec<TestResult> {
        self.run_selected(cache, &|test| !test.library, Runner::Machine)
    }

    /// Runs the tests of the core and of the library files loaded (all of
    /// them, in [`Session::with_library_tests`]).
    pub fn run_library_tests(&self, cache: &Cache) -> Vec<TestResult> {
        self.run_selected(cache, &|test| test.library, Runner::Reference)
    }

    /// The tests `selected` that `cache` has no result for, lowered together
    /// for the machine, if they can be. One that can't be lowered with the
    /// others is left out (and runs on the reference evaluator).
    fn lower_tests(&self, cache: &Cache, selected: &Selection, modes: &str) -> Option<TestMachine> {
        let g = &self.elab.ev();
        let wanted: Vec<stitchwort_core::DefId> = self
            .elab
            .tests()
            .iter()
            .filter(|test| selected(test))
            .filter(|test| {
                let _op = g.machine.budget.operation(self.elab.options.limits);
                match def_hash(g, test.def) {
                    Ok(Some(hash)) => cache
                        .get(&Cache::unit(&test.namespace, &test.name), &hash, modes)
                        .is_none(),
                    _ => false,
                }
            })
            .map(|test| test.def)
            .collect();
        if wanted.is_empty() {
            return None;
        }
        let lower = |ids: &[stitchwort_core::DefId]| {
            stitchwort_rt::lower_definitions(g, self.elab.options.limits, ids).ok()
        };
        // Together, so what they share is lowered once; one at a time only
        // if some test can't be lowered.
        let program = lower(&wanted).or_else(|| {
            let lowerable: Vec<_> = wanted
                .iter()
                .copied()
                .filter(|id| lower(&[*id]).is_some())
                .collect();
            lower(&lowerable)
        })?;
        Some(TestMachine { program })
    }

    fn run_selected(&self, cache: &Cache, selected: &Selection, runner: Runner) -> Vec<TestResult> {
        let g = &self.elab.ev();
        // A result is kept per runner: the two are only differentially
        // tested to agree (docs/proposals/fast-runtime.md).
        let modes = match runner {
            Runner::Reference => modes(g),
            Runner::Machine => format!("{}m", modes(g)),
        };
        let lowered = match runner {
            Runner::Reference => None,
            Runner::Machine => self.lower_tests(cache, selected, &modes),
        };
        let mut machine = lowered.as_ref().map(|lowered| {
            stitchwort_rt::Machine::new(
                &lowered.program,
                stitchwort_rt::Limits::from_core(self.elab.options.limits),
            )
        });
        self.elab
            .tests()
            .iter()
            .filter(|test| selected(test))
            .map(|test| {
                // Each test is one operation, with its own resource limits:
                // hashing it, then running it unless its result is cached.
                let _op = g.machine.budget.operation(self.elab.options.limits);
                let hash = match def_hash(g, test.def) {
                    Ok(hash) => hash.expect("tests are checked before they run"),
                    Err(e) => {
                        return TestResult {
                            name: test.name.clone(),
                            namespace: test.namespace.clone(),
                            outcome: Outcome::OutOfResources(e),
                            cached: false,
                            hash: None,
                            detail: None,
                        };
                    }
                };
                let unit = Cache::unit(&test.namespace, &test.name);
                if let Some(outcome) = cache.get(&unit, &hash, &modes) {
                    return TestResult {
                        name: test.name.clone(),
                        namespace: test.namespace.clone(),
                        outcome,
                        cached: true,
                        hash: Some(hash),
                        detail: self.failure(test, outcome),
                    };
                }
                // A test that runs partial code is a `Delay` (D1183).
                let partial = self.elab.is_partial(test.def).unwrap_or(false);
                let on_machine = match (&lowered, &mut machine) {
                    (Some(lowered), Some(machine)) => lowered.run(
                        machine,
                        test.def,
                        partial.then(|| stitchwort_rt::Limits::from_core(self.elab.options.limits)),
                    ),
                    _ => None,
                };
                let outcome = on_machine.unwrap_or_else(|| {
                    let value = if partial {
                        self.run_partial(&Term::Def(test.def))
                    } else {
                        // Proofs and types aren't computed (`erase.rs`).
                        let _erasing = g.machine.erasure.running();
                        eval(g, &[], &Term::Def(test.def)).and_then(|v| force(g, v))
                    };
                    match value {
                        // `Bool` is `False | True`: constructor 1 is `True`.
                        Ok(Value::Ctor(_, 1, _)) => Outcome::Passed,
                        Ok(_) => Outcome::Failed,
                        Err(e) => Outcome::OutOfResources(e),
                    }
                });
                cache.verify_result(test, &hash, &modes, outcome);
                cache.put(&unit, &hash, &modes, outcome);
                TestResult {
                    name: test.name.clone(),
                    namespace: test.namespace.clone(),
                    outcome,
                    cached: false,
                    hash: Some(hash),
                    detail: self.failure(test, outcome),
                }
            })
            .collect()
    }

    /// Steps `term`, a partial computation that performs nothing (a test
    /// that runs partial code, D1183), to its result, as [`Session::run_main`]
    /// steps `main`: each stretch between two ticks is one operation, with
    /// its own resource limits, and there's no tick limit.
    pub(crate) fn run_partial(&self, term: &Term) -> Result<Value, ResourceError> {
        let g = &self.elab.ev();
        let _erasing = g.machine.erasure.running();
        let mut machine = {
            let _op = g.machine.budget.operation(self.elab.options.limits);
            Machine::start(g, force(g, eval(g, &[], term)?)?)
        };
        loop {
            let _op = g.machine.budget.operation(self.elab.options.limits);
            match machine.step(g)? {
                Obs::Now(v) => return force(g, v),
                Obs::Later(rest) => machine = rest,
                Obs::Call(..) => unreachable!("a test performs nothing"),
            }
        }
    }
}
