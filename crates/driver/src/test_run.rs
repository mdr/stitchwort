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
enum Runner<'a> {
    /// The reference evaluator, the type checker's own.
    Reference,
    /// The machine of `stitchwort-rt`, falling back to the reference
    /// evaluator.
    Machine,
    /// Native code, compiled by `native`, falling back to the machine.
    Native(&'a dyn NativeTests),
}

/// What `stitchwort test --native` gives the driver to run tests as native
/// code: the compiler, which is in `stitchwort-native` (Cranelift), a crate
/// this one doesn't depend on, since the playground's WebAssembly build
/// uses it. Native code runs what the machine would, so a test it can't
/// run, for whatever reason, runs on the machine instead, and the outcome
/// is the machine's.
pub trait NativeTests {
    /// `program` compiled to native code, with a way into each constant of
    /// `roots` (global numbers), and the stack in bytes its runs need under
    /// `limits` (the thread's stack must be at least that); or why it
    /// can't be, as lines.
    fn compile(
        &self,
        program: &stitchwort_rt::Program,
        roots: &[u32],
        limits: stitchwort_rt::Limits,
    ) -> Result<NativeTestCode, Vec<String>>;

    /// Says `line`, about what ran natively and what didn't, if asked to
    /// (`--verbose`).
    fn note(&self, line: &str);
}

/// The tests' native code, from [`NativeTests::compile`].
pub struct NativeTestCode {
    pub code: Box<dyn stitchwort_rt::native_abi::NativeIslands>,
    /// The stack its runs reserve, in bytes (`native_abi::native_stack`).
    pub stack: usize,
    /// The limits its runs enforce: the session's, with native code's own
    /// frame limit ([`stitchwort_rt::Limits::for_native`]).
    pub limits: stitchwort_rt::Limits,
    /// What was compiled, for [`NativeTests::note`].
    pub summary: String,
}

/// The tests' native code, running: one executor for every test, so a
/// constant computed for one (a parsed input) is kept for the next, as on
/// the machine.
struct NativeTestRun {
    executor: stitchwort_rt::native_abi::NativeExecutor,
    true_: u32,
}

impl NativeTestRun {
    /// The outcome of the test `def` run natively, or why it wasn't: not
    /// compiled, out of resources (for the machine to try, and then the
    /// reference evaluator, whose limits a result is reported against), or
    /// not a `Bool`.
    fn run(
        &mut self,
        lowered: &TestMachine,
        def: stitchwort_core::DefId,
        partial: Option<stitchwort_rt::Limits>,
    ) -> Result<Outcome, String> {
        use stitchwort_rt::Executor as _;
        let global = lowered
            .global(def)
            .ok_or_else(|| "it wasn't lowered".to_string())?;
        self.executor.reset_steps();
        let value = match partial {
            // Stepped as on the machine, and as the machine runs it on a
            // machine of its own, with none of the constants other tests
            // computed, so that it costs the same steps and frames.
            Some(limits) => {
                let kept = self.executor.set_aside_globals();
                let value = self.executor.global(global.0).map(|value| {
                    value
                        .map_err(stitchwort_rt::host::RunError::from)
                        .and_then(|delay| {
                            stitchwort_rt::run_partial_on(&mut self.executor, limits, delay)
                        })
                });
                self.executor.restore_globals(kept);
                value
            }
            None => self
                .executor
                .global(global.0)
                .map(|v| v.map_err(Into::into)),
        };
        let value = value.ok_or_else(|| "it wasn't compiled".to_string())?;
        match value {
            Ok(stitchwort_rt::value::Value::Tag(tag)) => Ok(if tag == self.true_ {
                Outcome::Passed
            } else {
                Outcome::Failed
            }),
            Ok(_) => Err("its value isn't a `Bool`".to_string()),
            Err(e) => Err(e.to_string()),
        }
    }
}

/// Which of the session's tests to run.
type Selection<'a> = dyn Fn(&stitchwort_elab::TestDecl) -> bool + 'a;

/// Tests lowered for the machine.
struct TestMachine {
    program: stitchwort_rt::Program,
}

impl TestMachine {
    /// The global of the test `def`, if it was lowered.
    fn global(&self, def: stitchwort_core::DefId) -> Option<stitchwort_rt::ir::GlobalId> {
        let global = self.program.globals.iter().position(|g| g.def == def)?;
        Some(stitchwort_rt::ir::GlobalId(u32::try_from(global).ok()?))
    }

    /// The tests `defs` compiled to native code by `native`, where they're
    /// constants that were lowered, or `None`, with a note saying why.
    fn compile_native(
        &self,
        native: &dyn NativeTests,
        defs: &[stitchwort_core::DefId],
        limits: stitchwort_rt::Limits,
    ) -> Option<NativeTestRun> {
        let roots: Vec<u32> = defs
            .iter()
            .filter_map(|&def| self.global(def))
            .filter(|g| {
                matches!(
                    self.program.globals[g.0 as usize].kind,
                    stitchwort_rt::ir::GlobalKind::Constant { .. }
                )
            })
            .map(|g| g.0)
            .collect();
        if roots.is_empty() {
            return None;
        }
        match native.compile(&self.program, &roots, limits) {
            Ok(code) => {
                native.note(&code.summary);
                Some(NativeTestRun {
                    executor: stitchwort_rt::native_abi::NativeExecutor::new(
                        code.code,
                        code.limits,
                        code.stack,
                    ),
                    true_: self.program.shapes.true_,
                })
            }
            Err(why) => {
                native.note("native: the tests can't be compiled, so they run on the machine:");
                for line in why {
                    native.note(&format!("  {line}"));
                }
                None
            }
        }
    }

    /// The outcome of the test `def` on `machine`, if it was lowered and
    /// finished there: running out of resources is left to the reference
    /// evaluator, whose limits a test's result is reported against.
    fn run(
        &self,
        machine: &mut stitchwort_rt::Machine,
        def: stitchwort_core::DefId,
        partial: Option<stitchwort_rt::Limits>,
    ) -> Option<Outcome> {
        let global = self.global(def)?;
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
    /// Why `test` can't run, as the message of its failure, or `None` if
    /// it can. It can't if it relies on, or waits for, gaps in code (open
    /// goals, or declarations with an error standing in for their
    /// statements), which the message names with where each is, or uses an
    /// unfinished declaration. A gap that is a proof (or a type) is erased
    /// when the test runs, so a test that only mentions a theorem with a
    /// `?` or an error still runs (D3525).
    fn unfinished_message(&self, test: &stitchwort_elab::TestDecl) -> Option<String> {
        let relies = self.elab.relies_on_goal(test.def);
        let ids: std::collections::BTreeSet<_> = if relies {
            let relied = self.elab.goals_relied_on(test.def);
            let g = &self.elab.ev();
            let code: std::collections::BTreeSet<_> = relied
                .iter()
                .copied()
                .filter(|id| !stitchwort_core::erase::of_def(g, *id).is_some_and(|e| e.result))
                .collect();
            if code.is_empty() && !relied.is_empty() {
                return None;
            }
            code
        } else {
            self.elab.blocked_on(test.def).into_iter().collect()
        };
        let goals = self.goal_places(&ids);
        if goals.is_empty() {
            return Some(match &test.unfinished {
                Some(uses) => format!("`{uses}` isn't written yet: it has an open goal `?`"),
                None => "it uses a declaration that isn't written yet: it has an open goal `?`"
                    .to_string(),
            });
        }
        // The declaration the test names that leads to the gap, when it is
        // the only one: "it uses `twice`, which depends on `broken`".
        let through = (test.unfinished.as_deref())
            .map(crate::reliance::short_name)
            .filter(|_| goals.len() == 1);
        let named: Vec<String> = goals
            .iter()
            .take(3)
            .map(|g| match (g.is_error(), relies) {
                (false, _) => format!(
                    "`{}` isn't written yet: its body is `?` ({})",
                    g.short(),
                    g.place()
                ),
                (true, true) => match through.filter(|uses| *uses != g.short()) {
                    Some(uses) => format!(
                        "it uses `{uses}`, which depends on `{}`, which has an error ({})",
                        g.short(),
                        g.place()
                    ),
                    None => format!(
                        "it uses `{}`, which has an error ({})",
                        g.short(),
                        g.place()
                    ),
                },
                (true, false) => format!(
                    "it can't be checked until `{}` is fixed ({})",
                    g.short(),
                    g.place()
                ),
            })
            .collect();
        let more = match goals.len() {
            0..=3 => String::new(),
            n => format!("; and {} more", n - 3),
        };
        Some(format!("{}{more}", named.join("; ")))
    }

    /// [`Self::unfinished_message`] for a test that is unfinished at all.
    fn unfinished_message_if_unfinished(&self, test: &stitchwort_elab::TestDecl) -> Option<String> {
        self.elab
            .is_unfinished(test.def)
            .then(|| self.unfinished_message(test))
            .flatten()
    }

    /// The gaps `test` relies on, for a passing test's `(assuming …)`
    /// (SW-2939, D3525): the proofs and types it mentions, open goals or
    /// declarations with an error, which are erased when it runs. Empty for
    /// a test that relies on none.
    fn test_assuming(&self, test: &stitchwort_elab::TestDecl) -> Vec<crate::reliance::GoalPlace> {
        let goals = self.elab.goals_relied_on(test.def);
        self.goal_places(&goals)
    }

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

    /// [`Session::run_tests_fast`], for only the tests `keep` keeps.
    pub fn run_tests_fast_where(
        &self,
        cache: &Cache,
        keep: impl Fn(&stitchwort_elab::TestDecl) -> bool,
    ) -> Vec<TestResult> {
        self.run_selected(cache, &|test| !test.library && keep(test), Runner::Machine)
    }

    /// [`Session::run_tests_fast_where`], as native code where it can
    /// (`stitchwort test --native`): compiled by `native`, with a test it
    /// can't run going to the machine, and from there to the reference
    /// evaluator, as before. Results are cached under native code's own key,
    /// since its deeper recursion limit means an outcome at the limit can
    /// differ from the machine's.
    pub fn run_tests_native_where(
        &self,
        cache: &Cache,
        keep: impl Fn(&stitchwort_elab::TestDecl) -> bool,
        native: &dyn NativeTests,
    ) -> Vec<TestResult> {
        self.run_selected(
            cache,
            &|test| !test.library && keep(test),
            Runner::Native(native),
        )
    }

    /// Runs the tests of the core and of the library files loaded (all of
    /// them, in [`Session::with_library_tests`]).
    pub fn run_library_tests(&self, cache: &Cache) -> Vec<TestResult> {
        self.run_selected(cache, &|test| test.library, Runner::Reference)
    }

    /// The tests `selected` that `cache` has no result for, lowered together
    /// for the machine, if they can be, with those tests. One that can't be
    /// lowered with the others is left out (and runs on the reference
    /// evaluator).
    fn lower_tests(
        &self,
        cache: &Cache,
        selected: &Selection,
        modes: &str,
    ) -> Option<(TestMachine, Vec<stitchwort_core::DefId>)> {
        let g = &self.elab.ev();
        let wanted: Vec<stitchwort_core::DefId> = self
            .elab
            .tests()
            .iter()
            .filter(|test| selected(test) && self.unfinished_message_if_unfinished(test).is_none())
            // Run on the reference evaluator, which notes a transport on an
            // erased proof ([`Session::run_relying`]).
            .filter(|test| !self.elab.relies_on_goal(test.def))
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
        Some((TestMachine { program }, wanted))
    }

    fn run_selected(&self, cache: &Cache, selected: &Selection, runner: Runner) -> Vec<TestResult> {
        let g = &self.elab.ev();
        // A result is kept per runner: the two are only differentially
        // tested to agree (docs/proposals/fast-runtime.md).
        // Native code has its own recursion limit, deeper than the
        // machine's, so a test at the limit can differ between them.
        let modes = match runner {
            Runner::Reference => modes(g),
            Runner::Machine => format!("{}m", modes(g)),
            Runner::Native(_) => format!("{}x", modes(g)),
        };
        let limits = stitchwort_rt::Limits::from_core(self.elab.options.limits);
        let (lowered, wanted) = match runner {
            Runner::Reference => (None, Vec::new()),
            Runner::Machine | Runner::Native(_) => self
                .lower_tests(cache, selected, &modes)
                .map_or((None, Vec::new()), |(lowered, wanted)| {
                    (Some(lowered), wanted)
                }),
        };
        let mut native = match (runner, &lowered) {
            (Runner::Native(native), Some(lowered)) => {
                lowered.compile_native(native, &wanted, limits)
            }
            _ => None,
        };
        // Made when a test first needs it: with native code, perhaps never.
        let mut machine: Option<stitchwort_rt::Machine> = None;
        let (mut ran_natively, mut not_natively) = (0usize, 0usize);
        let results = self
            .elab
            .tests()
            .iter()
            .filter(|test| selected(test))
            .map(|test| {
                // Each test is one operation, with its own resource limits:
                // hashing it, then running it unless its result is cached.
                let _op = g.machine.budget.operation(self.elab.options.limits);
                if let Some(why) = self.unfinished_message_if_unfinished(test) {
                    return TestResult {
                        name: test.name.clone(),
                        namespace: test.namespace.clone(),
                        outcome: Outcome::Failed,
                        cached: false,
                        hash: None,
                        detail: None,
                        unfinished: Some(why),
                        assuming: Vec::new(),
                    };
                }
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
                            unfinished: None,
                            assuming: Vec::new(),
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
                        unfinished: None,
                        assuming: self.test_assuming(test),
                    };
                }
                // A test that runs partial code is a `Delay` (D1183).
                let partial = self.elab.is_partial(test.def).unwrap_or(false);
                if self.elab.relies_on_goal(test.def) {
                    let outcome = match self.run_relying(test, partial) {
                        Ok(outcome) => outcome,
                        Err(why) => {
                            return TestResult {
                                name: test.name.clone(),
                                namespace: test.namespace.clone(),
                                outcome: Outcome::Failed,
                                cached: false,
                                hash: None,
                                detail: None,
                                unfinished: Some(why),
                                assuming: Vec::new(),
                            };
                        }
                    };
                    cache.verify_result(test, &hash, &modes, outcome);
                    cache.put(&unit, &hash, &modes, outcome);
                    return TestResult {
                        name: test.name.clone(),
                        namespace: test.namespace.clone(),
                        outcome,
                        cached: false,
                        hash: Some(hash),
                        detail: self.failure(test, outcome),
                        unfinished: None,
                        assuming: self.test_assuming(test),
                    };
                }
                let on_native = match (&lowered, &mut native) {
                    (Some(lowered), Some(native)) => {
                        match native.run(lowered, test.def, partial.then_some(limits)) {
                            Ok(outcome) => {
                                ran_natively += 1;
                                Some(outcome)
                            }
                            Err(why) => {
                                not_natively += 1;
                                if let Runner::Native(n) = runner {
                                    n.note(&format!(
                                        "native: test \"{}\" runs on the machine: {why}",
                                        test.name
                                    ));
                                }
                                None
                            }
                        }
                    }
                    _ => None,
                };
                let on_machine = on_native.or_else(|| {
                    let lowered = lowered.as_ref()?;
                    let machine = machine.get_or_insert_with(|| {
                        stitchwort_rt::Machine::new(&lowered.program, limits)
                    });
                    lowered.run(machine, test.def, partial.then_some(limits))
                });
                let outcome =
                    on_machine.unwrap_or_else(|| self.run_on_reference(test.def, partial));
                cache.verify_result(test, &hash, &modes, outcome);
                cache.put(&unit, &hash, &modes, outcome);
                TestResult {
                    name: test.name.clone(),
                    namespace: test.namespace.clone(),
                    outcome,
                    cached: false,
                    hash: Some(hash),
                    detail: self.failure(test, outcome),
                    unfinished: None,
                    assuming: Vec::new(),
                }
            })
            .collect();
        if let Runner::Native(native) = runner
            && ran_natively + not_natively > 0
        {
            native.note(&format!(
                "native: {ran_natively} test(s) ran natively, {not_natively} on the machine"
            ));
        }
        results
    }

    /// The outcome of the test `def` on the reference evaluator.
    fn run_on_reference(&self, def: stitchwort_core::DefId, partial: bool) -> Outcome {
        let g = &self.elab.ev();
        let value = if partial {
            self.run_partial(&Term::Def(def))
        } else {
            // Proofs and types aren't computed (`erase.rs`).
            let _erasing = g.machine.erasure.running();
            eval(g, &[], &Term::Def(def)).and_then(|v| force(g, v))
        };
        match value {
            // `Bool` is `False | True`: constructor 1 is `True`.
            Ok(Value::Ctor(_, 1, _)) => Outcome::Passed,
            Ok(_) => Outcome::Failed,
            Err(e) => Outcome::OutOfResources(e),
        }
    }

    /// The outcome of `test`, which relies on gaps that are proofs, or why
    /// it has none. Erasure is sound only for true proofs, and a gap's
    /// statement may be false: then `J` on it takes its base as if it held,
    /// casting a value to the wrong type, and the run may compute nonsense
    /// or crash the evaluator. So it runs on the reference evaluator, which
    /// notes every transport on an erased proof, and a run with one gives no
    /// result, as does a crash. The note can't say which proof it was, so a
    /// test that also transports along a true proof isn't run either.
    fn run_relying(
        &self,
        test: &stitchwort_elab::TestDecl,
        partial: bool,
    ) -> Result<Outcome, String> {
        let g = &self.elab.ev();
        g.machine.erasure.take_transported();
        let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.run_on_reference(test.def, partial)
        }));
        let transported = g.machine.erasure.take_transported();
        let gaps = crate::reliance::describe_goals(&self.test_assuming(test), true);
        match run {
            Ok(outcome) if !transported => Ok(outcome),
            _ if transported => Err(format!("it computes with a proof, and relies on {gaps}")),
            _ => Err(format!(
                "no result: the evaluator stopped with an internal error, and it relies on {gaps}"
            )),
        }
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
