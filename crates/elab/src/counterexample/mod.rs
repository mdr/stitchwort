//! Counterexample search (docs/proposals/counterexample-search.md,
//! D1154-D1159), stages 1 and 2.
//!
//! When a theorem's statement checks but its proof doesn't (or its whole
//! proof is `?`), the statement is tried on inputs: small ones first, then
//! random larger ones. An input that makes every hypothesis true and the
//! conclusion false is a counterexample: the statement is false, and the
//! error says so in a note. `stitchwort check --counterexamples` runs the
//! same search on every theorem, with a larger budget (D1159).
//!
//! - The statement is turned into a *checker* (§6.1), an ordinary closed
//!   term: a function of the statement's data parameters to a `Nat`, `j` if
//!   hypothesis `j` is false (the input is discarded), `k` (the number of
//!   hypotheses) if the conclusion holds, `k + 1` if it's false. Each
//!   hypothesis and the conclusion is decided by the decision search `if`
//!   uses (`bind::decide`), each hypothesis's proof in scope for the rest.
//!   Type parameters are `Nat` (D1157); instance parameters are found at
//!   `Nat`. A statement nothing decides, or with a parameter there are no
//!   inputs for, is out of scope: nothing is said.
//! - Inputs come from the parameters' types ([`inputs`], §5): first every
//!   input up to a size, smallest total size first, so a counterexample
//!   found then is a smallest one; then random inputs of a growing size,
//!   seeded from the statement, and a counterexample found then is shrunk
//!   (§5.5).
//! - The checker runs on the fast runtime when the host gives one
//!   ([`FastRunner`], the driver's), else on the reference evaluator, as
//!   tests do; a counterexample is run again on the reference evaluator
//!   before it's shown (§6.2). A [`Budget`] limits the inputs and, where
//!   there's a clock, the time (D1154).
//! - It's advisory: nothing here makes a declaration check, and finding no
//!   counterexample is never shown on a failing proof (§8).

mod inputs;

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{eval, force, quote};
use stitchwort_core::{BigUint, DefId, Globals, Icit, Limits, Name, Sort, Term, Value};

use crate::check::{Ctx, builtin_data, builtin_def};
use crate::{Elaborator, shown};
use inputs::{Inputs, Rng};

/// How much one search may do (§6.3): inputs tried (half enumerated, half
/// random), and wall time where there's a clock.
#[derive(Clone, Copy, Debug)]
pub struct Budget {
    pub inputs: usize,
    pub millis: u64,
}

/// The search on a failing proof (D1154).
pub const ON_FAILURE: Budget = Budget {
    inputs: MAX_INPUTS,
    millis: TIME_LIMIT_MS,
};

/// The search `check --counterexamples` runs on each theorem by default
/// (§6.3; `--counterexample-budget` changes the time).
pub const ON_REQUEST: Budget = Budget {
    inputs: 10_000,
    millis: 500,
};

/// The most inputs a search on a failing proof tries (§6.3).
pub const MAX_INPUTS: usize = 2000;

/// The wall-time backstop of a search on a failing proof (§6.3).
pub const TIME_LIMIT_MS: u64 = 200;

/// Evaluation steps one input may take on the fast runtime.
pub const FAST_STEPS: u64 = 1_000_000;

/// Evaluation steps one input may take on the reference evaluator.
pub const REFERENCE_STEPS: u64 = 1_000_000;

/// Evaluation steps confirming a counterexample on the reference
/// evaluator may take.
const CONFIRM_STEPS: u64 = 50_000_000;

/// After this many inputs in a row ran out of steps, or this many in all,
/// the search stops.
const OUT_OF_STEPS_IN_A_ROW: usize = 20;
const OUT_OF_STEPS: usize = 50;

/// The size the random inputs grow to (§5.1): a random list is up to this
/// long, a random number up to this large (or at a machine word's edge).
pub const RANDOM_SIZE: usize = 40;

/// The most rounds of shrinking (§5.5).
const SHRINK_ROUNDS: usize = 200;

/// Runs a checker on the fast runtime: `checker` applied to each of
/// `inputs` in turn (closed terms, one per data parameter), telling `each`
/// the input's index and its result (`None` if it didn't finish); stops
/// when `each` says to. Returns `false`, having run nothing, if the
/// checker can't run there (the reference evaluator runs it instead).
pub type FastRunner = fn(
    g: &Globals,
    limits: Limits,
    checker: &Term,
    inputs: &[Vec<Term>],
    each: &mut dyn FnMut(usize, Option<u64>) -> bool,
) -> bool;

/// Which evaluator ran a search.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Runner {
    Fast,
    Reference,
}

/// Which phase of a search found its counterexample (§5.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Enumerated,
    Random,
}

/// What one search did, for tests, measurements and
/// `check --counterexamples`.
#[derive(Clone, Debug, Default)]
pub struct SearchLog {
    /// The theorem's name.
    pub theorem: String,
    /// Why it wasn't searched, if it wasn't (out of scope).
    pub out_of_scope: Option<String>,
    pub runner: Option<Runner>,
    /// Inputs enumerated, and those run (enumerated and random).
    pub inputs: usize,
    pub tried: usize,
    /// Random inputs run.
    pub random: usize,
    /// Inputs some hypothesis was false for.
    pub discarded: usize,
    pub out_of_steps: usize,
    /// The largest total size enumerated, and the size random inputs grew
    /// to.
    pub enumerated_size: usize,
    pub random_size: usize,
    /// Whether the enumeration covered every input there is.
    pub exhaustive: bool,
    /// The counterexample's bindings as shown, if one was found; the phase
    /// that found it; and how many times it was shrunk.
    pub found: Option<Vec<String>>,
    pub found_by: Option<Phase>,
    pub shrinks: usize,
    /// Whether the fast runtime's counterexample was not confirmed by the
    /// reference evaluator (an internal error).
    pub disagreed: bool,
    /// Whether the time limit stopped it.
    pub timed_out: bool,
    /// Microseconds the search took, where there's a clock.
    pub micros: Option<u64>,
}

/// One step of a statement's telescope that the checker binds.
enum Step {
    /// A data parameter: an input.
    Data { name: Name, ty: Term },
    /// Hypothesis `index`, decided by `decision`.
    Hypothesis {
        index: usize,
        prop: Term,
        decision: Term,
    },
}

/// A statement made runnable.
struct Checker {
    /// `x1 … xn => …: Nat`, closed.
    term: Term,
    /// The data parameters: name and closed type.
    params: Vec<(Name, Value)>,
    hypotheses: usize,
    /// The hypotheses as shown, `b <= a`.
    shown_hypotheses: Vec<String>,
    /// The type parameters taken as `Nat`.
    type_params: Vec<Name>,
    /// The conclusion as shown.
    shown_conclusion: String,
    /// If the conclusion is written as an equation: its sides, inside the
    /// statement's binders.
    sides: Option<(Term, Term)>,
    /// What each of the statement's binders stands for, in order.
    slots: Vec<Slot>,
}

/// How a batch of inputs ran.
struct Batch {
    /// The index of the first counterexample.
    found: Option<usize>,
    /// Whether the fast runtime ran it.
    fast: bool,
    /// Whether too many inputs ran out of steps.
    stopped: bool,
}

/// What one of a statement's binders stands for in the checker.
enum Slot {
    /// Input `i`.
    Input(usize),
    /// A hypothesis's proof.
    Proof,
    /// A type parameter's type, or an instance found: a term in the scope
    /// of the binders before it.
    Fixed(Term),
}

impl Elaborator {
    /// After the theorem `def` failed, a note saying its statement is
    /// false, with a counterexample, if one is found. Leaves the
    /// metavariables cleared.
    pub(crate) fn counterexample_note(&mut self, def: DefId) -> Option<String> {
        if self.no_counterexamples {
            return None;
        }
        let (log, note) = self.search_counterexample(def, ON_FAILURE);
        self.counterexample_log.borrow_mut().push(log);
        note.map(|note| self.with_opaque_counterexample_note(def, note))
    }

    /// The search runs the program, so it uses the real body of an opaque
    /// definition the statement mentions; the proof can't, unless the theorem
    /// unfolds it (docs/proposals/opaque-definitions.md §6.10).
    fn with_opaque_counterexample_note(&self, def: DefId, note: String) -> String {
        let g = &self.globals;
        let Ok(statement) = quote(g, 0, &g.def(def).ty_value) else {
            return note;
        };
        let ids: Vec<DefId> = crate::opaque::declined_in(g, [&statement])
            .into_iter()
            .filter(|id| !g.def(def).unfolding.contains(id))
            .collect();
        if ids.is_empty() {
            return note;
        }
        let names: Vec<String> = ids
            .iter()
            .map(|id| format!("`{}`", g.def(*id).name))
            .collect();
        let (are, its) = if ids.len() == 1 {
            ("is", "its")
        } else {
            ("are", "their")
        };
        let clause: Vec<String> = ids.iter().map(|id| g.def(*id).name.to_string()).collect();
        format!(
            "{note}\nthe search ran the real code, but {} {are} opaque, so a proof can't use \
             {its} body unless the theorem says `unfolding {}`",
            names.join(", "),
            clause.join(", ")
        )
    }

    /// Searches the statement of theorem `def`, whether its proof checked
    /// or not, within `budget` (`check --counterexamples` runs it on every
    /// theorem, D1159): what the search did, and the note if it found a
    /// counterexample. Leaves the metavariables cleared.
    pub fn search_counterexample(
        &mut self,
        def: DefId,
        budget: Budget,
    ) -> (SearchLog, Option<String>) {
        let started = clock::now();
        let theorem = self.globals.def(def).name.to_string();
        let saved = self.globals.budget.start(self.limits);
        let datas = (self.globals.defs.len(), self.globals.datas.len());
        let built = self.build_checker(def);
        self.clear_metas();
        self.globals.budget.restore(saved);
        let mut log = SearchLog {
            theorem,
            ..SearchLog::default()
        };
        let checker = match built {
            Ok(checker) => checker,
            Err(why) => {
                log.out_of_scope = Some(why);
                return (log, None);
            }
        };
        // Building a checker declares nothing (§12); were it ever to, the
        // search stops there.
        if datas != (self.globals.defs.len(), self.globals.datas.len()) {
            log.out_of_scope = Some("building the checker declared something".to_string());
            return (log, None);
        }
        // The time limit counts from here, unless searches are untimed.
        let timed = started.filter(|_| !self.untimed_counterexamples);
        let note = self.run_search(&checker, budget, timed, &mut log);
        log.micros = clock::elapsed_micros(started);
        (log, note)
    }

    /// Whether the theorem `def`'s statement is in scope for the search:
    /// `Err` says why not. For measuring (the proposal's §12); leaves the
    /// metavariables cleared.
    pub fn counterexample_scope(&mut self, def: DefId) -> Result<(), String> {
        let saved = self.globals.budget.start(self.limits);
        let built = self.build_checker(def).and_then(|checker| {
            let g = &self.globals;
            let _op = g.budget.operation(self.limits);
            let mut inputs = Inputs::new(g, 4 * MAX_INPUTS);
            for (name, ty) in &checker.params {
                if inputs.plan(ty).is_none() {
                    return Err(format!("no inputs for `{name}`"));
                }
            }
            Ok(())
        });
        self.clear_metas();
        self.globals.budget.restore(saved);
        built
    }

    /// The checker of theorem `def`'s statement, or why there's none.
    fn build_checker(&self, def: DefId) -> Result<Checker, String> {
        let g = &self.globals;
        let span = g.def(def).span;
        let mut cx = Ctx::new(self, span);
        let failed = |e: stitchwort_syntax::Diagnostic| e.message;
        let nat = builtin_data(&cx, Builtin::Nat).map_err(failed)?;
        let nat_ty = Value::Data(nat, Vec::new());
        let erased = stitchwort_core::check::telescope(g, &g.def(def).ty_value, span)
            .map_err(failed)?
            .params
            .into_iter()
            .map(|(_, _, erased)| erased)
            .collect::<Vec<bool>>();
        let mut steps = Vec::new();
        let mut params = Vec::new();
        let mut slots = Vec::new();
        let mut type_params = Vec::new();
        let mut shown_hypotheses = Vec::new();
        // The statement as written, for showing its parts: its binders'
        // names and types, and its conclusion.
        let mut written_binders: Vec<(Name, Term)> = Vec::new();
        let mut written = g.def(def).ty.strip_loc();
        while let Term::Pi(x, _, dom, cod) = written {
            written_binders.push((x.clone(), (**dom).clone()));
            written = cod.strip_loc();
        }
        let written_conclusion = written.clone();
        let shown_written = |at: usize, term: &Term| -> String {
            let names: Vec<Name> = written_binders[..at]
                .iter()
                .map(|(x, _)| x.clone())
                .collect();
            stitchwort_core::pretty::term_for_message(g, &names, term)
        };
        let mut ty = force(g, g.def(def).ty_value.clone()).map_err(|e| e.to_string())?;
        let mut position = 0;
        while let Value::Pi(x, icit, dom, cod) = ty.clone() {
            let dom = force(g, (*dom).clone()).map_err(|e| e.to_string())?;
            let is_erased = *erased.get(position).ok_or("the telescope changed")?;
            position += 1;
            let next = if is_erased
                && stitchwort_core::check::is_type_former(g, cx.level(), &dom)
                    .map_err(|e| e.to_string())?
            {
                // A type parameter: at `Nat` (D1157).
                if !matches!(dom, Value::Sort(Sort::Type(0))) {
                    return Err(format!("`{x}` isn't a type of data"));
                }
                type_params.push(x.clone());
                slots.push(Slot::Fixed(Term::Data(nat, Vec::new())));
                cod.apply(g, nat_ty.clone())
            } else if is_erased {
                // A hypothesis: decided, and assumed from here on.
                let prop = cx.quote(&dom).map_err(failed)?;
                let decision = crate::bind::decide(&mut cx, &prop)
                    .and_then(|d| d.term(&cx))
                    .map_err(|e| format!("nothing decides `{}`: {}", cx.show(&dom), e.message))?;
                shown_hypotheses.push(if erased.len() == written_binders.len() {
                    shown_written(position - 1, &written_binders[position - 1].1)
                } else {
                    cx.show(&dom)
                });
                steps.push(Step::Hypothesis {
                    index: shown_hypotheses.len() - 1,
                    prop,
                    decision,
                });
                slots.push(Slot::Proof);
                let level = cx.level();
                cx.bind(&x, dom);
                cod.apply(g, Value::var(level))
            } else if icit == Icit::Auto
                && crate::interfaces::interface_goal(self, &dom)
                    .map_err(failed)?
                    .is_some()
            {
                // An instance: found, at the types chosen.
                let meta = crate::check::implicit_arg(&mut cx, Icit::Auto, &dom);
                self.solve_tree(&meta, true).map_err(failed)?;
                let found = self.zonk(&meta, cx.level()).map_err(failed)?;
                let value = cx.eval(&found).map_err(failed)?;
                slots.push(Slot::Fixed(found));
                cod.apply(g, value)
            } else {
                // A data parameter: an input. Its type mustn't depend on the
                // ones before (stage 1).
                if matches!(dom, Value::Pi(..)) {
                    return Err(format!("`{x}` is a function"));
                }
                let ty_term = cx.quote(&dom).map_err(failed)?;
                if (0..cx.level()).any(|ix| ty_term.mentions(ix)) {
                    return Err(format!("the type of `{x}` depends on another parameter"));
                }
                slots.push(Slot::Input(params.len()));
                params.push((x.clone(), dom.clone()));
                steps.push(Step::Data {
                    name: x.clone(),
                    ty: ty_term,
                });
                let level = cx.level();
                cx.bind(&x, dom);
                cod.apply(g, Value::var(level))
            };
            ty = force(g, next.map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
        }
        let conclusion = cx.quote(&ty).map_err(failed)?;
        let shown_conclusion = if erased.len() == written_binders.len() {
            shown_written(written_binders.len(), &written_conclusion)
        } else {
            cx.show(&ty)
        };
        // The sides of an equation as written (not of what a `<` computes
        // to).
        let sides = match written_conclusion.strip_loc() {
            Term::Eq(_, a, b) if slots.len() == written_binders.len() => {
                Some(((**a).clone(), (**b).clone()))
            }
            _ => None,
        };
        let decided = crate::bind::decide(&mut cx, &conclusion)
            .and_then(|d| d.term(&cx))
            .map_err(|e| format!("nothing decides the conclusion: {}", e.message))?;
        let hypotheses = shown_hypotheses.len();
        let term = assemble(&cx, steps, conclusion, decided, hypotheses).map_err(failed)?;
        drop(cx);
        let term = self.finish(&term, 0).map_err(failed)?;
        Ok(Checker {
            term,
            params,
            hypotheses,
            shown_hypotheses,
            type_params,
            shown_conclusion,
            sides,
            slots,
        })
    }

    /// Runs the search for `checker` within `budget`, and makes the note if
    /// it finds a counterexample: every input up to a size first, then
    /// random ones of a growing size, a random counterexample shrunk
    /// (§5.1, §5.5).
    fn run_search(
        &self,
        checker: &Checker,
        budget: Budget,
        started: Option<clock::Instant>,
        log: &mut SearchLog,
    ) -> Option<String> {
        let g = &self.globals;
        let mut inputs = Inputs::new(g, 4 * budget.inputs);
        let mut plans = Vec::new();
        {
            let _op = g.budget.operation(self.limits);
            for (name, ty) in &checker.params {
                match inputs.plan(ty) {
                    Some(plan) => plans.push(plan),
                    None => {
                        log.out_of_scope = Some(format!("no inputs for `{name}`"));
                        return None;
                    }
                }
            }
        }
        let inputs = inputs;
        // Phase 1: every input up to a size, in at most two fifths of the
        // time.
        let (enumerated, largest, exhaustive) = {
            let _op = g.budget.operation(self.limits);
            inputs.enumerate(&plans, budget.inputs.div_ceil(2))
        };
        log.inputs = enumerated.len();
        log.enumerated_size = largest;
        log.exhaustive = exhaustive;
        let first = self.run_batch(
            checker,
            &enumerated,
            started,
            budget.millis * 2 / 5,
            true,
            log,
        )?;
        log.runner = Some(if first.fast {
            Runner::Fast
        } else {
            Runner::Reference
        });
        let mut found = first
            .found
            .map(|i| (enumerated[i].clone(), first.fast, Phase::Enumerated));
        // Phase 2: random inputs, sizes growing to `RANDOM_SIZE`, until
        // four fifths of the time.
        let more = budget.inputs.saturating_sub(log.tried);
        if found.is_none() && !first.stopped && !exhaustive && !plans.is_empty() && more > 0 {
            let mut rng = Rng::new(Rng::seed_of(&format!(
                "{:?} {:?} {}",
                checker
                    .params
                    .iter()
                    .map(|(x, _)| x.to_string())
                    .collect::<Vec<_>>(),
                checker.shown_hypotheses,
                checker.shown_conclusion
            )));
            let random: Vec<Vec<Term>> = {
                let _op = g.budget.operation(self.limits);
                (0..more)
                    .filter_map(|i| {
                        let size = 1 + i * RANDOM_SIZE / more.max(1);
                        log.random_size = log.random_size.max(size);
                        inputs.random_tuple(&plans, size, &mut rng)
                    })
                    .collect()
            };
            let before = log.tried;
            let batch =
                self.run_batch(checker, &random, started, budget.millis * 4 / 5, true, log)?;
            log.random = log.tried - before;
            found = batch
                .found
                .map(|i| (random[i].clone(), batch.fast, Phase::Random));
        }
        let (mut input, mut fast, phase) = found?;
        log.found_by = Some(phase);
        // Shrinking (§5.5): the first smaller input that is still a
        // counterexample, again and again, in the time left.
        if phase == Phase::Random {
            for _ in 0..SHRINK_ROUNDS {
                if clock::past(started, budget.millis) {
                    log.timed_out = true;
                    break;
                }
                let candidates = {
                    let _op = g.budget.operation(self.limits);
                    inputs.shrink_tuple(&plans, &input)
                };
                let batch =
                    self.run_batch(checker, &candidates, started, budget.millis, false, log)?;
                let Some(i) = batch.found else { break };
                input = candidates[i].clone();
                fast = batch.fast;
                log.shrinks += 1;
            }
        }
        let falsified = checker.hypotheses as u64 + 1;
        // Confirmed by the reference evaluator, the trusted semantics.
        let confirmed = matches!(
            self.run_reference(checker, &input, CONFIRM_STEPS),
            Ok(Some(code)) if code == falsified
        );
        let bindings = self.show_inputs(checker, &inputs, &plans, &input);
        if !confirmed {
            if fast {
                log.disagreed = true;
                return Some(format!(
                    "internal error: the fast runtime found a counterexample to this statement \
                     that the reference evaluator doesn't confirm ({}); please report it",
                    bindings.join(", ")
                ));
            }
            return None;
        }
        log.found = Some(bindings.clone());
        Some(self.counterexample_text(checker, &input, &bindings))
    }

    /// Runs `checker` on each of `inputs`, on the fast runtime if it can,
    /// until one is a counterexample or `until_ms` milliseconds have passed
    /// since `started`; if `counted`, each is counted in `log`, and too
    /// many running out of steps stops it. `None` if the check was
    /// cancelled.
    fn run_batch(
        &self,
        checker: &Checker,
        inputs: &[Vec<Term>],
        started: Option<clock::Instant>,
        until_ms: u64,
        counted: bool,
        log: &mut SearchLog,
    ) -> Option<Batch> {
        let g = &self.globals;
        let falsified = checker.hypotheses as u64 + 1;
        let mut found = None;
        let mut stopped = false;
        let mut timed_out = false;
        let mut in_a_row = 0;
        let mut each = |i: usize, result: Option<u64>| -> bool {
            if counted {
                log.tried += 1;
                match result {
                    Some(code) if code < falsified - 1 => log.discarded += 1,
                    None => log.out_of_steps += 1,
                    Some(_) => {}
                }
            }
            if result == Some(falsified) {
                found = Some(i);
                return false;
            }
            in_a_row = if result.is_none() { in_a_row + 1 } else { 0 };
            if counted && (in_a_row >= OUT_OF_STEPS_IN_A_ROW || log.out_of_steps >= OUT_OF_STEPS) {
                stopped = true;
                return false;
            }
            if clock::past(started, until_ms) {
                timed_out = true;
                return false;
            }
            true
        };
        let fast = match self.counterexample_runner {
            Some(run) if !checker.params.is_empty() && !inputs.is_empty() => {
                run(g, self.limits, &checker.term, inputs, &mut each)
            }
            _ => false,
        };
        if !fast {
            for (i, input) in inputs.iter().enumerate() {
                // Cancelled: no answer.
                let result = self.run_reference(checker, input, REFERENCE_STEPS).ok()?;
                if !each(i, result) {
                    break;
                }
            }
        }
        if timed_out {
            log.timed_out = true;
        }
        Some(Batch {
            found,
            fast,
            stopped,
        })
    }

    /// `checker` applied to `input` on the reference evaluator, within
    /// `steps`: its result, `None` if it didn't finish, `Err` if the check
    /// was cancelled.
    fn run_reference(
        &self,
        checker: &Checker,
        input: &[Term],
        steps: u64,
    ) -> Result<Option<u64>, ()> {
        let g = &self.globals;
        let _op = g.budget.operation(Limits {
            work: steps,
            ..self.limits
        });
        let _erasing = g.erasure.running();
        let call = input
            .iter()
            .fold(checker.term.clone(), |f, a| Term::app(f, a.clone()));
        match eval(g, &[], &call).and_then(|v| force(g, v)) {
            Ok(Value::Nat(k)) => Ok(u64::try_from(k.as_ref().clone()).ok()),
            Ok(Value::Ctor(_, 0, _)) => Ok(Some(0)),
            Ok(_) => Ok(None),
            Err(stitchwort_core::ResourceError::Cancelled) => Err(()),
            Err(_) => Ok(None),
        }
    }

    /// Each input as `name = value`. A map is shown as the `Map.fromList`
    /// it was made by, and a `Fin` as its number, rather than as their
    /// values.
    fn show_inputs(
        &self,
        checker: &Checker,
        inputs: &Inputs,
        plans: &[usize],
        input: &[Term],
    ) -> Vec<String> {
        let g = &self.globals;
        checker
            .params
            .iter()
            .zip(plans.iter().zip(input))
            .map(|((name, _), (plan, term))| {
                let shown = if inputs.shown_as_term(*plan) {
                    shown::cut(&stitchwort_core::pretty::term_for_message(
                        g,
                        &[],
                        &inputs.shown(*plan, term),
                    ))
                } else {
                    self.show_closed(term)
                };
                format!("{name} = {shown}")
            })
            .collect()
    }

    /// A closed term's value, printed and cut.
    fn show_closed(&self, term: &Term) -> String {
        let g = &self.globals;
        let _op = g.budget.operation(Limits {
            size: shown::SHOWN_NODES,
            work: CONFIRM_STEPS,
            ..self.limits
        });
        // In full first, so a `Float` keeps the proof it prints by.
        if let Ok(t) = eval(g, &[], term).and_then(|v| quote(g, 0, &v))
            && is_data(&t)
        {
            return shown::cut(&stitchwort_core::pretty::term(g, &[], &t));
        }
        let _erasing = g.erasure.running();
        self.shown_value(eval(g, &[], term).ok()).0
    }

    /// A value printed and cut, and its term.
    fn shown_value(&self, value: Option<Value>) -> (String, Option<Term>) {
        let g = &self.globals;
        let Some(value) = value else {
            return ("…".to_string(), None);
        };
        match quote(g, 0, &value) {
            Ok(t) => (
                shown::cut(&stitchwort_core::pretty::term(g, &[], &t)),
                Some(t),
            ),
            Err(_) => ("… (too large to show)".to_string(), None),
        }
    }

    /// The note for a confirmed counterexample (§9.1).
    fn counterexample_text(
        &self,
        checker: &Checker,
        input: &[Term],
        bindings: &[String],
    ) -> String {
        let g = &self.globals;
        let mut text = String::from("this statement is false");
        if !checker.type_params.is_empty() {
            let at: Vec<String> = checker
                .type_params
                .iter()
                .map(|a| format!("{a} := Nat"))
                .collect();
            text.push_str(&format!(" (with {})", at.join(", ")));
        }
        if bindings.is_empty() {
            text.push(':');
        } else {
            text.push_str("; a counterexample:");
            for binding in bindings {
                text.push_str(&format!("\n  {binding}"));
            }
        }
        for hypothesis in &checker.shown_hypotheses {
            text.push_str(&format!("\n`{}` holds", shown::cut(hypothesis)));
        }
        text.push_str(&format!(
            "\n`{}` is false",
            shown::cut(&checker.shown_conclusion)
        ));
        if let Some((left, right)) = &checker.sides {
            // The sides' values at the counterexample, each in its own
            // operation with a small limit on what's shown.
            // The statement's binders: the inputs, and what the checker
            // fixed.
            let mut env: Vec<Value> = Vec::new();
            for slot in &checker.slots {
                let _op = g.budget.operation(Limits {
                    work: CONFIRM_STEPS,
                    ..self.limits
                });
                let value = match slot {
                    Slot::Input(i) => eval(g, &env, &input[*i]),
                    Slot::Fixed(term) => eval(g, &env, term),
                    Slot::Proof => Ok(stitchwort_core::erase::erased()),
                };
                env.push(value.unwrap_or_else(|_| stitchwort_core::erase::erased()));
            }
            // Each side in full first: its value is data then, unless it
            // calls something that only computes when proofs are erased (a
            // definition by well-founded recursion), and then erased, as a
            // program runs.
            let side = |term: &Term| {
                let limits = Limits {
                    size: shown::SHOWN_NODES,
                    work: CONFIRM_STEPS,
                    ..self.limits
                };
                let in_full = {
                    let _op = g.budget.operation(limits);
                    eval(g, &env, term).and_then(|v| quote(g, 0, &v))
                };
                if let Ok(t) = in_full
                    && is_data(&t)
                {
                    let _op = g.budget.operation(limits);
                    return (
                        shown::cut(&stitchwort_core::pretty::term(g, &[], &t)),
                        Some(t),
                    );
                }
                let _op = g.budget.operation(limits);
                let _erasing = g.erasure.running();
                self.shown_value(eval(g, &env, term).ok())
            };
            let (left, left_term) = side(left);
            let (right, right_term) = side(right);
            text.push_str(&format!(":\n  left:  {left}\n  right: {right}"));
            if let (Some(l), Some(r)) = (&left_term, &right_term)
                && let Some(difference) = shown::first_difference(g, l, r)
            {
                text.push_str(&format!("\n  {difference}"));
            }
        }
        text
    }
}

/// Whether `term` is a value made of data: constructors, numbers and
/// text, and proofs inside them (a `Float`'s validity proof is part of how
/// it prints), with nothing left to compute.
fn is_data(term: &Term) -> bool {
    term.subterms().all(|(t, _)| {
        matches!(
            t,
            Term::Ctor(..) | Term::Nat(_) | Term::Chars(_) | Term::Refl | Term::Loc(..)
        )
    })
}

/// The checker's term from its steps: the conclusion's decision innermost,
/// each hypothesis's around what follows it, each data parameter a lambda.
fn assemble(
    cx: &Ctx,
    steps: Vec<Step>,
    conclusion: Term,
    decided: Term,
    hypotheses: usize,
) -> crate::check::Result<Term> {
    let elim = builtin_def(cx, Builtin::ElimDec)?;
    let nat = builtin_data(cx, Builtin::Nat)?;
    let number = |n: usize| Term::Nat(Rc::new(BigUint::from(n)));
    let constant = |n: usize, after: usize| -> Term {
        // `_ => _ … => n`: a refutation, then the inputs after it.
        (0..=after).fold(number(n), |body, _| {
            Term::Lam("_".into(), Icit::Explicit, Rc::new(body))
        })
    };
    let decide = |prop: Term, result: Term, decision: Term, yes: Term, no: Term| {
        let head = Term::app_icit(
            Term::app_icit(Term::Def(elim), prop, Icit::Implicit),
            result,
            Icit::Implicit,
        );
        Term::app(Term::app(Term::app(head, decision), yes), no)
    };
    let lam = |name: Name, body: Term| Term::Lam(name, Icit::Explicit, Rc::new(body));
    let nat_ty = Term::Data(nat, Vec::new());
    let mut body = decide(
        conclusion,
        nat_ty.clone(),
        decided,
        lam("_".into(), number(hypotheses)),
        lam("_".into(), number(hypotheses + 1)),
    );
    // The types of the inputs after the current step, innermost first.
    let mut later: Vec<(Name, Term)> = Vec::new();
    for step in steps.into_iter().rev() {
        match step {
            Step::Data { name, ty } => {
                body = lam(name.clone(), body);
                later.push((name, ty));
            }
            Step::Hypothesis {
                index,
                prop,
                decision,
            } => {
                // What follows takes the inputs after it, so its type is a
                // function type of their (closed) types.
                let result = later.iter().fold(nat_ty.clone(), |cod, (x, dom)| {
                    Term::Pi(
                        x.clone(),
                        Icit::Explicit,
                        Rc::new(dom.clone()),
                        Rc::new(cod),
                    )
                });
                body = decide(
                    prop,
                    result,
                    decision,
                    lam("h".into(), body),
                    constant(index, later.len()),
                );
            }
        }
    }
    Ok(body)
}

/// A clock where there is one: none in WebAssembly, where the count of
/// inputs is the only limit.
mod clock {
    #[cfg(not(target_arch = "wasm32"))]
    pub type Instant = std::time::Instant;
    #[cfg(target_arch = "wasm32")]
    #[derive(Clone, Copy)]
    pub struct Instant;

    pub fn now() -> Option<Instant> {
        #[cfg(not(target_arch = "wasm32"))]
        return Some(Instant::now());
        #[cfg(target_arch = "wasm32")]
        return None;
    }

    /// Whether more than `ms` milliseconds have passed since `start`.
    pub fn past(start: Option<Instant>, ms: u64) -> bool {
        elapsed_micros(start).is_some_and(|us| us > ms * 1000)
    }

    pub fn elapsed_micros(start: Option<Instant>) -> Option<u64> {
        #[cfg(not(target_arch = "wasm32"))]
        return start.map(|s| u64::try_from(s.elapsed().as_micros()).unwrap_or(u64::MAX));
        #[cfg(target_arch = "wasm32")]
        return {
            let _ = start;
            None
        };
    }
}
