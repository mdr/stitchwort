//! Counterexample search, stage 1 (docs/proposals/counterexample-search.md,
//! D1154-D1159).
//!
//! When a theorem's statement checks but its proof doesn't (or its whole
//! proof is `?`), the statement is tried on small inputs, smallest first.
//! An input that makes every hypothesis true and the conclusion false is a
//! counterexample: the statement is false, and the error says so in a note.
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
//! - Inputs are enumerated from the parameters' types (§5): numbers by
//!   value, and every data type and record of the program by its
//!   constructors, smallest total size first, so the first counterexample is
//!   a smallest one. A type with indices, a function field, or a proof or
//!   type field has no inputs in stage 1 (§5.4); `Map` and `Set` (quotients)
//!   neither.
//! - The checker runs on the fast runtime when the host gives one
//!   ([`FastRunner`], the driver's), else on the reference evaluator, as
//!   tests do; a counterexample is run again on the reference evaluator
//!   before it's shown (§6.2). At most [`MAX_INPUTS`] inputs, and about
//!   [`TIME_LIMIT_MS`] milliseconds where there's a clock (D1154).
//! - It's advisory: nothing here makes a declaration check, and finding no
//!   counterexample is never shown (§8).

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{eval, force, quote};
use stitchwort_core::{BigUint, DataId, DefId, Globals, Icit, Limits, Name, Sort, Term, Value};

use crate::check::{Ctx, builtin_data, builtin_def};
use crate::{Elaborator, shown};

/// The most inputs one search tries (§6.3).
pub const MAX_INPUTS: usize = 2000;

/// The wall-time backstop of one search, where there's a clock (§6.3).
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

/// The largest total input size enumerated.
const MAX_SIZE: usize = 100;

/// The most values of one type and size enumerated.
const TIER_CAP: usize = 4 * MAX_INPUTS;

/// The most data types one search makes inputs for.
const MAX_PLANS: usize = 64;

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

/// What one search did, for tests and measurements.
#[derive(Clone, Debug)]
pub struct SearchLog {
    /// The theorem's name.
    pub theorem: String,
    /// Why it wasn't searched, if it wasn't (out of scope).
    pub out_of_scope: Option<String>,
    pub runner: Option<Runner>,
    /// Inputs enumerated, and those run.
    pub inputs: usize,
    pub tried: usize,
    /// Inputs some hypothesis was false for.
    pub discarded: usize,
    pub out_of_steps: usize,
    /// The counterexample's bindings as shown, if one was found.
    pub found: Option<Vec<String>>,
    /// Whether the fast runtime's counterexample was not confirmed by the
    /// reference evaluator (an internal error).
    pub disagreed: bool,
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
        let started = clock::now();
        let theorem = self.globals.def(def).name.to_string();
        let saved = self.globals.budget.start(self.limits);
        let datas = (self.globals.defs.len(), self.globals.datas.len());
        let built = self.build_checker(def);
        self.clear_metas();
        self.globals.budget.restore(saved);
        let mut log = SearchLog {
            theorem,
            out_of_scope: None,
            runner: None,
            inputs: 0,
            tried: 0,
            discarded: 0,
            out_of_steps: 0,
            found: None,
            disagreed: false,
            micros: None,
        };
        let checker = match built {
            Ok(checker) => checker,
            Err(why) => {
                log.out_of_scope = Some(why);
                self.counterexample_log.borrow_mut().push(log);
                return None;
            }
        };
        // Building a checker declares nothing (§12); were it ever to, the
        // search stops there.
        if datas != (self.globals.defs.len(), self.globals.datas.len()) {
            log.out_of_scope = Some("building the checker declared something".to_string());
            self.counterexample_log.borrow_mut().push(log);
            return None;
        }
        let note = self.run_search(&checker, started, &mut log);
        log.micros = clock::elapsed_micros(started);
        self.counterexample_log.borrow_mut().push(log);
        note
    }

    /// Whether the theorem `def`'s statement is in scope for the search:
    /// `Err` says why not. For measuring (the proposal's §12); leaves the
    /// metavariables cleared.
    pub fn counterexample_scope(&mut self, def: DefId) -> Result<(), String> {
        let saved = self.globals.budget.start(self.limits);
        let built = self.build_checker(def).and_then(|checker| {
            let g = &self.globals;
            let _op = g.budget.operation(self.limits);
            let mut inputs = Enumerator::new(g);
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

    /// Runs the search for `checker`, and makes the note if it finds a
    /// counterexample.
    fn run_search(
        &self,
        checker: &Checker,
        started: Option<clock::Instant>,
        log: &mut SearchLog,
    ) -> Option<String> {
        let g = &self.globals;
        let inputs = {
            let _op = g.budget.operation(self.limits);
            let mut enumerator = Enumerator::new(g);
            let mut plans = Vec::new();
            for (name, ty) in &checker.params {
                match enumerator.plan(ty) {
                    Some(plan) => plans.push(plan),
                    None => {
                        log.out_of_scope = Some(format!("no inputs for `{name}`"));
                        return None;
                    }
                }
            }
            enumerator.inputs(&plans, MAX_INPUTS)
        };
        log.inputs = inputs.len();
        let falsified = checker.hypotheses as u64 + 1;
        let mut found = None;
        let mut in_a_row = 0;
        let mut each = |i: usize, result: Option<u64>| -> bool {
            log.tried += 1;
            match result {
                Some(code) if code == falsified => {
                    found = Some(i);
                    return false;
                }
                Some(code) if code < falsified - 1 => log.discarded += 1,
                Some(_) => {}
                None => log.out_of_steps += 1,
            }
            in_a_row = if result.is_none() { in_a_row + 1 } else { 0 };
            in_a_row < OUT_OF_STEPS_IN_A_ROW
                && log.out_of_steps < OUT_OF_STEPS
                && !clock::past(started, TIME_LIMIT_MS)
        };
        let fast = match self.counterexample_runner {
            Some(run) if !checker.params.is_empty() => {
                run(g, self.limits, &checker.term, &inputs, &mut each)
            }
            _ => false,
        };
        log.runner = Some(if fast {
            Runner::Fast
        } else {
            Runner::Reference
        });
        if !fast {
            for (i, input) in inputs.iter().enumerate() {
                let result = match self.run_reference(checker, input, REFERENCE_STEPS) {
                    Ok(result) => result,
                    // Cancelled: no answer.
                    Err(()) => return None,
                };
                if !each(i, result) {
                    break;
                }
            }
        }
        let input = &inputs[found?];
        // Confirmed by the reference evaluator, the trusted semantics.
        let confirmed = matches!(
            self.run_reference(checker, input, CONFIRM_STEPS),
            Ok(Some(code)) if code == falsified
        );
        let bindings = self.show_inputs(checker, input);
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
        Some(self.counterexample_text(checker, input, &bindings))
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

    /// Each input as `name = value`.
    fn show_inputs(&self, checker: &Checker, input: &[Term]) -> Vec<String> {
        checker
            .params
            .iter()
            .zip(input)
            .map(|((name, _), term)| format!("{name} = {}", self.show_closed(term)))
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

/// The values of one type of one size.
type Tier = Rc<Vec<Term>>;

/// How the values of one type are enumerated.
enum Plan {
    /// Being worked out (a recursive type refers to itself).
    Pending,
    /// No inputs: some part of it has none.
    Failed,
    Nat,
    Int {
        int: DataId,
    },
    /// A data type or record: for each constructor, its fields' plans.
    Data {
        data: DataId,
        ctors: Vec<Vec<usize>>,
    },
}

/// Enumerates the values of types by size (§5.2): a number's size is its
/// value, a constructor without fields has size 0, and one with fields
/// 1 plus theirs. Values of each size are made once.
struct Enumerator<'g> {
    g: &'g Globals,
    plans: Vec<Plan>,
    keys: HashMap<String, usize>,
    tiers: RefCell<HashMap<(usize, usize), Tier>>,
}

impl<'g> Enumerator<'g> {
    fn new(g: &'g Globals) -> Self {
        Enumerator {
            g,
            plans: Vec::new(),
            keys: HashMap::new(),
            tiers: RefCell::new(HashMap::new()),
        }
    }

    /// The plan for closed type `ty`, if it has inputs.
    fn plan(&mut self, ty: &Value) -> Option<usize> {
        let g = self.g;
        let ty = force(g, ty.clone()).ok()?;
        let Value::Data(d, args) = &ty else {
            return None;
        };
        let key = stitchwort_core::pretty::term(g, &[], &quote(g, 0, &ty).ok()?);
        if let Some(&plan) = self.keys.get(&key) {
            return match self.plans[plan] {
                Plan::Failed => None,
                _ => Some(plan),
            };
        }
        if self.plans.len() >= MAX_PLANS {
            return None;
        }
        let at = self.plans.len();
        self.keys.insert(key, at);
        let is = |b: Builtin| g.registry.is_data(b, *d);
        if is(Builtin::Nat) {
            self.plans.push(Plan::Nat);
            return Some(at);
        }
        self.plans.push(Plan::Pending);
        let plan = if is(Builtin::Int) {
            Some(Plan::Int { int: *d })
        } else {
            self.data_plan(*d, args)
        };
        match plan {
            Some(plan) => {
                self.plans[at] = plan;
                Some(at)
            }
            None => {
                self.plans[at] = Plan::Failed;
                None
            }
        }
    }

    /// The plan for data type `d` applied to `args`.
    fn data_plan(&mut self, d: DataId, args: &[Value]) -> Option<Plan> {
        let g = self.g;
        let data = g.data(d);
        if !data.indices.is_empty() || data.sort == Sort::Prop || args.len() != data.params.len() {
            return None;
        }
        let mut ctors = Vec::new();
        for ctor in &data.ctors {
            let mut env: Vec<Value> = args.to_vec();
            let mut fields = Vec::new();
            for (j, ((_, field_ty), erased)) in
                ctor.fields.iter().zip(&ctor.field_erased).enumerate()
            {
                // A proof or type field (stage 1), or one whose type
                // depends on an earlier field.
                if *erased || (0..j).any(|ix| field_ty.mentions(ix)) {
                    return None;
                }
                let field = eval(g, &env, field_ty).ok()?;
                fields.push(self.plan(&field)?);
                env.push(Value::var(args.len() + j));
            }
            ctors.push(fields);
        }
        Some(Plan::Data { data: d, ctors })
    }

    /// The values of plan `plan` of size `size`, at most [`TIER_CAP`].
    fn tier(&self, plan: usize, size: usize) -> Tier {
        if let Some(tier) = self.tiers.borrow().get(&(plan, size)) {
            return tier.clone();
        }
        let number = |n: usize| Term::Nat(Rc::new(BigUint::from(n)));
        let values = match &self.plans[plan] {
            Plan::Pending | Plan::Failed => Vec::new(),
            Plan::Nat => vec![number(size)],
            // 0, 1, -1, 2, -2, …: `OfNat n` and `NegSucc (n - 1)`.
            Plan::Int { int } => {
                let mut values = vec![Term::ctor(*int, 0, vec![number(size)])];
                if size > 0 {
                    values.push(Term::ctor(*int, 1, vec![number(size - 1)]));
                }
                values
            }
            Plan::Data { data, ctors } => {
                let mut values = Vec::new();
                for (c, fields) in ctors.iter().enumerate() {
                    if fields.is_empty() {
                        if size == 0 {
                            values.push(Term::ctor(*data, c, Vec::new()));
                        }
                    } else if size > 0 {
                        self.products(fields, size - 1, TIER_CAP, &mut |parts| {
                            values.push(Term::ctor(*data, c, parts));
                            values.len() < TIER_CAP
                        });
                    }
                    if values.len() >= TIER_CAP {
                        break;
                    }
                }
                values
            }
        };
        let values = Rc::new(values);
        self.tiers.borrow_mut().insert((plan, size), values.clone());
        values
    }

    /// Calls `each` with every tuple of values of `plans` whose sizes add up
    /// to `total`, in order (the first plan's smallest first), until it says
    /// to stop or `limit` tuples have been made. Whether it stopped.
    fn products(
        &self,
        plans: &[usize],
        total: usize,
        limit: usize,
        each: &mut dyn FnMut(Vec<Term>) -> bool,
    ) -> bool {
        let mut made = 0;
        let mut sizes = vec![0; plans.len()];
        let mut stop = false;
        compositions(total, plans.len(), &mut sizes, 0, &mut |sizes| {
            let tiers: Vec<Tier> = plans
                .iter()
                .zip(sizes)
                .map(|(p, s)| self.tier(*p, *s))
                .collect();
            if tiers.iter().any(|t| t.is_empty()) {
                return true;
            }
            // Every combination, the last plan's value changing fastest.
            let mut at = vec![0; tiers.len()];
            loop {
                let tuple = at.iter().zip(&tiers).map(|(i, t)| t[*i].clone()).collect();
                made += 1;
                if !each(tuple) || made >= limit {
                    stop = true;
                    return false;
                }
                let mut k = tiers.len();
                loop {
                    if k == 0 {
                        return true;
                    }
                    k -= 1;
                    at[k] += 1;
                    if at[k] < tiers[k].len() {
                        break;
                    }
                    at[k] = 0;
                }
            }
        });
        stop
    }

    /// Up to `max` tuples of inputs for `plans`, smallest total size first.
    fn inputs(&self, plans: &[usize], max: usize) -> Vec<Vec<Term>> {
        if plans.is_empty() {
            return vec![Vec::new()];
        }
        let mut out = Vec::new();
        let mut empty_sizes = 0;
        for total in 0..=MAX_SIZE {
            let before = out.len();
            let stopped = self.products(plans, total, max - out.len(), &mut |tuple| {
                out.push(tuple);
                out.len() < max
            });
            if stopped || out.len() >= max {
                break;
            }
            // Only finitely many values (all `Bool`s, say): done.
            empty_sizes = if out.len() == before {
                empty_sizes + 1
            } else {
                0
            };
            if empty_sizes > 8 {
                break;
            }
        }
        out
    }
}

/// Calls `each` with every way of writing `total` as `parts` sizes, in
/// order, until it says to stop. Whether it was told to stop.
fn compositions(
    total: usize,
    parts: usize,
    sizes: &mut Vec<usize>,
    from: usize,
    each: &mut dyn FnMut(&[usize]) -> bool,
) -> bool {
    if from + 1 >= parts {
        if parts == 0 {
            return total != 0 || each(sizes);
        }
        sizes[from] = total;
        return each(sizes);
    }
    for size in 0..=total {
        sizes[from] = size;
        if !compositions(total - size, parts, sizes, from + 1, each) {
            return false;
        }
    }
    true
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

#[cfg(test)]
mod tests {
    use super::compositions;

    fn all(total: usize, parts: usize) -> Vec<Vec<usize>> {
        let mut found = Vec::new();
        let mut sizes = vec![0; parts];
        compositions(total, parts, &mut sizes, 0, &mut |s| {
            found.push(s.to_vec());
            true
        });
        found
    }

    #[test]
    fn sizes_are_split_every_way_the_first_smallest_first() {
        assert_eq!(all(2, 2), [[0, 2], [1, 1], [2, 0]]);
        assert_eq!(all(1, 3), [[0, 0, 1], [0, 1, 0], [1, 0, 0]]);
        assert_eq!(all(3, 1), [[3]]);
        assert_eq!(all(0, 2), [[0, 0]]);
    }

    #[test]
    fn splitting_stops_when_told() {
        let mut seen = 0;
        let mut sizes = vec![0; 2];
        let finished = compositions(5, 2, &mut sizes, 0, &mut |_| {
            seen += 1;
            seen < 3
        });
        assert!(!finished);
        assert_eq!(seen, 3);
    }
}
