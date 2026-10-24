//! Running counterexample searches on the fast runtime
//! (docs/proposals/counterexample-search.md §6.2): the
//! [`stitchwort_elab::counterexample::FastRunner`] every session gives its
//! elaborator.
//!
//! The checker and its inputs are lowered together, as one program whose
//! entry is the pair of the checker and a balanced tree of the inputs (a
//! tree, not a list, so lowering doesn't nest as deep as there are inputs).
//! The machine computes the entry once, and then calls the checker on each
//! input in turn, each call with its own step budget. The machine's values
//! are taken apart only as pairs, whose shape the runtime fixes
//! ([`stitchwort_rt::ir::Shapes`]).

use std::rc::Rc;

use stitchwort_core::globals::State;
use stitchwort_core::registry::Builtin;
use stitchwort_core::{DefId, Globals, Limits, Term};
use stitchwort_elab::counterexample::{Budget, FAST_STEPS, SearchLog};
use stitchwort_rt::value::Value;

use crate::driver::Session;

/// One theorem's search for `check --counterexamples` (D1159).
pub struct TheoremSearch {
    /// Its name, as written from the root of its module.
    pub name: String,
    /// Whether its proof checked.
    pub checked: bool,
    pub log: SearchLog,
    /// The note, if a counterexample was found.
    pub note: Option<String>,
}

/// What a search says about a theorem's statement, as
/// `check --counterexamples` reports it (§9.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// A counterexample: the statement is false.
    False,
    /// None found in the inputs tried: evidence, not a proof.
    NoneFound,
    /// Fewer than one input in ten made the hypotheses true.
    GaveUp,
    /// Most inputs ran out of steps.
    Inconclusive,
    /// Out of scope: why.
    NotApplicable,
}

impl TheoremSearch {
    /// The verdict, and the line that says it.
    pub fn verdict(&self) -> (Verdict, String) {
        let log = &self.log;
        if let Some(why) = &log.out_of_scope {
            return (
                Verdict::NotApplicable,
                format!("not applicable: {}", stitchwort_elab::shown::cut(why)),
            );
        }
        if let Some(found) = &log.found {
            return (
                Verdict::False,
                format!("counterexample: {}", found.join(", ")),
            );
        }
        if log.disagreed {
            return (
                Verdict::False,
                "internal error: the fast runtime found a counterexample the reference \
                 evaluator doesn't confirm; please report it"
                    .to_string(),
            );
        }
        let held = log.tried - log.discarded - log.out_of_steps;
        if log.tried == 0 || log.out_of_steps * 2 > log.tried {
            return (
                Verdict::Inconclusive,
                "inconclusive (ran out of steps)".to_string(),
            );
        }
        if held * 10 < log.tried {
            return (
                Verdict::GaveUp,
                format!("gave up (hypotheses true in {held} of {} cases)", log.tried),
            );
        }
        let sizes = if log.exhaustive {
            "every input".to_string()
        } else {
            format!("sizes up to {}", log.enumerated_size.max(log.random_size))
        };
        let plural = if log.tried == 1 { "" } else { "s" };
        (
            Verdict::NoneFound,
            format!(
                "none in {} case{plural} ({sizes}; evidence, not a proof)",
                log.tried
            ),
        )
    }
}

impl Session {
    /// Searches the statement of every theorem of the program (not the
    /// library's) whose full name `keep` keeps, whether its proof checked or
    /// failed, within `budget`, in the order they were declared
    /// (docs/proposals/counterexample-search.md §7.3).
    pub fn search_theorems(
        &mut self,
        budget: Budget,
        keep: &dyn Fn(&str) -> bool,
    ) -> Vec<TheoremSearch> {
        let g = &self.elab.globals;
        let theorems: Vec<(DefId, String, bool)> = (0..g.defs.len())
            .map(DefId)
            .filter_map(|id| {
                let def = g.def(id);
                let path = def.path.to_string();
                let state = def.state();
                (def.theorem
                    && !path.contains('%')
                    && !path.starts_with("Std.")
                    && matches!(state, State::Final | State::Failed)
                    && keep(&path))
                .then(|| (id, def.name.to_string(), state == State::Final))
            })
            .collect();
        theorems
            .into_iter()
            .map(|(id, name, checked)| {
                let (log, note) = self.elab.search_counterexample(id, budget);
                TheoremSearch {
                    name,
                    checked,
                    log,
                    note,
                }
            })
            .collect()
    }
}

/// Runs `checker` on each of `inputs` on the fast runtime, telling `each`
/// the results, until it says to stop. `false` if it can't run there.
pub fn run_fast(
    g: &Globals,
    limits: Limits,
    checker: &Term,
    inputs: &[Vec<Term>],
    each: &mut dyn FnMut(usize, Option<u64>) -> bool,
) -> bool {
    let Some((pair, _)) = g.registry.ctor(Builtin::MkPair) else {
        return false;
    };
    let arity = inputs.first().map_or(0, Vec::len);
    if arity == 0 || inputs.iter().any(|input| input.len() != arity) {
        return false;
    }
    let mk_pair = |a: Term, b: Term| Term::Ctor(pair, 0, vec![Rc::new(a), Rc::new(b)]);
    // One input's values as nested pairs, `(x1, (x2, x3))`.
    let tuple = |input: &[Term]| -> Term {
        let mut values = input.iter().rev().cloned();
        let last = values.next().expect("at least one input");
        values.fold(last, |rest, value| mk_pair(value, rest))
    };
    fn tree(inputs: &[Term], mk_pair: &dyn Fn(Term, Term) -> Term) -> Term {
        if inputs.len() == 1 {
            return inputs[0].clone();
        }
        let middle = inputs.len() / 2;
        mk_pair(
            tree(&inputs[..middle], mk_pair),
            tree(&inputs[middle..], mk_pair),
        )
    }
    let tuples: Vec<Term> = inputs.iter().map(|input| tuple(input)).collect();
    let entry = mk_pair(checker.clone(), tree(&tuples, &mk_pair));
    let Ok(program) = stitchwort_rt::lower_main(g, limits, &entry) else {
        return false;
    };
    let pair_tag = program.shapes.pair;
    let mut machine = stitchwort_rt::Machine::new(
        &program,
        stitchwort_rt::Limits {
            steps: FAST_STEPS,
            frames: limits.frames,
        },
    );
    let parts = |value: &Value| -> Option<(Value, Value)> {
        match value {
            Value::Data(tag, fields) if *tag == pair_tag && fields.len() == 2 => {
                Some((fields[0].clone(), fields[1].clone()))
            }
            _ => None,
        }
    };
    machine.reset_steps();
    let Some((function, inputs_tree)) = machine.entry().ok().as_ref().and_then(parts) else {
        return false;
    };
    // The leaves of the tree, in order, as the machine's values.
    let mut leaves = Vec::with_capacity(tuples.len());
    let mut pending = vec![(inputs_tree, tuples.len())];
    while let Some((node, count)) = pending.pop() {
        if count == 1 {
            leaves.push(node);
            continue;
        }
        let Some((left, right)) = parts(&node) else {
            return false;
        };
        let middle = count / 2;
        // The left half is taken first.
        pending.push((right, count - middle));
        pending.push((left, middle));
    }
    // Each input's values, taken apart before any is run.
    let mut calls = Vec::with_capacity(leaves.len());
    for leaf in leaves {
        let mut args = Vec::with_capacity(arity);
        let mut rest = leaf;
        for _ in 1..arity {
            let Some((value, more)) = parts(&rest) else {
                return false;
            };
            args.push(value);
            rest = more;
        }
        args.push(rest);
        calls.push(args);
    }
    for (i, args) in calls.into_iter().enumerate() {
        machine.reset_steps();
        let result = match machine.call(function.clone(), args) {
            Ok(Value::Nat(code)) => Some(code),
            _ => None,
        };
        if !each(i, result) {
            break;
        }
    }
    true
}
