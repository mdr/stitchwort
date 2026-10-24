//! Size-change termination (SCT) for a group of recursive definitions
//! (docs/proposals/mutual-recursion.md §6.5), after Lee, Jones and
//! Ben-Amram, *The Size-Change Principle for Program Termination* (2001).
//!
//! Each call from one member of a group to another is summarised by a
//! [`Graph`]: for each argument position of the callee, which parameter of
//! the caller that argument is strictly smaller than (`<`) or at most (`≤`),
//! if any. The group terminates if, in the closure of the call graphs under
//! composition (every nonempty path of calls), every graph from a member to
//! itself that is *idempotent* (composing it with itself gives itself) has a
//! strict arc from some parameter to itself.
//!
//! The rules that matter for soundness, each tested against an independent
//! reference implementation (`crates/core/tests/sct.rs`):
//!
//! - **Graphs are never merged.** Two calls with the same endpoints (say, in
//!   different branches of a `case`) stay two graphs. One branch decreasing
//!   argument 0 and another decreasing argument 1 doesn't mean either
//!   decreases both.
//! - **Unknown stays unknown.** A position with no relation is `None`, and
//!   nothing turns it into `≤`.
//! - **Composition only of matching graphs**: `a ; b` needs `a.to == b.from`,
//!   and graphs need not be square.
//! - **Closure over nonempty paths only.** An identity graph (the empty
//!   path) is idempotent with no strict arc, so adding it would reject every
//!   recursive definition.
//! - **Running out is inconclusive**: [`Group::check`] returns a
//!   [`ResourceError`], never acceptance.
//!
//! Each argument position holds at most one arc (the representation can't
//! hold two), which is what the termination checker produces: an argument is
//! related to at most one parameter, the one it was matched out of.
//! [`Graph::new`] keeps the strongest when given more; dropping an arc can
//! only turn an acceptance into a rejection.

use crate::collections::HashMap;
use std::collections::hash_map::Entry;

use crate::budget::{Budget, ResourceError};

/// How an argument relates to a parameter of the caller.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Label {
    /// At most the parameter: the parameter itself, or the value it was
    /// matched as, rebuilt exactly.
    Le,
    /// Strictly smaller: a part of a value matched out of the parameter.
    Lt,
}

impl Label {
    /// The label of a path through two arcs: strict if either is.
    fn then(self, other: Label) -> Label {
        self.max(other)
    }
}

/// An arc into one argument position of the callee.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Arc {
    /// The caller's parameter position.
    pub from: usize,
    pub label: Label,
}

/// A size-change graph from member `from` to member `to`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Graph {
    pub from: usize,
    pub to: usize,
    /// The arity of `from`: every arc's `from` is below it.
    from_arity: usize,
    /// One entry per parameter position of `to`.
    entries: Box<[Option<Arc>]>,
}

impl Graph {
    /// A graph from `from` (with `from_arity` parameters) to `to` (with
    /// `to_arity`), with arcs `(caller position, callee position, label)`.
    /// Of several arcs into one callee position, keeps the strongest: a `<`
    /// over a `≤`, and of equals the first given. `None` if a position is
    /// out of range.
    pub fn new(
        from: usize,
        from_arity: usize,
        to: usize,
        to_arity: usize,
        arcs: &[(usize, usize, Label)],
    ) -> Option<Graph> {
        let mut entries = vec![None; to_arity];
        for &(i, j, label) in arcs {
            if i >= from_arity || j >= to_arity {
                return None;
            }
            let entry: &mut Option<Arc> = &mut entries[j];
            if entry.is_none_or(|old| label > old.label) {
                *entry = Some(Arc { from: i, label });
            }
        }
        Some(Graph {
            from,
            to,
            from_arity,
            entries: entries.into(),
        })
    }

    pub fn from_arity(&self) -> usize {
        self.from_arity
    }

    /// For each parameter position of `to`, the arc into it, if any.
    pub fn entries(&self) -> &[Option<Arc>] {
        &self.entries
    }

    /// The graph of a call by `self` followed by a call by `next`: `None`
    /// unless `next` starts where `self` ends.
    pub fn compose(&self, next: &Graph) -> Option<Graph> {
        if self.to != next.from || self.entries.len() != next.from_arity {
            return None;
        }
        let entries = next
            .entries
            .iter()
            .map(|entry| {
                let second = (*entry)?;
                let first = self.entries[second.from]?;
                Some(Arc {
                    from: first.from,
                    label: first.label.then(second.label),
                })
            })
            .collect();
        Some(Graph {
            from: self.from,
            to: next.to,
            from_arity: self.from_arity,
            entries,
        })
    }

    /// From a member to itself, and composing it with itself gives itself.
    pub fn is_idempotent(&self) -> bool {
        self.from == self.to && self.compose(self).as_ref() == Some(self)
    }

    /// Some parameter is strictly smaller than itself.
    pub fn has_strict_diagonal(&self) -> bool {
        self.entries.iter().enumerate().any(|(k, entry)| {
            *entry
                == Some(Arc {
                    from: k,
                    label: Label::Lt,
                })
        })
    }
}

/// The calls between the members of a group, numbered from 0.
pub struct Group {
    arities: Vec<usize>,
    calls: Vec<Graph>,
}

/// A call in a [`Group`], numbered in the order they were added.
pub type CallId = usize;

/// Why a group might not terminate.
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Terminates,
    /// `path` is a cycle of calls (each starting where the previous ended,
    /// the last ending where the first starts) whose composition is
    /// `graph`: idempotent, with nothing strictly decreasing to itself.
    NoDescent {
        path: Vec<CallId>,
        graph: Graph,
    },
}

/// How a graph in the closure was found, for rebuilding its path.
#[derive(Clone, Copy)]
enum Parent {
    Call(CallId),
    /// The graph at this index in the closure, followed by this call.
    Then(usize, CallId),
}

/// The default limit on the number of distinct graphs in a closure.
pub const MAX_GRAPHS: usize = 100_000;

impl Group {
    /// A group whose members have these arities (definition-entry arities,
    /// counting implicit parameters).
    pub fn new(arities: Vec<usize>) -> Group {
        Group {
            arities,
            calls: Vec::new(),
        }
    }

    pub fn arities(&self) -> &[usize] {
        &self.arities
    }

    pub fn calls(&self) -> &[Graph] {
        &self.calls
    }

    /// Adds a call from member `from` to member `to`, with arcs `(caller
    /// position, callee position, label)`. Positions with no arc are
    /// unknown. `None` (adding nothing) if a member or position is out of
    /// range. Never merged with another call, even one with the same ends.
    pub fn call(
        &mut self,
        from: usize,
        to: usize,
        arcs: &[(usize, usize, Label)],
    ) -> Option<CallId> {
        let graph = Graph::new(
            from,
            *self.arities.get(from)?,
            to,
            *self.arities.get(to)?,
            arcs,
        )?;
        self.calls.push(graph);
        Some(self.calls.len() - 1)
    }

    /// Decides the group, counting a step of `budget` per composition and
    /// allowing at most `max_graphs` distinct graphs in the closure. Running
    /// out of either is an error: there's no answer, so nothing is
    /// accepted.
    pub fn check(&self, budget: &Budget, max_graphs: usize) -> Result<Outcome, ResourceError> {
        let mut seen: HashMap<Graph, usize> = HashMap::default();
        let mut closure: Vec<(Graph, Parent)> = Vec::new();
        // Adds a graph unless it's already there; returns the outcome if
        // it's a loop that fails the check.
        let mut add = |closure: &mut Vec<(Graph, Parent)>, graph: Graph, parent: Parent| {
            let Entry::Vacant(slot) = seen.entry(graph) else {
                return Ok(None);
            };
            // Each graph after the calls' own comes from one composition,
            // so this is a bound on work too, but mainly on memory.
            if closure.len() >= max_graphs {
                return Err(ResourceError::Work);
            }
            let graph = slot.key().clone();
            slot.insert(closure.len());
            let fails = graph.is_idempotent() && !graph.has_strict_diagonal();
            closure.push((graph, parent));
            Ok(fails.then(|| closure.len() - 1))
        };

        let mut failed = None;
        for (c, graph) in self.calls.iter().enumerate() {
            failed = failed.or(add(&mut closure, graph.clone(), Parent::Call(c))?);
        }
        // Every path is a call followed by more calls, so extending every
        // graph on the right by every call reaches all of them.
        let mut next = 0;
        while failed.is_none() && next < closure.len() {
            for (c, call) in self.calls.iter().enumerate() {
                if call.from != closure[next].0.to {
                    continue;
                }
                budget.step()?;
                let graph = closure[next]
                    .0
                    .compose(call)
                    .expect("internal error: the group's graphs have its arities");
                if let Some(f) = add(&mut closure, graph, Parent::Then(next, c))? {
                    failed = Some(f);
                    break;
                }
            }
            next += 1;
        }

        Ok(match failed {
            None => Outcome::Terminates,
            Some(f) => {
                let mut path = Vec::new();
                let mut at = f;
                loop {
                    match closure[at].1 {
                        Parent::Call(c) => {
                            path.push(c);
                            break;
                        }
                        Parent::Then(prev, c) => {
                            path.push(c);
                            at = prev;
                        }
                    }
                }
                path.reverse();
                Outcome::NoDescent {
                    path,
                    graph: closure[f].0.clone(),
                }
            }
        })
    }
}
