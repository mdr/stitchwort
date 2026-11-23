//! `stitchwort audit`, stage 1 (SW-912, D2040;
//! docs/research/agentic-proving.md §7.1 and T1): the trust check a proof
//! lane runs before it reports, and the merge gate runs. For each theorem it
//! reports
//! - the axioms it depends on beyond an allowlist (a failure; [`axioms`]),
//! - whether it, or anything it uses, is unfinished, with an open goal `?`
//!   (a failure; `Kernel::unfinished`), or failed to check (a failure),
//! - and, for a theorem that checked, what the counterexample search says
//!   about its statement: a counterexample is a failure (the proof checked,
//!   so an axiom, the compiler or the search is wrong), and hypotheses that
//!   held for none of the inputs tried are a warning, since the theorem may
//!   be vacuous (T2; [`Verdict::NeverHeld`]).
//!
//! The statement hash (`--base`, `--challenge`) is stage 2, and changed
//! programs and instances stage 3.

use std::collections::BTreeSet;
use std::rc::Rc;

use serde::Serialize;
use stitchwort_core::collections::HashMap;
use stitchwort_core::globals::{HashKey, State};
use stitchwort_core::value::force;
use stitchwort_core::{DefId, Ev, Limits, Term, Value};
use stitchwort_elab::counterexample::{Budget, STATEMENT_STEPS};
use stitchwort_syntax::Span;

use crate::axioms::AxiomWalk;
use crate::counterexample::{TheoremSearch, Verdict};
use crate::driver::Session;
use crate::reliance::{ErrorPlace, Errors, GoalPlace, describe_goals};

/// Every axiom there is. Today the core has one (docs/core.md, Axioms).
pub const AXIOMS: &[&str] = &["Quot.sound"];

/// The axioms a theorem may use unless the project says otherwise
/// (`audit: allowed-axioms:` in `stitchwort.yaml`, or `--allowed-axioms`):
/// all of them, which is today `Quot.sound`. It is part of the core's
/// trusted base, as `propext`, `Quot.sound` and `Classical.choice` are
/// Lean's, and a project can narrow the list to none.
pub const DEFAULT_ALLOWED: &[&str] = &["Quot.sound"];

/// How bad a finding is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    /// Evidence that something may be wrong; fails only with `--strict`.
    Warn,
    /// The theorem can't be trusted as it stands.
    Fail,
}

/// What a finding is about, as the JSON's `check` names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Check {
    /// It depends on an axiom outside the allowlist.
    Axioms,
    /// It, or something it uses, has an open goal (`?`).
    Unfinished,
    /// It didn't check.
    Failed,
    /// It can't be checked until an error elsewhere is fixed.
    Waiting,
    /// The search found a counterexample to a theorem that checked.
    Counterexample,
    /// The search found no input that made its hypotheses true.
    Vacuous,
}

#[derive(Clone, Debug, Serialize)]
pub struct Finding {
    pub check: Check,
    pub severity: Severity,
    pub message: String,
}

/// How the theorem's checking ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    Checked,
    /// Checked by the kernel assuming gaps hold: it has an open goal, or
    /// relies on one or on a declaration with an error (its statement).
    /// Never passes.
    Assuming,
    /// Not checked: it waits for an open goal to be filled or an error to
    /// be fixed, or uses something unfinished.
    Unfinished,
    /// Not checked: it uses a declaration with an error (SW-2943).
    Waiting,
    Failed,
}

/// One theorem's audit.
#[derive(Clone, Debug, Serialize)]
pub struct TheoremAudit {
    /// Its full name.
    pub name: String,
    /// Whether the compiler generated it rather than the source (an
    /// equation, a functional induction, an update lemma or a record's
    /// extensionality lemma).
    pub generated: bool,
    pub status: Status,
    /// The gaps it relies on (`assuming`) or waits for (`unfinished`), in
    /// source order, each with its kind: an open goal or a declaration
    /// with an error.
    #[serde(rename = "openGoals")]
    pub open_goals: Vec<GoalPlace>,
    /// For a theorem that has an error (`failed`) or waits for one
    /// (`waiting`): the declaration with the error and where it is
    /// reported.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<ErrorPlace>,
    /// The axioms it depends on, allowed or not (only if it checked).
    pub axioms: Vec<&'static str>,
    /// The counterexample search's verdict and line (only if it checked
    /// and the search ran).
    pub search: Option<SearchSummary>,
    pub findings: Vec<Finding>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SearchSummary {
    pub verdict: Verdict,
    pub line: String,
    /// Inputs tried, and those every hypothesis held for.
    pub tried: usize,
    pub held: usize,
    /// Whether it concludes an empty type, so claims its hypotheses
    /// contradict each other ([`concludes_empty`]).
    pub refutes: bool,
    /// For a theorem whose hypotheses held for no input, a checked theorem
    /// that applies it to arguments for all its parameters and hypotheses
    /// ([`witness_of`]): they can hold together, so it isn't vacuous.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub witness: Option<String>,
}

impl TheoremAudit {
    /// The worst finding, if any.
    pub fn worst(&self) -> Option<Severity> {
        self.findings.iter().map(|f| f.severity).max()
    }
}

/// The options of an audit.
pub struct Options {
    /// The axioms a theorem may use.
    pub allowed: BTreeSet<String>,
    /// The counterexample search's budget per theorem; `None` skips the
    /// search (and so the vacuity warning).
    pub search: Option<Budget>,
}

/// Which declarations the compiler made rather than the reader wrote: a
/// definition's equation (`f.eq2`) or functional induction (`f.induct`), a
/// shared field's update lemma (`T.f.update.g`), and every declaration made
/// for another one: `f.unfold` for a `decreasing` definition, `T.ext` and
/// `T.size` for a type, whatever the name.
///
/// The first two have reserved names ([`stitchwort_elab::is_generated_name`]).
/// An update lemma's name can't be written, and its owner is a data type.
/// For the rest the elaborator gives what it makes for a declaration that
/// declaration's own span, so a declaration whose name extends another's
/// (`Book.gcd2.unfold` after `Book.gcd2`) and whose span is the same one was
/// made for it. A written `T.ext` has a span of its own.
pub(crate) struct Generated {
    /// The full names of the declarations at each span.
    at: HashMap<Span, Vec<Rc<str>>>,
    /// Each full name, to the definition that has it.
    by_path: HashMap<Rc<str>, DefId>,
}

impl Generated {
    pub(crate) fn new(g: &Ev) -> Self {
        let mut at: HashMap<Span, Vec<Rc<str>>> = HashMap::default();
        let mut by_path: HashMap<Rc<str>, DefId> = HashMap::default();
        for (i, def) in g.env.defs().iter().enumerate() {
            at.entry(def.span()).or_default().push(def.path().clone());
            by_path.insert(def.path().clone(), DefId(i));
        }
        for data in g.env.datas() {
            at.entry(data.span()).or_default().push(data.path().clone());
        }
        Generated { at, by_path }
    }

    /// Whether `id` is a declaration the compiler made.
    pub(crate) fn contains(&self, g: &Ev, id: DefId) -> bool {
        let def = g.def(id);
        if stitchwort_elab::is_generated_name(g, def.name()) {
            return true;
        }
        let path = def.path().to_string();
        if is_update_lemma(g, &path) {
            return true;
        }
        (self.at.get(&def.span()).into_iter().flatten()).any(|owner| {
            path.strip_prefix(&**owner)
                .is_some_and(|rest| rest.starts_with('.'))
        })
    }

    /// Whether the definition with full name `path` is one the compiler
    /// made; `false` for a name no definition has (a hypothesis, say).
    pub(crate) fn contains_name(&self, g: &Ev, path: &str) -> bool {
        self.by_path
            .get(path)
            .is_some_and(|id| self.contains(g, *id))
    }
}

/// Whether `T.f.update.g` names a shared field's generated update lemma:
/// `update` is its third part from the end, and `T` is a data type.
fn is_update_lemma(g: &Ev, path: &str) -> bool {
    let mut parts = path.rsplitn(4, '.');
    let (Some(_read), Some(op), Some(field), Some(owner)) =
        (parts.next(), parts.next(), parts.next(), parts.next())
    else {
        return false;
    };
    op == "update" && !field.is_empty() && (g.env.datas().iter()).any(|d| &**d.path() == owner)
}

/// The theorems of `g` whose full name `keep` keeps, in the order they were
/// declared, with their full names. Local definitions lifted out of a
/// theorem (`%` names) aren't theorems of their own, nor are the
/// assumptions that stand for a gap in one.
pub fn theorems(g: &Ev, keep: &dyn Fn(&str) -> bool) -> Vec<(DefId, String)> {
    (0..g.env.defs().len())
        .map(DefId)
        .filter_map(|id| {
            let def = g.def(id);
            let path = def.path().to_string();
            (def.theorem() && def.assumption().is_none() && !path.contains('%') && keep(&path))
                .then_some((id, path))
        })
        .collect()
}

/// An allowlist's names that aren't axioms, for an error.
pub fn unknown_axioms<'a>(allowed: impl IntoIterator<Item = &'a String>) -> Vec<&'a String> {
    allowed
        .into_iter()
        .filter(|a| !AXIOMS.contains(&a.as_str()))
        .collect()
}

impl Session {
    /// The audits of the theorems that have an error or can't be checked
    /// until one is fixed, which have no definition for [`Session::audit`]
    /// to look at (`keep` as for [`theorems`], on their full names).
    pub fn audit_failed(&self, keep: &dyn Fn(&str) -> bool) -> Vec<TheoremAudit> {
        let errors = self.errors();
        let mut audits = Vec::new();
        for f in self.elab.failed_decls().iter().filter(|f| f.theorem) {
            let name = f.full_name();
            if !keep(&name) {
                continue;
            }
            let Some((status, check, error, message)) = failure_of(&errors, &name) else {
                continue;
            };
            audits.push(TheoremAudit {
                name,
                generated: false,
                status,
                open_goals: Vec::new(),
                error,
                axioms: Vec::new(),
                search: None,
                findings: vec![Finding {
                    check,
                    severity: Severity::Fail,
                    message,
                }],
            });
        }
        audits
    }

    /// Audits each of `theorems` (as [`theorems`] gives them).
    pub fn audit(&mut self, theorems: &[(DefId, String)], options: &Options) -> Vec<TheoremAudit> {
        let mut walk = AxiomWalk::new();
        let generated = Generated::new(&self.elab.ev());
        let mut audits: Vec<TheoremAudit> = theorems
            .iter()
            .map(|(id, name)| self.audit_one(*id, name, options, &mut walk, &generated))
            .collect();
        // A theorem that didn't check says why, from the errors found. One
        // waiting only for declarations with an error that stand in for
        // their statements (D3527) waits for an error, not a goal.
        let for_error = |a: &TheoremAudit| {
            a.status == Status::Failed
                || (a.status == Status::Unfinished
                    && !a.open_goals.is_empty()
                    && a.open_goals.iter().all(GoalPlace::is_error))
        };
        if audits.iter().any(for_error) {
            let errors = self.errors();
            for a in audits.iter_mut().filter(|a| for_error(a)) {
                if let Some((status, check, error, message)) = failure_of(&errors, &a.name) {
                    a.status = status;
                    a.error = error;
                    a.findings = vec![Finding {
                        check,
                        severity: Severity::Fail,
                        message,
                    }];
                }
            }
        }
        audits
    }

    fn audit_one(
        &mut self,
        id: DefId,
        name: &str,
        options: &Options,
        walk: &mut AxiomWalk,
        generated: &Generated,
    ) -> TheoremAudit {
        let g = &self.elab.ev();
        let (status, goals) = match g.def(id).state() {
            // Checked assuming an open goal holds, which never passes
            // (docs/core.md "Assumptions (open goals)").
            State::Final if self.elab.relies_on_goal(id) => {
                let ids = self.elab.goals_relied_on(id);
                (Status::Assuming, self.goal_places(&ids))
            }
            State::Final => (Status::Checked, Vec::new()),
            _ if self.elab.marked_unfinished(HashKey::Def(id)) => {
                let ids = self.elab.blocked_on(id).into_iter().collect();
                (Status::Unfinished, self.goal_places(&ids))
            }
            _ => (Status::Failed, Vec::new()),
        };
        let g = &self.elab.ev();
        let mut audit = TheoremAudit {
            name: name.to_string(),
            generated: generated.contains(g, id),
            status,
            open_goals: goals.clone(),
            error: None,
            axioms: Vec::new(),
            search: None,
            findings: Vec::new(),
        };
        match status {
            Status::Assuming => {
                audit.findings.push(Finding {
                    check: Check::Unfinished,
                    severity: Severity::Fail,
                    message: assuming_message(g.def(id).path().as_ref(), &goals),
                });
                return audit;
            }
            Status::Unfinished => {
                let message = if goals.is_empty() {
                    "unfinished: it, or something it uses, has an open goal (`?`), so it isn't \
                     checked"
                        .to_string()
                } else {
                    format!("can't be checked until {}", crate::reliance::until(&goals))
                };
                audit.findings.push(Finding {
                    check: Check::Unfinished,
                    severity: Severity::Fail,
                    message,
                });
                return audit;
            }
            // Only `audit_failed` makes these: they have no definition.
            Status::Waiting => unreachable!("a definition that exists was checked"),
            Status::Failed => {
                audit.findings.push(Finding {
                    check: Check::Failed,
                    severity: Severity::Fail,
                    message: "it didn't check (see the errors above)".to_string(),
                });
                return audit;
            }
            Status::Checked => {}
        }
        audit.axioms = walk.axioms(g, id).into_iter().collect();
        let refused: Vec<&str> = (audit.axioms.iter().copied())
            .filter(|a| !options.allowed.contains(*a))
            .collect();
        if !refused.is_empty() {
            audit.findings.push(Finding {
                check: Check::Axioms,
                severity: Severity::Fail,
                message: format!(
                    "uses {} beyond the allowed axioms ({})",
                    refused.join(", "),
                    if options.allowed.is_empty() {
                        "none".to_string()
                    } else {
                        (options.allowed.iter().cloned())
                            .collect::<Vec<_>>()
                            .join(", ")
                    }
                ),
            });
        }
        let Some(budget) = options.search else {
            return audit;
        };
        let search = self.search_theorem(id, name, true, budget);
        let (verdict, line) = search.verdict();
        let log = &search.log;
        let mut witness = None;
        let held = log.tried.saturating_sub(log.discarded + log.out_of_steps);
        match verdict {
            Verdict::False => audit.findings.push(Finding {
                check: Check::Counterexample,
                severity: Severity::Fail,
                message: format!(
                    "{line}; this theorem checked, so an axiom it uses, the compiler or the \
                     search is wrong: please report it"
                ),
            }),
            Verdict::NeverHeld if !search.refutes && !audit.generated => {
                witness = self.witness_of(id);
                if witness.is_none() {
                    audit.findings.push(Finding {
                        check: Check::Vacuous,
                        severity: Severity::Warn,
                        message: format!(
                            "no input made the hypotheses true ({held} of {} cases){}: if they \
                             contradict each other, the theorem is vacuous",
                            log.tried,
                            rejecting(log)
                        ),
                    });
                }
            }
            _ => {}
        }
        audit.search = Some(SearchSummary {
            verdict,
            line,
            tried: log.tried,
            held,
            refutes: search.refutes,
            witness,
        });
        audit
    }

    /// A witness that theorem `id`'s hypotheses can hold together: a
    /// checked theorem with no parameters, counting those its type has
    /// once nicknames are unfolded, whose proof is `id` applied to
    /// arguments for every parameter and hypothesis of its statement
    /// (`closesWordExample := closesWord ")" byComputing`). Its statement
    /// has no free variables, so those arguments are closed proofs of the
    /// hypotheses at one input. Only an application of `id` itself counts,
    /// not a theorem that mentions it. Of those, the first declared.
    fn witness_of(&self, id: DefId) -> Option<String> {
        let g = &self.elab.ev();
        let arity = pi_arity(g, id)?;
        (0..g.env.defs().len()).map(DefId).find_map(|w| {
            let def = g.def(w);
            let applies = || {
                def.body().is_some_and(|body| {
                    let (head, args) = spine(body);
                    matches!(head, Term::Def(d) if *d == id) && args >= arity
                })
            };
            // The cheap tests first: unfolding a type is costly, and this
            // runs over every definition for each warning.
            (w != id
                && def.theorem()
                && def.assumption().is_none()
                && matches!(def.state(), State::Final)
                && applies()
                && pi_arity(g, w) == Some(0)
                && !self.elab.relies_on_goal(w))
            .then(|| def.path().to_string())
        })
    }

    /// Searches one theorem's statement within `budget`.
    pub fn search_theorem(
        &mut self,
        id: DefId,
        name: &str,
        checked: bool,
        budget: Budget,
    ) -> TheoremSearch {
        let (log, note) = self.elab.search_counterexample(id, budget);
        let g = &self.elab.ev();
        let limits = Limits {
            work: self.elab.options.limits.work.min(STATEMENT_STEPS),
            ..self.elab.options.limits
        };
        let saved = g.machine.budget.start(limits);
        let refutes = concludes_empty(g, id);
        g.machine.budget.restore(saved);
        TheoremSearch {
            name: name.to_string(),
            checked,
            refutes,
            log,
            note,
        }
    }
}

/// The leading binders of a statement: its parameters and hypotheses. Its
/// type is unfolded at the head, so a nickname for a forall type
/// (`def Claim: Prop := ∀ (n: Nat) (h: n + 1 = 0) => …`) is seen through.
/// `None` when the type can't be walked within the budget: then nothing
/// counts as a witness, since its arity isn't known.
fn pi_arity(g: &Ev, id: DefId) -> Option<usize> {
    let def = g.def(id);
    stitchwort_core::check::telescope(g, def.ty_value(), def.span())
        .ok()
        .map(|tel| tel.params.len())
}

/// A proof term's head and how many arguments it is applied to.
fn spine(mut term: &Term) -> (&Term, usize) {
    let mut args = 0;
    loop {
        match term {
            Term::App(f, _, _) => {
                args += 1;
                term = f;
            }
            Term::Ann(t, _) | Term::Loc(_, t) => term = t,
            _ => return (term, args),
        }
    }
}

/// What the warning says of the hypothesis that rejected the inputs, when
/// one hypothesis was the first false one for every input discarded and
/// none held: ` — all rejected by `h: n + 1 = 0``.
fn rejecting(log: &stitchwort_elab::counterexample::SearchLog) -> String {
    let mut named = log.rejected_by.iter().enumerate().filter(|(_, n)| **n > 0);
    match (named.next(), named.next()) {
        (Some((j, _)), None) if log.discarded > 0 => match log.hypotheses.get(j) {
            Some(h) => format!(", every one rejected by hypothesis `{h}`"),
            None => String::new(),
        },
        _ => String::new(),
    }
}

/// How a declaration called `name` failed, if the load found an error in
/// it or one it waits for: its status, the check, the error's place and
/// what to say.
fn failure_of(errors: &Errors, name: &str) -> Option<(Status, Check, Option<ErrorPlace>, String)> {
    if let Some(own) = errors.has.iter().find(|e| e.declaration == name) {
        let message = match own.place().as_str() {
            "" => "has an error".to_string(),
            place => format!("has an error ({place})"),
        };
        return Some((Status::Failed, Check::Failed, Some(own.clone()), message));
    }
    let waiting = errors.waiting.iter().find(|w| w.name == name)?;
    let at = match waiting.needs.place().as_str() {
        "" => String::new(),
        place => format!(" ({place})"),
    };
    let message = format!(
        "can't be checked until `{}` is fixed{at}",
        waiting.needs.short()
    );
    Some((
        Status::Waiting,
        Check::Waiting,
        Some(waiting.needs.clone()),
        message,
    ))
}

/// What audit says of a declaration checked assuming `goals` hold: that it
/// has one of its own, and that it relies on the others. A declaration
/// with an error stands in for its statement (D3527), so relying on one is
/// said as relying on that declaration.
fn assuming_message(name: &str, goals: &[GoalPlace]) -> String {
    let (errors, goals): (Vec<GoalPlace>, Vec<GoalPlace>) =
        goals.iter().cloned().partition(GoalPlace::is_error);
    let (own, others): (Vec<GoalPlace>, Vec<GoalPlace>) =
        goals.into_iter().partition(|g| g.declaration == name);
    let mut parts = Vec::new();
    if !errors.is_empty() {
        let statement = if errors.len() == 1 {
            "its statement"
        } else {
            "their statements"
        };
        parts.push(format!(
            "relies on {}; checked assuming {statement}",
            describe_goals(&errors, false)
        ));
    }
    if !own.is_empty() {
        let places: Vec<String> = own.iter().map(GoalPlace::place).collect();
        parts.push(match places.as_slice() {
            [one] => format!("has an open goal ({one})"),
            many => format!("has {} open goals ({})", many.len(), many.join(", ")),
        });
    }
    if !others.is_empty() {
        let (a, it) = if others.len() == 1 {
            ("an open goal".to_string(), "it holds")
        } else {
            (format!("{} open goals", others.len()), "they hold")
        };
        parts.push(format!(
            "relies on {a}: {}; checked assuming {it}",
            describe_goals(&others, false)
        ));
    }
    parts.join("; ")
}

/// Whether theorem `id` concludes an empty type (`Void`, or a `Not`, which
/// unfolds to `… → Void`): then it says its hypotheses contradict each
/// other, and the search finding none of its inputs satisfied them is what
/// it claims, not a sign it's vacuous (`someNotNone (found: Some m = None):
/// Void`).
pub fn concludes_empty(g: &Ev, id: DefId) -> bool {
    let Ok(mut ty) = force(g, g.def(id).ty_value().clone()) else {
        return false;
    };
    let mut level = 0;
    while let Value::Pi(_, _, _, cod, _) = &ty {
        let Ok(next) = cod.apply(g, Value::var(level)).and_then(|v| force(g, v)) else {
            return false;
        };
        level += 1;
        ty = next;
    }
    matches!(ty, Value::Data(d, _) if g.data(d).ctors().is_empty())
}

#[cfg(test)]
mod tests {
    use super::assuming_message;
    use crate::reliance::{GapKind, GoalPlace, until};

    fn place(declaration: &str, line: usize, kind: GapKind) -> GoalPlace {
        GoalPlace {
            declaration: declaration.to_string(),
            file: "src/a.sw".to_string(),
            line,
            column: 1,
            kind,
        }
    }

    /// What audit says names each gap by its kind: a declaration with an
    /// error stands in for its statement (D3527), never as an open goal.
    #[test]
    fn audit_names_a_gap_by_its_kind() {
        let error = place("A.doubleTwo", 9, GapKind::Error);
        let goal = place("A.addComm", 3, GapKind::Goal);
        assert_eq!(
            assuming_message("A.usesTwo", std::slice::from_ref(&error)),
            "relies on `doubleTwo`, which has an error (src/a.sw:9:1); checked assuming its \
             statement"
        );
        assert_eq!(
            assuming_message("A.both", &[error.clone(), goal.clone()]),
            "relies on `doubleTwo`, which has an error (src/a.sw:9:1); checked assuming its \
             statement; relies on an open goal: `addComm`'s (src/a.sw:3:1); checked assuming \
             it holds"
        );
        assert_eq!(
            until(&[goal, error]),
            "`addComm`'s goal (src/a.sw:3:1) is filled and `doubleTwo` (src/a.sw:9:1) is fixed"
        );
    }
}
