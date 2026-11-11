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

use serde::Serialize;
use stitchwort_core::globals::{HashKey, State};
use stitchwort_core::value::force;
use stitchwort_core::{DefId, Ev, Limits, Value};
use stitchwort_elab::counterexample::{Budget, STATEMENT_STEPS};

use crate::axioms::AxiomWalk;
use crate::counterexample::{TheoremSearch, Verdict};
use crate::driver::Session;
use crate::reliance::{GoalPlace, describe_goals};

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
    /// Checked by the kernel assuming open goals hold: it has one, or
    /// relies on one. Never passes.
    Assuming,
    /// Not checked: it waits for an open goal to be filled, or uses
    /// something unfinished.
    Unfinished,
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
    /// The open goals it relies on (`assuming`) or waits for
    /// (`unfinished`), in source order.
    #[serde(rename = "openGoals")]
    pub open_goals: Vec<GoalPlace>,
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

/// Whether `id` is a declaration the compiler made rather than one written
/// in source: a definition's equation (`f.eq2`) or functional induction
/// (`f.induct`), a shared field's update lemma (`T.f.update.g`), or a
/// record's extensionality lemma (`T.ext`).
///
/// The first two have reserved names ([`stitchwort_elab::is_generated_name`]).
/// An update lemma's name can't be written, and its owner is a data type. A
/// record gets `T.ext` unless it writes one, so a written `T.ext` is told
/// apart by its span: the generated one is at its type's own.
pub(crate) fn is_generated(g: &Ev, id: DefId) -> bool {
    let def = g.def(id);
    if stitchwort_elab::is_generated_name(g, def.name()) {
        return true;
    }
    let path = def.path().to_string();
    if is_update_lemma(g, &path) {
        return true;
    }
    let Some(owner) = path.strip_suffix(".ext") else {
        return false;
    };
    (g.env.datas().iter()).any(|d| &**d.path() == owner && d.record() && d.span() == def.span())
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
/// theorem (`%` names) aren't theorems of their own.
pub fn theorems(g: &Ev, keep: &dyn Fn(&str) -> bool) -> Vec<(DefId, String)> {
    (0..g.env.defs().len())
        .map(DefId)
        .filter_map(|id| {
            let def = g.def(id);
            let path = def.path().to_string();
            (def.theorem() && !path.contains('%') && keep(&path)).then_some((id, path))
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
    /// Audits each of `theorems` (as [`theorems`] gives them).
    pub fn audit(&mut self, theorems: &[(DefId, String)], options: &Options) -> Vec<TheoremAudit> {
        let mut walk = AxiomWalk::new();
        theorems
            .iter()
            .map(|(id, name)| self.audit_one(*id, name, options, &mut walk))
            .collect()
    }

    fn audit_one(
        &mut self,
        id: DefId,
        name: &str,
        options: &Options,
        walk: &mut AxiomWalk,
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
            generated: is_generated(g, id),
            status,
            open_goals: goals.clone(),
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
                    format!(
                        "can't be checked until {} {} filled",
                        describe_goals(&goals, true),
                        if goals.len() == 1 { "is" } else { "are" }
                    )
                };
                audit.findings.push(Finding {
                    check: Check::Unfinished,
                    severity: Severity::Fail,
                    message,
                });
                return audit;
            }
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
                audit.findings.push(Finding {
                    check: Check::Vacuous,
                    severity: Severity::Warn,
                    message: format!(
                        "no input made the hypotheses true ({held} of {} cases): if they \
                         contradict each other, the theorem is vacuous",
                        log.tried
                    ),
                });
            }
            _ => {}
        }
        audit.search = Some(SearchSummary {
            verdict,
            line,
            tried: log.tried,
            held,
            refutes: search.refutes,
        });
        audit
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

/// What audit says of a declaration checked assuming `goals` hold: that it
/// has one of its own, and that it relies on the others.
fn assuming_message(name: &str, goals: &[GoalPlace]) -> String {
    let (own, others): (Vec<GoalPlace>, Vec<GoalPlace>) =
        goals.iter().cloned().partition(|g| g.declaration == name);
    let mut parts = Vec::new();
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
    while let Value::Pi(_, _, _, cod) = &ty {
        let Ok(next) = cod.apply(g, Value::var(level)).and_then(|v| force(g, v)) else {
            return false;
        };
        level += 1;
        ty = next;
    }
    matches!(ty, Value::Data(d, _) if g.data(d).ctors().is_empty())
}
