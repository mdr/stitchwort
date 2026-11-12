//! What relies on which open goal (docs/proposals/using-unfinished-proofs.md
//! §5, D3504-D3507): `check`'s summary, `stitchwort goal`, `audit` and
//! `axioms` all read it from here.
//!
//! Reliance is read off the checked terms (`Elaborator::goals_relied_on`),
//! and a goal is named from its assumption's label and span, never from the
//! elaborator's bookkeeping. A declaration that was not checked because a
//! computation it needs is stuck on a goal is *blocked* on it
//! (`Elaborator::blocked_on`).
//!
//! The same for errors, which are declarations' own (docs/proposals/
//! tests-with-errors.md §4.3): [`Errors`] says which declarations have one
//! and which can't be checked until one is fixed.

use std::collections::BTreeSet;

use serde::Serialize;
use stitchwort_core::DefId;
use stitchwort_syntax::{Diagnostic, Severity};

use crate::audit::Generated;
use crate::driver::Session;

/// One gap's place: where its `?` or error is and which declaration it is
/// in.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct GoalPlace {
    /// The full name of the declaration the gap is in.
    pub declaration: String,
    pub file: String,
    pub line: usize,
    pub column: usize,
    pub kind: GapKind,
}

/// What an assumption stands for: an open goal, or a declaration with an
/// error whose statement checked (its stand-in, D3527).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum GapKind {
    Goal,
    Error,
}

impl GoalPlace {
    /// `file:line:column`.
    pub fn place(&self) -> String {
        format!("{}:{}:{}", self.file, self.line, self.column)
    }

    /// The declaration's own name, without its namespace: `addComm`.
    pub fn short(&self) -> &str {
        short_name(&self.declaration)
    }

    /// "`addComm`'s goal (src/Demo/Demo.sw:3:46)", or without "goal" if
    /// `word` is false; for an error, "`beats`, which has an error (…)".
    pub fn describe(&self, word: bool) -> String {
        if self.is_error() {
            return format!("`{}`, which has an error ({})", self.short(), self.place());
        }
        let goal = if word { " goal" } else { "" };
        format!("`{}`'s{goal} ({})", self.short(), self.place())
    }

    /// Whether it is a declaration with an error, not an open goal.
    pub fn is_error(&self) -> bool {
        self.kind == GapKind::Error
    }
}

/// `name` without its namespace: the part after the last `.`, except that
/// a test's name is written in quotes and may contain dots.
pub fn short_name(name: &str) -> &str {
    if let Some(i) = name.find("test \"") {
        return &name[i..];
    }
    name.rsplit_once('.').map_or(name, |(_, last)| last)
}

/// Up to the first three goals, then "and N more".
pub fn describe_goals(goals: &[GoalPlace], word: bool) -> String {
    let mut parts: Vec<String> = (goals.iter().take(3)).map(|g| g.describe(word)).collect();
    if goals.len() > 3 {
        parts.push(format!("and {} more", goals.len() - 3));
    }
    parts.join(", ")
}

/// What must happen before a declaration waiting for `gaps` can be
/// checked: "`half`'s goal (…) is filled", "`beats` (…) is fixed", or
/// both, joined by "and".
pub fn until(gaps: &[GoalPlace]) -> String {
    let (errors, goals): (Vec<GoalPlace>, Vec<GoalPlace>) =
        gaps.iter().cloned().partition(GoalPlace::is_error);
    let verb = |n: usize| if n == 1 { "is" } else { "are" };
    let mut parts = Vec::new();
    if !goals.is_empty() {
        parts.push(format!(
            "{} {} filled",
            describe_goals(&goals, true),
            verb(goals.len())
        ));
    }
    if !errors.is_empty() {
        let mut named: Vec<String> = (errors.iter().take(3))
            .map(|g| format!("`{}` ({})", g.short(), g.place()))
            .collect();
        if errors.len() > 3 {
            named.push(format!("and {} more", errors.len() - 3));
        }
        parts.push(format!("{} {} fixed", named.join(", "), verb(errors.len())));
    }
    parts.join(" and ")
}

/// A declaration, written in source, and the goals it relies on or waits
/// for.
#[derive(Clone, Debug)]
pub struct Dependent {
    pub name: String,
    pub goals: Vec<GoalPlace>,
}

/// One open goal, as `stitchwort goal` lists it.
#[derive(Clone, Debug)]
pub struct OpenGoal {
    pub place: GoalPlace,
    /// What must be shown, as after `⊢`, as written (D3522).
    pub target: String,
    /// What it computes to, when that prints differently.
    pub computed: Option<String>,
    /// The declarations written in source that rely on it, checked
    /// assuming it holds.
    pub relied_on_by: Vec<String>,
    /// The declarations that can't be checked until it is filled.
    pub blocking: Vec<String>,
    /// The equation lemmas (`half.eq1`) made for the definition with the
    /// `?`, unfinished too.
    pub equations: Vec<String>,
}

/// Every open goal, and what relies on or waits for goals.
#[derive(Clone, Debug, Default)]
pub struct Reliance {
    pub goals: Vec<OpenGoal>,
    /// Declarations checked assuming goals hold (not the ones that have
    /// the goal themselves: they're the goal's own).
    pub relying: Vec<Dependent>,
    /// Declarations not checked, waiting for a goal.
    pub blocked: Vec<Dependent>,
}

/// Where an error is reported, and the declaration it is in.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ErrorPlace {
    /// The full name of the declaration with the error.
    pub declaration: String,
    /// Its place, if the error has one.
    pub file: Option<String>,
    pub line: Option<usize>,
    pub column: Option<usize>,
}

impl ErrorPlace {
    /// `file:line:column`, empty if the error has no place.
    pub fn place(&self) -> String {
        match (&self.file, self.line, self.column) {
            (Some(file), Some(line), Some(column)) => format!("{file}:{line}:{column}"),
            _ => String::new(),
        }
    }

    /// The declaration's own name, without its namespace.
    pub fn short(&self) -> &str {
        short_name(&self.declaration)
    }

    /// "`broken` (src/a.sw:5:29)", or just the name if it has no place.
    pub fn describe(&self) -> String {
        match self.place().as_str() {
            "" => format!("`{}`", self.short()),
            place => format!("`{}` ({place})", self.short()),
        }
    }
}

/// A declaration that can't be checked until an error is fixed.
#[derive(Clone, Debug)]
pub struct WaitingForError {
    /// Its full name.
    pub name: String,
    pub theorem: bool,
    pub test: bool,
    /// The declaration with the error it needs, and where the error is.
    pub needs: ErrorPlace,
}

/// The errors of the last load: which declarations have one, and which
/// can't be checked until one is fixed. Errors in declarations that don't
/// parse are counted, with no place if the parser gave none.
#[derive(Clone, Debug, Default)]
pub struct Errors {
    /// Declarations with an error of their own, in the order checked.
    pub has: Vec<ErrorPlace>,
    pub waiting: Vec<WaitingForError>,
}

impl Errors {
    pub fn is_empty(&self) -> bool {
        self.has.is_empty() && self.waiting.is_empty()
    }
}

/// Whether `d` reports an open goal, as an error-level goal or, under
/// `check: open-goals: warn`, a warning.
pub fn is_goal(d: &Diagnostic) -> bool {
    d.severity == Severity::Goal || (d.severity == Severity::Warning && d.code == "GOAL")
}

impl Session {
    /// The errors the last load found and what waits for them.
    pub fn errors(&self) -> Errors {
        let place = |declaration: String, span: Option<stitchwort_syntax::Span>| {
            let at = span
                .filter(|s| s.file.index() < self.sources.len())
                .map(|span| {
                    let file = self.sources.get(span.file);
                    let before = &file.text[..(span.start as usize).min(file.text.len())];
                    (
                        file.name.clone(),
                        before.matches('\n').count() + 1,
                        before.rsplit('\n').next().unwrap_or("").chars().count() + 1,
                    )
                });
            ErrorPlace {
                declaration,
                file: at.as_ref().map(|a| a.0.clone()),
                line: at.as_ref().map(|a| a.1),
                column: at.as_ref().map(|a| a.2),
            }
        };
        let mut errors = Errors::default();
        for f in self.elab.failed_decls() {
            if f.own {
                errors.has.push(place(f.full_name(), f.error_at));
            } else {
                errors.waiting.push(WaitingForError {
                    name: f.full_name(),
                    theorem: f.theorem,
                    test: f.test,
                    needs: place(f.root.clone(), f.error_at),
                });
            }
        }
        // What waits for a declaration with an error that stands in for its
        // statement (D3527): it was checked as far as computing through the
        // stand-in, so it is blocked on it, not failed.
        let g = &self.elab.ev();
        for d in self.reliance(&[]).blocked {
            let Some(gap) = d.goals.iter().find(|gap| gap.is_error()) else {
                continue;
            };
            if errors.waiting.iter().any(|w| w.name == d.name) {
                continue;
            }
            let theorem = (g.env.defs().iter()).any(|def| **def.path() == *d.name && def.theorem());
            errors.waiting.push(WaitingForError {
                test: short_name(&d.name).starts_with("test \""),
                theorem,
                needs: ErrorPlace {
                    declaration: gap.short().to_string(),
                    file: Some(gap.file.clone()),
                    line: Some(gap.line),
                    column: Some(gap.column),
                },
                name: d.name,
            });
        }
        errors
    }

    /// Where assumption `id`'s `?` or error is written.
    pub fn goal_place(&self, id: DefId) -> GoalPlace {
        let span = self.elab.assumption_span(id);
        let file = self.sources.get(span.file);
        let before = &file.text[..(span.start as usize).min(file.text.len())];
        GoalPlace {
            declaration: self.elab.assumption_owner(id).unwrap_or_default(),
            file: file.name.clone(),
            line: before.matches('\n').count() + 1,
            column: before.rsplit('\n').next().unwrap_or("").chars().count() + 1,
            kind: if self.elab.is_error_stand_in(id) {
                GapKind::Error
            } else {
                GapKind::Goal
            },
        }
    }

    /// Assumption `id`'s goal as a type, `(n m: Nat) -> n + m = m + n`.
    pub fn goal_type_text(&self, id: DefId) -> String {
        let g = &self.elab.ev();
        stitchwort_core::pretty::term(g, &[], g.def(id).ty())
    }

    /// The places of `ids`, in source order.
    pub fn goal_places(&self, ids: &BTreeSet<DefId>) -> Vec<GoalPlace> {
        let mut places: Vec<GoalPlace> = ids.iter().map(|id| self.goal_place(*id)).collect();
        places.sort();
        places.dedup();
        places
    }

    /// Whether `id` is a declaration written in source, as opposed to one
    /// the compiler made (an equation lemma, a lifted `match`).
    fn written(&self, generated: &Generated, id: DefId) -> bool {
        let g = &self.elab.ev();
        let def = g.def(id);
        def.assumption().is_none() && !def.path().contains('%') && !generated.contains(g, id)
    }

    /// The goals `reported` lists, and what relies on or waits for them.
    /// Goals the elaborator couldn't state as an assumption (see
    /// `assume.rs`) are listed with nothing that relies on them. Only
    /// definitions and theorems are listed in `relied_on_by` and the rely
    /// counts, never types.
    pub fn reliance(&self, reported: &[Diagnostic]) -> Reliance {
        let assumptions = self.elab.assumptions();
        let defs = self.elab.ev().env.defs().len();
        let made = Generated::new(&self.elab.ev());
        let mut relying: Vec<(DefId, BTreeSet<DefId>)> = Vec::new();
        let mut blocked: Vec<(DefId, BTreeSet<DefId>)> = Vec::new();
        let mut generated: Vec<(DefId, BTreeSet<DefId>)> = Vec::new();
        if let Some(first) = assumptions.first() {
            for i in first.0..defs {
                let id = DefId(i);
                if !self.written(&made, id) {
                    if self.elab.relies_on_goal(id) && made.contains(&self.elab.ev(), id) {
                        generated.push((id, self.elab.goals_relied_on(id)));
                    }
                    continue;
                }
                let waits: BTreeSet<DefId> = self.elab.blocked_on(id).into_iter().collect();
                if !waits.is_empty() {
                    blocked.push((id, waits));
                } else if self.elab.relies_on_goal(id)
                    // One with an error of its own is reported as that,
                    // not as relying on another's.
                    && self.elab.ev().def(id).state() == stitchwort_core::globals::State::Final
                {
                    let goals = self.elab.goals_relied_on(id);
                    // A declaration with a `?` relies on its own goal.
                    let own = |a: &DefId| {
                        self.elab.assumption_owner(*a).as_deref()
                            == Some(&*self.elab.ev().def(id).path().to_string())
                    };
                    if !goals.iter().all(own) {
                        relying.push((id, goals));
                    }
                }
            }
        }
        let name = |id: &DefId| self.elab.ev().def(*id).path().to_string();
        let named = |list: Vec<(DefId, BTreeSet<DefId>)>| -> Vec<(String, BTreeSet<DefId>)> {
            list.into_iter()
                .map(|(id, goals)| (name(&id), goals))
                .collect()
        };
        let (relying, generated) = (named(relying), named(generated));
        let mut blocked = named(blocked);
        // A declaration whose signature waited has no definition.
        blocked.extend(
            (self.elab.waiting_without_definition().into_iter())
                .map(|(name, goals)| (name, goals.into_iter().collect())),
        );
        blocked.sort_by(|a, b| a.0.cmp(&b.0));
        // Each reported goal, with the assumption made for it, if any.
        let mut goals: Vec<OpenGoal> = Vec::new();
        for d in reported.iter().filter(|d| is_goal(d)) {
            let (Some(span), Some(data)) = (d.primary_span(), d.goal_data()) else {
                continue;
            };
            let assumption = assumptions
                .iter()
                .copied()
                .find(|a| self.elab.assumption_span(*a) == span);
            let place = match assumption {
                Some(a) => self.goal_place(a),
                None => {
                    let file = self.sources.get(span.file);
                    let before = &file.text[..(span.start as usize).min(file.text.len())];
                    GoalPlace {
                        declaration: d.message.trim_start_matches("in ").replace('`', ""),
                        file: file.name.clone(),
                        line: before.matches('\n').count() + 1,
                        column: before.rsplit('\n').next().unwrap_or("").chars().count() + 1,
                        kind: GapKind::Goal,
                    }
                }
            };
            let names_for = |list: &[(String, BTreeSet<DefId>)]| -> Vec<String> {
                match assumption {
                    Some(a) => (list.iter())
                        .filter(|(_, goals)| goals.contains(&a))
                        .map(|(name, _)| name.clone())
                        .filter(|n| *n != place.declaration)
                        .collect(),
                    None => Vec::new(),
                }
            };
            goals.push(OpenGoal {
                relied_on_by: names_for(&relying),
                blocking: names_for(&blocked),
                equations: names_for(&generated)
                    .into_iter()
                    .filter(|e| {
                        e.strip_prefix(place.declaration.as_str())
                            .is_some_and(|rest| rest.starts_with(".eq"))
                    })
                    .collect(),
                target: data.shown().to_string(),
                computed: data.computed().map(str::to_string),
                place,
            });
        }
        goals.sort_by(|a, b| a.place.cmp(&b.place));
        let dependents = |list: Vec<(String, BTreeSet<DefId>)>| -> Vec<Dependent> {
            list.into_iter()
                .map(|(name, goals)| Dependent {
                    name,
                    goals: self.goal_places(&goals),
                })
                .collect()
        };
        Reliance {
            goals,
            relying: dependents(relying),
            blocked: dependents(blocked),
        }
    }
}
