//! `stitchwort search --at`, stage 2 (SW-915; docs/proposals/search.md
//! §5.7, §8 S2): what closes the goal at a `?`. The elaborator plans
//! (`stitchwort_elab::closing`): the candidates whose conclusion the goal's
//! target is an instance of (the hypotheses rigid, unfiltered: D2066), each
//! premise filled from a hypothesis where one fits. Here each plan becomes
//! proof text, and is checked: elaborated in the file's scope inside
//! `(((h: A) => …): (h: A) → … → T)`, and, with no `?` left, checked by
//! the kernel. A `?` the plan leaves is tried with `rfl`, `omega`, `ring`,
//! `cases` and `byDecision`; what still fails is a goal the suggestion leaves.
//!
//! Results come in four classes (review point 12): `exact` (the lemma
//! applied to the goal's terms), `withHypotheses` (premises filled from
//! hypotheses), `afterObligations` (premises closed by `rfl`, `omega`, `ring`,
//! `cases` or `byDecision`), each kernel-checked; and `applicable` (it applies,
//! leaving goals, listed). Separately, `rewrites`: equations and `Iff`s
//! whose side is a call in the target, as `rewrite L in ?` with the goal
//! that leaves (`rw?`'s direction, S2c). Nothing is reported as closing
//! the goal unless the kernel accepted it.

use std::cell::Cell;
use std::rc::Rc;
use std::time::Duration;

use stitchwort_core::budget::Instant;

use serde::Serialize;
use stitchwort_core::DataId;
use stitchwort_elab::Checked;
use stitchwort_elab::closing::{Arg, Goal, Plan};
use stitchwort_elab::search::{Candidate, Kind};
use stitchwort_syntax::{Diagnostic, FileId, GoalData, Hypothesis, Severity, SourceMap};

use crate::audit::Generated;
use crate::driver::Session;
use crate::project::Files;
use crate::search::{Scope, hidden, import_line};

/// What `search --at` was asked for.
#[derive(Clone, Debug)]
pub struct AtOptions {
    /// How many results of each list to show.
    pub limit: usize,
    /// How many of the matching candidates are tried, in rank order.
    pub max_candidates: usize,
    /// How long the checking may take in all; past it, what is left isn't
    /// tried, and the JSON says so (`exhausted: false`).
    pub time: Duration,
    /// Also the library's hidden helpers.
    pub all: bool,
    /// Declarations not to suggest, by full name (a benchmark leaves out
    /// the theorem whose statement is the goal).
    pub exclude: Vec<String>,
    /// Only declarations in these namespaces (`--in`, SW-993); none: all.
    /// The induction hypothesis and the goal's hypotheses are offered
    /// regardless.
    pub within: Vec<String>,
    /// Stop trying candidates once this many have closed the goal (rather
    /// than only applying to it): for the code action, which shows no more
    /// than that. None: try them all.
    pub stop_after_closing: Option<usize>,
    /// Try the simple closers one at a time first ([`Rung`], the ladder),
    /// and answer with the first that closes the goal alone, without the
    /// search: the editor's "Search for a proof" (SW-2966).
    pub simplest_first: bool,
}

impl Default for AtOptions {
    fn default() -> AtOptions {
        AtOptions {
            limit: 10,
            max_candidates: 50,
            time: Duration::from_secs(10),
            all: false,
            exclude: Vec::new(),
            within: Vec::new(),
            stop_after_closing: None,
            simplest_first: false,
        }
    }
}

/// Which goal: the one at a line (and column), or the n-th of the file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GoalAt {
    /// 1-based; with a column (1-based, in characters), the goal there,
    /// else the line's first.
    Line(usize, Option<usize>),
    /// 1-based, in source order.
    Index(usize),
}

/// A goal of a file: where it is, and its data.
#[derive(Clone, Debug)]
pub struct FoundGoal {
    pub line: usize,
    pub column: usize,
    /// 1-based among the file's goals, in source order.
    pub index: usize,
    /// The `?`, as byte offsets in the file's text.
    pub span: (usize, usize),
    /// The file, in the session that found the goal: with `span`, where to
    /// find the goal as the elaborator had it (`Elaborator::goal_snapshot`).
    pub file: Option<FileId>,
    pub data: GoalData,
}

impl FoundGoal {
    /// The goal as `session`'s elaborator had it at its `?` (SW-989), if
    /// it checked this file and kept it.
    fn snapshot(&self, session: &Session) -> Option<Rc<stitchwort_elab::GoalSnapshot>> {
        session.elab.goal_snapshot(stitchwort_syntax::Span {
            file: self.file?,
            start: self.span.0 as u32,
            end: self.span.1 as u32,
        })
    }
}

/// The goals among `diagnostics` that are in `file`, in source order.
pub fn goals_in(sources: &SourceMap, file: FileId, diagnostics: &[Diagnostic]) -> Vec<FoundGoal> {
    let text = &sources.get(file).text;
    let mut found: Vec<(u32, u32, GoalData)> = (diagnostics.iter())
        .filter(|d| d.severity == Severity::Goal)
        .filter_map(|d| {
            let span = d.primary_span()?;
            (span.file == file).then(|| Some((span.start, span.end, d.goal_data()?.clone())))?
        })
        .collect();
    found.sort_by_key(|(at, _, _)| *at);
    found
        .into_iter()
        .enumerate()
        .map(|(i, (at, end, data))| {
            let before = &text[..(at as usize).min(text.len())];
            let line = before.matches('\n').count() + 1;
            let column = before.rsplit('\n').next().unwrap_or("").chars().count() + 1;
            FoundGoal {
                line,
                column,
                index: i + 1,
                span: (at as usize, end as usize),
                file: Some(file),
                data,
            }
        })
        .collect()
}

/// `text` with the goal `?` at `span` replaced by `proof`: in brackets
/// unless the `?` is a whole body or argument already (after `:=`, `=>`,
/// `in`, `then`, `else`, an opening bracket or a comma, at the start of a
/// line), or the proof is one word.
pub fn paste(text: &str, span: (usize, usize), proof: &str) -> String {
    format!(
        "{}{}{}",
        &text[..span.0],
        paste_text(text, span, proof),
        &text[span.1..]
    )
}

/// What [`paste`] writes in place of the `?`.
pub fn paste_text(text: &str, span: (usize, usize), proof: &str) -> String {
    let before = text[..span.0].trim_end_matches([' ', '\t']);
    let alone = before.is_empty()
        || before.ends_with('\n')
        || [":=", "=>", "(", "[", ",", "→", "->"]
            .iter()
            .any(|t| before.ends_with(t))
        || ["in", "then", "else"].iter().any(|w| {
            before.ends_with(w)
                && !before[..before.len() - w.len()]
                    .ends_with(|c: char| c.is_alphanumeric() || c == '_')
        });
    let after = text[span.1..].trim_start_matches([' ', '\t']);
    let ends = after.is_empty() || after.starts_with(['\n', ')', ']', ',']);
    if (alone && ends) || atom(proof) == proof {
        proof.to_string()
    } else {
        format!("({proof})")
    }
}

/// The goal `at` asks for among `goals`, or why there is none.
pub fn pick(goals: &[FoundGoal], at: GoalAt) -> Result<&FoundGoal, String> {
    let listing = || {
        if goals.is_empty() {
            "the file has no open goal `?`".to_string()
        } else {
            let places: Vec<String> = (goals.iter())
                .map(|g| format!("{}:{} (goal {})", g.line, g.column, g.index))
                .collect();
            format!("its goals are at {}", places.join(", "))
        }
    };
    let found = match at {
        GoalAt::Index(n) => goals.iter().find(|g| g.index == n),
        GoalAt::Line(line, None) => goals.iter().find(|g| g.line == line),
        GoalAt::Line(line, Some(col)) => (goals.iter())
            .filter(|g| g.line == line)
            .min_by_key(|g| g.column.abs_diff(col)),
    };
    found.ok_or_else(|| match at {
        GoalAt::Index(n) => format!("there is no goal {n}: {}", listing()),
        GoalAt::Line(line, _) => format!("there is no goal `?` on line {line}: {}", listing()),
    })
}

/// The JSON contract of `search --at`, version 1.
#[derive(Serialize, Debug)]
pub struct AtReport {
    pub version: u32,
    pub goal: GoalJson,
    /// The closers that close the goal on their own (`rfl`, `omega`, `ring`,
    /// `cases`, `byDecision`), kernel-checked, written as the file writes them
    /// (`Std.byDecision` without `import Std (byDecision)`).
    pub tactics: Vec<String>,
    /// Set when the ladder answered ([`AtOptions::simplest_first`]): the
    /// rung that closed the goal, and the only thing in `tactics` or
    /// `results`; nothing else was searched for.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub simplest: Option<&'static str>,
    /// Suggestions that close the goal, every one checked by the kernel,
    /// then those that apply leaving goals; best first.
    pub results: Vec<Suggestion>,
    pub rewrites: Vec<Rewrite>,
    /// The induction hypothesis (SW-993), when nothing above uses it: calls
    /// of the declaration being proved on structurally smaller arguments,
    /// the others as at the goal. Termination is checked only once a proof
    /// using one is pasted.
    #[serde(rename = "inductionHypotheses", skip_serializing_if = "Vec::is_empty")]
    pub induction: Vec<String>,
    pub total: Totals,
    pub budget: AtBudget,
    pub warnings: Vec<String>,
}

#[derive(Serialize, Debug)]
pub struct GoalJson {
    pub file: String,
    pub line: usize,
    pub column: usize,
    pub index: usize,
    pub hypotheses: Vec<HypJson>,
    pub target: String,
    /// Variables the target's leading arrows bind, which each proof below
    /// introduces (`x => …`).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub introduced: Vec<String>,
}

#[derive(Serialize, Debug, Clone)]
pub struct HypJson {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
}

/// One suggestion.
#[derive(Serialize, Debug)]
pub struct Suggestion {
    /// `exact`, `withHypotheses`, `afterObligations` or `applicable`.
    pub class: &'static str,
    /// What to write in place of the `?`.
    pub proof: String,
    /// The declaration applied: its full name, kind, type, place and the
    /// import that brings it into scope (`null` if none is needed).
    pub name: String,
    pub kind: &'static str,
    #[serde(rename = "type")]
    pub ty: String,
    pub file: String,
    pub line: usize,
    pub import: Option<String>,
    /// `kernel`: the proof (for `applicable`, with each goal it leaves as a
    /// hypothesis) was elaborated and the kernel accepted it; `elaborated`:
    /// only elaborated (an `applicable` one whose goals can't be written).
    pub checked: &'static str,
    /// For `afterObligations`: each premise closed by a tactic, as the
    /// goal it was and what closed it.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub obligations: Vec<Obligation>,
    /// For `applicable`: the goals the proof leaves, at its `?`s in order.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub goals: Vec<LeftGoal>,
    /// Its rank in the search of the target (stage 1's order); absent for
    /// a rewrite followed by `rfl` or `omega`.
    #[serde(rename = "searchRank", skip_serializing_if = "Option::is_none")]
    pub search_rank: Option<usize>,
    /// It has a `?` for a witness, nothing solved (shown after the rest).
    #[serde(skip)]
    pub witnesses: bool,
    /// It uses the induction hypothesis, a call of the declaration being
    /// proved on a structurally smaller argument (SW-993): checked given
    /// that call; termination only once pasted (in a project's file, as
    /// every closing suggestion is).
    #[serde(rename = "inductionHypothesis", skip_serializing_if = "is_false")]
    pub recursive: bool,
    /// For a conjunct of the theorem `name` (SW-993): which (`left`,
    /// `right.left`); the proof takes it with `And.left` and the like.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub conjunct: Option<String>,
    /// The declaration applied, when known.
    #[serde(skip)]
    pub item: Option<stitchwort_elab::search::Item>,
}

#[derive(Serialize, Debug, Clone)]
pub struct Obligation {
    pub target: String,
    pub closer: &'static str,
}

#[derive(Serialize, Debug, Clone)]
pub struct LeftGoal {
    pub target: String,
    /// The goal as a declaration of its own, when it can be written so.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lemma: Option<String>,
}

/// A rewrite suggestion.
#[derive(Serialize, Debug)]
pub struct Rewrite {
    /// `rewrite L … in ?`.
    pub proof: String,
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub file: String,
    pub line: usize,
    pub import: Option<String>,
    /// The call of the target it rewrites.
    pub at: String,
    /// `leftToRight` or `rightToLeft` (`rewrite <-`).
    pub direction: &'static str,
    /// `eq` or `iff`.
    pub equation: &'static str,
    /// The goal at the `?` after rewriting.
    pub goal: String,
    /// What closes the rewritten goal, if `rfl` or `omega` does (kernel
    /// checked, with it in place of the `?`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub closes: Option<&'static str>,
    /// `kernel` (with the rewritten goal as a hypothesis) or `elaborated`.
    pub checked: &'static str,
    /// The rule is the induction hypothesis (SW-993), as for a suggestion.
    #[serde(rename = "inductionHypothesis", skip_serializing_if = "is_false")]
    pub recursive: bool,
    /// The goal left, for a second round.
    #[serde(skip)]
    pub left: Option<GoalData>,
}

#[derive(Serialize, Debug, Default)]
pub struct Totals {
    pub closing: usize,
    pub applicable: usize,
    pub rewrites: usize,
}

/// The share of the search's time one check may take (SW-1017).
const PER_CHECK_SHARE: f32 = 0.5;

#[derive(Serialize, Debug, Default)]
pub struct AtBudget {
    /// The declarations searched.
    pub candidates: usize,
    /// Those whose conclusion the target is an instance of.
    pub matched: usize,
    /// Those tried (the first `maxCandidates` matched, in rank order).
    pub tried: usize,
    #[serde(rename = "maxCandidates")]
    pub max_candidates: usize,
    /// Proofs elaborated (and, when complete, kernel-checked).
    pub checks: usize,
    /// More matched than were tried.
    pub truncated: bool,
    /// Everything planned was checked: false if the time ran out first.
    pub exhausted: bool,
    #[serde(rename = "outOfBudget")]
    pub out_of_budget: usize,
    /// Checks stopped at the per-check time limit (SW-1017: half the
    /// search's time): abandoned, not failed, so what they would have shown
    /// is unknown.
    #[serde(rename = "gaveUp", skip_serializing_if = "is_zero")]
    pub gave_up: usize,
    #[serde(rename = "internalErrors")]
    pub internal_errors: usize,
    /// In a project's file: the suggestions checked in the file (pasted in,
    /// its namespace checked again), and those that failed there and were
    /// dropped.
    #[serde(rename = "inFile", skip_serializing_if = "Option::is_none")]
    pub in_file: Option<InFile>,
}

#[derive(Serialize, Debug, Default, Clone, Copy)]
pub struct InFile {
    pub checked: usize,
    pub rejected: usize,
    /// Not checked in the file before the time ran out, so not listed.
    #[serde(skip_serializing_if = "is_zero")]
    pub unchecked: usize,
}

fn is_zero(n: &usize) -> bool {
    *n == 0
}

fn is_false(b: &bool) -> bool {
    !*b
}

/// The order of the classes.
fn class_rank(class: &str) -> usize {
    match class {
        "exact" => 0,
        "withHypotheses" => 1,
        "afterObligations" => 2,
        _ => 3,
    }
}

/// `text` as an argument: in brackets unless it is one word or already
/// bracketed.
fn atom(text: &str) -> String {
    let simple = !text.contains([' ', '→', '=']) && !text.starts_with('-');
    let bracketed = (text.starts_with('(') && text.ends_with(')'))
        || (text.starts_with('[') && text.ends_with(']'));
    if simple || bracketed {
        text.to_string()
    } else {
        format!("({text})")
    }
}

/// A plan as proof text: each `Open` argument in turn takes the next of
/// `fills` (`?` once they run out); with `infer`, solved arguments are `_`.
fn render(plan: &Plan, fills: &[String], infer: bool) -> String {
    let mut out = plan.head.clone();
    let mut fills = fills.iter();
    for (i, arg) in plan.args.iter().enumerate() {
        // A conjunct (SW-993): the theorem's arguments, then the projections
        // that take it (`And.left (T …)`), then its own.
        if let Some((fields, own)) = &plan.part
            && i == *own
        {
            for field in fields {
                out = format!("{field} ({out})");
            }
        }
        out.push(' ');
        match arg {
            Arg::Given(_) if infer => out.push('_'),
            Arg::Given(text) => out.push_str(&atom(text)),
            Arg::Infer | Arg::Unsolved => out.push('_'),
            Arg::Hyp(name) => out.push_str(name),
            Arg::Open => out.push_str(&atom(fills.next().map_or("?", String::as_str))),
        }
    }
    if let Some((fields, own)) = &plan.part
        && plan.args.len() <= *own
    {
        for field in fields {
            out = format!("{field} ({out})");
        }
    }
    match &plan.sym {
        Some(sym) => format!("{sym} ({out})"),
        None => out,
    }
}

/// A type after `:` in a binder: a record update would read as a block.
fn bracket_type(ty: &str) -> String {
    if ty.starts_with('{') {
        format!("({ty})")
    } else {
        ty.to_string()
    }
}

/// The checking context of a goal: `body` checked against the goal, its
/// hypotheses bound, `extra` hypotheses added after them.
fn wrap(goal: &GoalData, extra: &[(String, String)], body: &str) -> String {
    let binders: Vec<(String, String)> = (goal.hypotheses.iter())
        .map(|h| (h.name.clone(), bracket_type(&h.ty)))
        .chain(extra.iter().map(|(n, t)| (n.clone(), bracket_type(t))))
        .collect();
    if binders.is_empty() {
        return format!("(({body}): {})", goal.target);
    }
    let lambdas: String = binders
        .iter()
        .map(|(n, t)| format!("({n}: {t}) => "))
        .collect();
    let arrows: String = binders
        .iter()
        .map(|(n, t)| format!("({n}: {t}) → "))
        .collect();
    format!("(({lambdas}{body}): {arrows}{})", goal.target)
}

/// The goal's statement, `(h: A) → … → T`.
fn statement(goal: &GoalData) -> String {
    let mut out = String::new();
    for h in &goal.hypotheses {
        out.push_str(&format!("({}: {}) → ", h.name, bracket_type(&h.ty)));
    }
    out.push_str(&goal.target);
    out
}

/// What checking a proof found.
enum Outcome {
    Closed,
    Goals(Vec<GoalData>),
    Failed,
}

/// The checker of one `search --at`: counts checks, and stops at the
/// deadline.
struct Checker<'s> {
    session: &'s mut Session,
    /// The goal as the checking session's elaborator had it: proofs are
    /// checked there, with no text read back. `None`: by text, inside
    /// [`wrap`].
    snapshot: Option<Rc<stitchwort_elab::GoalSnapshot>>,
    goal: GoalData,
    intros: Vec<String>,
    /// The target, printed as goals are (the introduced variables named).
    target_now: String,
    checks: usize,
    deadline: Instant,
    /// The longest one check may take (SW-1017): a share of the search's time.
    per_check: Duration,
    /// The checks stopped at that limit (the proofs, as written).
    gave_up: Vec<String>,
    /// While trying the induction hypothesis: the name the proofs call
    /// the declaration being proved by, bound as a hypothesis (SW-993).
    recursive: Option<String>,
}

impl Checker<'_> {
    fn out_of_time(&self) -> bool {
        Instant::now() >= self.deadline
    }

    /// Checks `proof` at the goal, with `extra` hypotheses.
    fn check(&mut self, proof: &str, extra: &[(String, String)]) -> Outcome {
        let body = if self.intros.is_empty() {
            proof.to_string()
        } else {
            format!("{} => {proof}", self.intros.join(" => "))
        };
        let began = Instant::now();
        self.checks += 1;
        // A check may take its share of the time, and no more than is left.
        let limit = (began + self.per_check).min(self.deadline.max(began));
        let checked = match &self.snapshot {
            Some(snapshot) => {
                let Ok(expr) = self.session.parse_expression("<search --at>", &body) else {
                    return Outcome::Failed;
                };
                let mut hyps = Vec::new();
                for (name, ty) in extra {
                    let Ok(ty) = self.session.parse_expression("<search --at>", ty) else {
                        return Outcome::Failed;
                    };
                    hyps.push((name.clone(), ty));
                }
                let recursive = self.recursive.as_deref();
                (self.session.elab.kernel.machine.budget).set_deadline(Some(limit));
                (self.session.elab).check_proof_at(snapshot, &hyps, recursive, &expr)
            }
            None if self.recursive.is_some() => return Outcome::Failed,
            None => {
                let text = wrap(&self.goal, extra, &body);
                let Ok(expr) = self.session.parse_expression("<search --at>", &text) else {
                    return Outcome::Failed;
                };
                (self.session.elab.kernel.machine.budget).set_deadline(Some(limit));
                self.session.elab.check_proof(&expr)
            }
        };
        (self.session.elab.kernel.machine.budget).set_deadline(None);
        if self.session.elab.kernel.machine.budget.take_timed_out() {
            self.gave_up.push(proof.to_string());
        }
        debug_time(&format!("checked `{body}`"), began);
        match checked {
            Ok(Checked::Closed) => Outcome::Closed,
            Ok(Checked::Goals(goals)) => Outcome::Goals(
                goals
                    .into_iter()
                    .filter_map(|d| d.detail.and_then(|x| x.goal))
                    .collect(),
            ),
            Err(_) => Outcome::Failed,
        }
    }
}

/// The ladder (SW-2966): the simple closers that "Search for a proof" tries
/// one at a time, cheapest first, before any search. The first that closes
/// the goal is the whole answer: a goal `rfl` closes isn't also offered
/// lemmas, and one `omega` closes isn't offered `omega` beside `ring`. Only
/// when no rung closes it does the full search run, and it skips the rungs
/// that failed. To change the ladder, change [`LADDER`] and [`Rung::texts`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Rung {
    /// A hypothesis that is `False = True` (or `True = False`) rules the
    /// goal out: `Void.exfalso (Bool.falseNotTrue h)`, which says why,
    /// where `omega` and `cases` only happen to find it. First, since a
    /// proof from a contradiction closes any goal, so the rungs after it
    /// would add nothing.
    Absurd,
    /// The goal holds by computation.
    Rfl,
    /// A hypothesis is exactly the goal.
    Hypothesis,
    /// A closed goal with a decision procedure, run (`byDecision`).
    Decision,
    Omega,
    Ring,
    /// `cases`, tried only where a hypothesis is an equation, which is what
    /// can rule a case out (`h: False = True`, two different constructors);
    /// the language has no `cases h`, so the tactic finds that hypothesis
    /// itself. A goal that only needs a split is left to the full search.
    Cases,
}

/// The rungs, in the order they are tried.
const LADDER: [Rung; 7] = [
    Rung::Absurd,
    Rung::Rfl,
    Rung::Hypothesis,
    Rung::Decision,
    Rung::Omega,
    Rung::Ring,
    Rung::Cases,
];

/// The longest one rung's check may take. A rung that runs out is given up
/// (not counted as failed: the full search tries it again with its own
/// share), so a slow one costs this much and no more.
const RUNG_TIME: Duration = Duration::from_millis(500);

/// All the rungs together, however many give up.
const LADDER_TIME: Duration = Duration::from_secs(2);

impl Rung {
    /// What the rung writes in place of the `?`, as the file writes it;
    /// nothing when it doesn't apply to this goal.
    fn texts(
        self,
        hypotheses: &[Hypothesis],
        by_decision: Option<&str>,
        absurd: &[String],
    ) -> Vec<String> {
        match self {
            Rung::Absurd => absurd.to_vec(),
            Rung::Rfl => vec!["rfl".to_string()],
            Rung::Hypothesis => hypotheses
                .iter()
                .filter(|h| is_name(&h.name))
                .map(|h| h.name.clone())
                .collect(),
            Rung::Decision => by_decision.map(str::to_string).into_iter().collect(),
            Rung::Omega => vec!["omega".to_string()],
            Rung::Ring => vec!["ring".to_string()],
            Rung::Cases => {
                if hypotheses.iter().any(|h| h.ty.contains(" = ")) {
                    vec!["cases".to_string()]
                } else {
                    Vec::new()
                }
            }
        }
    }
}

/// The direct proofs from hypotheses that are an equation of the two
/// `Bool`s: what ruling a case out by `h: False = True` reads as. The
/// library's names are written as the file can write them, so none when it
/// can't name them all.
fn absurd_proofs(elab: &stitchwort_elab::Elaborator, hypotheses: &[Hypothesis]) -> Vec<String> {
    let name = |path: &str| elab.write_name(path);
    let (Some(exfalso), Some(false_not_true), Some(true_not_false)) = (
        name("Std.Void.exfalso"),
        name("Std.Bool.falseNotTrue"),
        name("Std.Bool.trueNotFalse"),
    ) else {
        return Vec::new();
    };
    hypotheses
        .iter()
        .filter(|h| is_name(&h.name))
        .filter_map(|h| {
            let lemma = match h.ty.trim() {
                "False = True" => &false_not_true,
                "True = False" => &true_not_false,
                _ => return None,
            };
            Some(format!("{exfalso} ({lemma} {})", h.name))
        })
        .collect()
}

/// Whether `name` can be written as a proof as it is.
fn is_name(name: &str) -> bool {
    name.chars()
        .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
}

/// What [`climb`] found.
enum Climb {
    /// The first rung that closes the goal, and what it writes.
    Closed(Rung, String),
    /// None did; what was tried and failed outright, so the full search
    /// needn't try it again (a check that ran out of time isn't here).
    Open(Vec<String>),
}

/// Tries the [`LADDER`] at the checker's goal, each rung under its own
/// time, the whole under [`LADDER_TIME`]. Each proof is checked as the full
/// search's are: elaborated, and kernel-checked.
fn climb(
    checker: &mut Checker,
    hypotheses: &[Hypothesis],
    by_decision: Option<&str>,
    absurd: &[String],
) -> Climb {
    let mut failed = Vec::new();
    checker.per_check = RUNG_TIME;
    checker.deadline = checker.deadline.min(Instant::now() + LADDER_TIME);
    for rung in LADDER {
        for text in rung.texts(hypotheses, by_decision, absurd) {
            if checker.out_of_time() {
                return Climb::Open(failed);
            }
            let gave_up = checker.gave_up.len();
            match checker.check(&text, &[]) {
                Outcome::Closed => return Climb::Closed(rung, text),
                _ if checker.gave_up.len() > gave_up => {}
                _ => failed.push(text),
            }
        }
    }
    Climb::Open(failed)
}

impl Session {
    /// What closes `goal` (one of this session's goals, `found` in a file
    /// whose names this session's scope sees): the four classes and the
    /// rewrites, every closing one kernel-checked.
    ///
    /// This session searches, so it has the whole library loaded. The
    /// proofs are checked in `checker` if given: a session with only the
    /// file loaded, as it would be with the proof pasted in, so that
    /// nothing a library file the file doesn't load provides (an instance,
    /// a decision procedure) makes a proof check here and fail there.
    pub fn search_at(
        &mut self,
        found: &FoundGoal,
        file: &str,
        options: &AtOptions,
        scope: &Scope,
        checker: Option<&mut Session>,
    ) -> Result<AtReport, Diagnostic> {
        let started = Instant::now();
        // The core's equations, put off until now (`equations.rs`).
        self.elab.generate_deferred_equations()?;
        let mut checker = checker;
        if let Some(c) = checker.as_deref_mut() {
            c.elab.generate_deferred_equations()?;
        }
        let data = found.data.clone();
        // The goal as the elaborator had it, if it kept it; else its
        // statement, printed and read back.
        let snapshot = found.snapshot(self);
        // Opening the goal computes its target (a closed list of 130,000
        // sequences took seconds, AoC 2024 day 22), so it is under the
        // search's time too.
        self.elab.kernel.machine.budget.take_timed_out();
        (self.elab.kernel.machine.budget).set_deadline(Some(started + options.time));
        let opened = match &snapshot {
            Some(snapshot) => {
                let span = stitchwort_syntax::Span {
                    file: found.file.expect("a snapshot has a file"),
                    start: found.span.0 as u32,
                    end: found.span.1 as u32,
                };
                self.elab.open_goal_at(snapshot, span)
            }
            None => {
                let stmt = statement(&data);
                match self.parse_expression("<goal>", &stmt) {
                    Ok(expr) => self.elab.open_goal(&expr, data.hypotheses.len()),
                    Err(d) => Err(d),
                }
            }
        };
        (self.elab.kernel.machine.budget).set_deadline(None);
        if self.elab.kernel.machine.budget.take_timed_out() {
            return Ok(ran_out_opening(found, file, options));
        }
        let mut goal: Goal = opened.map_err(|d| cannot_open(&data, d))?;
        goal.deadline = Some(started + options.time);
        let mut failed: Vec<String> = Vec::new();
        let mut ladder_checks = 0;
        let absurd = absurd_proofs(&self.elab, &data.hypotheses);
        if options.simplest_first {
            let by_decision = self.elab.write_name("Std.byDecision");
            let on_checker: &mut Session = match checker.as_deref_mut() {
                Some(other) => other,
                None => &mut *self,
            };
            let mut ladder = Checker {
                snapshot: snapshot.as_ref().and_then(|_| found.snapshot(on_checker)),
                session: on_checker,
                goal: data.clone(),
                intros: goal.intros.clone(),
                target_now: goal.target.clone(),
                checks: 0,
                deadline: started + options.time,
                per_check: options.time,
                gave_up: Vec::new(),
                recursive: None,
            };
            let climbed = climb(
                &mut ladder,
                &data.hypotheses,
                by_decision.as_deref(),
                &absurd,
            );
            ladder_checks = ladder.checks;
            drop(ladder);
            debug_time("ladder", started);
            match climbed {
                Climb::Closed(rung, proof) => {
                    return Ok(simplest_report(
                        found,
                        file,
                        &data,
                        &goal.intros,
                        rung,
                        proof,
                    ));
                }
                Climb::Open(f) => failed = f,
            }
        }
        let g = &self.elab.ev();
        let prop = goal.prop;
        let mut candidates = searchable(&self.elab, options, prop);
        // The theorem the goal is in is a candidate too once it is open
        // (it has this `?`), but closing the goal with it is circular.
        if let Some(owner) = snapshot.as_ref().and_then(|s| s.owner()) {
            candidates.retain(|c| {
                !matches!(c.item,
                    stitchwort_elab::search::Item::Def(id)
                    | stitchwort_elab::search::Item::Part(id, _) if id == owner)
            });
        }
        let keep = |_: &Candidate| true;
        debug_time("opened", started);
        let closing = self
            .elab
            .closing_plans(&goal, &candidates, &keep, options.max_candidates);
        let iff = (0..g.env.datas().len())
            .map(DataId)
            .find(|d| &**g.data(*d).path() == "Std.Iff");
        debug_time("closing searched", started);
        let rewrite_plans = if prop {
            self.elab
                .rewrite_plans(&goal, &candidates, &keep, iff, 3, 30)
        } else {
            Vec::new()
        };
        // Calls of the declaration being proved (SW-993), for a goal in one.
        let recursive_plans = match snapshot.as_ref().and_then(|s| s.owner()) {
            Some(owner) if prop => self.elab.recursive_plans(&goal, owner, iff, 8),
            _ => Vec::new(),
        };
        // Its type and place, for what uses it (it isn't a declaration
        // the search found, and a file's own may not be found by name).
        let owner_place = (snapshot.as_ref().and_then(|s| s.owner())).map(|id| {
            let item = stitchwort_elab::search::Item::Def(id);
            let (file, line) = crate::render::location(&self.sources, item.span(g));
            (
                stitchwort_core::pretty::term(g, &[], &item.ty(g)),
                file,
                line,
            )
        });
        let closers: Vec<(&'static str, String)> = [
            ("rfl", Some("rfl".to_string())),
            ("omega", Some("omega".to_string())),
            ("ring", Some("ring".to_string())),
            ("cases", Some("cases".to_string())),
            ("byDecision", self.elab.write_name("Std.byDecision")),
        ]
        .into_iter()
        .filter_map(|(name, text)| Some((name, text?)))
        .collect();
        let intros = goal.intros.clone();
        let target_now = goal.target.clone();
        let matched = (closing.found.hits.iter())
            .filter(|h| h.relation == stitchwort_elab::search::Relation::Instance)
            .count();
        let mut budget = AtBudget {
            candidates: closing.found.stats.candidates,
            matched,
            tried: closing.plans.len(),
            max_candidates: options.max_candidates,
            truncated: matched > closing.plans.len(),
            exhausted: !closing.found.stats.stopped,
            out_of_budget: closing.found.stats.out_of_budget,
            gave_up: 0,
            internal_errors: closing.found.stats.internal_errors,
            checks: 0,
            in_file: None,
        };
        // Each declaration's place in the search's ranking.
        let ranks: Vec<_> = closing.found.hits.iter().map(|h| h.item).collect();
        // A file on its own: its proofs aren't checked again pasted in.
        let on_its_own = checker.is_some();
        let checking: &mut Session = match checker {
            Some(other) => other,
            None => self,
        };
        // The checking session's own: its declarations are numbered as it
        // loaded them. Both or neither, so that what is checked is what was
        // searched.
        let check_snapshot = snapshot.as_ref().and_then(|_| found.snapshot(checking));
        let mut checker = Checker {
            snapshot: check_snapshot,
            session: checking,
            goal: data.clone(),
            intros: intros.clone(),
            target_now: target_now.clone(),
            checks: 0,
            deadline: started + options.time,
            per_check: options.time.mul_f32(PER_CHECK_SHARE),
            gave_up: Vec::new(),
            recursive: None,
        };
        // The closers on their own first: a goal `omega` closes needs no
        // lemma.
        debug_time("rewrites planned", started);
        let mut tactics = Vec::new();
        for text in absurd.iter().chain(closers.iter().map(|(_, text)| text)) {
            if failed.contains(text) {
                continue;
            }
            if matches!(checker.check(text, &[]), Outcome::Closed) {
                tactics.push(text.clone());
            }
        }
        let mut results: Vec<(Suggestion, usize)> = Vec::new();
        // A hypothesis that is the goal (SW-989): it closes it alone.
        for h in &data.hypotheses {
            if is_name(&h.name)
                && !failed.contains(&h.name)
                && !checker.out_of_time()
                && matches!(checker.check(&h.name, &[]), Outcome::Closed)
            {
                let s = Suggestion {
                    class: "withHypotheses",
                    proof: h.name.clone(),
                    name: h.name.clone(),
                    kind: "hypothesis",
                    ty: h.ty.clone(),
                    file: String::new(),
                    line: 0,
                    import: None,
                    checked: "kernel",
                    obligations: Vec::new(),
                    goals: Vec::new(),
                    search_rank: None,
                    witnesses: false,
                    recursive: false,
                    conjunct: None,
                    item: None,
                };
                results.push((s, 0));
            }
        }
        'hits: for (order, (hit, plans)) in closing.plans.iter().enumerate() {
            if let Some(wanted) = options.stop_after_closing
                && results
                    .iter()
                    .filter(|(s, _)| s.class != "applicable")
                    .count()
                    >= wanted
            {
                break;
            }
            let rank = ranks.iter().position(|i| *i == hit.item).unwrap_or(0) + 1;
            let mut best: Option<Suggestion> = None;
            for plan in plans {
                if checker.out_of_time() {
                    budget.exhausted = false;
                    break 'hits;
                }
                let Some(s) = try_plan(&mut checker, plan, &closers, rank) else {
                    continue;
                };
                let better = best.as_ref().is_none_or(|b| {
                    (class_rank(s.class), s.goals.len()) < (class_rank(b.class), b.goals.len())
                });
                if better {
                    let closes = s.class != "applicable";
                    best = Some(s);
                    if closes {
                        break;
                    }
                }
            }
            if let Some(s) = best
                && !results.iter().any(|(r, _)| r.proof == s.proof)
            {
                // In the order tried (`closing_plans`), not the search's.
                results.push((s, order + 1));
            }
        }
        debug_time("closing checked", started);
        let mut rewrites = Vec::new();
        for rp in &rewrite_plans {
            if checker.out_of_time() {
                budget.exhausted = false;
                break;
            }
            // A different lemma reaching the same goal is another proof to
            // offer (`Nat.addComm a b` and a lemma stating it for `double`).
            if let Some(r) = try_rewrite(&mut checker, rp, &target_now)
                && !rewrites
                    .iter()
                    .any(|x: &Rewrite| x.goal == r.goal && x.name == r.name)
            {
                rewrites.push(r);
            }
        }
        // The goal's equations, each way (SW-976: `rewrite <- h in …`).
        for h in &data.hypotheses {
            let equation = h.ty.contains(" = ") || h.ty.contains(" ↔ ");
            if !is_name(&h.name) || !equation || checker.out_of_time() {
                continue;
            }
            for backwards in [false, true] {
                let rule = Rule {
                    text: &h.name,
                    backwards,
                    iff: h.ty.contains(" ↔ "),
                    name: &h.name,
                    at: "",
                };
                if let Some(r) = try_rule(&mut checker, &rule, &target_now)
                    && !rewrites.iter().any(|x: &Rewrite| x.goal == r.goal)
                {
                    // Then a lemma (SW-993): `rewrite <- h in L …`.
                    if let (None, Some(left)) = (r.closes, &r.left) {
                        let arrow = if backwards { "<- " } else { "" };
                        let prefix = format!("rewrite {arrow}{} in ", h.name);
                        let mine = (!on_its_own).then_some(candidates.as_slice());
                        for s in after_rewrite(&mut checker, left, &prefix, mine, options, 3) {
                            if !results.iter().any(|(r, _)| r.proof == s.proof) {
                                results.push((s, usize::MAX - 2));
                            }
                        }
                    }
                    rewrites.push(r);
                }
            }
        }
        // The induction hypothesis (SW-993): calls of the declaration being
        // proved, on smaller arguments, checked with it bound as a
        // hypothesis. Alone, in `omega [IH]`, or as a rewrite.
        let mut induction: Vec<String> = Vec::new();
        if let Some(place) = owner_place.as_ref().filter(|_| checker.snapshot.is_some()) {
            let mut used = false;
            for rp in &recursive_plans {
                if checker.out_of_time() {
                    budget.exhausted = false;
                    break;
                }
                let call = render(&rp.plan, &[], false);
                checker.recursive = Some(rp.plan.head.clone());
                // Alone or in `omega` (a rewrite's call too: what matching a
                // side solved may be what `omega` needs, `dyAfter n (step
                // probe)`).
                let alone = rp.rewrite.is_none().then(|| call.clone());
                if !call.contains('?') {
                    for proof in alone.into_iter().chain([format!("omega [{call}]")]) {
                        if results.iter().any(|(s, _)| s.proof == proof) {
                            continue;
                        }
                        if matches!(checker.check(&proof, &[]), Outcome::Closed) {
                            used = true;
                            let s = Suggestion {
                                class: "withHypotheses",
                                proof,
                                name: rp.plan.item_path.clone(),
                                kind: "theorem",
                                ty: place.0.clone(),
                                file: place.1.clone(),
                                line: place.2,
                                import: None,
                                checked: "kernel",
                                obligations: Vec::new(),
                                goals: Vec::new(),
                                search_rank: None,
                                witnesses: false,
                                recursive: true,
                                conjunct: None,
                                item: None,
                            };
                            results.push((s, usize::MAX - 1));
                            break;
                        }
                    }
                }
                if let Some(backwards) = rp.rewrite {
                    let rule = Rule {
                        text: &call,
                        backwards,
                        iff: false,
                        name: &rp.plan.item_path,
                        at: "",
                    };
                    if let Some(mut r) = try_rule(&mut checker, &rule, &target_now)
                        && !rewrites.iter().any(|x: &Rewrite| x.goal == r.goal)
                    {
                        used = true;
                        (r.ty, r.file, r.line) = place.clone();
                        rewrites.push(r);
                    }
                }
                checker.recursive = None;
                if rp.rewrite.is_none() && !induction.contains(&call) {
                    induction.push(call);
                }
            }
            if used {
                induction.clear();
            }
        }
        // A rewrite after which `rfl` or `omega` closes the goal closes it:
        // a suggestion of its own, after the lemmas that close it directly.
        for r in &rewrites {
            if let Some(closer) = r.closes {
                let proof = r.proof.replacen(" in ?", &format!(" in {closer}"), 1);
                // Not when the closer alone closes the goal: the rewrite
                // adds nothing.
                if tactics.iter().any(|t| t == closer)
                    || results.iter().any(|(s, _)| s.proof == proof)
                {
                    continue;
                }
                let suggestion = Suggestion {
                    class: "afterObligations",
                    proof,
                    name: r.name.clone(),
                    kind: "theorem",
                    // Empty but for the induction hypothesis's: filled in
                    // below, as the rewrite's are.
                    ty: r.ty.clone(),
                    file: r.file.clone(),
                    line: r.line,
                    import: None,
                    checked: "kernel",
                    obligations: vec![Obligation {
                        target: r.goal.clone(),
                        closer,
                    }],
                    goals: Vec::new(),
                    search_rank: None,
                    witnesses: false,
                    recursive: r.recursive,
                    conjunct: None,
                    item: None,
                };
                results.push((suggestion, usize::MAX));
            }
        }
        debug_time("checks done", started);
        budget.checks = checker.checks + ladder_checks;
        budget.gave_up = checker.gave_up.len();
        let gave_up = std::mem::take(&mut checker.gave_up);
        drop(checker);
        let session = &*self;
        let generated = Generated::new(&session.elab.ev());
        // What closes before what applies; among either, a written theorem
        // before a generated equation (`f.eqK`, whose side may compute to
        // the goal's: docs/proposals/function-equations.md §3.4, SW-1055),
        // then by class.
        results.sort_by_key(|(s, rank)| {
            (
                s.class == "applicable",
                generated.contains_name(&session.elab.ev(), &s.name),
                class_rank(s.class),
                s.witnesses,
                s.goals.len(),
                *rank,
            )
        });
        let mut results: Vec<Suggestion> = results.into_iter().map(|(s, _)| s).collect();
        // A proof using the induction hypothesis is checked given it; in a
        // file on its own, nothing checks that its call terminates
        // (SW-993). In a project's file each is checked pasted in.
        for s in results.iter_mut().filter(|s| s.recursive && on_its_own) {
            s.checked = "elaborated";
        }
        for s in results.iter_mut() {
            session.describe(s, scope);
        }
        for r in rewrites.iter_mut() {
            session.describe_rewrite(r, scope);
        }
        // Closing rewrites first.
        rewrites.sort_by_key(|r| r.closes.is_none());
        // The proofs as written at the `?`: introducing the target's
        // variables first.
        if !intros.is_empty() {
            let prefix = format!("{} => ", intros.join(" => "));
            for s in results.iter_mut() {
                s.proof.insert_str(0, &prefix);
            }
            for r in rewrites.iter_mut() {
                r.proof.insert_str(0, &prefix);
            }
        }
        let totals = Totals {
            closing: results.iter().filter(|s| s.class != "applicable").count(),
            applicable: results.iter().filter(|s| s.class == "applicable").count(),
            rewrites: rewrites.len(),
        };
        let mut warnings: Vec<String> =
            (crate::search::within_warning(&options.within, candidates.len()).into_iter())
                .collect();
        if !budget.exhausted {
            warnings.push(format!(
                "the time ran out ({} s) before every candidate was checked: --time for more",
                options.time.as_secs_f32()
            ));
        }
        if !gave_up.is_empty() {
            let shown: Vec<_> = (gave_up.iter().take(3)).map(|p| format!("`{p}`")).collect();
            warnings.push(format!(
                "{} checks gave up after {} ms each (half of --time), so whether they close the goal is unknown: {}{}",
                gave_up.len(),
                options.time.mul_f32(PER_CHECK_SHARE).as_millis(),
                shown.join(", "),
                if gave_up.len() > 3 { " and more" } else { "" }
            ));
        }
        if budget.truncated {
            warnings.push(format!(
                "{} declarations match the target; the first {} were tried (--candidates N for more)",
                budget.matched, budget.tried
            ));
        }
        if let Some(w) = crate::search::out_of_budget_warning(&self.elab.ev(), &closing.found.stats)
        {
            warnings.push(w);
        }
        let mut shown_closing = 0;
        let mut shown_applicable = 0;
        results.retain(|s| {
            let n = if s.class == "applicable" {
                &mut shown_applicable
            } else {
                &mut shown_closing
            };
            *n += 1;
            *n <= options.limit
        });
        rewrites.truncate(options.limit);
        Ok(AtReport {
            version: 1,
            goal: GoalJson {
                file: file.to_string(),
                line: found.line,
                column: found.column,
                index: found.index,
                hypotheses: (data.hypotheses.iter())
                    .map(|h| HypJson {
                        name: h.name.clone(),
                        ty: h.ty.clone(),
                    })
                    .collect(),
                target: data.target.clone(),
                introduced: intros,
            },
            tactics,
            simplest: None,
            results,
            rewrites,
            induction,
            total: totals,
            budget,
            warnings,
        })
    }

    /// Fills in a suggestion's declaration: name, kind, type, place, import.
    fn describe(&self, s: &mut Suggestion, scope: &Scope) {
        let g = &self.elab.ev();
        // A hypothesis, or the declaration being proved (filled in already).
        if s.kind == "hypothesis" || s.recursive {
            return;
        }
        let Some(item) = s.item.or_else(|| find_item(self, &s.name)) else {
            return;
        };
        let (file, line) = crate::render::location(&self.sources, item.span(g));
        s.kind = item.kind(g).name();
        s.ty = stitchwort_core::pretty::term(g, &[], &item.ty(g));
        s.file = file;
        s.line = line;
        s.import = import_line(g, item, scope);
    }

    fn describe_rewrite(&self, r: &mut Rewrite, scope: &Scope) {
        let g = &self.elab.ev();
        if r.recursive {
            return;
        }
        let Some(item) = find_item(self, &r.name) else {
            return;
        };
        let (file, line) = crate::render::location(&self.sources, item.span(g));
        r.ty = stitchwort_core::pretty::term(g, &[], &item.ty(g));
        r.file = file;
        r.line = line;
        r.import = import_line(g, item, scope);
    }
}

/// The report when a rung of the ladder closed the goal: that proof alone.
fn simplest_report(
    found: &FoundGoal,
    file: &str,
    data: &GoalData,
    intros: &[String],
    rung: Rung,
    proof: String,
) -> AtReport {
    let mut tactics = Vec::new();
    let mut results = Vec::new();
    let name = match rung {
        Rung::Absurd => "absurd",
        Rung::Rfl => "rfl",
        Rung::Hypothesis => "hypothesis",
        Rung::Decision => "byDecision",
        Rung::Omega => "omega",
        Rung::Ring => "ring",
        Rung::Cases => "cases",
    };
    if rung == Rung::Hypothesis {
        let ty = (data.hypotheses.iter())
            .find(|h| h.name == proof)
            .map_or(String::new(), |h| h.ty.clone());
        let mut written = intros
            .iter()
            .map(|x| format!("{x} => "))
            .collect::<String>();
        written.push_str(&proof);
        results.push(Suggestion {
            class: "withHypotheses",
            proof: written,
            name: proof,
            kind: "hypothesis",
            ty,
            file: String::new(),
            line: 0,
            import: None,
            checked: "kernel",
            obligations: Vec::new(),
            goals: Vec::new(),
            search_rank: None,
            witnesses: false,
            recursive: false,
            conjunct: None,
            item: None,
        });
    } else {
        tactics.push(proof);
    }
    AtReport {
        version: 1,
        goal: GoalJson {
            file: file.to_string(),
            line: found.line,
            column: found.column,
            index: found.index,
            hypotheses: (data.hypotheses.iter())
                .map(|h| HypJson {
                    name: h.name.clone(),
                    ty: h.ty.clone(),
                })
                .collect(),
            target: data.target.clone(),
            introduced: intros.to_vec(),
        },
        simplest: Some(name),
        total: Totals {
            closing: results.len(),
            applicable: 0,
            rewrites: 0,
        },
        tactics,
        results,
        rewrites: Vec::new(),
        induction: Vec::new(),
        budget: AtBudget {
            exhausted: true,
            checks: 1,
            ..AtBudget::default()
        },
        warnings: Vec::new(),
    }
}

/// The declarations `elab` searches for a goal (a proposition if `prop`):
/// all but hidden helpers (unless `--all`), definitions for a proposition,
/// and those `options` leaves out.
fn searchable(
    elab: &stitchwort_elab::Elaborator,
    options: &AtOptions,
    prop: bool,
) -> Vec<Candidate> {
    let g = &elab.ev();
    elab.search_candidates(&|item, path| {
        (options.all || !hidden(path))
            && (!prop || item.kind(g) != Kind::Definition)
            && !options.exclude.iter().any(|e| e == path)
            && crate::search::in_namespaces(path, &options.within)
    })
}

/// A second round after a rewrite by a hypothesis (SW-993): the goal it
/// leaves, `left`, opened from its statement in the checking session, and
/// the lemmas that close it there (premises from hypotheses, nothing left
/// open), each checked at the first goal after `prefix` (`rewrite <- h
/// in `). At most `max` found.
fn after_rewrite(
    checker: &mut Checker,
    left: &GoalData,
    prefix: &str,
    candidates: Option<&[Candidate]>,
    options: &AtOptions,
    max: usize,
) -> Vec<Suggestion> {
    let mut out = Vec::new();
    let Ok(expr) = checker.session.parse_expression("<goal>", &statement(left)) else {
        return out;
    };
    let Ok(mut goal) = checker.session.elab.open_goal(&expr, left.hypotheses.len()) else {
        return out;
    };
    goal.deadline = Some(checker.deadline);
    // The search session's own, when it is the checking session (in a
    // project); else the checking session's.
    let own;
    let candidates = match candidates {
        Some(c) => c,
        None => {
            own = searchable(&checker.session.elab, options, goal.prop);
            &own
        }
    };
    let keep = |_: &Candidate| true;
    let closing = (checker.session.elab).closing_plans(&goal, candidates, &keep, 20);
    for (_, plans) in &closing.plans {
        let Some(plan) = plans.iter().find(|p| !p.args.contains(&Arg::Open)) else {
            continue;
        };
        if out.len() >= max || checker.out_of_time() {
            break;
        }
        let proof = format!("{prefix}{}", render(plan, &[], false));
        if proof.contains('?') || !matches!(checker.check(&proof, &[]), Outcome::Closed) {
            continue;
        }
        out.push(Suggestion {
            class: "withHypotheses",
            proof,
            name: plan.item_path.clone(),
            kind: "theorem",
            ty: String::new(),
            file: String::new(),
            line: 0,
            import: None,
            checked: "kernel",
            obligations: Vec::new(),
            goals: Vec::new(),
            search_rank: None,
            witnesses: false,
            recursive: false,
            conjunct: None,
            item: None,
        });
    }
    out
}

/// The declaration with full name `path`.
fn find_item(session: &Session, path: &str) -> Option<stitchwort_elab::search::Item> {
    let g = &session.elab.ev();
    if let Some(id) = session.elab.lookup_def(path) {
        return Some(stitchwort_elab::search::Item::Def(id));
    }
    // A file's own (`Main.…`, its scope's keys have no `Main.`), a
    // generated `T.ext`: by its path.
    let def = (0..g.env.defs().len())
        .map(|id| stitchwort_elab::search::Item::Def(stitchwort_core::DefId(id)))
        .find(|item| item.path(g) == path);
    if def.is_some() {
        return def;
    }
    (0..g.env.datas().len()).find_map(|d| {
        let data = g.data(DataId(d));
        (0..data.ctors().len())
            .map(|c| stitchwort_elab::search::Item::Ctor(DataId(d), c))
            .find(|item| item.path(g) == path)
    })
}

/// The error for a goal that can't be opened here.
/// The report of a search whose time ran out while opening the goal: no
/// suggestions, and the time-out warning the other phases give.
fn ran_out_opening(found: &FoundGoal, file: &str, options: &AtOptions) -> AtReport {
    let data = &found.data;
    AtReport {
        version: 1,
        goal: GoalJson {
            file: file.to_string(),
            line: found.line,
            column: found.column,
            index: found.index,
            hypotheses: (data.hypotheses.iter())
                .map(|h| HypJson {
                    name: h.name.clone(),
                    ty: h.ty.clone(),
                })
                .collect(),
            target: data.target.clone(),
            introduced: Vec::new(),
        },
        tactics: Vec::new(),
        simplest: None,
        results: Vec::new(),
        rewrites: Vec::new(),
        induction: Vec::new(),
        total: Totals {
            closing: 0,
            applicable: 0,
            rewrites: 0,
        },
        budget: AtBudget {
            max_candidates: options.max_candidates,
            exhausted: false,
            ..AtBudget::default()
        },
        warnings: vec![format!(
            "the time ran out ({} s) while opening the goal, before any candidate was tried: --time for more",
            options.time.as_secs_f32()
        )],
    }
}

fn cannot_open(goal: &GoalData, d: Diagnostic) -> Diagnostic {
    let why = if goal.lemma.is_none() {
        "it can't be written as a statement of its own here (a name is shadowed or \
         compiler-made, a `let` of data is in scope, or a part isn't known yet)"
    } else {
        "its statement doesn't elaborate on its own"
    };
    Diagnostic::error(
        "E-SEARCH-AT",
        format!("can't search for what closes this goal: {why}"),
    )
    .with_note(format!("{}: {}", d.code, d.message))
}

/// Checks one plan: what it closes, or the goals it leaves.
fn try_plan(
    checker: &mut Checker,
    plan: &Plan,
    closers: &[(&'static str, String)],
    rank: usize,
) -> Option<Suggestion> {
    let tried = try_plan_with(checker, plan, closers, rank, &[]);
    if tried.is_some() || !plan.specific || !plan.args.contains(&Arg::Unsolved) {
        return tried;
    }
    // What nothing solved and `_` can't work out (`List.memFlatMapIntro`'s
    // `x`, `List.distinctFlatMap`'s `key`): a `?` for the writer, the goals
    // after it mentioning it (SW-989). Which `?`s are such.
    let witness: Vec<bool> = (plan.args.iter())
        .filter(|a| matches!(a, Arg::Open | Arg::Unsolved))
        .map(|a| *a == Arg::Unsolved)
        .collect();
    let mut witnesses = plan.clone();
    for arg in &mut witnesses.args {
        if *arg == Arg::Unsolved {
            *arg = Arg::Open;
        }
    }
    try_plan_with(checker, &witnesses, closers, rank, &witness)
}

/// [`try_plan`]; with `witnesses` (`?`s that stand for data), the goals it
/// leaves may mention an unknown.
fn try_plan_with(
    checker: &mut Checker,
    plan: &Plan,
    closers: &[(&'static str, String)],
    rank: usize,
    witness: &[bool],
) -> Option<Suggestion> {
    let mut text = render(plan, &[], false);
    let mut first = checker.check(&text, &[]);
    let has_given = plan.args.iter().any(|a| matches!(a, Arg::Given(_)));
    if matches!(first, Outcome::Failed) && has_given {
        text = render(plan, &[], true);
        first = checker.check(&text, &[]);
    } else if (plan.args.iter()).any(|a| matches!(a, Arg::Given(t) if t.chars().count() > 40)) {
        // A long argument, often the goal's term computed (`List.concat
        // (List.map …)` for a `flatMap`): `_` reads better, where it does
        // as well (SW-989).
        let short = render(plan, &[], true);
        let second = checker.check(&short, &[]);
        let same = match (&first, &second) {
            (Outcome::Closed, Outcome::Closed) => true,
            (Outcome::Goals(a), Outcome::Goals(b)) => a.len() == b.len(),
            _ => false,
        };
        if same {
            text = short;
            first = second;
        }
    }
    let infer = text != render(plan, &[], false);
    let uses_hyp = plan.args.iter().any(|a| matches!(a, Arg::Hyp(_)));
    let base = |class: &'static str, proof: String| Suggestion {
        class,
        proof,
        name: String::new(),
        kind: "theorem",
        ty: String::new(),
        file: String::new(),
        line: 0,
        import: None,
        checked: "kernel",
        obligations: Vec::new(),
        goals: Vec::new(),
        search_rank: Some(rank),
        witnesses: !witness.is_empty(),
        recursive: false,
        conjunct: None,
        item: None,
    };
    let mut suggestion = match first {
        Outcome::Failed => return None,
        Outcome::Closed => {
            let class = if uses_hyp { "withHypotheses" } else { "exact" };
            base(class, text)
        }
        Outcome::Goals(goals) => {
            // A lemma about any `x = y` (`Nat.succInjective`) leaves the
            // goal in another form: worth suggesting only if it closes it
            // with what the goal has.
            if plan.general {
                return None;
            }
            // Close each `?` in turn with the first closer that does.
            let n = goals.len();
            let mut fills: Vec<String> = vec!["?".to_string(); n];
            let mut obligations = Vec::new();
            for (j, left) in goals.iter().enumerate() {
                // With a witness to give, every goal is the writer's: the
                // goals needn't line up with the `?`s (a witness's goal may
                // not be listed), and a closer could take a witness's place.
                if !witness.is_empty() {
                    break;
                }
                for (name, closer) in closers {
                    if checker.out_of_time() {
                        break;
                    }
                    let mut trial = fills.clone();
                    trial[j] = closer.clone();
                    let ok = match checker.check(&render(plan, &trial, infer), &[]) {
                        Outcome::Closed => true,
                        Outcome::Goals(g) => g.len() < n - obligations.len(),
                        Outcome::Failed => false,
                    };
                    if ok {
                        fills[j] = closer.clone();
                        obligations.push(Obligation {
                            target: left.target.clone(),
                            closer: name,
                        });
                        break;
                    }
                }
            }
            let proof = render(plan, &fills, infer);
            // An obligation that is the goal itself: the closer alone
            // does it (reported once, as `tactics`).
            if obligations
                .iter()
                .any(|o| o.target == checker.target_now || o.target.contains('?'))
            {
                return None;
            }
            if obligations.len() == n {
                match checker.check(&proof, &[]) {
                    Outcome::Closed => {
                        let mut s = base("afterObligations", proof);
                        s.obligations = obligations;
                        s
                    }
                    _ => return None,
                }
            } else {
                // Applicable: the goals it leaves, and a kernel check with
                // each as a hypothesis when they can all be written.
                let left = match checker.check(&proof, &[]) {
                    Outcome::Goals(g) => g,
                    _ => return None,
                };
                // A goal with an unknown in it (`?3 m n`) says nothing
                // about what to prove next.
                if witness.is_empty() && left.iter().any(|g| g.target.contains('?')) {
                    return None;
                }
                // Nor does one that leaves the goal as it was
                // (`Bool.canonicalTrue … ?`, SW-963).
                if (left.iter())
                    .any(|g| g.target == checker.target_now || g.target == checker.goal.target)
                {
                    return None;
                }
                let mut s = base("applicable", proof.clone());
                s.obligations = obligations;
                let writable = checker.intros.is_empty()
                    && left.iter().all(|g| g.lemma.is_some())
                    && left
                        .iter()
                        .all(|g| g.hypotheses.len() == checker.goal.hypotheses.len());
                s.checked = "elaborated";
                if writable {
                    let taken: Vec<&str> = (checker.goal.hypotheses.iter())
                        .map(|h| h.name.as_str())
                        .collect();
                    let names: Vec<String> = (1..)
                        .map(|i| format!("goal{i}"))
                        .filter(|n| !taken.contains(&n.as_str()))
                        .take(left.len())
                        .collect();
                    let extra: Vec<(String, String)> = (names.iter().cloned())
                        .zip(left.iter().map(|g| g.target.clone()))
                        .collect();
                    let mut k = 0;
                    let filled: Vec<String> = fills
                        .iter()
                        .map(|f| {
                            if f == "?" {
                                k += 1;
                                names[k - 1].clone()
                            } else {
                                f.clone()
                            }
                        })
                        .collect();
                    if k == names.len()
                        && matches!(
                            checker.check(&render(plan, &filled, infer), &extra),
                            Outcome::Closed
                        )
                    {
                        s.checked = "kernel";
                    }
                }
                s.goals = left
                    .into_iter()
                    .map(|g| LeftGoal {
                        target: g.target,
                        lemma: g.lemma,
                    })
                    .collect();
                s
            }
        }
    };
    suggestion.name = plan.item_path.clone();
    suggestion.item = Some(plan.item);
    suggestion.conjunct = plan.item.part().map(|p| p.name());
    Some(suggestion)
}

/// Checks one rewrite: the goal it leaves, whether `rfl` or `omega` then
/// closes it, and a kernel check with the rewritten goal as a hypothesis.
fn try_rewrite(
    checker: &mut Checker,
    rp: &stitchwort_elab::closing::RewritePlan,
    target_now: &str,
) -> Option<Rewrite> {
    let rule = render(&rp.plan, &[], false);
    let rule = Rule {
        text: &rule,
        backwards: rp.backwards,
        iff: rp.iff,
        name: &rp.plan.item_path,
        at: &rp.subterm,
    };
    try_rule(checker, &rule, target_now)
}

/// A rewrite to try: `rewrite [<-] text in ?`.
struct Rule<'a> {
    text: &'a str,
    backwards: bool,
    iff: bool,
    /// The lemma's full name, or the hypothesis's.
    name: &'a str,
    /// The call it rewrites, printed (empty for a hypothesis).
    at: &'a str,
}

/// [`try_rewrite`] for any rule.
fn try_rule(checker: &mut Checker, rp: &Rule, target_now: &str) -> Option<Rewrite> {
    let rule = rp.text;
    let arrow = if rp.backwards { "<- " } else { "" };
    let proof = format!("rewrite {arrow}{rule} in ?");
    let left = match checker.check(&proof, &[]) {
        Outcome::Goals(mut g) if g.len() == 1 => g.pop()?,
        _ => return None,
    };
    let left_goal = left.clone();
    if left.target == target_now || left.target == checker.goal.target {
        return None;
    }
    let mut closes = None;
    for closer in ["rfl", "omega", "cases"] {
        let closed = format!("rewrite {arrow}{rule} in {closer}");
        if matches!(checker.check(&closed, &[]), Outcome::Closed) {
            closes = Some(closer);
            break;
        }
    }
    let mut checked = "elaborated";
    if left.lemma.is_some() && checker.intros.is_empty() {
        let taken: Vec<&str> = (checker.goal.hypotheses.iter())
            .map(|h| h.name.as_str())
            .collect();
        let name = (0..)
            .map(|i| {
                if i == 0 {
                    "rewritten".to_string()
                } else {
                    format!("rewritten{i}")
                }
            })
            .find(|n| !taken.contains(&n.as_str()))
            .expect("a free name");
        let with = format!("rewrite {arrow}{rule} in {name}");
        if matches!(
            checker.check(&with, &[(name, left.target.clone())]),
            Outcome::Closed
        ) {
            checked = "kernel";
        }
    }
    Some(Rewrite {
        proof,
        name: rp.name.to_string(),
        ty: String::new(),
        file: String::new(),
        line: 0,
        import: None,
        at: rp.at.to_string(),
        direction: if rp.backwards {
            "rightToLeft"
        } else {
            "leftToRight"
        },
        equation: if rp.iff { "iff" } else { "eq" },
        goal: left.target,
        closes,
        checked,
        recursive: checker.recursive.is_some(),
        left: Some(left_goal),
    })
}

/// What closes goal `at` of `text`, a file on its own named `name`: loaded
/// into a session that then loads the whole library to search, and into a
/// second with only the file, to check the proofs in (as
/// [`Session::search_at`] explains); `new_session` makes both. With `cache`, both load through that
/// check cache. For the language server's code action; the command does
/// the same with the file's includes and project context.
pub fn search_at_text(
    new_session: &dyn Fn() -> Session,
    name: &str,
    text: &str,
    at: GoalAt,
    options: &AtOptions,
    cache: Option<&std::path::Path>,
) -> Result<AtReport, String> {
    let load = |session: &mut Session| -> Vec<Diagnostic> {
        if let Some(dir) = cache {
            session.use_check_cache(dir);
        }
        let mut diagnostics = session.load(name, text).err().unwrap_or_default();
        diagnostics.append(&mut session.warnings);
        diagnostics
    };
    let mut session = new_session();
    let diagnostics = load(&mut session);
    let file = (session.sources.iter())
        .filter(|(_, f)| f.name == name)
        .map(|(id, _)| id)
        .last()
        .ok_or("the file didn't load")?;
    let goals = goals_in(&session.sources, file, &diagnostics);
    let found = pick(&goals, at)?.clone();
    session
        .elab
        .load_all_libraries()
        .map_err(|_| "the library didn't load".to_string())?;
    let mut checking = new_session();
    load(&mut checking);
    session
        .search_at(&found, name, options, &Scope::File, Some(&mut checking))
        .map_err(|d| format!("{}: {}", d.code, d.message))
}

/// A project's files, with some of them given other text (the editor's
/// unsaved text, a benchmark's goal), by path within the project.
pub struct Overlay<'a> {
    pub base: &'a dyn Files,
    pub texts: std::collections::BTreeMap<String, String>,
}

impl Files for Overlay<'_> {
    fn entries(&self, dir: &str) -> std::io::Result<Vec<crate::project::Entry>> {
        self.base.entries(dir)
    }
    fn read(&self, path: &str) -> std::io::Result<String> {
        match self.texts.get(path) {
            Some(text) => Ok(text.clone()),
            None => self.base.read(path),
        }
    }
    fn include_files(&self) -> Option<Rc<dyn stitchwort_elab::project::IncludeFiles>> {
        self.base.include_files()
    }
    fn config(
        &self,
        text: &str,
        display: &str,
        sources: &mut stitchwort_syntax::SourceMap,
    ) -> Result<crate::project::Config, stitchwort_syntax::Diagnostic> {
        self.base.config(text, display, sources)
    }
}

/// A goal in a file of a project, for [`Session::search_at_project`].
pub struct ProjectGoal<'a> {
    /// The project's name, for display (its folder's name).
    pub project: &'a str,
    pub files: &'a dyn Files,
    /// The file, by its path within the project (`src/Aoc/…/Proofs.sw`).
    pub path: &'a str,
    /// The check cache's folder, if one is used.
    pub cache: Option<&'a std::path::Path>,
    pub at: GoalAt,
}

/// The check cache, with writing switched off while the goal's namespace
/// is checked with a suggestion pasted in: that text isn't the file's, and
/// an entry for it would only churn the cache.
struct Gated {
    inner: crate::check_cache::CheckCache,
    writable: Rc<Cell<bool>>,
}

impl stitchwort_elab::cache::Store for Gated {
    fn compiler(&self) -> &str {
        self.inner.compiler()
    }
    fn salt(&self) -> [u8; 16] {
        self.inner.salt()
    }
    fn read(&self, unit: &str, key: &stitchwort_elab::cache::Key) -> Option<Vec<u8>> {
        self.inner.read(unit, key)
    }
    fn write(&self, unit: &str, key: &stitchwort_elab::cache::Key, entry: &[u8]) {
        if self.writable.get() {
            self.inner.write(unit, key, entry);
        }
    }
}

impl Session {
    /// What closes a goal in a file of a project (SW-915, D2100). This
    /// session (a fresh one) loads the whole library, then the project's
    /// namespaces through the check cache: every one except those that use
    /// the file's (they can't be imported by it), the file's last, whose
    /// scope it stays in. So the goal is read, and the proofs written and
    /// checked, with the file's namespace and imports; the candidates are
    /// the library's and those namespaces' declarations, less the goal's own
    /// declaration and what uses it (unfinished, so not searched).
    ///
    /// Then each closing suggestion shown (and each tactic that closes it
    /// alone) is checked in the file: pasted in place of the `?`, the
    /// file's namespace checked again (from a mark, the rest as it was).
    /// One that leaves an error there, or doesn't close the goal, is
    /// dropped (`budget.inFile`).
    pub fn search_at_project(
        &mut self,
        goal: &ProjectGoal,
        options: &AtOptions,
    ) -> Result<AtReport, Diagnostic> {
        let t0 = Instant::now();
        let fail = |message: String| Diagnostic::error("E-SEARCH-AT", message);
        let writable = Rc::new(Cell::new(true));
        if let Some(dir) = goal.cache {
            self.elab.set_check_cache(Rc::new(Gated {
                inner: crate::check_cache::CheckCache::at(dir),
                writable: writable.clone(),
            }));
        }
        if let Some(include) = goal.files.include_files() {
            self.include_from(include);
        }
        // Every library file first, before the project, as the language
        // server loads them (`LiveProject::new`): then rewinding to check
        // the namespace again unloads none.
        if self.elab.load_all_libraries().is_err() {
            return Err(fail("the library didn't load".into()));
        }
        let sources = crate::project::project_sources(goal.files, goal.project, &mut self.sources)
            .map_err(|ds| first_error(&ds, "the project can't be read"))?;
        if !sources.iter().any(|(p, _)| p == goal.path) {
            return Err(fail(format!(
                "{} isn't one of the project {}'s source files",
                goal.path, goal.project
            )));
        }
        debug_time("project: library loaded", t0);
        let parsed = crate::project::parse_files(self, goal.project, sources);
        let file = (parsed.iter())
            .find(|f| f.path == goal.path)
            .map(|f| (f.id, f.text.clone(), f.display.clone()))
            .expect("the file was read");
        let (file_id, text, display) = file;
        let analysis = crate::project::analyse_parsed(&mut self.elab, goal.project, parsed.clone());
        let ns = (analysis.namespaces.iter())
            .find(|n| n.files.contains(&file_id))
            .map(|n| n.name.clone())
            .ok_or_else(|| first_error(&analysis.diagnostics, "the file has no namespace"))?;
        let namespaces: Vec<String> = analysis.namespaces.iter().map(|n| n.name.clone()).collect();
        debug_time("project: analysed", t0);
        let load = self
            .load_for_goal(goal.project, &analysis, &ns)
            .map_err(|ds| first_error(&ds, "the project can't be checked"))?;
        let errors =
            |ds: &[Diagnostic]| ds.iter().filter(|d| d.severity == Severity::Error).count();
        let mut warnings = Vec::new();
        if errors(&load.diagnostics) > 0 {
            let first = first_error(&load.diagnostics, "");
            warnings.push(format!(
                "{ns} doesn't check ({} errors; the first: [{}] {}): its goals are searched as they stand",
                errors(&load.diagnostics),
                first.code,
                first.message
            ));
        }
        let goals = goals_in(&self.sources, file_id, &load.diagnostics);
        let found = pick(&goals, goal.at)
            .map_err(|m| fail(format!("{display}: {m}")))?
            .clone();
        self.elab.use_file_scope(file_id);
        let scope = Scope::ProjectFile {
            namespaces,
            own: ns.clone(),
        };
        debug_time("project: loaded", t0);
        if std::env::var_os("STITCHWORT_SEARCH_DEBUG").is_some() {
            eprintln!("search --at: cache {:?}", self.elab.check_cache_stats());
        }
        let mut report = self.search_at(&found, &display, options, &scope, None)?;
        report.warnings.extend(warnings);
        // Each closing suggestion shown, checked in the file.
        writable.set(false);
        let mut in_file = InFile::default();
        let mut dropped: Vec<String> = Vec::new();
        let errors_before = errors(&load.diagnostics);
        // Each check here checks the whole namespace again: for a namespace
        // of heavy proofs, seconds each. They have a `--time` of their own;
        // past it (after the first), the rest aren't checked, so not listed.
        let deadline = Instant::now() + options.time;
        let mut confirm = |session: &mut Session, proof: &str| -> bool {
            if in_file.checked > 0 && Instant::now() >= deadline {
                in_file.unchecked += 1;
                return false;
            }
            let pasted = paste(&text, found.span, proof);
            let (diagnostics, id) =
                session.recheck_for_goal(goal.project, &parsed, (goal.path, &pasted), &ns, &load);
            in_file.checked += 1;
            let left = goals_in(&session.sources, id, &diagnostics).len();
            // The namespace's errors before (a file being written may have
            // some) may stay; none may come from the proof, and none more.
            let pasted_end = found.span.0 + paste_text(&text, found.span, proof).len();
            let at_proof = |d: &&&Diagnostic| {
                d.primary_span().is_some_and(|s| {
                    s.file == id && (s.start as usize) < pasted_end && s.end as usize > found.span.0
                })
            };
            let new_errors = (diagnostics.iter())
                .filter(|d| d.severity == Severity::Error)
                .collect::<Vec<_>>();
            let culprit = (new_errors.iter())
                .find(at_proof)
                .or_else(|| (new_errors.len() > errors_before).then(|| &new_errors[0]));
            let why = match culprit {
                Some(d) => format!("[{}] {}", d.code, d.message),
                None if left + 1 != goals.len() => "the goal is still open".to_string(),
                None => return true,
            };
            in_file.rejected += 1;
            dropped.push(format!("`{proof}`: {why}"));
            false
        };
        // The ladder's answer stands only if it holds in the file too;
        // otherwise the full search's answers are the ones to show.
        let simplest_holds = report.simplest.is_some() && {
            let proof = match (report.tactics.first(), report.results.first()) {
                (Some(t), _) => tactic_proof(&report, t),
                (None, Some(s)) => s.proof.clone(),
                (None, None) => String::new(),
            };
            confirm(self, &proof)
        };
        if report.simplest.is_some() && !simplest_holds {
            let full = AtOptions {
                simplest_first: false,
                ..options.clone()
            };
            let mut again = self.search_at(&found, &display, &full, &scope, None)?;
            again.warnings.append(&mut report.warnings);
            report = again;
        }
        if !simplest_holds {
            let mut tactics = Vec::new();
            for t in std::mem::take(&mut report.tactics) {
                if confirm(self, &tactic_proof(&report, &t)) {
                    tactics.push(t);
                }
            }
            report.tactics = tactics;
            let mut results = Vec::new();
            for s in std::mem::take(&mut report.results) {
                if s.class == "applicable" || confirm(self, &s.proof) {
                    results.push(s);
                } else {
                    report.total.closing -= 1;
                }
            }
            report.results = results;
        }
        for d in dropped {
            (report.warnings).push(format!(
                "checked at the goal but not in the file, so dropped: {d}"
            ));
        }
        if in_file.unchecked > 0 {
            report.warnings.push(format!(
                "the time ran out checking suggestions in the file (each checks {ns} again): \
                 {} more weren't checked there, so aren't listed (--time for more)",
                in_file.unchecked
            ));
        }
        debug_time("project: confirmed", t0);
        report.budget.in_file = Some(in_file);
        report.goal.file = display;
        writable.set(true);
        Ok(report)
    }
}

/// What to write in place of the `?` for tactic `tactic`, which closes the
/// goal alone: after the variables the target introduces, as the other
/// suggestions are.
pub fn tactic_proof(report: &AtReport, tactic: &str) -> String {
    let mut proof = String::new();
    for x in &report.goal.introduced {
        proof.push_str(&format!("{x} => "));
    }
    proof.push_str(tactic);
    proof
}

/// The first error of `diagnostics`, as one, or `why` if there is none.
fn first_error(diagnostics: &[Diagnostic], why: &str) -> Diagnostic {
    let errors: Vec<&Diagnostic> = (diagnostics.iter())
        .filter(|d| d.severity == Severity::Error)
        .collect();
    match errors.first() {
        Some(d) => {
            let mut d = (*d).clone();
            if errors.len() > 1 {
                d = d.with_note(format!("and {} more errors", errors.len() - 1));
            }
            d
        }
        None => Diagnostic::error("E-SEARCH-AT", why.to_string()),
    }
}

/// With `STITCHWORT_SEARCH_DEBUG` set, how long `search --at` has taken by
/// each of its phases.
fn debug_time(phase: &str, started: Instant) {
    if std::env::var_os("STITCHWORT_SEARCH_DEBUG").is_some() {
        eprintln!(
            "search --at: {phase} at {:.2} s",
            started.elapsed().as_secs_f64()
        );
    }
}

/// The report as text.
pub fn render_text(report: &AtReport) -> String {
    let mut out = String::new();
    let g = &report.goal;
    out.push_str(&format!(
        "goal {} at {}:{}:{}\n",
        g.index, g.file, g.line, g.column
    ));
    for h in &g.hypotheses {
        out.push_str(&format!("  {}: {}\n", h.name, h.ty));
    }
    out.push_str(&format!("  ⊢ {}\n", g.target));
    if !report.tactics.is_empty() {
        out.push_str(&format!(
            "\n{} alone closes it (checked by the kernel)\n",
            report.tactics.join(", ")
        ));
    }
    let closing: Vec<&Suggestion> = (report.results.iter())
        .filter(|s| s.class != "applicable")
        .collect();
    let applicable: Vec<&Suggestion> = (report.results.iter())
        .filter(|s| s.class == "applicable")
        .collect();
    let place = |s: &Suggestion| {
        let import = s
            .import
            .as_ref()
            .map(|i| format!("  ({i})"))
            .unwrap_or_default();
        format!("{}  {}:{}{import}", s.name, s.file, s.line)
    };
    if !closing.is_empty() {
        out.push_str("\ncloses it (checked by the kernel):\n");
        for (i, s) in closing.iter().enumerate() {
            out.push_str(&format!("{:>2}. {}  [{}]\n", i + 1, s.proof, s.class));
            if let Some(part) = &s.conjunct {
                out.push_str(&format!("    the {part} conjunct of:\n"));
            }
            out.push_str(&format!("    {}\n", place(s)));
            if s.recursive {
                out.push_str("    uses the induction hypothesis: a call of the declaration being proved, on a structurally smaller argument; termination is checked once the proof is pasted\n");
            }
            for o in &s.obligations {
                out.push_str(&format!("    {} closes ⊢ {}\n", o.closer, o.target));
            }
        }
    }
    if !applicable.is_empty() {
        out.push_str("\napplies, leaving goals:\n");
        for (i, s) in applicable.iter().enumerate() {
            out.push_str(&format!("{:>2}. {}\n", i + 1, s.proof));
            out.push_str(&format!("    {}\n", place(s)));
            for left in &s.goals {
                out.push_str(&format!("    leaves ⊢ {}\n", left.target));
            }
        }
    }
    if !report.rewrites.is_empty() {
        out.push_str("\nrewrites:\n");
        for (i, r) in report.rewrites.iter().enumerate() {
            let closes = r
                .closes
                .map(|c| format!("  (then {c} closes it)"))
                .unwrap_or_default();
            out.push_str(&format!("{:>2}. {}{closes}\n", i + 1, r.proof));
            if r.recursive {
                out.push_str("    uses the induction hypothesis: a call of the declaration being proved, on a structurally smaller argument; termination is checked once the proof is pasted\n");
            }
            out.push_str(&format!("    leaves ⊢ {}\n", r.goal));
        }
    }
    if !report.induction.is_empty() {
        out.push_str("\ninduction hypothesis (calls of the declaration being proved, on structurally smaller arguments; termination is checked once the proof is pasted), for a closer such as omega [h], or to rewrite with:\n");
        for (i, call) in report.induction.iter().enumerate() {
            out.push_str(&format!("{:>2}. {call}\n", i + 1));
        }
    }
    let t = &report.total;
    out.push_str(&format!(
        "\n{} closing, {} applicable, {} rewrites; tried {} of {} matching declarations, {} checks\n",
        t.closing,
        t.applicable,
        t.rewrites,
        report.budget.tried,
        report.budget.matched,
        report.budget.checks
    ));
    for w in &report.warnings {
        out.push_str(&format!("warning: {w}\n"));
    }
    out
}
