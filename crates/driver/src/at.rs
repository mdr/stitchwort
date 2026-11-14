//! Answers at a position (docs/proposals/editor-and-playground-roadmap.md
//! §3): the goal at the cursor, the hover, the parameters of the call being
//! typed, the quick fixes for a goal, and the context at any cursor.
//!
//! Each is a function over what checking recorded ([`FileAnswers`], the
//! text) or over a [`Session`], and answers with a plain struct that
//! serialises: the language server turns them into `lsp-types`, the
//! playground into JSON. Positions are zero-based lines and UTF-16 columns,
//! as in the language server protocol; ranges are [`Range`]s,
//! `[start line, start column, end line, end column]`.

use std::time::Duration;

use serde::Serialize;
use stitchwort_syntax::Severity;

use crate::completion::{self, Parameter};
use crate::driver::Session;
use crate::live::{FileAnswers, LiveRef, Place, ScopeName};
use crate::nav::Range;
use crate::project::Files;
use crate::search_at::{
    AtOptions, AtReport, GoalAt, ProjectGoal, paste_text, search_at_text, tactic_proof,
};

// ---- text positions -----------------------------------------------------

/// The byte offset of a position (UTF-16 columns), clamped to the text.
pub fn offset_at(text: &str, line: u32, character: u32) -> usize {
    let (mut l, mut col) = (0u32, 0u32);
    for (i, c) in text.char_indices() {
        if l > line || (l == line && col >= character) {
            return i;
        }
        if c == '\n' {
            (l, col) = (l + 1, 0);
        } else {
            col += c.len_utf16() as u32;
        }
    }
    text.len()
}

/// The position (line, UTF-16 column) of a byte offset.
pub fn position_at(text: &str, offset: usize) -> (u32, u32) {
    let before = &text[..offset];
    let line = before.matches('\n').count() as u32;
    let start = before.rfind('\n').map_or(0, |i| i + 1);
    let col = before[start..].chars().map(|c| c.len_utf16() as u32).sum();
    (line, col)
}

/// `selection` without the whitespace at its ends (a selection often takes
/// in the space or the line break beside an expression). Unchanged if it is
/// all whitespace.
pub fn trimmed(text: &str, selection: Range) -> Range {
    let start = (selection[0], selection[1]);
    let end = (selection[2], selection[3]);
    let mut first = None;
    let mut last = None;
    let (mut line, mut col) = (0u32, 0u32);
    for c in text.chars() {
        let here = (line, col);
        if here >= end {
            break;
        }
        let after = (line, col + c.len_utf16() as u32);
        if here >= start && !c.is_whitespace() {
            first.get_or_insert(here);
            last = Some(after);
        }
        if c == '\n' {
            (line, col) = (line + 1, 0);
        } else {
            col = after.1;
        }
    }
    match (first, last) {
        (Some(s), Some(e)) => [s.0, s.1, e.0, e.1],
        _ => selection,
    }
}

/// The identifier (letters, digits, `_` and `'`) the position is in or at
/// the end of, as a range; none if it isn't on one.
pub fn word_at(text: &str, line: u32, character: u32) -> Option<Range> {
    let line_text = text.split('\n').nth(line as usize)?;
    let line_text = line_text.strip_suffix('\r').unwrap_or(line_text);
    let is_word = |c: char| c.is_alphanumeric() || c == '_' || c == '\'';
    // UTF-16 columns of each character's start, and the end of the line.
    let mut columns = Vec::new();
    let mut col = 0u32;
    for c in line_text.chars() {
        columns.push((col, c));
        col += c.len_utf16() as u32;
    }
    let index = columns
        .iter()
        .position(|(c, _)| *c >= character)
        .unwrap_or(columns.len());
    let in_word = |i: usize| columns.get(i).is_some_and(|(_, c)| is_word(*c));
    // The cursor sits between two characters: the word is the one it touches.
    let mut at_i = if columns.get(index).is_some_and(|(c, _)| *c == character) && in_word(index) {
        index
    } else if index > 0 && in_word(index - 1) {
        index - 1
    } else {
        return None;
    };
    let mut start = at_i;
    while start > 0 && in_word(start - 1) {
        start -= 1;
    }
    while in_word(at_i + 1) {
        at_i += 1;
    }
    let end_col = columns[at_i].0 + columns[at_i].1.len_utf16() as u32;
    Some([line, columns[start].0, line, end_col])
}

// ---- goals --------------------------------------------------------------

/// One name in scope at a goal or a cursor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Local {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    /// For a `let` of data, its value.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value: Option<String>,
    /// How it splits into its type's constructors, as written where it is
    /// in scope ([`Session::split_patterns`]).
    #[serde(skip)]
    pub splits: Option<Vec<String>>,
}

/// An open goal `?`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Goal {
    pub range: Range,
    /// What the hole is in: "`addZero`".
    pub owner: String,
    /// What must be shown (after `⊢`), as written (D3522).
    pub goal: String,
    /// What it computes to, when that prints differently.
    #[serde(rename = "goalComputed")]
    pub goal_computed: Option<String>,
    pub context: Vec<Local>,
    /// Whether the goal is a proposition (a proof goal), if its sort was
    /// known when the hole was checked.
    #[serde(skip)]
    pub prop: Option<bool>,
    /// The goal as the command line prints it (the label, then the notes).
    pub text: String,
}

/// The open goals of a file, in the order checking reported them.
pub fn goals_of(file: &FileAnswers) -> Vec<Goal> {
    file.diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Goal)
        .filter_map(|d| {
            let data = d.goal.as_ref()?;
            let mut body: Vec<String> = Vec::new();
            if let Some((_, first)) = d.labels.first()
                && !first.is_empty()
                && *first != d.message
            {
                body.push(first.clone());
            }
            body.extend(note_lines(&d.notes));
            Some(Goal {
                range: d.range,
                owner: d
                    .message
                    .strip_prefix("in ")
                    .unwrap_or(&d.message)
                    .to_string(),
                goal: data.shown().to_string(),
                goal_computed: data.computed().map(str::to_string),
                context: (data.hypotheses.iter())
                    .map(|h| Local {
                        name: h.name.clone(),
                        ty: h.ty.clone(),
                        value: h.value.clone(),
                        splits: h.splits.clone(),
                    })
                    .collect(),
                prop: data.prop,
                text: body.join("\n"),
            })
        })
        .collect()
}

/// The notes of a diagnostic as the command line labels them: `Note: …` for
/// a lone note, `Note 1: …`, `Note 2: …` when there are several, so a
/// message that refers to "note 3" matches what the editor shows.
pub fn note_lines(notes: &[String]) -> Vec<String> {
    notes
        .iter()
        .enumerate()
        .map(|(i, note)| match notes.len() {
            1 => format!("Note: {note}"),
            _ => format!("Note {}: {note}", i + 1),
        })
        .collect()
}

/// The goal at `(line, character)`: the one whose `?` the position is on or
/// touches, else the nearest one (by line) in the same declaration of
/// `file` (its outline), else none. `goals` are the goals to choose from:
/// [`goals_of`] the file, or what an editor still shows (goals kept while
/// the text between declarations doesn't parse).
pub fn goal_at<'g>(
    goals: &'g [Goal],
    file: Option<&FileAnswers>,
    line: u32,
    character: u32,
) -> Option<&'g Goal> {
    let at = (line, character);
    let within = |r: Range, p: (u32, u32)| (r[0], r[1]) <= p && p <= (r[2], r[3]);
    goals.iter().find(|g| within(g.range, at)).or_else(|| {
        let declaration = file?
            .outline
            .iter()
            .find(|item| item.parent.is_none() && within(item.full_range, at))?
            .full_range;
        goals
            .iter()
            .filter(|g| within(declaration, (g.range[0], g.range[1])))
            .min_by_key(|g| g.range[0].abs_diff(line))
    })
}

// ---- hover --------------------------------------------------------------

/// What to show over a position.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Hover {
    pub range: Range,
    pub markdown: String,
}

/// The reference at a position of the file `place`: a name written there,
/// or (in the program) a binder, which is a reference too when something
/// uses it.
pub fn reference_at(
    file: &FileAnswers,
    place: &Place,
    line: u32,
    character: u32,
) -> Option<LiveRef> {
    if let Place::Library(_) = place {
        return file.ref_at(line, character).cloned();
    }
    Some(match file.ref_at(line, character) {
        Some(r) if r.kind == "local" && r.ty.is_none() => {
            // A binder's own reference has no type: a use of it does.
            let ty = file
                .binder_exactly(place, r.target.range)
                .and_then(|b| b.ty);
            LiveRef { ty, ..r.clone() }
        }
        Some(r) => r.clone(),
        None => file.binder_at(place, line, character)?,
    })
}

/// The hover of a reference: its type, then what it is, its doc, and the
/// defaults a call left out.
pub fn hover_of(r: &LiveRef) -> Hover {
    let mut text = String::new();
    // A function shows its declaration's header, with its parameters named,
    // in place of the type and the line saying what it is.
    match (&r.header, r.kind) {
        (Some(header), "def" | "theorem" | "instance") => {
            text.push_str(&format!(
                "```stitchwort\n{} {} {header}\n```",
                r.kind, r.name
            ));
            if let Some(unfolded) = &r.unfolded {
                text.push_str(&format!("\nthat is, {unfolded}"));
            }
        }
        _ => {
            if let Some(ty) = &r.ty {
                text.push_str(&format!("```stitchwort\n{ty}\n```\n"));
                if let Some(unfolded) = &r.unfolded {
                    text.push_str(&format!("that is, {unfolded}\n"));
                }
            }
            text.push_str(&format!("{} `{}`", r.kind, r.name));
        }
    }
    if let Some(doc) = &r.doc {
        text.push_str(&format!("\n\n{doc}"));
    }
    if let Some(defaults) = &r.defaults {
        text.push_str(&format!("\n\n{defaults}"));
    }
    if let Some(equations) = &r.equations {
        text.push_str(&format!("\n\n{equations}"));
    }
    Hover {
        range: r.range,
        markdown: text,
    }
}

/// The hover at `(line, character)` of the file `place`. With a
/// `selection` (not empty), the type of the smallest expression containing
/// it, if there is one; else what the name under the position is.
pub fn hover_at(
    file: &FileAnswers,
    place: &Place,
    text: Option<&str>,
    line: u32,
    character: u32,
    selection: Option<Range>,
) -> Option<Hover> {
    let selection = selection.map(|s| match text {
        Some(text) => trimmed(text, s),
        None => s,
    });
    if let Some(found) = selection.and_then(|s| selection_hover(file, place, text, s)) {
        return Some(found);
    }
    if let Some(r) = reference_at(file, place, line, character) {
        return Some(hover_of(&r));
    }
    // A `?` itself: its goal, as the Goals panel shows it.
    let at = (line, character);
    let goal = goals_of(file)
        .into_iter()
        .find(|g| (g.range[0], g.range[1]) <= at && at <= (g.range[2], g.range[3]))?;
    let mut markdown = String::from("```stitchwort\n");
    for local in &goal.context {
        markdown.push_str(&format!("{}: {}\n", local.name, local.ty));
    }
    markdown.push_str(&format!("⊢ {}\n```", goal.goal));
    if !goal.text.is_empty() {
        markdown.push_str(&format!("\n\n{}", goal.text));
    }
    Some(Hover {
        range: goal.range,
        markdown,
    })
}

/// The type of the smallest expression containing `selection`.
fn selection_hover(
    file: &FileAnswers,
    place: &Place,
    text: Option<&str>,
    selection: Range,
) -> Option<Hover> {
    // A name on its own: a binder gets its own type (or nothing, when it's
    // unused); the expression around it isn't what was selected.
    if text.and_then(|t| word_at(t, selection[0], selection[1])) == Some(selection) {
        if let Some(binder) = file.binder_exactly(place, selection) {
            return Some(hover_of(&binder));
        }
        if file.exprs.iter().all(|(r, _, _)| *r != selection) {
            return None;
        }
    }
    let (range, ty, unfolded) = file.expr_covering(selection)?;
    let mut markdown = format!("```stitchwort\n{ty}\n```");
    if let Some(unfolded) = unfolded {
        markdown.push_str(&format!("\nthat is, {unfolded}"));
    }
    Some(Hover { range, markdown })
}

// ---- signature ----------------------------------------------------------

/// The call whose argument the cursor is in, and the function's parameters.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Signature {
    /// The function, as written (`clampTo`, `xs.map`).
    pub function: String,
    /// The function's type with its parameters named
    /// (`(low: Nat) -> [n: Nat] -> Nat`).
    pub signature: String,
    /// The bracket was `[`: implicit parameters are wanted.
    pub implicit: bool,
    /// The parameters already given by name.
    pub given: Vec<String>,
    /// All the named parameters, in order.
    pub parameters: Vec<Parameter>,
}

impl Signature {
    /// The parameters that can still be named here: of the kind of bracket
    /// the cursor follows, and not given yet.
    pub fn wanted(&self) -> impl Iterator<Item = &Parameter> {
        (self.parameters.iter())
            .filter(|p| p.implicit == self.implicit && !self.given.contains(&p.name))
    }
}

/// The call whose argument is being started at byte `offset` of `text` (the
/// cursor right after `(` or `[` and a partial name), with the function's
/// parameters. The function is found by its name among the file's last
/// published references, so an edit that doesn't parse (the call being
/// typed) doesn't hide it.
pub fn signature_at(file: &FileAnswers, text: &str, offset: usize) -> Option<Signature> {
    let call = completion::call_at(text, offset)?;
    let signature = printed_signature(file, &call.head, None)?;
    Some(Signature {
        function: call.head,
        signature: signature.to_string(),
        implicit: call.implicit,
        given: call.given,
        parameters: completion::parameters(signature),
    })
}

/// The printed type of the function `head` (as written), from the
/// references the file last published. Where `head` is written (byte
/// offsets in `text`) the reference recorded there says which function it
/// is, even when another in the file has the same short name; only a head
/// with no function referenced there (text that didn't check) is found by
/// its name.
fn printed_signature<'a>(
    file: &'a FileAnswers,
    head: &str,
    written: Option<(&str, (usize, usize))>,
) -> Option<&'a str> {
    if let Some((text, (from, to))) = written {
        let (start, end) = (position_at(text, from), position_at(text, to));
        // `xs.map`: the last reference in the head is the function.
        let found = (file.refs.iter())
            .filter(|r| (r.range[0], r.range[1]) >= start && (r.range[2], r.range[3]) <= end)
            .max_by_key(|r| (r.range[0], r.range[1]));
        if let Some(signature) = found.and_then(|r| r.signature.as_deref()) {
            return Some(signature);
        }
    }
    let last = head.rsplit('.').next().unwrap_or(head);
    file.refs
        .iter()
        .filter(|r| r.name == last || r.name.ends_with(&format!(".{last}")))
        .find_map(|r| r.signature.as_deref())
}

/// A call's signature for the editor to show, with the parameter the
/// cursor is at.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignatureHelp {
    /// `clampTo (low: Nat) (high: Nat) (value: Nat): Nat`.
    pub label: String,
    /// Where each parameter is in `label`, in UTF-16 units, in order.
    pub parameters: Vec<[u32; 2]>,
    /// The parameter (an index in `parameters`) the cursor is at.
    pub active: Option<usize>,
}

/// The signature of the innermost call around byte `offset` of `text`
/// whose function has a published type with parameters, and the parameter
/// the cursor is at: the next one without a name, or the one the cursor's
/// `(name := …)` names.
pub fn signature_help_at(file: &FileAnswers, text: &str, offset: usize) -> Option<SignatureHelp> {
    completion::calls_at(text, offset)
        .into_iter()
        .find_map(|call| {
            let ty = printed_signature(file, &call.head, Some((text, call.head_at)))?;
            let mut parts = completion::segments(ty);
            let result = parts.pop()?;
            if parts.is_empty() {
                return None;
            }
            let mut label = call.head.clone();
            let mut spans = Vec::new();
            let width = |s: &str| u32::try_from(s.encode_utf16().count()).unwrap_or(u32::MAX);
            for part in &parts {
                label.push(' ');
                let start = width(&label);
                // An unnamed parameter is its type: bracketed where it
                // has several words, so that it reads as one.
                if part.contains(' ') && !part.starts_with(['(', '[']) {
                    label.push_str(&format!("({part})"));
                } else {
                    label.push_str(part);
                }
                spans.push([start, width(&label)]);
            }
            label.push_str(": ");
            label.push_str(result);
            let named = |p: &&str| completion::parameter(p);
            let active = match &call.named {
                Some(name) => parts
                    .iter()
                    .position(|p| named(p).is_some_and(|p| &p.name == name)),
                None => parts
                    .iter()
                    .enumerate()
                    .filter(|(_, p)| !p.starts_with('['))
                    .filter(|(_, p)| named(p).is_none_or(|p| !call.given.contains(&p.name)))
                    .map(|(i, _)| i)
                    .nth(call.position),
            };
            Some(SignatureHelp {
                label,
                parameters: spans,
                active,
            })
        })
}

// ---- quick fixes --------------------------------------------------------

/// A quick fix: replace `range` with `new_text`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Action {
    pub title: String,
    pub range: Range,
    #[serde(rename = "newText")]
    pub new_text: String,
}

/// Options for the quick fixes' search: the simplest closer alone if one
/// closes the goal (SW-2966); else the top three, within 5 s, and no more
/// candidates once `wanted` have closed the goal.
pub fn action_options(wanted: usize) -> AtOptions {
    AtOptions {
        limit: 3,
        stop_after_closing: Some(wanted),
        simplest_first: true,
        time: Duration::from_secs(5),
        ..Default::default()
    }
}

/// The quick fixes for what `search --at` found at the `?` at `range` of
/// `text`: each tactic that closes it alone, then the top three closing
/// proofs, written as they go there (in brackets where the `?` is an
/// argument).
pub fn actions_from(report: &AtReport, text: &str, range: Range) -> Vec<Action> {
    let span = (
        offset_at(text, range[0], range[1]),
        offset_at(text, range[2], range[3]),
    );
    let action = |title: String, proof: &str| Action {
        title,
        range,
        new_text: paste_text(text, span, proof),
    };
    let mut actions: Vec<Action> = (report.tactics.iter())
        .map(|t| {
            let proof = tactic_proof(report, t);
            action(
                format!("Replace ? with `{proof}` (closes it alone)"),
                &proof,
            )
        })
        .collect();
    for s in report
        .results
        .iter()
        .filter(|s| s.class != "applicable")
        .take(3)
    {
        actions.push(action(
            format!("Replace ? with `{}` ({}, {})", s.proof, s.class, s.name),
            &s.proof,
        ));
    }
    actions
}

fn goal_line(range: Range) -> GoalAt {
    GoalAt::Line(range[0] as usize + 1, Some(range[1] as usize + 1))
}

/// The quick fixes that replace the goal `?` at `range` of `text` (a file
/// on its own, named `name`) with a proof that closes it; `cache` is the
/// check cache's folder, if one is used. `None` if the search can't run.
pub fn actions_at_text(
    new_session: &dyn Fn() -> Session,
    name: &str,
    text: &str,
    range: Range,
    options: &AtOptions,
    cache: Option<&std::path::Path>,
) -> Option<Vec<Action>> {
    let report = search_at_text(new_session, name, text, goal_line(range), options, cache).ok()?;
    Some(actions_from(&report, text, range))
}

impl Session {
    /// [`actions_at_text`] for a goal in the file `path` of a project, whose
    /// files are `files` (the editor's unsaved text laid over the disk's,
    /// say): the project's namespaces through its check cache, the goal
    /// read and the proofs checked in the file's namespace, as `search
    /// --at` does ([`Session::search_at_project`]). `text` is the file's
    /// text as the editor has it.
    #[allow(clippy::too_many_arguments)]
    pub fn actions_at_project(
        &mut self,
        project: &str,
        files: &dyn Files,
        path: &str,
        cache: Option<&std::path::Path>,
        text: &str,
        range: Range,
        options: &AtOptions,
    ) -> Option<Vec<Action>> {
        let goal = ProjectGoal {
            project,
            files,
            path,
            cache,
            at: goal_line(range),
        };
        let report = self.search_at_project(&goal, options).ok()?;
        Some(actions_from(&report, text, range))
    }
}

// ---- context -----------------------------------------------------------

/// What is known at a cursor: the type of the smallest expression there,
/// and the names in scope; or, on a step of a proof, the goal after it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Context {
    /// The expression (or step) the answer is about.
    pub range: Range,
    /// Its type: what it was checked against when `checked` (the expected
    /// type), else the type found for it.
    #[serde(rename = "type")]
    pub ty: String,
    /// What `ty` computes to, when that prints differently (D3522: `ty` is
    /// as written).
    #[serde(rename = "typeComputed")]
    pub ty_computed: Option<String>,
    pub checked: bool,
    /// Whether `ty` is a proposition: the answer is a goal to prove, not the
    /// type of a program's expression.
    pub proof: bool,
    /// The type found for the expression, when it isn't `ty`, the one it
    /// was checked against (D3499: `expected T`, `has type U`).
    pub found: Option<String>,
    /// The names in scope there, a variable before anything whose type
    /// mentions it; the same list and the same printing as a goal's.
    pub locals: Vec<Local>,
    /// The declaration it is in, as written.
    pub declaration: Option<String>,
    /// The step of the proof the cursor is on, if any.
    pub step: Option<Step>,
    /// Every step of the declaration, in source order.
    pub steps: Vec<Step>,
}

/// A step of a proof: a place where its goal changes
/// (docs/proposals/goal-at-any-point.md §3.1).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Step {
    /// `match`, `arm`, `rewriteRule`, `calcLine`, `lambda`, `let`, `if`, or
    /// `statement` in a declaration's signature (its body's goal).
    pub form: &'static str,
    /// Where it is, as a reader would name it: "rule 2 of 2 of `rewrite`".
    pub description: String,
    /// The text it answers for: a rule, an arm's pattern, a calc line up to
    /// its proof, a parameter, a `let`'s name.
    pub range: Range,
    /// Which of how many, from 1: a rule of its `rewrite`, an arm of its
    /// `match`, a line of its `calc`, `then` (1) or `else` (2).
    pub index: Option<usize>,
    pub of: Option<usize>,
    /// The goal before the step: for a `calc` line, what the lines before
    /// it prove.
    pub before: Option<String>,
    /// What `before` computes to, when that prints differently.
    #[serde(rename = "beforeComputed")]
    pub before_computed: Option<String>,
    /// The goal after it: for a `calc` line, the line's statement.
    pub after: String,
    /// What `after` computes to, when that prints differently.
    #[serde(rename = "afterComputed")]
    pub after_computed: Option<String>,
    /// Whether the goals are propositions.
    pub proof: bool,
    /// The names the step brings into scope.
    pub adds: Vec<String>,
    /// A rewrite rule's equation as used, its unknowns solved.
    pub rule: Option<String>,
    /// For `rewrite … at h`: `h`, whose type the rules rewrite.
    pub target: Option<String>,
    /// The names in scope after the step.
    pub locals: Vec<Local>,
}

impl Step {
    fn of(step: stitchwort_elab::StepAt, text: &str) -> Step {
        use stitchwort_elab::StepForm;
        let (l1, c1) = position_at(text, step.head.start as usize);
        let (l2, c2) = position_at(text, step.head.end as usize);
        let written = (text.get(step.head.start as usize..step.head.end as usize))
            .unwrap_or("")
            .trim()
            .trim_end_matches("=>")
            .trim_end_matches(":=")
            .trim();
        let numbered = |what: &str| match step.index {
            Some((i, n)) => format!("{what} {} of {n}", i + 1),
            None => what.to_string(),
        };
        // A declaration's own body, `name (params): T := body`, is the arm
        // of no `match`: its head is the signature, and what it adds are the
        // parameters, the declaration's own.
        let statement = step.form == StepForm::Arm && !written.starts_with('|');
        let description = match step.form {
            _ if statement => "the statement".into(),
            StepForm::Match => match step.index {
                Some((_, n)) => format!("`match` with {n} arm{}", if n == 1 { "" } else { "s" }),
                None => "`match`".into(),
            },
            StepForm::Arm => format!("{}, `{written}`", numbered("arm")),
            StepForm::RewriteRule => match &step.target {
                Some(h) => format!("{} of `rewrite … at {h}`", numbered("rule")),
                None => format!("{} of `rewrite`", numbered("rule")),
            },
            StepForm::CalcLine => format!("{} of `calc`, `{written}`", numbered("line")),
            StepForm::Lambda => format!("parameter `{written}`"),
            StepForm::Let => format!("`let {written}`"),
            StepForm::If => match step.index {
                Some((1, _)) => "`else` of `if`".into(),
                _ => "`then` of `if`".into(),
            },
        };
        let before = match step.before {
            Some(computed) => {
                let (shown, computed) = written_first(computed, step.before_written);
                (Some(shown), computed)
            }
            None => (None, None),
        };
        let after = written_first(step.after, step.after_written);
        Step {
            form: if statement {
                "statement"
            } else {
                step.form.name()
            },
            description,
            range: [l1, c1, l2, c2],
            index: step.index.map(|(i, _)| i + 1),
            of: step.index.map(|(_, n)| n),
            before: before.0,
            before_computed: before.1,
            after: after.0,
            after_computed: after.1,
            proof: step.proof,
            adds: if statement { Vec::new() } else { step.adds },
            rule: step.rule,
            target: step.target,
            locals: step.locals.into_iter().map(Local::of).collect(),
        }
    }
}

/// What a reader sees first and what it computes to, from a goal's computed
/// print and its print as written, if that differs (D3522).
fn written_first(computed: String, written: Option<String>) -> (String, Option<String>) {
    match written {
        Some(written) => (written, Some(computed)),
        None => (computed, None),
    }
}

impl Local {
    fn of(h: stitchwort_syntax::Hypothesis) -> Local {
        Local {
            name: h.name,
            ty: h.ty,
            value: h.value,
            splits: h.splits,
        }
    }
}

/// The line `computes to …` under a goal printed after `indent` columns,
/// plain (the editors dim it), cut to [`stitchwort_syntax::COMPUTES_TO_LIMIT`].
fn computes_to(out: &mut String, indent: usize, computed: &Option<String>) {
    if let Some(computed) = computed {
        let cut = stitchwort_syntax::cut_computed(computed);
        out.push_str(&format!("{:indent$}computes to {cut}\n", ""));
    }
}

impl Context {
    /// The answer as the command line prints it: where it is, the names in
    /// scope, then `⊢ goal` in a proof or `expected T` in a program (and
    /// `has type U` when the expression's own type differs); on a step, the
    /// goal before and after it.
    pub fn render_text(&self) -> String {
        let mut out = String::new();
        if let Some(declaration) = &self.declaration {
            match &self.step {
                Some(step) => out.push_str(&format!("in `{declaration}`, {}\n", step.description)),
                None => out.push_str(&format!("in `{declaration}`\n")),
            }
        }
        let added =
            |name: &str| (self.step.as_ref()).is_some_and(|s| s.adds.iter().any(|a| a == name));
        for local in &self.locals {
            let mark = if added(&local.name) { "+ " } else { "" };
            match &local.value {
                Some(value) => out.push_str(&format!(
                    "  {mark}{}: {} := {value}\n",
                    local.name, local.ty
                )),
                None => out.push_str(&format!("  {mark}{}: {}\n", local.name, local.ty)),
            }
        }
        let goal = |proof: bool| if proof { "⊢" } else { "expected" };
        match &self.step {
            Some(step) => {
                // `rewrite … at h` rewrites `h`'s type, not the goal.
                let target = step.target.as_ref().map(|h| format!("{h}:"));
                let label = target.as_deref().unwrap_or(goal(step.proof));
                match step.form {
                    "calcLine" => {
                        if let Some(before) = &step.before {
                            out.push_str(&format!("  so far {before}\n"));
                            computes_to(&mut out, 9, &step.before_computed);
                        }
                        out.push_str(&format!("  line   {label} {}\n", step.after));
                        computes_to(&mut out, 9, &step.after_computed);
                    }
                    "match" | "statement" => {
                        out.push_str(&format!("  {label} {}\n", step.after));
                        computes_to(&mut out, 2, &step.after_computed);
                    }
                    _ => {
                        let at = 9;
                        if let Some(before) = &step.before {
                            out.push_str(&format!("  before {label} {before}\n"));
                            computes_to(&mut out, at, &step.before_computed);
                        }
                        if let Some(rule) = &step.rule {
                            out.push_str(&format!("  rule   {rule}\n"));
                        }
                        out.push_str(&format!("  after  {label} {}\n", step.after));
                        computes_to(&mut out, at, &step.after_computed);
                    }
                }
            }
            // Nothing was expected: the type is the one found.
            None if !self.checked && !self.proof => {
                out.push_str(&format!("  has type {}\n", self.ty))
            }
            None => {
                out.push_str(&format!("  {} {}\n", goal(self.proof), self.ty));
                computes_to(&mut out, 2, &self.ty_computed);
                if let Some(found) = &self.found {
                    out.push_str(&format!("  has type {found}\n"));
                }
            }
        }
        out
    }
}

impl Session {
    fn probed(&self, text: &str) -> Option<Context> {
        let found = self.elab.take_probed_context()?;
        let (l1, c1) = position_at(text, found.span.start as usize);
        let (l2, c2) = position_at(text, found.span.end as usize);
        let ty = written_first(found.ty, found.ty_written);
        Some(Context {
            range: [l1, c1, l2, c2],
            ty: ty.0,
            ty_computed: ty.1,
            checked: found.checked,
            proof: found.proof,
            found: found.found,
            locals: found.locals.into_iter().map(Local::of).collect(),
            declaration: found.declaration,
            step: found.step.map(|s| Step::of(s, text)),
            steps: (found.steps.into_iter())
                .map(|s| Step::of(s, text))
                .collect(),
        })
    }

    /// The context at `(line, character)` of `text`, a file on its own
    /// named `name`, loaded into this session (a fresh one): the file is
    /// checked with a probe at the position ([`stitchwort_elab::Elaborator::
    /// probe_context`]), so it costs a check of the file. None if no
    /// expression that was checked contains the position: it is in a
    /// signature, a pattern, a comment, or a declaration that doesn't parse
    /// or whose checking stopped before reaching it.
    pub fn context_at_text(
        &mut self,
        name: &str,
        text: &str,
        line: u32,
        character: u32,
    ) -> Option<Context> {
        let offset = offset_at(text, line, character) as u32;
        self.elab.enable_navigation();
        self.elab.probe_context(self.sources.next_id(), offset);
        let _ = self.load(name, text);
        self.probed(text)
    }

    /// [`Session::context_at_text`] for a file of a project, as
    /// [`Session::actions_at_project`] reads one: the project's other
    /// namespaces through the check cache, then the file's namespace with
    /// the probe, its text taken from `files` (the editor's text laid over
    /// the disk's, say).
    pub fn context_at_project(
        &mut self,
        project: &str,
        files: &dyn Files,
        path: &str,
        cache: Option<&std::path::Path>,
        line: u32,
        character: u32,
    ) -> Option<Context> {
        let (text, _) = self.probe_project(project, files, path, cache, |e, file, text| {
            e.probe_context(file, offset_at(text, line, character) as u32);
        })?;
        self.probed(&text)
    }

    /// What can be written after the `.` at byte `dot` of `text`, a file
    /// on its own named `name`, loaded into this session (a fresh one): the
    /// file is checked with a dummy name after the dot, which a probe
    /// records the members for ([`stitchwort_elab::Elaborator::
    /// probe_members`]), so it costs a check of the file. `wanted` is the
    /// part of the name typed already, which the dummy replaces. None if
    /// checking never reaches the dot.
    pub fn members_at_text(
        &mut self,
        name: &str,
        text: &str,
        dot: usize,
        wanted: usize,
    ) -> Option<Vec<ScopeName>> {
        let probed = with_dummy(text, dot, wanted);
        self.elab.enable_navigation();
        self.elab
            .probe_members(self.sources.next_id(), (dot + 1) as u32);
        let _ = self.load(name, &probed);
        self.elab.take_probed_members()
    }

    /// [`Session::members_at_text`] for a file of a project, read as
    /// [`Session::context_at_project`] reads one: `files` give its text
    /// with the dummy written in already ([`with_dummy`]).
    pub fn members_at_project(
        &mut self,
        project: &str,
        files: &dyn Files,
        path: &str,
        cache: Option<&std::path::Path>,
        dot: usize,
    ) -> Option<Vec<ScopeName>> {
        let (text, namespaces) =
            self.probe_project(project, files, path, cache, |e, file, _| {
                e.probe_members(file, (dot + 1) as u32);
            })?;
        let mut found = self.elab.take_probed_members()?;
        // After a prefix of the project's namespaces (`Proj.`), those under
        // it, though the file's namespace doesn't use them and they aren't
        // loaded.
        let written = text[..dot]
            .rsplit(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\'' || c == '.'))
            .next()
            .unwrap_or_default();
        // A relative prefix (`Other.` in `Proj.Main`) means the namespace
        // beside the file's own.
        let own = text
            .lines()
            .find_map(|l| l.strip_prefix("namespace "))
            .map(str::trim)
            .unwrap_or_default();
        let beside = own.rfind('.').map_or("", |i| &own[..=i]);
        for ns in &namespaces {
            let Some(under) = (ns.strip_prefix(&format!("{written}.")))
                .or_else(|| ns.strip_prefix(&format!("{beside}{written}.")))
            else {
                continue;
            };
            let name = under.split('.').next().unwrap_or_default();
            if !written.is_empty() && !found.iter().any(|n| n.name == name) {
                found.push(ScopeName {
                    name: name.to_string(),
                    key: format!("{written}.{name}"),
                    kind: "namespace",
                    ty: None,
                    own: false,
                    import: None,
                });
            }
        }
        Some(found)
    }

    /// Turns navigation recording on and loads every library file, as the
    /// probes of a project's file need; false if the library doesn't load.
    /// A session marked ([`Session::mark`]) after this and rewound to the
    /// mark keeps the library, so the probes that follow don't do it again.
    pub fn load_libraries_for_probes(&mut self) -> bool {
        if self.elab.all_libraries_loaded() {
            return true;
        }
        self.elab.enable_navigation();
        self.elab.load_all_libraries().is_ok()
    }

    /// Loads what the namespace of the project's file `path` uses, and that
    /// namespace with the probe `probe` sets (given the file's id and
    /// text): its text, if it got that far.
    fn probe_project(
        &mut self,
        project: &str,
        files: &dyn Files,
        path: &str,
        cache: Option<&std::path::Path>,
        probe: impl FnOnce(&stitchwort_elab::Elaborator, stitchwort_syntax::FileId, &str),
    ) -> Option<(String, Vec<String>)> {
        if let Some(dir) = cache {
            self.use_check_cache(dir);
        }
        if let Some(include) = files.include_files() {
            self.include_from(include);
        }
        self.load_libraries_for_probes().then_some(())?;
        let sources = crate::project::project_sources(files, project, &mut self.sources).ok()?;
        if !sources.iter().any(|(p, _)| p == path) {
            return None;
        }
        let parsed = crate::project::parse_files(self, project, sources);
        let (file_id, text) = (parsed.iter())
            .find(|f| f.path == path)
            .map(|f| (f.id, f.text.clone()))?;
        let analysis = crate::project::analyse_parsed(&mut self.elab, project, parsed);
        let ns = (analysis.namespaces.iter())
            .find(|n| n.files.contains(&file_id))
            .map(|n| n.name.clone())?;
        // The probe goes in just before the file's namespace is checked,
        // which the file id keys.
        probe(&self.elab, file_id, &text);
        self.load_for_probe(project, &analysis, &ns).ok()?;
        Some((
            text,
            analysis.namespaces.iter().map(|n| n.name.clone()).collect(),
        ))
    }
}

impl Session {
    /// The patterns that split the variable `local` of `context` into its
    /// constructors (`MissingCases::fills` form), if its type is a data
    /// type ([`stitchwort_elab::Elaborator::constructor_patterns`], found
    /// from the elaborated type, not its printed name).
    pub fn split_patterns(&self, context: &Context, local: &str) -> Option<Vec<String>> {
        context
            .locals
            .iter()
            .rev()
            .find(|l| l.name == local)?
            .splits
            .clone()
    }

    /// The variables of `context` that can be split, each with the
    /// patterns of its type's constructors ([`Session::split_patterns`]),
    /// in scope order. A name that a later variable shadows is not offered.
    pub fn splittable(&self, context: &Context) -> Vec<(String, Vec<String>)> {
        splittable_locals(&context.locals)
    }
}

/// [`Session::splittable`] from the locals alone: a published goal's
/// context carries each variable's constructor patterns, so the splits at
/// a `?` need no session.
pub fn splittable_locals(locals: &[Local]) -> Vec<(String, Vec<String>)> {
    let mut out = Vec::new();
    for (i, local) in locals.iter().enumerate() {
        let shadowed = locals[i + 1..].iter().any(|l| l.name == local.name);
        if shadowed || !local.name.starts_with(|c: char| c.is_lowercase()) {
            continue;
        }
        if let Some(patterns) = &local.splits {
            out.push((local.name.clone(), patterns.clone()));
        }
    }
    out
}

/// The name completion writes after a `.` so that the text parses while
/// the members are found.
pub use stitchwort_elab::COMPLETION_DUMMY as DUMMY;

/// `text` with the `wanted` bytes after the `.` at byte `dot` replaced by
/// [`DUMMY`].
pub fn with_dummy(text: &str, dot: usize, wanted: usize) -> String {
    let after = (dot + 1 + wanted).min(text.len());
    format!("{}{DUMMY}{}", &text[..dot + 1], &text[after..])
}
