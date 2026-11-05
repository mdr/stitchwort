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
use crate::live::{FileAnswers, LiveRef, Place};
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
}

/// An open goal `?`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Goal {
    pub range: Range,
    /// What the hole is in: "`addZero`".
    pub owner: String,
    /// What must be shown (after `⊢`).
    pub goal: String,
    pub context: Vec<Local>,
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
            body.extend(d.notes.iter().map(|n| format!("Note: {n}")));
            Some(Goal {
                range: d.range,
                owner: d
                    .message
                    .strip_prefix("in ")
                    .unwrap_or(&d.message)
                    .to_string(),
                goal: data.target.clone(),
                context: (data.hypotheses.iter())
                    .map(|h| Local {
                        name: h.name.clone(),
                        ty: h.ty.clone(),
                        value: h.value.clone(),
                    })
                    .collect(),
                text: body.join("\n"),
            })
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
        }
        _ => {
            if let Some(ty) = &r.ty {
                text.push_str(&format!("```stitchwort\n{ty}\n```\n"));
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
    reference_at(file, place, line, character).map(|r| hover_of(&r))
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
        if file.exprs.iter().all(|(r, _)| *r != selection) {
            return None;
        }
    }
    let (range, ty) = file.expr_covering(selection)?;
    Some(Hover {
        range,
        markdown: format!("```stitchwort\n{ty}\n```"),
    })
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
    let signature = printed_signature(file, &call.head)?;
    Some(Signature {
        function: call.head,
        signature: signature.to_string(),
        implicit: call.implicit,
        given: call.given,
        parameters: completion::parameters(signature),
    })
}

/// The printed type of the function `head` (as written), from the
/// references the file last published.
fn printed_signature<'a>(file: &'a FileAnswers, head: &str) -> Option<&'a str> {
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
            let ty = printed_signature(file, &call.head)?;
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

/// Options for the quick fixes' search: the top three, within 5 s, and no
/// more candidates once `wanted` have closed the goal.
pub fn action_options(wanted: usize) -> AtOptions {
    AtOptions {
        limit: 3,
        stop_after_closing: Some(wanted),
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
    stack: usize,
    name: &str,
    text: &str,
    range: Range,
    options: &AtOptions,
    cache: Option<&std::path::Path>,
) -> Option<Vec<Action>> {
    let report = search_at_text(stack, name, text, goal_line(range), options, cache).ok()?;
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
/// and the names in scope.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Context {
    /// The expression the answer is about.
    pub range: Range,
    /// Its type: what it was checked against when `checked` (the expected
    /// type), else the type found for it.
    #[serde(rename = "type")]
    pub ty: String,
    pub checked: bool,
    /// The names in scope there, a variable before anything whose type
    /// mentions it; the same list and the same printing as a goal's.
    pub locals: Vec<Local>,
}

impl Session {
    fn probed(&self, text: &str) -> Option<Context> {
        let found = self.elab.take_probed_context()?;
        let (l1, c1) = position_at(text, found.span.start as usize);
        let (l2, c2) = position_at(text, found.span.end as usize);
        Some(Context {
            range: [l1, c1, l2, c2],
            ty: found.ty,
            checked: found.checked,
            locals: (found.locals.into_iter())
                .map(|h| Local {
                    name: h.name,
                    ty: h.ty,
                    value: h.value,
                })
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
        if let Some(dir) = cache {
            self.use_check_cache(dir);
        }
        if let Some(include) = files.include_files() {
            self.include_from(include);
        }
        self.elab.enable_navigation();
        self.elab.load_all_libraries().ok()?;
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
        let offset = offset_at(&text, line, character) as u32;
        // Namespaces that use the file's are not checked, and the others
        // only matter to the file's: the probe goes in just before the
        // file's namespace would be checked, which the file id keys.
        self.elab.probe_context(file_id, offset);
        self.load_for_goal(project, &analysis, &ns).ok()?;
        self.probed(&text)
    }
}
