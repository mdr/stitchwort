//! A trial check of edits (docs/proposals/refactoring.md §3.1): what a
//! refactoring's text edits would do to a checked project, found by
//! checking the edited text, before anyone commits to them.
//!
//! [`LiveProject::trial`] applies the edits, rewinds to the mark before the
//! first namespace they change and checks from there (the namespaces that
//! use the edited ones last, see the module `live`), then compares with the
//! state before: the diagnostics (by file, code and declaration, so those
//! already there stay allowed) and the content hash of every declaration of
//! the edited namespaces and those using them against the refactoring's
//! [`Promise`]. What
//! it finds is a list of problems, not a verdict: the caller refuses the
//! edit when there are any, or applies it anyway and leaves the few
//! problem spots for the user to fix (D3467). Then [`LiveProject::keep`]
//! keeps the checked state, so applying costs no second check, or
//! [`LiveProject::restore`] goes back to the texts before and checks them
//! again (from the check cache, when the session has one).
//!
//! Some edits can't be checked at all, because they might land in the wrong
//! place or the comparison would mean nothing: those are [`Refusal`]s, with
//! no "anyway".

use std::collections::{BTreeMap, BTreeSet};

use stitchwort_core::erase::proof_positions;
use stitchwort_core::hash::{
    ContentHash, data_hash, def_hash, proofless_data_hash, proofless_hash, type_hash,
};
use stitchwort_core::{DataId, DefId, Ev};
use stitchwort_elab::search::{constants, data_types};
use stitchwort_syntax::{Diagnostic, Severity, Span};

use super::term_diff::{self, DeclTerms, Difference};
use super::{
    LiveProject, NamespaceOutcome, OutlineItem, Place, Progress, lsp_range, syntactic_outline,
};
use crate::declhash::{DeclHash, owner};
use crate::nav::Range;
use crate::project::dependents;
use crate::rewind::Cancelled;

/// A text edit: `range` of the file at `place`, in the text as it is now,
/// becomes `new_text`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edit {
    pub place: Place,
    pub range: Range,
    pub new_text: String,
}

/// What a refactoring promises about the meaning of the project
/// (docs/proposals/refactoring.md §3.2). Only the promise renames of locals,
/// functions and theorems make exists yet; renames of data types, fields
/// and constructors, whose names are hashed, will need a variant that
/// hashes through a name map (R7).
#[derive(Clone, Debug)]
pub enum Promise {
    /// Every declaration keeps its content hash. Declarations are matched
    /// by position in their namespace, and their names through `renames`
    /// (full names, old to new; a declaration generated from a renamed one,
    /// `f.eq1` or `f.induct`, follows it).
    SameMeaning { renames: BTreeMap<String, String> },
    /// Every statement stays what it is, and the proofs may change: for
    /// edits to a theorem's proof term that keep its statement (moving a
    /// `∀` variable before the colon turns `:= Nat.addZero` into
    /// `:= n => Nat.addZero n`, another term for the same theorem). A
    /// theorem may have another content hash if its type hash (what the
    /// statement says, whatever the proof) holds. Everything else keeps its
    /// content hash: a definition whose hash moves is a problem, and so is a
    /// theorem whose statement changed. A theorem that uses another that
    /// changed only in its proof has another hash too, which is accepted on
    /// the same terms. Matched and renamed as for `SameMeaning`.
    SameStatement { renames: BTreeMap<String, String> },
    /// Only proofs change, inside definitions too: for edits to theorems'
    /// proofs that definitions embed (a structure's invariant, a
    /// `Quot.lift`'s respects-proof, a `decreasing` proof). A declaration
    /// may have another content hash if its hash without proofs
    /// (`proofless_hash`: the hash with every proof position left out,
    /// statements kept) holds, so it computes what it did and its
    /// statement says what it did, up to the proofs inside what it
    /// mentions. A theorem's hash without proofs is its statement's. The
    /// kernel still checks every declaration in full: this decides only
    /// which edits a refactoring calls safe. Matched and renamed as for
    /// `SameMeaning`.
    ProofsOnly { renames: BTreeMap<String, String> },
}

impl Promise {
    fn renames(&self) -> &BTreeMap<String, String> {
        match self {
            Promise::SameMeaning { renames }
            | Promise::SameStatement { renames }
            | Promise::ProofsOnly { renames } => renames,
        }
    }

    /// Whether `now` is what the promise allows for `was`.
    pub(crate) fn keeps(&self, was: &Decl, now: &Decl) -> bool {
        if was.hash == now.hash {
            return true;
        }
        match (self, &was.statement, &now.statement) {
            (Promise::SameStatement { .. }, Some(a), Some(b)) => {
                a.theorem && b.theorem && a.ty.is_some() && a.ty == b.ty
            }
            (Promise::ProofsOnly { .. }, _, _) => {
                was.proofless.is_some() && was.proofless == now.proofless
            }
            _ => false,
        }
    }

    pub(crate) fn compares_statements(&self) -> bool {
        matches!(
            self,
            Promise::SameStatement { .. } | Promise::ProofsOnly { .. }
        )
    }

    /// The name declaration `old` should have after the edit.
    pub(crate) fn renamed(&self, old: &str) -> String {
        let renames = self.renames();
        // The longest renamed name that `old` is or is under.
        let mut best: Option<(&String, &String)> = None;
        for (from, to) in renames {
            let under = old == from
                || old
                    .strip_prefix(from.as_str())
                    .is_some_and(|rest| rest.starts_with('.'));
            if under && best.is_none_or(|(b, _)| from.len() > b.len()) {
                best = Some((from, to));
            }
        }
        match best {
            Some((from, to)) => format!("{to}{}", &old[from.len()..]),
            None => old.to_string(),
        }
    }
}

/// Why edits can't be checked. None of these can be applied anyway: the
/// edits might land in the wrong place, or there's nothing to compare them
/// with.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// The project hasn't finished checking: the edits may miss uses in the
    /// namespaces not checked yet, and there is no "before" to compare with.
    NotChecked,
    /// The project can't be checked at all (a file without a namespace
    /// line, an import cycle).
    CantCheck,
    /// A file of the project doesn't parse: the positions the edits were
    /// made from may be from older text.
    Unparsed { path: String, range: Range },
    /// An edit is to a library file, which is never changed here.
    Library { path: String },
    /// An edit doesn't fit the file's text (a file not in the project, a
    /// range past its end, two edits overlapping).
    BadEdit { path: String, reason: &'static str },
}

/// A diagnostic the edited project has and the project before didn't.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NewDiagnostic {
    pub path: String,
    pub range: Range,
    pub severity: Severity,
    pub code: &'static str,
    pub message: String,
    /// The declaration it's in, as named in its namespace, if it's in one.
    pub declaration: Option<String>,
}

/// A declaration that still checks but means something else: its content
/// hash isn't the one the promise says. No diagnostic will ever point at
/// it, so the trial does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChangedMeaning {
    pub namespace: String,
    /// As named in its namespace, after the edit.
    pub name: String,
    /// Where it's declared in the edited text, if that is known.
    pub path: Option<String>,
    pub range: Option<Range>,
    /// Another declaration whose meaning changed that this one uses, if
    /// any: then this one may have changed only because of it. Those
    /// without one are where to look first.
    pub uses: Option<String>,
    /// The theorems whose proof changed (and whose statement held) that
    /// this declaration mentions, directly or through other such
    /// theorems, and that mention no other: a definition's hash covers the
    /// proofs it mentions, so one of these may be why it moved. By full
    /// name; a name generated from a theorem (`t.%match1`) is part of its
    /// proof.
    pub reproved: Vec<String>,
    /// Under [`Promise::ProofsOnly`]: the first place its old and new terms
    /// differ outside proof positions, when it has one.
    pub difference: Option<Difference>,
}

/// What the edits would break.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Problems {
    pub diagnostics: Vec<NewDiagnostic>,
    /// Those that use none of the others first.
    pub changed: Vec<ChangedMeaning>,
}

impl Problems {
    pub fn is_empty(&self) -> bool {
        self.diagnostics.is_empty() && self.changed.is_empty()
    }

    /// Each problem in plain words, for `doing` (`renaming `h` to `n``):
    /// "renaming `h` to `n` would change what `step` means
    /// (src/Day05.sw, line 12)".
    pub fn describe(&self, doing: &str) -> Vec<String> {
        let mut out = Vec::new();
        for d in &self.diagnostics {
            let what = match d.severity {
                Severity::Error => "an error",
                _ => "a warning",
            };
            let line = d.range[0] + 1;
            let at = match &d.declaration {
                Some(decl) => format!("in `{decl}` ({}, line {line})", d.path),
                None => format!("in {}, line {line}", d.path),
            };
            out.push(format!("{doing} would cause {what} {at}: {}", d.message));
        }
        for c in &self.changed {
            let at = match (&c.path, &c.range) {
                (Some(path), Some(range)) => format!(" ({path}, line {})", range[0] + 1),
                _ => format!(" (in `{}`)", c.namespace),
            };
            let because = match &c.uses {
                Some(other) => format!(", because it uses `{other}`"),
                None => String::new(),
            };
            let differs = match &c.difference {
                Some(d) => format!(
                    "; the first difference is at {} (`{}` → `{}`)",
                    d.at, d.old, d.new
                ),
                None => String::new(),
            };
            out.push(format!(
                "{doing} would change what `{}` means{at}{because}{differs}",
                c.name
            ));
        }
        out
    }
}

impl Refusal {
    /// The refusal in plain words, for `doing` (`renaming `h` to `n``).
    pub fn describe(&self, doing: &str) -> String {
        match self {
            Refusal::NotChecked => {
                format!("can't check {doing} yet: the project is still being checked")
            }
            Refusal::CantCheck => {
                format!("can't check {doing}: the project has errors that stop it being checked")
            }
            Refusal::Unparsed { path, range } => format!(
                "can't check {doing}: `{path}` doesn't parse (line {})",
                range[0] + 1
            ),
            Refusal::Library { path } => format!(
                "{doing} would change `{path}`, which is in the standard library and can't be changed here"
            ),
            Refusal::BadEdit { path, reason } => {
                format!("can't check {doing}: the edits don't fit `{path}` ({reason})")
            }
        }
    }
}

/// A trial that ran: its problems, and what [`LiveProject::restore`] needs
/// to undo it. Dropping it is the same as [`LiveProject::keep`].
#[derive(Debug)]
#[must_use = "keep or restore the trial"]
pub struct Trial {
    pub problems: Problems,
    /// Under [`Promise::SameStatement`]: the theorems (full names) whose
    /// proof changed and whose statement held, accepted. Empty under the
    /// other promises.
    pub proofs_changed: Vec<String>,
    /// Under [`Promise::ProofsOnly`]: the definitions and data types (full
    /// names) whose hash moved and whose hash without proofs held,
    /// accepted. Empty under the other promises.
    pub proofs_only: Vec<String>,
    /// The edited files' texts before.
    before: BTreeMap<String, String>,
}

#[derive(Debug)]
pub enum TrialOutcome {
    Refused(Vec<Refusal>),
    Checked(Trial),
}

/// A declaration's hash, by kind and position in its namespace.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Id {
    Data(usize),
    Def(usize),
}

/// A namespace's declarations as checked: (full name, hash), datas then
/// definitions, in the order they were added.
struct Hashed {
    outcome: NamespaceOutcome,
    decls: Vec<Decl>,
}

/// A declaration as the trial compares it.
pub(crate) struct Decl {
    pub(crate) name: String,
    pub(crate) hash: Option<ContentHash>,
    /// Only when the promise compares statements, and for definitions.
    pub(crate) statement: Option<Statement>,
    /// The hash without proofs, only when the promise compares statements.
    pub(crate) proofless: Option<ContentHash>,
    /// The definition's type and body, only on the "before" side of a
    /// proofs-only trial, for saying where an edit first differs.
    pub(crate) terms: Option<DeclTerms>,
}

pub(crate) struct Statement {
    pub(crate) theorem: bool,
    /// `None` while something its type mentions isn't final.
    pub(crate) ty: Option<ContentHash>,
}

/// A diagnostic as plain data: (path, range), and the rest.
struct Placed<'a> {
    path: String,
    range: Range,
    diagnostic: &'a Diagnostic,
}

impl LiveProject {
    /// Every declaration of the project as checked, with its hashes:
    /// datas then definitions, namespace by namespace in checking order.
    pub fn declaration_hashes(&self) -> Vec<DeclHash> {
        let hashed = self.hashes(|_, _| true, true, false);
        let g = &self.session.elab.ev();
        let mut out = Vec::new();
        for step in &self.steps {
            let Some(h) = hashed.get(&step.name) else {
                continue;
            };
            // Datas, then the step's definitions in order.
            let defs = (0..step.datas.len())
                .map(|_| None)
                .chain(step.defs.clone().map(Some));
            for (decl, def) in h.decls.iter().zip(defs) {
                let mut listed = DeclHash::from_decl(decl);
                if let Some(i) = def {
                    listed.uses = crate::declhash::def_uses(g, i);
                }
                out.push(listed);
            }
        }
        out
    }

    /// Where the environment is: (data types, definitions).
    pub(super) fn env_sizes(&self) -> (usize, usize) {
        let env = &self.session.elab.kernel.env;
        (env.datas().len(), env.defs().len())
    }

    /// Checks the project with `edits` applied and compares it with the
    /// project now, which must be fully checked. Unless refused, the edits
    /// stay applied and checked until [`LiveProject::restore`]. Cancelled
    /// through the session's flag, the texts are put back as they were and
    /// the project is left to check them again ([`LiveProject::step`]).
    pub fn trial(&mut self, edits: &[Edit], promise: &Promise) -> Result<TrialOutcome, Cancelled> {
        let refusals = self.refusals(edits);
        if !refusals.is_empty() {
            return Ok(TrialOutcome::Refused(refusals));
        }
        let edited = match self.edited_texts(edits) {
            Ok(edited) => edited,
            Err(refusal) => return Ok(TrialOutcome::Refused(vec![refusal])),
        };
        // What is compared: the diagnostics of every namespace, and the
        // hashes of the declarations of the namespaces with an edited file
        // and those that use them. The others keep their declarations, so
        // their hashes can't differ.
        let affected: BTreeSet<String> = {
            let analysis = self.analysis.as_ref().expect("checked");
            self.steps
                .iter()
                .filter(|s| s.files.iter().any(|(p, _)| edited.contains_key(p)))
                .flat_map(|s| dependents(analysis, &s.name))
                .collect()
        };
        // Under the proofs-only promise, keep the old terms too: the rewind
        // below forgets them, and a refusal says where they first differ.
        let terms = matches!(promise, Promise::ProofsOnly { .. });
        let hashes_before = self.hashes(
            |_, name| affected.contains(name),
            promise.compares_statements(),
            terms,
        );
        let diagnostics_before = self.diagnostic_keys(promise);

        let mut before = BTreeMap::new();
        for (path, text) in edited {
            let old = self
                .texts
                .get(&path)
                .cloned()
                .expect("an edited file is in the project");
            before.insert(path.clone(), old);
            self.set_text(&path, Some(text));
        }
        if let Err(Cancelled) = self.finish() {
            for (path, text) in before {
                self.set_text(&path, Some(text));
            }
            return Err(Cancelled);
        }
        let mut problems = Problems {
            diagnostics: self.new_diagnostics(diagnostics_before),
            changed: Vec::new(),
        };
        let mut accepted = Accepted::default();
        if self.fatal.is_empty() {
            (problems.changed, accepted) = self.changed_meaning(&hashes_before, promise);
        }
        Ok(TrialOutcome::Checked(Trial {
            problems,
            proofs_changed: accepted.theorems,
            proofs_only: accepted.others,
            before,
        }))
    }

    /// Keeps a trial's edits, as checked.
    pub fn keep(&mut self, trial: Trial) {
        drop(trial);
    }

    /// Puts back the texts from before a trial, and checks them again. The
    /// diagnostics and answers are then those from before the trial.
    /// Cancelled, the texts are back but not all checked yet: stepping the
    /// project finishes it.
    pub fn restore(&mut self, trial: Trial) -> Result<(), Cancelled> {
        for (path, text) in trial.before {
            self.set_text(&path, Some(text));
        }
        self.finish()
    }

    fn finish(&mut self) -> Result<(), Cancelled> {
        while let Progress::Checked { .. } = self.step()? {}
        Ok(())
    }

    /// Why `edits` can't be checked, if they can't.
    fn refusals(&self, edits: &[Edit]) -> Vec<Refusal> {
        if !self.fatal.is_empty() {
            return vec![Refusal::CantCheck];
        }
        if self.pending() || self.analysis.is_none() {
            return vec![Refusal::NotChecked];
        }
        let mut out = Vec::new();
        let mut library = BTreeSet::new();
        for edit in edits {
            if let Place::Library(path) = &edit.place
                && library.insert(path.clone())
            {
                out.push(Refusal::Library { path: path.clone() });
            }
        }
        for (path, parsed) in &self.parsed {
            if let Some(error) = parsed.errors.first() {
                let range = error.labels.first().map_or([0; 4], |l| {
                    lsp_range(&parsed.text, l.span.start as usize, l.span.end as usize)
                });
                out.push(Refusal::Unparsed {
                    path: path.clone(),
                    range,
                });
            }
        }
        out
    }

    /// The texts of the files `edits` change, edited.
    fn edited_texts(&self, edits: &[Edit]) -> Result<BTreeMap<String, String>, Refusal> {
        let mut by_file: BTreeMap<&str, Vec<(usize, usize, &str)>> = BTreeMap::new();
        for edit in edits {
            let Place::Program(path) = &edit.place else {
                unreachable!("refused")
            };
            let bad = |reason| Refusal::BadEdit {
                path: path.clone(),
                reason,
            };
            let text = self
                .texts
                .get(path)
                .ok_or_else(|| bad("not a file of the project"))?;
            let [l1, c1, l2, c2] = edit.range;
            let start = offset_of(text, l1, c1).ok_or_else(|| bad("a range outside the text"))?;
            let end = offset_of(text, l2, c2).ok_or_else(|| bad("a range outside the text"))?;
            if end < start {
                return Err(bad("a range that ends before it starts"));
            }
            by_file
                .entry(path)
                .or_default()
                .push((start, end, &edit.new_text));
        }
        let mut out = BTreeMap::new();
        for (path, mut edits) in by_file {
            edits.sort_by_key(|&(start, end, _)| (start, end));
            if edits.windows(2).any(|w| w[1].0 < w[0].1) {
                return Err(Refusal::BadEdit {
                    path: path.to_string(),
                    reason: "two edits overlap",
                });
            }
            let mut text = self.texts[path].clone();
            for (start, end, new) in edits.into_iter().rev() {
                text.replace_range(start..end, new);
            }
            out.insert(path.to_string(), text);
        }
        Ok(out)
    }

    /// The hashes of the declarations of the steps `wanted` picks, by
    /// namespace.
    fn hashes(
        &self,
        wanted: impl Fn(usize, &str) -> bool,
        statements: bool,
        terms: bool,
    ) -> BTreeMap<String, Hashed> {
        let g = &self.session.elab.ev();
        let _op = g.machine.budget.operation(self.session.elab.options.limits);
        let mut out = BTreeMap::new();
        for (k, step) in self.steps.iter().enumerate() {
            if !wanted(k, &step.name) {
                continue;
            }
            let mut decls = Vec::new();
            for i in step.datas.clone() {
                let hash = data_hash(g, DataId(i)).ok().flatten();
                let proofless = statements
                    .then(|| proofless_data_hash(g, DataId(i)).ok().flatten())
                    .flatten();
                decls.push(Decl {
                    name: g.env.datas()[i].path().to_string(),
                    hash,
                    statement: None,
                    proofless,
                    terms: None,
                });
            }
            for i in step.defs.clone() {
                let hash = def_hash(g, DefId(i)).ok().flatten();
                let statement = statements.then(|| Statement {
                    theorem: g.env.defs()[i].theorem(),
                    ty: type_hash(g, DefId(i)).ok().flatten(),
                });
                let proofless = statements
                    .then(|| proofless_hash(g, DefId(i)).ok().flatten())
                    .flatten();
                let terms = terms.then(|| {
                    let def = &g.env.defs()[i];
                    DeclTerms {
                        ty: std::rc::Rc::new(def.ty().clone()),
                        body: def.body().cloned(),
                        proof_result: proof_positions(g, DefId(i))
                            .is_some_and(|positions| positions.result),
                        names: term_diff::ref_names(
                            g,
                            def.ty(),
                            def.body().map(|body| body.as_ref()),
                        ),
                    }
                });
                decls.push(Decl {
                    name: g.env.defs()[i].path().to_string(),
                    hash,
                    statement,
                    proofless,
                    terms,
                });
            }
            out.insert(
                step.name.clone(),
                Hashed {
                    outcome: step.outcome,
                    decls,
                },
            );
        }
        out
    }

    /// Every diagnostic of the project now, with where it is.
    fn placed_diagnostics(&self) -> Vec<Placed<'_>> {
        let all: Box<dyn Iterator<Item = &Diagnostic>> = if self.fatal.is_empty() {
            Box::new(self.steps.iter().flat_map(|s| &s.diagnostics))
        } else {
            Box::new(self.fatal.iter())
        };
        all.map(|d| {
            let (path, range) = match d.labels.first() {
                Some(label) => self.locate(label.span),
                None => ("stitchwort.yaml".to_string(), [0; 4]),
            };
            Placed {
                path,
                range,
                diagnostic: d,
            }
        })
        .collect()
    }

    /// The file (path within the project) and range of `span` of the
    /// session.
    fn locate(&self, span: Span) -> (String, Range) {
        let file = self.session.sources.get(span.file);
        let root = format!("{}/", self.project);
        let path = file.name.strip_prefix(&root).unwrap_or(&file.name);
        let range = lsp_range(&file.text, span.start as usize, span.end as usize);
        (path.to_string(), range)
    }

    /// The declaration of the file at `path` that `range` is in, as named
    /// in its namespace: the last top-level one to start before it (the
    /// outline from syntax has only the names' ranges; a definition's
    /// equations follow its signature).
    fn declaration_at(&self, outlines: &mut Outlines, path: &str, range: Range) -> Option<String> {
        let (namespace, items) = outlines.of(self, path)?;
        let start = |r: Range| (r[0], r[1]);
        items
            .iter()
            .filter(|item| item.parent.is_none() && start(item.full_range) <= start(range))
            .max_by_key(|item| start(item.full_range))
            .map(|item| short(namespace, &item.name))
    }

    /// The diagnostics now, each as (path, code, declaration after the
    /// promise's renames), with how many there are of each.
    fn diagnostic_keys(
        &self,
        promise: &Promise,
    ) -> BTreeMap<(String, &'static str, Option<String>), usize> {
        let mut outlines = Outlines::default();
        let mut keys = BTreeMap::new();
        for placed in self.placed_diagnostics() {
            let decl = self
                .declaration_at(&mut outlines, &placed.path, placed.range)
                .map(|short_name| {
                    let namespace = outlines.namespace(&placed.path).unwrap_or_default();
                    short(&namespace, &promise.renamed(&full(&namespace, &short_name)))
                });
            *keys
                .entry((placed.path, placed.diagnostic.code, decl))
                .or_insert(0) += 1;
        }
        keys
    }

    /// The diagnostics now that aren't among `before` (by file, code and
    /// declaration, counting each).
    fn new_diagnostics(
        &self,
        mut before: BTreeMap<(String, &'static str, Option<String>), usize>,
    ) -> Vec<NewDiagnostic> {
        let mut outlines = Outlines::default();
        let mut out = Vec::new();
        for placed in self.placed_diagnostics() {
            let d = placed.diagnostic;
            if d.code == "E-USES-FAILED" {
                // Says only that something used has errors, and those are
                // listed themselves.
                continue;
            }
            let declaration = self.declaration_at(&mut outlines, &placed.path, placed.range);
            let key = (placed.path.clone(), d.code, declaration.clone());
            match before.get_mut(&key) {
                Some(n) if *n > 0 => *n -= 1,
                _ => out.push(NewDiagnostic {
                    path: placed.path,
                    range: placed.range,
                    severity: d.severity,
                    code: d.code,
                    message: d.message.clone(),
                    declaration,
                }),
            }
        }
        out
    }

    /// The declarations whose hash isn't what `promise` says, comparing the
    /// namespaces `before` has that were checked cleanly then and now. A
    /// namespace with errors now has them among the new diagnostics.
    fn changed_meaning(
        &self,
        before: &BTreeMap<String, Hashed>,
        promise: &Promise,
    ) -> (Vec<ChangedMeaning>, Accepted) {
        let now = self.hashes(
            |_, name| before.contains_key(name),
            promise.compares_statements(),
            false,
        );
        let g = &self.session.elab.ev();
        // The re-checked ids, by name: an edit that adds or removes a
        // declaration shifts the ids after it.
        let new_ids = term_diff::NewIds::of(g);
        // (namespace, full name, the declaration now, if there is one, and
        // where its terms first differ outside proofs).
        let mut changed: Vec<(String, String, Option<Id>, Option<Difference>)> = Vec::new();
        // Declarations whose hash moved and the promise allows.
        let mut accepted: Vec<String> = Vec::new();
        // Those of them that aren't theorems.
        let mut others: Vec<String> = Vec::new();
        // Every accepted declaration, generated ones included.
        let mut accepted_ids: BTreeMap<Id, String> = BTreeMap::new();
        for step in &self.steps {
            let (Some(was), Some(is)) = (before.get(&step.name), now.get(&step.name)) else {
                continue;
            };
            if was.outcome != NamespaceOutcome::Checked || is.outcome != NamespaceOutcome::Checked {
                continue;
            }
            let ids: Vec<Id> = step
                .datas
                .clone()
                .map(Id::Data)
                .chain(step.defs.clone().map(Id::Def))
                .collect();
            let expected: Vec<(String, &Decl)> = was
                .decls
                .iter()
                .map(|decl| (promise.renamed(&decl.name), decl))
                .collect();
            let same_names = expected.len() == is.decls.len()
                && expected.iter().zip(&is.decls).all(|(e, i)| e.0 == i.name);
            if same_names {
                for ((exp, decl), id) in expected.iter().zip(&is.decls).zip(&ids) {
                    if !promise.keeps(exp.1, decl) {
                        changed.push((
                            step.name.clone(),
                            decl.name.clone(),
                            Some(*id),
                            definition_difference(g, &new_ids, exp.1, *id),
                        ));
                    } else if exp.1.hash != decl.hash {
                        accepted.push(decl.name.clone());
                        if !is_theorem(decl) {
                            others.push(decl.name.clone());
                        }
                        accepted_ids.insert(*id, decl.name.clone());
                    }
                }
                continue;
            }
            // The declarations moved, or some appeared or went: match by
            // name, and what has no match changed.
            let was_by_name: BTreeMap<&str, &Decl> =
                expected.iter().map(|(n, d)| (n.as_str(), *d)).collect();
            let is_names: BTreeSet<&str> = is.decls.iter().map(|d| d.name.as_str()).collect();
            for (decl, id) in is.decls.iter().zip(&ids) {
                match was_by_name.get(decl.name.as_str()) {
                    Some(was) if promise.keeps(was, decl) => {
                        if was.hash != decl.hash {
                            accepted.push(decl.name.clone());
                            if !is_theorem(decl) {
                                others.push(decl.name.clone());
                            }
                            accepted_ids.insert(*id, decl.name.clone());
                        }
                    }
                    Some(was) => changed.push((
                        step.name.clone(),
                        decl.name.clone(),
                        Some(*id),
                        definition_difference(g, &new_ids, was, *id),
                    )),
                    None => changed.push((step.name.clone(), decl.name.clone(), Some(*id), None)),
                }
            }
            for (name, _) in &expected {
                if !is_names.contains(name.as_str()) {
                    changed.push((step.name.clone(), name.clone(), None, None));
                }
            }
        }
        // A declaration generated from a changed one (`f.eq1`) isn't one
        // more place to look.
        let names: BTreeSet<String> = changed.iter().map(|c| c.1.clone()).collect();
        let generated = |name: &str, owners: &BTreeSet<String>| {
            owners.iter().any(|owner| {
                name.len() > owner.len()
                    && name.starts_with(owner.as_str())
                    && name.as_bytes()[owner.len()] == b'.'
            })
        };
        let accepted_names: BTreeSet<String> = accepted.iter().cloned().collect();
        let owners: BTreeSet<String> = names.union(&accepted_names).cloned().collect();
        // A changed declaration generated from a re-proved theorem is part
        // of its proof: the cones below go through it.
        for (_, name, id, _) in &changed {
            if let Some(id) = id
                && generated(name, &accepted_names)
            {
                accepted_ids.insert(*id, name.clone());
            }
        }
        changed.retain(|(_, name, _, _)| !generated(name, &owners));
        accepted.retain(|name| !generated(name, &accepted_names));
        others.retain(|name| !generated(name, &accepted_names));
        let other_names: BTreeSet<&String> = others.iter().collect();
        accepted.retain(|name| !other_names.contains(name));
        let ids: BTreeMap<Id, &str> = changed
            .iter()
            .filter_map(|(_, name, id, _)| Some(((*id)?, name.as_str())))
            .collect();
        let mentioned = |i: usize| -> BTreeSet<Id> {
            let def = &g.env.defs()[i];
            let mut terms = vec![def.ty()];
            terms.extend(def.body().map(|b| b.as_ref()));
            terms
                .into_iter()
                .flat_map(|t| {
                    let defs = constants(t).into_iter().map(|d| Id::Def(d.0));
                    let datas = data_types(t).into_iter().map(Id::Data);
                    defs.chain(datas).collect::<Vec<_>>()
                })
                .collect()
        };
        let mut where_declared = self.declared_at();
        let mut out: Vec<ChangedMeaning> = changed
            .iter()
            .map(|(namespace, name, id, difference)| {
                let used: BTreeSet<Id> = match id {
                    Some(Id::Def(i)) => mentioned(*i),
                    _ => BTreeSet::new(),
                };
                let cone = reproved_cone(&used, &accepted_ids, &mentioned, &|i| {
                    let path = g.env.defs()[i].path();
                    path.len() > name.len()
                        && path.starts_with(name.as_str())
                        && path.as_bytes()[name.len()] == b'.'
                });
                // What it mentions, and what its cone does: a re-proved
                // theorem may have been re-proved because of another change.
                let mut reach = used.clone();
                for c in &cone {
                    if let Id::Def(i) = c {
                        reach.extend(mentioned(*i));
                    }
                }
                let uses = reach
                    .iter()
                    .filter(|u| Some(**u) != *id)
                    .filter_map(|u| ids.get(u))
                    .find(|other| !other.starts_with(&format!("{name}.")))
                    .map(|other| short(namespace, other));
                // Only where the change starts: a re-proved theorem whose
                // proof, its lifted matches included (which may call it
                // back), mentions another may have been re-proved because
                // of it.
                let path = |c: &Id| match c {
                    Id::Def(i) => g.env.defs()[*i].path().to_string(),
                    Id::Data(i) => g.env.datas()[*i].path().to_string(),
                };
                let outside: BTreeSet<String> = cone
                    .iter()
                    .filter(|c| match c {
                        Id::Def(i) => {
                            let me = path(c);
                            mentioned(*i).iter().any(|u| {
                                accepted_ids
                                    .get(u)
                                    .is_some_and(|name| owner(name) != owner(&me))
                            })
                        }
                        Id::Data(_) => false,
                    })
                    .map(|c| owner(&path(c)).to_string())
                    .collect();
                let reproved = cone
                    .iter()
                    .filter(|c| !outside.contains(owner(&path(c))))
                    .filter_map(|c| accepted_ids.get(c).cloned())
                    .collect();
                let (path, range) = match where_declared.find(name) {
                    Some((path, range)) => (Some(path), Some(range)),
                    None => (None, None),
                };
                ChangedMeaning {
                    namespace: namespace.clone(),
                    name: short(namespace, name),
                    path,
                    range,
                    uses,
                    reproved,
                    difference: difference.clone(),
                }
            })
            .collect();
        out.sort_by_key(|c| c.uses.is_some());
        (
            out,
            Accepted {
                theorems: accepted,
                others,
            },
        )
    }

    /// Where each declaration of the project's files is declared, by full
    /// name, from their syntax.
    fn declared_at(&self) -> Declarations {
        let mut by_name = BTreeMap::new();
        for (path, parsed) in &self.parsed {
            for item in syntactic_outline(parsed, None) {
                by_name.insert(item.name, (path.clone(), item.range));
            }
        }
        Declarations { by_name }
    }
}

/// The declarations whose hash moved as the promise allows: theorems whose
/// proof changed, and (under [`Promise::ProofsOnly`]) the others.
#[derive(Default)]
struct Accepted {
    theorems: Vec<String>,
    others: Vec<String>,
}

fn is_theorem(decl: &Decl) -> bool {
    decl.statement.as_ref().is_some_and(|s| s.theorem)
}

/// Where definition `id`'s old and new type or body first differ outside
/// proof positions, if `was` kept its terms (a proofs-only trial) and the
/// declaration is a definition.
fn definition_difference(
    g: &Ev,
    ids: &term_diff::NewIds,
    was: &Decl,
    id: Id,
) -> Option<Difference> {
    let Id::Def(i) = id else {
        return None;
    };
    let old = was.terms.as_ref()?;
    let def = &g.env.defs()[i];
    let new_proof = proof_positions(g, DefId(i)).is_some_and(|positions| positions.result);
    // A declaration whose result is a proof is its type alone without
    // proofs: its body is a proof, so a difference there isn't one.
    let old_body = (!old.proof_result).then_some(old.body.as_deref()).flatten();
    let new_body = (!new_proof)
        .then(|| def.body().map(|body| body.as_ref()))
        .flatten();
    term_diff::declaration(g, old, old_body, def.ty(), new_body, ids)
}

/// The accepted declarations (re-proved theorems) that `start` mentions,
/// directly or through other accepted ones, and the definitions generated
/// from the declaration `start` belongs to that lead to them (`own`: a
/// recursive definition's `decreasing` proofs).
fn reproved_cone(
    start: &BTreeSet<Id>,
    accepted: &BTreeMap<Id, String>,
    mentioned: &dyn Fn(usize) -> BTreeSet<Id>,
    own: &dyn Fn(usize) -> bool,
) -> BTreeSet<Id> {
    let follow = |u: &Id| accepted.contains_key(u) || matches!(u, Id::Def(i) if own(*i));
    let mut seen: BTreeSet<Id> = BTreeSet::new();
    let mut todo: Vec<Id> = start.iter().filter(|u| follow(u)).copied().collect();
    while let Some(id) = todo.pop() {
        if !seen.insert(id) {
            continue;
        }
        if let Id::Def(i) = id {
            todo.extend(
                mentioned(i)
                    .into_iter()
                    .filter(|u| follow(u) && !seen.contains(u)),
            );
        }
    }
    seen
}

struct Declarations {
    by_name: BTreeMap<String, (String, Range)>,
}

impl Declarations {
    /// Where `name` is declared, or the declaration it was generated from
    /// (`f` for `f.eq1`).
    fn find(&mut self, name: &str) -> Option<(String, Range)> {
        let mut name = name;
        loop {
            if let Some(found) = self.by_name.get(name) {
                return Some(found.clone());
            }
            name = &name[..name.rfind('.')?];
        }
    }
}

/// The syntactic outline of each file asked about, made once.
#[derive(Default)]
struct Outlines {
    by_path: BTreeMap<String, Option<(String, Vec<OutlineItem>)>>,
}

impl Outlines {
    fn of(&mut self, project: &LiveProject, path: &str) -> Option<(&str, &[OutlineItem])> {
        let entry = self.by_path.entry(path.to_string()).or_insert_with(|| {
            let parsed = project.parsed.get(path)?;
            let namespace = parsed.module.namespace.as_ref()?.path.text.clone();
            Some((namespace, syntactic_outline(parsed, None)))
        });
        entry
            .as_ref()
            .map(|(n, items)| (n.as_str(), items.as_slice()))
    }

    fn namespace(&self, path: &str) -> Option<String> {
        self.by_path.get(path)?.as_ref().map(|(n, _)| n.clone())
    }
}

/// `name` as named in `namespace`.
fn short(namespace: &str, name: &str) -> String {
    name.strip_prefix(namespace)
        .and_then(|n| n.strip_prefix('.'))
        .unwrap_or(name)
        .to_string()
}

/// `name`, named in `namespace`, in full.
fn full(namespace: &str, name: &str) -> String {
    if namespace.is_empty() {
        name.to_string()
    } else {
        format!("{namespace}.{name}")
    }
}

/// The byte offset of a position (UTF-16 columns) in `text`, if it is in
/// it: an edit at a position past a line's end or the text's is from some
/// other text.
fn offset_of(text: &str, line: u32, character: u32) -> Option<usize> {
    let start = if line == 0 {
        0
    } else {
        text.match_indices('\n').nth(line as usize - 1)?.0 + 1
    };
    let rest = &text[start..];
    let line_text = &rest[..rest.find('\n').unwrap_or(rest.len())];
    let mut column = 0;
    for (i, c) in line_text.char_indices() {
        if column == character {
            return Some(start + i);
        }
        column += c.len_utf16() as u32;
    }
    (column == character).then_some(start + line_text.len())
}
