//! A project, or a file on its own, kept checked in memory while its text
//! changes: the language server's engine (docs/proposals/language-server.md
//! §4.1, level 1).
//!
//! A [`LiveProject`] checks the project's namespaces one at a time
//! ([`LiveProject::step`]), marking the session before each. When a file's
//! text changes, it rewinds to the mark before the first namespace whose
//! files changed and checks from there on: what the edited namespace uses
//! (if it was rewound too), then the edited namespace, then the rest,
//! among them the namespaces that use it. The caller decides
//! when to stop between steps, and takes what to show
//! ([`LiveProject::answers`]) whenever it likes: diagnostics and navigation,
//! as plain data with LSP positions.
//!
//! Nothing here reads files or starts threads (D498): texts come in, and
//! answers go out.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::rc::Rc;

use stitchwort_elab::project::{IncludeFiles, NamespaceSyntax, SourceUnit};
use stitchwort_syntax::{
    Diagnostic, Severity, SourceMap, parse_module_recovering, parse_namespace_line,
};

use crate::driver::Session;
use crate::nav::{Index, Range, RefTarget, index_data, index_data_of};
use crate::project::{
    Analysis, Namespace, NamespaceOutcome, NamespaceSources, ParsedFile, analyse, analyse_parsed,
    canonical_order, closure, cycle_diagnostic, namespace_keys,
};
use crate::rewind::{Cancelled, Mark};

/// A file an answer is about.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Place {
    /// A file of the program: its path within the project, or for a file on
    /// its own, its name.
    Program(String),
    /// An embedded library file, by its path under `std/` (`List/Toolkit.sw`;
    /// `core/Data.sw` is a file of the core).
    Library(String),
}

/// A range in a file.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Loc {
    pub place: Place,
    pub range: Range,
}

/// A name written in a file, and what it refers to.
#[derive(Clone, Debug)]
pub struct LiveRef {
    pub range: Range,
    /// The declaration's name, or the local variable's binder.
    pub target: Loc,
    /// The declaration's full name, or the local's.
    pub name: String,
    /// The declaration's kind (`def`, `ctor`, ...), or `local`.
    pub kind: &'static str,
    pub ty: Option<String>,
}

/// A declaration of a file, for its outline.
#[derive(Clone, Debug)]
pub struct OutlineItem {
    /// Its full name.
    pub name: String,
    pub kind: &'static str,
    pub ty: Option<String>,
    /// Its name.
    pub range: Range,
    /// The whole declaration.
    pub full_range: Range,
    /// The item it's declared in (a constructor's type), by index.
    pub parent: Option<usize>,
}

#[derive(Clone, Debug)]
pub struct LiveDiagnostic {
    pub severity: Severity,
    pub code: &'static str,
    pub message: String,
    pub range: Range,
    /// Every label, the first (where the diagnostic is) included.
    pub labels: Vec<(Loc, String)>,
    pub notes: Vec<String>,
}

/// Everything known about one file.
#[derive(Clone, Debug, Default)]
pub struct FileAnswers {
    /// Sorted by position.
    pub refs: Vec<LiveRef>,
    /// The type of each expression, sorted by start, then longest first
    /// (empty unless the session records them).
    pub exprs: Vec<(Range, String)>,
    pub outline: Vec<OutlineItem>,
    pub diagnostics: Vec<LiveDiagnostic>,
}

/// Whether range `outer` contains range `inner`.
fn contains(outer: Range, inner: Range) -> bool {
    (outer[0], outer[1]) <= (inner[0], inner[1]) && (inner[2], inner[3]) <= (outer[2], outer[3])
}

/// A sort key putting the inner of two nested ranges first.
fn innermost_first(r: Range) -> (std::cmp::Reverse<(u32, u32)>, (u32, u32)) {
    (std::cmp::Reverse((r[0], r[1])), (r[2], r[3]))
}

impl FileAnswers {
    /// The smallest expression whose range contains `range`, with its
    /// type. Of two expressions with the same range (an application and
    /// its last step) the outer one is found first and the type is the
    /// same anyway.
    pub fn expr_covering(&self, range: Range) -> Option<(Range, &str)> {
        self.exprs
            .iter()
            .filter(|(r, _)| contains(*r, range))
            .min_by_key(|(r, _)| innermost_first(*r))
            .map(|(r, ty)| (*r, ty.as_str()))
    }

    /// The ranges of the expressions containing `range`, smallest first,
    /// each once: what Expand Selection steps through.
    pub fn expr_chain(&self, range: Range) -> Vec<Range> {
        let mut chain: Vec<Range> = self
            .exprs
            .iter()
            .map(|(r, _)| *r)
            .filter(|r| contains(*r, range))
            .collect();
        // Nested ranges: the later the start, then the earlier the end,
        // the smaller.
        chain.sort_by_key(|r| innermost_first(*r));
        chain.dedup();
        chain
    }

    /// The reference whose range contains the position: the innermost, if
    /// ranges nest. (The VS Code extension's `refAt` searched by binary
    /// search, which assumes they don't.)
    pub fn ref_at(&self, line: u32, character: u32) -> Option<&LiveRef> {
        let at = (line, character);
        // A file has thousands of references at most: a scan takes
        // microseconds.
        self.refs
            .iter()
            .filter(|r| (r.range[0], r.range[1]) <= at && at < (r.range[2], r.range[3]))
            .min_by_key(|r| {
                (
                    (r.range[2], r.range[3]),
                    std::cmp::Reverse((r.range[0], r.range[1])),
                )
            })
    }
}

/// What one step of checking did.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Progress {
    /// Everything is checked.
    Done,
    /// A namespace (or the file) was checked. `focus`: it's the namespace of
    /// the file last edited; `done`: nothing is left to check.
    Checked { focus: bool, done: bool },
}

/// The answers of a check: for each file, what to show now, replacing
/// whatever was shown for it before. Files not listed keep theirs.
pub type Answers = BTreeMap<Place, FileAnswers>;

/// Answers from `index`, for the program's files `wanted` (each listed,
/// empty if the index has nothing) and every library file the index has
/// references in. A diagnostic with no place goes on `unplaced`, at its
/// start.
pub fn answers_from(index: &Index, wanted: &BTreeSet<String>, unplaced: &str) -> Answers {
    let place = |f: usize| match &index.files[f].std {
        Some(std) => Place::Library(std.clone()),
        None => Place::Program(index.files[f].path.clone()),
    };
    let keep = |p: &Place| match p {
        Place::Library(_) => true,
        Place::Program(path) => wanted.contains(path) || path == unplaced,
    };
    let mut out: Answers = wanted
        .iter()
        .chain(std::iter::once(&unplaced.to_string()))
        .map(|p| (Place::Program(p.clone()), FileAnswers::default()))
        .collect();
    for (file, range, ty) in &index.exprs {
        let at = place(*file);
        if keep(&at) {
            out.entry(at).or_default().exprs.push((*range, ty.clone()));
        }
    }
    for r in &index.refs {
        let at = place(r.file);
        if !keep(&at) {
            continue;
        }
        let (target, name, kind, ty) = match &r.target {
            RefTarget::Symbol(s) => {
                let s = &index.symbols[*s];
                let target = Loc {
                    place: place(s.file),
                    range: s.range,
                };
                (
                    target,
                    s.name.clone(),
                    s.kind,
                    r.ty.clone().or(s.ty.clone()),
                )
            }
            RefTarget::Binder { name, file, range } => {
                let target = Loc {
                    place: place(*file),
                    range: *range,
                };
                (target, name.clone(), "local", r.ty.clone())
            }
        };
        out.entry(at).or_default().refs.push(LiveRef {
            range: r.range,
            target,
            name,
            kind,
            ty,
        });
    }
    // The outline: the program's declarations, by file.
    let mut local: BTreeMap<usize, usize> = BTreeMap::new();
    for (i, s) in index.symbols.iter().enumerate() {
        let at = place(s.file);
        let (Some(full_range), Place::Program(_)) = (s.full_range, &at) else {
            continue;
        };
        if !keep(&at) {
            continue;
        }
        let items = &mut out.entry(at).or_default().outline;
        local.insert(i, items.len());
        items.push(OutlineItem {
            name: s.name.clone(),
            kind: s.kind,
            ty: s.ty.clone(),
            range: s.range,
            full_range,
            parent: s.container,
        });
    }
    for answers in out.values_mut() {
        for item in &mut answers.outline {
            item.parent = item.parent.and_then(|c| local.get(&c).copied());
        }
    }
    for d in &index.diagnostics {
        let (at, range) = match d.at {
            Some((file, range)) => (place(file), range),
            None => (Place::Program(unplaced.to_string()), [0; 4]),
        };
        if matches!(at, Place::Library(_)) || !keep(&at) {
            continue;
        }
        let labels = d
            .labels
            .iter()
            .map(|(file, range, message)| {
                let loc = Loc {
                    place: place(*file),
                    range: *range,
                };
                (loc, message.clone())
            })
            .collect();
        out.entry(at).or_default().diagnostics.push(LiveDiagnostic {
            severity: d.severity,
            code: d.code,
            message: d.message.clone(),
            range,
            labels,
            notes: d.notes.clone(),
        });
    }
    out
}

// ---- projects -----------------------------------------------------------

/// A namespace checked, and the mark before it.
struct Step {
    name: String,
    mark: Mark,
    /// Its files as checked: (path, text), by path.
    files: Vec<(String, String)>,
    outcome: NamespaceOutcome,
    diagnostics: Vec<Diagnostic>,
}

/// A project kept checked in memory.
pub struct LiveProject {
    pub session: Session,
    /// Its name, for display (`aoc`).
    project: String,
    /// The text of `stitchwort.yaml`.
    config: Option<String>,
    /// Every source file's text now, by path within the project.
    texts: BTreeMap<String, String>,
    /// The file last edited.
    focus: Option<String>,
    /// The session before anything of the project.
    base: Mark,
    /// The namespaces checked, in the order they were.
    steps: Vec<Step>,
    /// The namespaces to check next, in order.
    plan: VecDeque<String>,
    /// Whether the texts changed since the plan was made.
    dirty: bool,
    /// What the project's files declare and use, read from their texts
    /// (with spans in `scratch`, so only the names are used).
    analysis: Option<Analysis>,
    /// Every namespace in canonical order.
    canonical: Vec<String>,
    /// Each namespace's files, by path: (path, text).
    namespace_files: BTreeMap<String, Vec<(String, String)>>,
    /// Problems that stop the whole project (a file without a namespace
    /// line, a cycle): with them, nothing is checked.
    fatal: Vec<Diagnostic>,
    /// The files as parsed to find the namespaces, kept while their text is
    /// the same; their spans are in `scratch`, not the session.
    scratch: SourceMap,
    /// Whether [`LiveProject::answers`] has given the library files' answers:
    /// they never change (the library is loaded before the first mark), so
    /// later answers leave them out, which halves their cost.
    library_answered: bool,
    parsed: BTreeMap<String, ParsedFile>,
    /// Whether the files were read again since [`LiveProject::take_outlines`].
    outlines_stale: bool,
}

impl LiveProject {
    /// A project called `project` (for display), in `session` (made with
    /// navigation on; the caller sets up its check cache and `include`).
    /// `files` are (path within the project, text). Nothing is checked
    /// until [`LiveProject::step`].
    pub fn new(
        mut session: Session,
        project: &str,
        config: Option<String>,
        files: BTreeMap<String, String>,
    ) -> Self {
        // Every library file now, before the first mark, so that rewinding
        // never unloads one: loaded on demand, a library file a namespace
        // uses would be loaded again (from the check cache, but running the
        // kernel) each time the namespace is re-checked; `Mod` made
        // re-checking `Aoc.Day01` take 140 ms instead of 30. Loading them
        // all changes nothing a check reports (`tests/std_library.rs`).
        let library = session.elab.load_all_libraries();
        let base = session.mark();
        LiveProject {
            session,
            project: project.to_string(),
            config,
            texts: files,
            focus: None,
            base,
            steps: Vec::new(),
            plan: VecDeque::new(),
            dirty: true,
            analysis: None,
            canonical: Vec::new(),
            namespace_files: BTreeMap::new(),
            fatal: library.err().unwrap_or_default(),
            scratch: SourceMap::new(),
            library_answered: false,
            parsed: BTreeMap::new(),
            outlines_stale: true,
        }
    }

    /// The text of the file at `path` is now `text`; `None` removes it.
    pub fn set_text(&mut self, path: &str, text: Option<String>) {
        let changed = match text {
            Some(text) => self.texts.insert(path.to_string(), text.clone()).as_ref() != Some(&text),
            None => self.texts.remove(path).is_some(),
        };
        self.dirty |= changed;
    }

    /// The file at `path` is the one being edited: when its namespace has to
    /// be checked, it is checked as soon as what it uses has been, before
    /// any other namespace, so that its diagnostics come first.
    pub fn set_focus(&mut self, path: &str) {
        self.focus = Some(path.to_string());
    }

    pub fn text(&self, path: &str) -> Option<&str> {
        self.texts.get(path).map(String::as_str)
    }

    pub fn paths(&self) -> impl Iterator<Item = &str> {
        self.texts.keys().map(String::as_str)
    }

    /// Whether [`LiveProject::step`] has work to do.
    pub fn pending(&self) -> bool {
        self.dirty || !self.plan.is_empty()
    }

    /// The namespace the last step checked.
    pub fn last_checked(&self) -> Option<&str> {
        self.steps.last().map(|s| s.name.as_str())
    }

    /// The namespaces in the order they're checked: those checked, then
    /// those still to check.
    pub fn order(&self) -> Vec<String> {
        let checked = self.steps.iter().map(|s| s.name.clone());
        checked.chain(self.plan.iter().cloned()).collect()
    }

    /// Checks the next namespace. Cancelled through the session's flag,
    /// the session is as before the step, and the namespace is checked again
    /// by the next.
    pub fn step(&mut self) -> Result<Progress, Cancelled> {
        if self.dirty {
            self.make_plan();
        }
        let Some(name) = self.plan.pop_front() else {
            return Ok(Progress::Done);
        };
        let focus = self.focus_namespace().as_deref() == Some(name.as_str());
        let mark = self.session.mark();
        let files = self.namespace_files.get(&name).cloned().unwrap_or_default();
        let project = self.project.clone();
        let analysis = self.analysis.as_ref().expect("a plan has an analysis");
        let canonical = &self.canonical;
        let outcomes: BTreeMap<&str, NamespaceOutcome> = self
            .steps
            .iter()
            .map(|s| (s.name.as_str(), s.outcome))
            .collect();
        let checked = self.session.cancellable_at(&mark, |s| {
            let ns = parse_namespace(s, &project, &name, &files);
            let found =
                s.check_project_namespace(analysis, canonical, &ns, &|m| outcomes.get(m).copied());
            s.elab.leave_namespace();
            found
        });
        let (diagnostics, outcome) = match checked {
            Ok(found) => found,
            Err(Cancelled) => {
                self.plan.push_front(name);
                return Err(Cancelled);
            }
        };
        self.steps.push(Step {
            name,
            mark,
            files,
            outcome,
            diagnostics,
        });
        Ok(Progress::Checked {
            focus,
            done: self.plan.is_empty(),
        })
    }

    /// What the namespaces checked so far found, for their files and the
    /// library files the session has references in (or for every file, if
    /// the project can't be checked). Diagnostics with no place go on
    /// `stitchwort.yaml`. Every file of a namespace checked is answered
    /// again, not only those just checked: a namespace checked later can
    /// add to an earlier one's answers (a use of a generated declaration
    /// such as a record's `ext` makes it a symbol, at its declaration).
    pub fn answers(&mut self) -> Answers {
        let (diagnostics, wanted): (Vec<Diagnostic>, BTreeSet<String>) = if self.fatal.is_empty() {
            let fresh = &self.steps;
            (
                fresh.iter().flat_map(|s| s.diagnostics.clone()).collect(),
                fresh
                    .iter()
                    .flat_map(|s| s.files.iter().map(|(p, _)| p.clone()))
                    .collect(),
            )
        } else {
            (self.fatal.clone(), self.texts.keys().cloned().collect())
        };
        let root = format!("{}/", self.project);
        let index = index_data_of(&self.session, &root, &diagnostics, !self.library_answered);
        self.library_answered = true;
        answers_from(&index, &wanted, "stitchwort.yaml")
    }

    /// The outline of every file of the project, read from its syntax alone
    /// (so it covers namespaces not checked yet), if the files were read
    /// again since the last call. Files without a namespace line have none.
    pub fn take_outlines(&mut self) -> Option<BTreeMap<String, Vec<OutlineItem>>> {
        if !std::mem::take(&mut self.outlines_stale) {
            return None;
        }
        Some(
            self.parsed
                .iter()
                .map(|(path, file)| (path.clone(), syntactic_outline(file)))
                .collect(),
        )
    }

    /// The namespace of the file being edited.
    fn focus_namespace(&self) -> Option<String> {
        let focus = self.focus.as_ref()?;
        self.namespace_files
            .iter()
            .find(|(_, files)| files.iter().any(|(p, _)| p == focus))
            .map(|(name, _)| name.clone())
    }

    /// Rewinds to the steps that are still good, and plans the rest.
    fn make_plan(&mut self) {
        self.dirty = false;
        self.parse_scratch();
        self.outlines_stale = true;
        let mut namespace_files: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
        for (path, parsed) in &self.parsed {
            let name = if parsed.errors.is_empty() {
                parsed.module.namespace.clone()
            } else {
                parse_namespace_line(parsed.id, &parsed.text).ok().flatten()
            };
            if let Some(name) = name {
                namespace_files
                    .entry(name.path.text)
                    .or_default()
                    .push((path.clone(), parsed.text.clone()));
            }
        }
        // The first step whose files changed; with a namespace more or
        // less, everything.
        let same_names = self.namespace_files.keys().eq(namespace_files.keys());
        let keep = if same_names && self.fatal.is_empty() {
            self.steps
                .iter()
                .position(|s| namespace_files.get(&s.name) != Some(&s.files))
                .unwrap_or(self.steps.len())
        } else {
            0
        };
        self.namespace_files = namespace_files;
        self.rewind_to(keep);
        let analysis = loop {
            let parsed: Vec<ParsedFile> = self.parsed.values().cloned().collect();
            let analysis = analyse_parsed(&mut self.session.elab, &self.project, parsed);
            if !analysis.diagnostics.is_empty() {
                return self.fail();
            }
            // The steps kept must still use only namespaces before them
            // (what a namespace uses can change when another's names do).
            let valid = self.steps.iter().enumerate().all(|(k, s)| {
                analysis.namespace(&s.name).is_some_and(|ns| {
                    ns.edges
                        .iter()
                        .all(|e| self.steps[..k].iter().any(|p| p.name == e.target))
                })
            });
            if valid {
                break analysis;
            }
            // Rewinding puts back the project's tables, so read it again.
            self.rewind_to(0);
        };
        let all: BTreeSet<String> = self.namespace_files.keys().cloned().collect();
        let Ok(canonical) = canonical_order(&analysis, &all) else {
            return self.fail();
        };
        let done: BTreeSet<&str> = self.steps.iter().map(|s| s.name.as_str()).collect();
        let rest: BTreeSet<String> = all
            .iter()
            .filter(|n| !done.contains(n.as_str()))
            .cloned()
            .collect();
        let ordered = |among: &BTreeSet<String>| {
            canonical_order(&analysis, among).expect("a part of an acyclic project is acyclic")
        };
        let plan = match self.focus_namespace().filter(|f| rest.contains(f)) {
            Some(focus) => {
                // What the edited namespace needs, then it, then the rest.
                let needs: BTreeSet<String> = closure(&analysis, std::slice::from_ref(&focus))
                    .into_iter()
                    .filter(|n| *n != focus && rest.contains(n))
                    .collect();
                let after: BTreeSet<String> = rest
                    .iter()
                    .filter(|n| **n != focus && !needs.contains(*n))
                    .cloned()
                    .collect();
                let mut plan = ordered(&needs);
                plan.push(focus);
                plan.extend(ordered(&after));
                plan
            }
            None => ordered(&rest),
        };
        if self.session.elab.uses_check_cache() {
            let namespaces: Vec<NamespaceSources> = analysis
                .namespaces
                .iter()
                .map(|ns| NamespaceSources {
                    name: ns.name.as_str(),
                    parsed: ns.parse_errors.is_empty(),
                    // By display name, as the command line's are.
                    files: self
                        .namespace_files
                        .get(&ns.name)
                        .into_iter()
                        .flatten()
                        .map(|(path, text)| (format!("{}/{path}", self.project), text.as_str()))
                        .collect(),
                })
                .collect();
            let keys = namespace_keys(self.config.as_deref(), &namespaces);
            self.session.elab.set_namespace_sources(keys);
        }
        self.fatal.clear();
        self.analysis = Some(analysis);
        self.canonical = canonical;
        self.plan = plan.into();
    }

    /// Keeps the first `keep` steps, rewinding the session to the mark
    /// after them.
    fn rewind_to(&mut self, keep: usize) {
        if keep < self.steps.len() {
            self.session.rewind(&self.steps[keep].mark);
        } else if self.steps.is_empty() {
            // What a failed plan read.
            self.session.rewind(&self.base);
        }
        self.steps.truncate(keep);
        self.plan.clear();
    }

    /// The project can't be checked: reads it again into the session (so
    /// that the diagnostics' spans are the session's) for what's wrong.
    fn fail(&mut self) {
        self.rewind_to(0);
        let files: Vec<(String, String)> = self
            .texts
            .iter()
            .map(|(p, t)| (p.clone(), t.clone()))
            .collect();
        let analysis = analyse(&mut self.session, &self.project, files);
        self.fatal = if analysis.diagnostics.is_empty() {
            let all: BTreeSet<String> =
                analysis.namespaces.iter().map(|n| n.name.clone()).collect();
            match canonical_order(&analysis, &all) {
                Ok(_) => Vec::new(),
                Err(cycles) => cycles
                    .iter()
                    .map(|c| cycle_diagnostic(&analysis, c))
                    .collect(),
            }
        } else {
            analysis.diagnostics
        };
        self.analysis = None;
    }

    /// Parses the files whose text changed into `scratch`.
    fn parse_scratch(&mut self) {
        // Edited texts pile up in the scratch source map: start it again
        // once most of it is old.
        if self.scratch.len() > 2 * self.texts.len() + 64 {
            self.scratch = SourceMap::new();
            self.parsed.clear();
        }
        self.parsed
            .retain(|path, p| self.texts.get(path) == Some(&p.text));
        let stack = self.session.elab.limits.stack;
        for (path, text) in &self.texts {
            if self.parsed.contains_key(path) {
                continue;
            }
            let display = format!("{}/{path}", self.project);
            let id = self.scratch.add(display.clone(), text.clone());
            let (module, errors) = parse_module_recovering(id, text, stack);
            self.parsed.insert(
                path.clone(),
                ParsedFile {
                    path: path.clone(),
                    display,
                    id,
                    text: text.clone(),
                    module,
                    errors,
                },
            );
        }
    }
}

/// Adds the files of namespace `name` to the session and parses them, as
/// [`analyse`] does.
fn parse_namespace(
    session: &mut Session,
    project: &str,
    name: &str,
    files: &[(String, String)],
) -> Namespace {
    let mut ids = Vec::new();
    let mut displays = Vec::new();
    let mut modules = Vec::new();
    let mut parse_errors = Vec::new();
    for (path, text) in files {
        let display = format!("{project}/{path}");
        let id = session.sources.add(display.clone(), text.clone());
        session.elab.set_include_location(id, path.clone());
        let (module, errors) = parse_module_recovering(id, text, session.elab.limits.stack);
        ids.push(id);
        displays.push(display);
        modules.push(module);
        parse_errors.extend(errors);
    }
    let edges = if modules.is_empty() {
        Vec::new()
    } else {
        let syntax = NamespaceSyntax {
            name: name.to_string(),
            files: displays
                .iter()
                .zip(&ids)
                .zip(&modules)
                .map(|((display, id), module)| SourceUnit {
                    file: Some(*id),
                    name: display,
                    module,
                })
                .collect(),
        };
        session.elab.namespace_edges(&syntax)
    };
    Namespace {
        name: name.to_string(),
        files: ids,
        modules,
        parse_errors,
        edges,
    }
}

// ---- a file on its own --------------------------------------------------

/// A file on its own (not in a project), kept checked in memory.
pub struct LiveFile {
    pub session: Session,
    /// Its name: its path, as the caller names it.
    name: String,
    text: String,
    /// Where `include` reads from, and the file's name there.
    include: Option<(Rc<dyn IncludeFiles>, String)>,
    base: Mark,
    dirty: bool,
    diagnostics: Vec<Diagnostic>,
}

impl LiveFile {
    pub fn new(
        session: Session,
        name: &str,
        text: String,
        include: Option<(Rc<dyn IncludeFiles>, String)>,
    ) -> Self {
        let base = session.mark();
        LiveFile {
            session,
            name: name.to_string(),
            text,
            include,
            base,
            dirty: true,
            diagnostics: Vec::new(),
        }
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn set_text(&mut self, text: String) {
        if text != self.text {
            self.text = text;
            self.dirty = true;
        }
    }

    pub fn pending(&self) -> bool {
        self.dirty
    }

    /// Checks the file again, if its text changed.
    pub fn step(&mut self) -> Result<Progress, Cancelled> {
        if !self.dirty {
            return Ok(Progress::Done);
        }
        self.session.rewind(&self.base);
        if let Some((files, name)) = &self.include {
            self.session.include_in_folder(files.clone(), name);
        }
        let (name, text) = (self.name.clone(), self.text.clone());
        match self
            .session
            .cancellable_at(&self.base, |s| s.load_file(&name, &text, None))
        {
            Err(Cancelled) => Err(Cancelled),
            Ok(loaded) => {
                self.diagnostics = match loaded {
                    Ok(_) => std::mem::take(&mut self.session.warnings),
                    Err(diagnostics) => diagnostics,
                };
                self.dirty = false;
                Ok(Progress::Checked {
                    focus: true,
                    done: true,
                })
            }
        }
    }

    pub fn answers(&mut self) -> Answers {
        let index = index_data(&self.session, "", &self.diagnostics);
        let wanted = BTreeSet::from([self.name.clone()]);
        answers_from(&index, &wanted, &self.name)
    }
}

// ---- outlines from syntax alone -------------------------------------------

/// `[line, UTF-16 column, line, column]` of the byte offsets `start` and
/// `end` in `text`.
fn lsp_range(text: &str, start: usize, end: usize) -> Range {
    let position = |offset: usize| {
        let mut offset = offset.min(text.len());
        while !text.is_char_boundary(offset) {
            offset -= 1;
        }
        let before = &text[..offset];
        let line = before.matches('\n').count();
        let from = before.rfind('\n').map_or(0, |i| i + 1);
        (line as u32, before[from..].encode_utf16().count() as u32)
    };
    let (l1, c1) = position(start);
    let (l2, c2) = position(end);
    [l1, c1, l2, c2]
}

/// The outline of a parsed file, read from its syntax alone: the
/// declarations as written (not the generated ones), named as the checked
/// outline names them. It exists before the file is checked, which lets a
/// workspace search cover the namespaces the checker hasn't reached yet.
fn syntactic_outline(file: &ParsedFile) -> Vec<OutlineItem> {
    use stitchwort_syntax::ast::{Decl, Name};
    let Some(namespace) = &file.module.namespace else {
        return Vec::new();
    };
    let prefix = format!("{}.", namespace.path.text);
    let text = &file.text;
    // A name's range: the last component of a dotted name, as the checked
    // outline has it.
    let name_range = |name: &Name| {
        let (start, end) = (name.span.start as usize, name.span.end as usize);
        let last = name.text.rsplit('.').next().unwrap_or_default();
        let ends_with_last = text.get(start..end).is_some_and(|w| w.ends_with(last));
        let start = if end - start > last.len() && ends_with_last {
            end - last.len()
        } else {
            start
        };
        lsp_range(text, start, end)
    };
    let mut out: Vec<OutlineItem> = Vec::new();
    let item = |out: &mut Vec<OutlineItem>,
                name: String,
                kind: &'static str,
                range: Range,
                parent: Option<usize>| {
        out.push(OutlineItem {
            name,
            kind,
            ty: None,
            range,
            full_range: range,
            parent,
        });
        out.len() - 1
    };
    for decl in &file.module.decls {
        match decl {
            Decl::Data {
                name,
                ctors,
                record,
                interface,
                ..
            } => {
                let kind = if *interface {
                    "interface"
                } else if *record {
                    "record"
                } else {
                    "data"
                };
                let full = format!("{prefix}{}", name.text);
                let owner = item(&mut out, full, kind, name_range(name), None);
                for ctor in ctors {
                    if *record {
                        for binder in &ctor.fields {
                            for field in &binder.names {
                                let full = format!("{prefix}{}.{}", name.text, field.text);
                                item(&mut out, full, "field", name_range(field), Some(owner));
                            }
                        }
                    } else {
                        let full = format!("{prefix}{}", ctor.name.text);
                        item(&mut out, full, "ctor", name_range(&ctor.name), Some(owner));
                    }
                }
            }
            Decl::Signature {
                name,
                theorem,
                instance,
                synonym,
                ..
            } => {
                let kind = if *theorem {
                    "theorem"
                } else if *instance {
                    "instance"
                } else if *synonym {
                    "data"
                } else {
                    "def"
                };
                let full = format!("{prefix}{}", name.text);
                item(&mut out, full, kind, name_range(name), None);
            }
            Decl::Ability { name, ops, .. } => {
                let full = format!("{prefix}{}", name.text);
                let owner = item(&mut out, full, "ability", name_range(name), None);
                for (op, _) in ops {
                    let full = format!("{prefix}{}.{}", name.text, op.text);
                    item(&mut out, full, "op", name_range(op), Some(owner));
                }
            }
            Decl::Test { name, span, .. } => {
                let range = lsp_range(text, span.start as usize, span.end as usize);
                item(&mut out, format!("{prefix}{name}"), "test", range, None);
            }
            Decl::Equation { .. } => {}
        }
    }
    out
}
