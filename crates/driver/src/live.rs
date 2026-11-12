//! A project, or a file on its own, kept checked in memory while its text
//! changes: the language server's engine (docs/proposals/language-server.md
//! §4.1, level 1).
//!
//! A [`LiveProject`] checks the project's namespaces one at a time
//! ([`LiveProject::step`]), marking the session before each. When a file's
//! text changes, it rewinds to the mark before the first namespace whose
//! files changed. The session's rewind is a stack, so every namespace
//! checked after that mark goes with it; those that neither changed nor
//! use what did are checked again first (replayed from the check cache,
//! when the session has one), then the edited namespaces, then what uses
//! them. So the edited namespace and its dependants end up the last steps,
//! and the next edit to them rewinds no further. The caller decides
//! when to stop between steps, and takes what to show
//! ([`LiveProject::answers`]) whenever it likes: diagnostics and navigation,
//! as plain data with LSP positions.
//!
//! Nothing here reads files or starts threads (D498): texts come in, and
//! answers go out.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::rc::Rc;

pub use stitchwort_elab::ScopeName;
use stitchwort_elab::project::{IncludeFiles, NamespaceSyntax, SourceUnit};
use stitchwort_syntax::{
    Diagnostic, GoalData, MissingCases, Severity, SourceMap, SuggestedImport,
    parse_module_recovering, parse_namespace_line,
};

use crate::driver::Session;
use crate::nav::{Index, Range, RefTarget, index_data, index_data_of};
use crate::project::{
    Analysis, Namespace, NamespaceOutcome, NamespaceSources, ParsedFile, analyse, analyse_parsed,
    canonical_order, closure, cycle_diagnostic, dependents, namespace_keys,
};
use crate::rewind::{Cancelled, Mark};

pub(crate) mod term_diff;
pub(crate) mod trial;
pub use term_diff::Difference;
pub use trial::{
    ChangedMeaning, Edit, NewDiagnostic, Problems, Promise, Refusal, Trial, TrialOutcome,
};

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
    /// The type with an outermost `Not`, if it has one, written as
    /// `p → Void` (`NavRef::unfolded`), for hover.
    pub unfolded: Option<String>,
    /// For a function, its parameters with their names
    /// (`(low: Nat) -> [n: Nat] -> Nat`).
    pub signature: Option<String>,
    /// For a function: its header after its name, as its declaration
    /// writes it (`(what: Text): {Parse} Char`), for hover.
    pub header: Option<String>,
    /// The declaration's doc (docs/proposals/documentation.md §4), for hover.
    pub doc: Option<String>,
    /// For a definition: its generated equations, for hover.
    pub equations: Option<String>,
    /// For the head of a call that left defaulted parameters out: the
    /// defaults it used, "`step` left out: its default `1`".
    pub defaults: Option<String>,
    /// What a rename of the target edits: the last component of the written
    /// name (`map` in `List.map`; `range` covers the whole name).
    pub name_range: Range,
    /// The text written here is not the target's name (a use of an import's
    /// alias, or an operator's symbol): a rename of the target leaves it.
    pub alias: bool,
    /// A punned record field `{ name }`: this and another reference (the
    /// field, the variable) have one range. A rename edits it to
    /// `{ label = name }` (the field) or `{ name = who }` (the variable).
    pub pun: bool,
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

/// A top-level declaration of a namespace, as `LiveProject::declared` has it.
struct Declared {
    namespace: String,
    kind: &'static str,
    ty: Option<String>,
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
    /// For a goal: its hypotheses and target, each printed alone.
    pub goal: Option<GoalData>,
    /// For an unknown name an import brings in: the import to add.
    pub import: Option<SuggestedImport>,
    /// For a non-exhaustive `match`: the arms it lacks.
    pub missing: Option<MissingCases>,
}

/// Everything known about one file.
#[derive(Clone, Debug, Default)]
pub struct FileAnswers {
    /// Sorted by position.
    pub refs: Vec<LiveRef>,
    /// The type of each expression, sorted by start, then longest first
    /// (empty unless the session records them), and that type with an
    /// outermost `Not` written as `p → Void`, when it has one.
    pub exprs: Vec<(Range, String, Option<String>)>,
    pub outline: Vec<OutlineItem>,
    pub diagnostics: Vec<LiveDiagnostic>,
    /// The names the file can write unqualified, its own first (empty
    /// for a file whose namespace was last checked as a dependency, not
    /// as the file being edited).
    pub names: Vec<ScopeName>,
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
    pub fn expr_covering(&self, range: Range) -> Option<(Range, &str, Option<&str>)> {
        self.exprs
            .iter()
            .filter(|(r, _, _)| contains(*r, range))
            .min_by_key(|(r, _, _)| innermost_first(*r))
            .map(|(r, ty, unfolded)| (*r, ty.as_str(), unfolded.as_deref()))
    }

    /// The ranges of the expressions containing `range`, smallest first,
    /// each once: what Expand Selection steps through.
    pub fn expr_chain(&self, range: Range) -> Vec<Range> {
        let mut chain: Vec<Range> = self
            .exprs
            .iter()
            .map(|(r, _, _)| *r)
            .filter(|r| contains(*r, range))
            .collect();
        // Nested ranges: the later the start, then the earlier the end,
        // the smaller.
        chain.sort_by_key(|r| innermost_first(*r));
        chain.dedup();
        chain
    }

    /// A local variable's name and type, as a reference at its binder in the
    /// file `place`, for a hover there (a binder is only a reference in the
    /// index when something uses it). The binder is the one whose range
    /// satisfies `at`.
    fn binder_where(&self, place: &Place, at: impl Fn(Range) -> bool) -> Option<LiveRef> {
        // The uses know the type; the binder's own reference may not.
        self.refs
            .iter()
            .filter(|r| r.kind == "local" && r.target.place == *place && at(r.target.range))
            .max_by_key(|r| r.ty.is_some())
            .map(|r| LiveRef {
                range: r.target.range,
                ..r.clone()
            })
    }

    /// The local variable whose binder, in the file `place`, contains the
    /// position.
    pub fn binder_at(&self, place: &Place, line: u32, character: u32) -> Option<LiveRef> {
        self.binder_where(place, |r| {
            (r[0], r[1]) <= (line, character) && (line, character) < (r[2], r[3])
        })
    }

    /// The local variable whose binder, in the file `place`, is exactly
    /// `range`.
    pub fn binder_exactly(&self, place: &Place, range: Range) -> Option<LiveRef> {
        self.binder_where(place, |r| r == range)
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
                    // Of two references to the same name, the local one: a punned
                    // field `{ x }` is a field and a use of the local `x`.
                    r.kind != "local",
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
    for (file, range, ty, unfolded) in &index.exprs {
        let at = place(*file);
        if keep(&at) {
            out.entry(at)
                .or_default()
                .exprs
                .push((*range, ty.clone(), unfolded.clone()));
        }
    }
    for r in &index.refs {
        let at = place(r.file);
        if !keep(&at) {
            continue;
        }
        let mut signature = None;
        let mut header = None;
        let mut doc = None;
        let mut equations = None;
        let (target, name, kind, ty, unfolded) = match &r.target {
            RefTarget::Symbol(s) => {
                let s = &index.symbols[*s];
                signature = s.signature.clone();
                header = s.header.clone();
                equations = s.equations.clone();
                doc = s.doc.as_ref().map(|d| d.text.clone());
                let target = Loc {
                    place: place(s.file),
                    range: s.range,
                };
                (
                    target,
                    s.name.clone(),
                    s.kind,
                    r.ty.clone().or(s.ty.clone()),
                    r.unfolded.clone().or(s.unfolded.clone()),
                )
            }
            RefTarget::Binder { name, file, range } => {
                let target = Loc {
                    place: place(*file),
                    range: *range,
                };
                (
                    target,
                    name.clone(),
                    "local",
                    r.ty.clone(),
                    r.unfolded.clone(),
                )
            }
        };
        out.entry(at).or_default().refs.push(LiveRef {
            range: r.range,
            target,
            name,
            kind,
            ty,
            unfolded,
            signature,
            header,
            doc,
            equations,
            defaults: r.defaults.clone(),
            name_range: r.name_range,
            alias: r.alias,
            pun: r.pun,
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
            goal: d.goal.clone(),
            import: d.import.clone(),
            missing: d.missing.clone(),
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
    /// The data types and definitions it added to the kernel's environment,
    /// by index, in the order they were added.
    datas: std::ops::Range<usize>,
    defs: std::ops::Range<usize>,
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
    /// Files the editor wants checked and published next to the focus's
    /// ([`LiveProject::set_also`]).
    also: Vec<String>,
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
    /// The top-level declarations of every namespace, by name, each with
    /// its namespace, kind and written signature: what
    /// `importable_from_project` filters for each file. Made from the
    /// syntax on the first answers after the files are read again.
    declared: Option<BTreeMap<String, Vec<Declared>>>,
    /// The names in scope in each file of the namespaces checked as the
    /// focus's, by path: what the session knows only while it is still in
    /// that namespace.
    names: BTreeMap<String, Vec<ScopeName>>,
}

impl LiveProject {
    /// A project called `project` (for display), in `session` (made with
    /// navigation on; the caller sets up its check cache and `include`).
    /// `files` are (path within the project, text). Nothing is checked
    /// until [`LiveProject::step`].
    pub fn new(
        session: Session,
        project: &str,
        config: Option<String>,
        files: BTreeMap<String, String>,
    ) -> Self {
        Self::new_except(session, project, config, files, &BTreeSet::new())
    }

    /// [`LiveProject::new`], leaving the library files `skip` (paths under
    /// `std/`) and those that need them to load when a namespace needs
    /// them: those that don't check under the session's limits (a
    /// [`LibraryBundle`](crate::check_cache::LibraryBundle)'s `left_out`),
    /// which would only spend the first check's time failing.
    pub fn new_except(
        mut session: Session,
        project: &str,
        config: Option<String>,
        files: BTreeMap<String, String>,
        skip: &BTreeSet<String>,
    ) -> Self {
        // Every library file now, before the first mark, so that rewinding
        // never unloads one: loaded on demand, a library file a namespace
        // uses would be loaded again (from the check cache, but running the
        // kernel) each time the namespace is re-checked; `Mod` made
        // re-checking `Aoc.Year2025.Day01` take 140 ms instead of 30. Loading them
        // all changes nothing a check reports (`tests/std_library.rs`).
        let library = session.elab.load_libraries_except(skip);
        let base = session.mark();
        LiveProject {
            session,
            project: project.to_string(),
            config,
            texts: files,
            focus: None,
            also: Vec::new(),
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
            declared: None,
            names: BTreeMap::new(),
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

    /// The files whose namespaces are wanted along with the focus's (the
    /// files of the day an editor shows, say): each is checked as soon as
    /// what it uses has been, together with the focus and before any other
    /// namespace, and its diagnostics are published as it is. Replaces the
    /// files given before.
    pub fn set_also(&mut self, paths: Vec<String>) {
        if self.also == paths {
            return;
        }
        self.also = paths;
        if self.dirty || self.plan.is_empty() {
            return;
        }
        // The plan is made: order what is left of it again.
        let Some(analysis) = self.analysis.take() else {
            return;
        };
        let rest: BTreeSet<String> = self.plan.iter().cloned().collect();
        self.plan = self.order_rest(&analysis, &rest).into();
        self.analysis = Some(analysis);
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

    /// Whether the namespaces of the focus and the `also` files, which are
    /// checked first, still have to be checked (or the files changed since).
    pub fn focus_pending(&self) -> bool {
        if self.dirty {
            return true;
        }
        let focus = self.focus_namespaces();
        self.plan.iter().any(|n| focus.contains(n))
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
        let planned = self.dirty;
        if planned {
            self.make_plan();
        }
        let Some(name) = self.plan.pop_front() else {
            // A project that can't be analysed has nothing to check; its
            // errors are the answer, and are published like any other.
            if planned && !self.fatal.is_empty() {
                return Ok(Progress::Checked {
                    focus: true,
                    done: true,
                });
            }
            return Ok(Progress::Done);
        };
        let focus = self.focus_namespaces().contains(&name);
        let mark = self.session.mark();
        let files = self.namespace_files.get(&name).cloned().unwrap_or_default();
        let project = self.project.clone();
        let analysis = self.analysis.as_ref().expect("a plan has an analysis");
        let first = self.env_sizes();
        let checked = self.session.cancellable_at(&mark, |s| {
            let ns = parse_namespace(s, &project, &name, &files);
            let found = s.check_project_namespace(analysis, &ns);
            let mut names: Vec<(String, Vec<ScopeName>)> = Vec::new();
            if focus {
                for ((path, _), id) in files.iter().zip(&ns.files) {
                    if s.elab.use_file_scope(*id) {
                        names.push((path.clone(), s.elab.names_in_scope()));
                    }
                }
            }
            s.elab.leave_namespace();
            (found, names)
        });
        let (diagnostics, outcome) = match checked {
            Ok((found, names)) => {
                self.names.extend(names);
                found
            }
            Err(Cancelled) => {
                // Rewound to it, and checked again from a new one.
                self.session.release(mark);
                self.plan.push_front(name);
                return Err(Cancelled);
            }
        };
        let last = self.env_sizes();
        self.steps.push(Step {
            name,
            mark,
            files,
            outcome,
            diagnostics,
            datas: first.0..last.0,
            defs: first.1..last.1,
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
        let library = !self.library_answered;
        let index = index_data_of(&self.session, &root, &diagnostics, library);
        self.library_answered = true;
        let mut answers = answers_from(&index, &wanted, "stitchwort.yaml");
        self.declared_names();
        for (place, file) in answers.iter_mut() {
            if let Place::Program(path) = place
                && let Some(names) = self.names.get(path)
            {
                file.names = names.clone();
                let others = self.importable_from_project(path, names);
                file.names.extend(others);
            }
        }
        if !library {
            // The index left out the library files' references, bar a few
            // that remain (some 300 of Set.sw's 640, SW-1110); published,
            // those would replace the full answers given before, and
            // navigation inside a library document would stop working.
            answers.retain(|place, _| !matches!(place, Place::Library(_)));
        }
        answers
    }

    /// The declarations of the project's other namespaces that the file at
    /// `path` (whose names in scope are `names`) could import: each with
    /// the import that brings it, and no type (the namespace may not be
    /// checked). Left out: names already in scope, names two namespaces
    /// declare (which import would it be?), and any namespace that uses the
    /// file's own, directly or not: importing it would make a cycle.
    fn importable_from_project(&self, path: &str, names: &[ScopeName]) -> Vec<ScopeName> {
        let Some(analysis) = &self.analysis else {
            return Vec::new();
        };
        let Some(own) = (self.namespace_files.iter())
            .find(|(_, files)| files.iter().any(|(p, _)| p == path))
            .map(|(name, _)| name)
        else {
            return Vec::new();
        };
        let Some(declared) = &self.declared else {
            return Vec::new();
        };
        let cyclic: BTreeSet<String> = dependents(analysis, own).into_iter().collect();
        let visible: BTreeSet<&str> = names.iter().map(|n| n.name.as_str()).collect();
        declared
            .iter()
            .filter(|(name, _)| !visible.contains(name.as_str()))
            .filter_map(|(name, found)| {
                let mut usable = found.iter().filter(|d| !cyclic.contains(&d.namespace));
                match (usable.next(), usable.next()) {
                    (Some(d), None) => Some(ScopeName {
                        key: format!("{}.{name}", d.namespace),
                        import: Some((d.namespace.clone(), name.clone())),
                        name: name.clone(),
                        kind: d.kind,
                        ty: d.ty.clone(),
                        own: false,
                    }),
                    _ => None,
                }
            })
            .collect()
    }

    /// Makes `declared`, if the files were read again since it was.
    fn declared_names(&mut self) {
        if self.declared.is_some() {
            return;
        }
        let mut declared: BTreeMap<String, Vec<Declared>> = BTreeMap::new();
        for parsed in self.parsed.values() {
            let Some(namespace) = &parsed.module.namespace else {
                continue;
            };
            let namespace = namespace.path.text.as_str();
            for item in syntactic_outline(parsed, None) {
                let Some(name) = item
                    .name
                    .strip_prefix(namespace)
                    .and_then(|n| n.strip_prefix('.'))
                else {
                    continue;
                };
                if item.parent.is_none() && item.kind != "test" && !name.contains('.') {
                    declared
                        .entry(name.to_string())
                        .or_default()
                        .push(Declared {
                            namespace: namespace.to_string(),
                            kind: item.kind,
                            ty: item.ty,
                        });
                }
            }
        }
        self.declared = Some(declared);
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
                .map(|(path, file)| (path.clone(), syntactic_outline(file, None)))
                .collect(),
        )
    }

    /// The namespaces of the file being edited and of the `also` files.
    fn focus_namespaces(&self) -> BTreeSet<String> {
        let wanted: BTreeSet<&str> = self
            .focus
            .iter()
            .chain(&self.also)
            .map(String::as_str)
            .collect();
        self.namespace_files
            .iter()
            .filter(|(_, files)| files.iter().any(|(p, _)| wanted.contains(p.as_str())))
            .map(|(name, _)| name.clone())
            .collect()
    }

    /// The order to check `rest` in: the focus namespaces and what they use,
    /// then the others, each in canonical order.
    fn order_rest(&self, analysis: &Analysis, rest: &BTreeSet<String>) -> Vec<String> {
        let ordered = |among: &BTreeSet<String>| {
            canonical_order(analysis, among).expect("a part of an acyclic project is acyclic")
        };
        let focus: BTreeSet<String> = self
            .focus_namespaces()
            .into_iter()
            .filter(|f| rest.contains(f))
            .collect();
        if focus.is_empty() {
            return ordered(rest);
        }
        let needs: BTreeSet<String> = closure(analysis, &focus.iter().cloned().collect::<Vec<_>>())
            .into_iter()
            .filter(|n| !focus.contains(n) && rest.contains(n))
            .collect();
        let after: BTreeSet<String> = rest
            .iter()
            .filter(|n| !focus.contains(*n) && !needs.contains(*n))
            .cloned()
            .collect();
        // One order for both: a namespace that is only needed can itself
        // use a focus namespace.
        let mut plan = ordered(&needs.union(&focus).cloned().collect());
        plan.extend(ordered(&after));
        plan
    }

    /// Rewinds to the steps that are still good, and plans the rest.
    fn make_plan(&mut self) {
        self.dirty = false;
        self.parse_scratch();
        self.outlines_stale = true;
        self.declared = None;
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
        // What the rewind throws away, and of it what the edit changed.
        // The rewind is a stack, so the steps after the first changed one
        // go with it, whether or not they use it; those that don't (the
        // settled ones) are checked again after the edited namespace.
        let changed: Vec<String> = if same_names && self.fatal.is_empty() {
            (self.steps.iter())
                .filter(|s| namespace_files.get(&s.name) != Some(&s.files))
                .map(|s| s.name.clone())
                .collect()
        } else {
            Vec::new()
        };
        let mut settled: BTreeSet<String> = (self.steps.iter().skip(keep))
            .map(|s| s.name.clone())
            .filter(|n| !changed.contains(n))
            .collect();
        let old_analysis = self.analysis.take();
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
        // Settled: thrown away but not changed, and not using anything
        // changed, under the edited texts' uses or the ones before.
        let mut affected: BTreeSet<String> = BTreeSet::new();
        for name in &changed {
            affected.extend(dependents(&analysis, name));
            if let Some(old) = &old_analysis {
                affected.extend(dependents(old, name));
            }
        }
        settled.retain(|n| rest.contains(n) && !affected.contains(n));
        // A settled namespace must not use one that isn't (one never
        // checked, say): the order below puts it first.
        while let Some(bad) = settled
            .iter()
            .find(|n| {
                analysis.namespace(n).is_some_and(|ns| {
                    ns.edges
                        .iter()
                        .any(|e| rest.contains(&e.target) && !settled.contains(&e.target))
                })
            })
            .cloned()
        {
            settled.remove(&bad);
        }
        // What the edit changed is checked first, with what it uses, so
        // that its diagnostics come at once; the settled steps (checked
        // again from the cache, or in full without one: minutes, for a
        // large project) follow. None of them uses the first part, as
        // `settled` was made above.
        let mut front: BTreeSet<String> = rest.difference(&settled).cloned().collect();
        front.extend(
            self.focus_namespaces()
                .into_iter()
                .filter(|n| rest.contains(n)),
        );
        let needed: Vec<String> = front.iter().cloned().collect();
        let front: BTreeSet<String> = (closure(&analysis, &needed).into_iter())
            .filter(|n| rest.contains(n))
            .chain(front)
            .collect();
        let tail: BTreeSet<String> = settled.difference(&front).cloned().collect();
        let mut plan = self.order_rest(&analysis, &front);
        plan.extend(
            canonical_order(&analysis, &tail).expect("a part of an acyclic project is acyclic"),
        );
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
    /// after them. That mark is released, and the later ones were dropped
    /// by the rewind: the session holds a mark for each step kept and the
    /// base, so its journal holds what they need and no more.
    fn rewind_to(&mut self, keep: usize) {
        if keep < self.steps.len() {
            self.session.rewind(&self.steps[keep].mark);
            self.steps.truncate(keep + 1);
            let step = self.steps.pop().expect("the step rewound to");
            self.session.release(step.mark);
        } else if self.steps.is_empty() {
            // What a failed plan read.
            self.session.rewind(&self.base);
        }
        self.steps.truncate(keep);
        self.plan.clear();
        // The logs of failed declarations and broken tests aren't rewound
        // with the session; those of the namespaces dropped go here.
        let kept: BTreeSet<&str> = self.steps.iter().map(|s| s.name.as_str()).collect();
        (self.session.elab).retain_broken_tests(|ns| kept.contains(ns));
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
        let stack = self.session.elab.options.limits.stack;
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
        let (module, errors) = parse_module_recovering(id, text, session.elab.options.limits.stack);
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
    /// The names in scope in the file, as last checked.
    names: Vec<ScopeName>,
}

impl LiveFile {
    pub fn new(
        mut session: Session,
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
            names: Vec::new(),
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
                self.names = self.session.elab.names_in_scope();
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
        let mut answers = answers_from(&index, &wanted, &self.name);
        if let Some(file) = answers.get_mut(&Place::Program(self.name.clone())) {
            file.names = self.names.clone();
        }
        answers
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

/// What a definition's header writes after its name (`(b: Box): Nat`, or
/// just the type, `Nat`, with no parameters), on one line.
fn written_signature(
    text: &str,
    name: &stitchwort_syntax::ast::Name,
    span: stitchwort_syntax::Span,
) -> Option<String> {
    let header = text.get(name.span.end as usize..span.end as usize)?;
    let header = header.split(":=").next()?;
    let header = header.split_whitespace().collect::<Vec<_>>().join(" ");
    let header = header.strip_prefix(": ").map_or(header.as_str(), |t| t);
    (!header.is_empty()).then(|| header.to_string())
}

/// The outline of program text, read from its syntax alone, for a file
/// asked about before its first check has finished.
pub fn outline_of_text(text: &str, stack: usize) -> Vec<OutlineItem> {
    let mut sources = stitchwort_syntax::SourceMap::new();
    let id = sources.add("outline".to_string(), text.to_string());
    let (module, errors) = parse_module_recovering(id, text, stack);
    // A file on its own, without a namespace line, is the namespace `Main`.
    syntactic_outline(
        &ParsedFile {
            path: String::new(),
            display: String::new(),
            id,
            text: text.to_string(),
            module,
            errors,
        },
        Some("Main"),
    )
}

/// The outline of a parsed file, read from its syntax alone: the
/// declarations as written (not the generated ones), named as the checked
/// outline names them. It exists before the file is checked, which lets a
/// workspace search cover the namespaces the checker hasn't reached yet.
/// A file without a namespace line has none, unless `implicit_namespace`
/// names the one it gets.
fn syntactic_outline(file: &ParsedFile, implicit_namespace: Option<&str>) -> Vec<OutlineItem> {
    use stitchwort_syntax::ast::{Decl, Name};
    let namespace = match &file.module.namespace {
        Some(namespace) => namespace.path.text.as_str(),
        None => match implicit_namespace {
            Some(name) => name,
            None => return Vec::new(),
        },
    };
    let prefix = format!("{namespace}.");
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
                parent: Option<usize>,
                ty: Option<String>| {
        out.push(OutlineItem {
            name,
            kind,
            ty,
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
                let owner = item(&mut out, full, kind, name_range(name), None, None);
                for ctor in ctors {
                    if *record {
                        for binder in &ctor.fields {
                            for field in &binder.names {
                                let full = format!("{prefix}{}.{}", name.text, field.text);
                                item(
                                    &mut out,
                                    full,
                                    "field",
                                    name_range(field),
                                    Some(owner),
                                    None,
                                );
                            }
                        }
                    } else {
                        let full = format!("{prefix}{}", ctor.name.text);
                        item(
                            &mut out,
                            full,
                            "ctor",
                            name_range(&ctor.name),
                            Some(owner),
                            None,
                        );
                    }
                }
            }
            Decl::Signature {
                name,
                theorem,
                instance,
                synonym,
                span,
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
                let ty = (!*synonym)
                    .then(|| written_signature(text, name, *span))
                    .flatten();
                item(&mut out, full, kind, name_range(name), None, ty);
            }
            Decl::Ability { name, ops, .. } => {
                let full = format!("{prefix}{}", name.text);
                let owner = item(&mut out, full, "ability", name_range(name), None, None);
                for (op, _) in ops {
                    let full = format!("{prefix}{}.{}", name.text, op.text);
                    item(&mut out, full, "op", name_range(op), Some(owner), None);
                }
            }
            Decl::Test { name, span, .. } => {
                let range = lsp_range(text, span.start as usize, span.end as usize);
                item(
                    &mut out,
                    format!("{prefix}{name}"),
                    "test",
                    range,
                    None,
                    None,
                );
            }
            Decl::Equation { .. } => {}
        }
    }
    out
}
