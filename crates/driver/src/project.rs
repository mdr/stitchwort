//! Projects of several files (docs/proposals/multi-file.md §4): which
//! namespaces the files make, what each uses, and the order to check them
//! in. Nothing here checks a declaration.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, VecDeque};
use std::path::{Path, PathBuf};

use stitchwort_elab::project::{
    Edge, NamespaceSyntax, PlanNamespace, SourceUnit, direct_names, plan_theorems,
};
use stitchwort_syntax::ast::{Decl, Module};
use stitchwort_syntax::{
    Diagnostic, FileId, Severity, SourceMap, Span, parse_module_recovering, parse_namespace_line,
};

use crate::driver::Session;

/// Which namespaces a command needs.
pub enum Target {
    Everything,
    Namespaces(Vec<String>),
    /// Each name's namespace (if there is one) and every namespace under it
    /// (`Aoc.Year2025.Day01` and `Aoc.Year2025.Day01.Tests`), and what they use.
    Subtrees(Vec<String>),
    /// Like `Namespaces`, but checking only the theorems `only` names (full
    /// names), and those they need, in the namespaces named; the namespaces
    /// are those of the theorems if none is named. What they use is checked
    /// in full. [`Loaded::theorems`] says how many theorems were checked.
    Theorems {
        namespaces: Vec<String>,
        only: Vec<String>,
    },
}

/// What the command loading a project does with it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Load {
    /// Uses what it loads (runs it, searches it, indexes it, ...): every
    /// namespace the target needs is loaded.
    Everything,
    /// Only reports the diagnostics (a plain `check`): a namespace whose
    /// cache entry fits and that nothing being checked again needs is
    /// reported from its entry without being loaded (SW-1193).
    /// `STITCHWORT_SKIP_UNNEEDED=0` turns this off.
    Diagnostics,
}

/// What loading a project checked.
pub struct Loaded {
    pub project: String,
    /// The namespaces checked, in canonical order.
    pub checked: Vec<String>,
    /// For [`Target::Theorems`]: how many of the theorems of the namespaces
    /// named were checked, and how many there are.
    pub theorems: Option<TheoremCount>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TheoremCount {
    pub checked: usize,
    pub total: usize,
}

impl Session {
    /// Checks the namespaces `target` needs (and the namespaces they use),
    /// one at a time in canonical order, each with its dependencies in scope
    /// (docs/proposals/multi-file.md §4.7, §9.1). `files` are (path within
    /// the project, text).
    pub fn load_project_sources(
        &mut self,
        project: &str,
        files: Vec<(String, String)>,
        target: &Target,
    ) -> Result<Loaded, Vec<Diagnostic>> {
        self.load_project_sources_for(project, files, target, Load::Everything)
    }

    /// [`Session::load_project_sources`], for a command that does `load`
    /// with the result.
    pub fn load_project_sources_for(
        &mut self,
        project: &str,
        files: Vec<(String, String)>,
        target: &Target,
        load: Load,
    ) -> Result<Loaded, Vec<Diagnostic>> {
        let analysis = analyse(self, project, files);
        self.load_analysis_for(project, analysis, target, load)
    }

    /// [`Session::load_project_sources`], from the files already read
    /// (`analyse`).
    pub fn load_analysis(
        &mut self,
        project: &str,
        analysis: Analysis,
        target: &Target,
    ) -> Result<Loaded, Vec<Diagnostic>> {
        self.load_analysis_for(project, analysis, target, Load::Everything)
    }

    /// [`Session::load_analysis`], for a command that does `load` with the
    /// result.
    pub fn load_analysis_for(
        &mut self,
        project: &str,
        analysis: Analysis,
        target: &Target,
        load: Load,
    ) -> Result<Loaded, Vec<Diagnostic>> {
        self.elab.clear_broken_tests();
        if !analysis.diagnostics.is_empty() {
            return Err(analysis.diagnostics);
        }
        let known: BTreeSet<String> = analysis.namespaces.iter().map(|n| n.name.clone()).collect();
        // For `Target::Theorems`: the namespaces whose unneeded theorems are
        // left out, and the theorems wanted.
        let mut pruned: Vec<String> = Vec::new();
        let needed: BTreeSet<String> = match target {
            Target::Theorems { namespaces, only } => {
                let names: Vec<String> = if namespaces.is_empty() {
                    let mut own = BTreeSet::new();
                    for full in only {
                        let owner = known
                            .iter()
                            .filter(|n| {
                                full.strip_prefix(n.as_str())
                                    .is_some_and(|r| r.starts_with('.'))
                            })
                            .max_by_key(|n| n.len());
                        match owner {
                            Some(n) => {
                                own.insert(n.clone());
                            }
                            None => {
                                return Err(vec![Diagnostic::error(
                                    "E-UNKNOWN-THEOREM",
                                    format!("there's no theorem `{full}` in the project"),
                                )]);
                            }
                        }
                    }
                    own.into_iter().collect()
                } else {
                    namespaces.clone()
                };
                let unknown: Vec<Diagnostic> = names
                    .iter()
                    .filter(|n| !known.contains(*n))
                    .map(|n| unknown_namespace(project, n, &known))
                    .collect();
                if !unknown.is_empty() {
                    return Err(unknown);
                }
                let needed = closure(&analysis, &names).into_iter().collect();
                pruned = names;
                needed
            }
            Target::Everything => known.clone(),
            Target::Namespaces(names) => {
                let unknown: Vec<Diagnostic> = names
                    .iter()
                    .filter(|n| !known.contains(*n))
                    .map(|n| unknown_namespace(project, n, &known))
                    .collect();
                if !unknown.is_empty() {
                    return Err(unknown);
                }
                closure(&analysis, names).into_iter().collect()
            }
            Target::Subtrees(names) => {
                let under = |n: &str, root: &str| {
                    n == root || n.strip_prefix(root).is_some_and(|r| r.starts_with('.'))
                };
                let unknown: Vec<Diagnostic> = names
                    .iter()
                    .filter(|r| !known.iter().any(|n| under(n, r)))
                    .map(|n| unknown_namespace(project, n, &known))
                    .collect();
                if !unknown.is_empty() {
                    return Err(unknown);
                }
                let roots: Vec<String> = known
                    .iter()
                    .filter(|n| names.iter().any(|r| under(n, r)))
                    .cloned()
                    .collect();
                closure(&analysis, &roots).into_iter().collect()
            }
        };
        let order = match canonical_order(&analysis, &needed) {
            Ok(order) => order,
            Err(cycles) => {
                return Err(cycles
                    .iter()
                    .map(|c| cycle_diagnostic(&analysis, c))
                    .collect());
            }
        };
        let mut counted = None;
        if let Target::Theorems { only, .. } = target {
            let syntax: Vec<PlanNamespace> = order
                .iter()
                .map(|name| {
                    let ns = analysis.namespace(name).expect("a namespace");
                    PlanNamespace {
                        name,
                        modules: ns.modules.iter().collect(),
                        pruned: pruned.contains(name),
                    }
                })
                .collect();
            let plan = plan_theorems(&syntax, only)
                .map_err(|message| vec![Diagnostic::error("E-UNKNOWN-THEOREM", message)])?;
            self.elab.options.skip_theorems = plan.skip;
            counted = Some(TheoremCount {
                checked: plan.checked,
                total: plan.total,
            });
        }
        if self.elab.uses_check_cache() {
            let sources = self.namespace_sources(project, &analysis);
            self.elab.set_namespace_sources(sources);
        }
        // (A namespace read from the cache is not elaborated, so its theorems
        // couldn't be counted: `check --only` loads everything.)
        let skipped = if load == Load::Diagnostics
            && counted.is_none()
            && skip_unneeded_enabled()
            && self.elab.uses_check_cache()
            && !self.elab.options.recheck_namespaces
        {
            self.plan_skips(&analysis, &order)
        } else {
            BTreeMap::new()
        };
        let diagnostics = if skipped.is_empty() {
            self.check_in_order(&analysis, &order, &skipped)
                .expect("nothing is left out")
        } else {
            let mark = self.mark();
            match self.check_in_order(&analysis, &order, &skipped) {
                Some(found) => {
                    self.release(mark);
                    for name in order.iter().filter(|n| skipped.contains_key(*n)) {
                        self.elab.count_skipped_namespace(name);
                    }
                    found
                }
                None => {
                    self.rewind(&mark);
                    self.release(mark);
                    self.elab.note_skipping_undone();
                    self.check_in_order(&analysis, &order, &BTreeMap::new())
                        .expect("nothing is left out")
                }
            }
        };
        self.elab.leave_namespace();
        self.elab.options.skip_theorems.clear();
        if diagnostics.iter().any(|d| d.severity == Severity::Error) {
            return Err(diagnostics);
        }
        self.warnings.extend(diagnostics);
        Ok(Loaded {
            project: project.to_string(),
            checked: order,
            theorems: counted,
        })
    }

    /// Checks the namespaces of `order` in that order, but reports those in
    /// `skipped` from their entries (the warnings given) without loading
    /// them; their diagnostics, in order. `None`, having stopped, if a
    /// namespace after one left out has an error or a goal: what those
    /// report can depend on every namespace loaded before (`E-UNKNOWN-FIELD`
    /// names the namespace that would add a missing function), so the
    /// caller checks them all again, loading everything.
    fn check_in_order(
        &mut self,
        analysis: &Analysis,
        order: &[String],
        skipped: &BTreeMap<String, Vec<Diagnostic>>,
    ) -> Option<Vec<Diagnostic>> {
        let mut diagnostics: Vec<Diagnostic> = Vec::new();
        let mut left_out = false;
        for name in order {
            if let Some(warnings) = skipped.get(name) {
                left_out = true;
                diagnostics.extend(warnings.iter().cloned());
                continue;
            }
            let ns = analysis.namespace(name).expect("a namespace");
            let (found, _) = self.check_project_namespace(analysis, ns);
            if left_out
                && (found.iter()).any(|d| matches!(d.severity, Severity::Error | Severity::Goal))
            {
                return None;
            }
            diagnostics.extend(found);
        }
        Some(diagnostics)
    }

    /// The namespaces of `order` (canonical, closed under dependencies) a
    /// plain `check` can report from their cache entries without loading
    /// them, with the warnings each reports. One is left out if its entry
    /// fits ([`stitchwort_elab::Elaborator::plan_namespace`]) and nothing
    /// that is loaded needs it. Loaded: the misses; the namespaces with
    /// syntax errors or doc links, whose diagnostics aren't all in the
    /// entry; the namespaces that use a miss or one with syntax errors
    /// (which may fail, and so make some of theirs wait); and everything
    /// those use.
    fn plan_skips(
        &mut self,
        analysis: &Analysis,
        order: &[String],
    ) -> BTreeMap<String, Vec<Diagnostic>> {
        let mut fits: BTreeMap<String, Vec<Diagnostic>> = BTreeMap::new();
        // Those that may not be checked the way their entry says.
        let mut uncertain: BTreeSet<&str> = BTreeSet::new();
        let mut loaded: Vec<String> = Vec::new();
        for name in order {
            let ns = analysis.namespace(name).expect("a namespace");
            let planned = self
                .elab
                .plan_namespace(name, &dependencies(analysis, name));
            let certain = ns.parse_errors.is_empty()
                && !ns
                    .edges
                    .iter()
                    .any(|e| uncertain.contains(e.target.as_str()));
            match planned {
                Some(warnings) if certain && ns.modules.iter().all(|m| m.doc_links.is_empty()) => {
                    fits.insert(name.clone(), warnings);
                }
                Some(_) if certain => loaded.push(name.clone()),
                _ => {
                    uncertain.insert(name);
                    loaded.push(name.clone());
                }
            }
        }
        for needed in closure(analysis, &loaded) {
            fits.remove(&needed);
        }
        fits
    }

    /// Checks one namespace `ns` of a project, after the namespaces it uses
    /// (`analysis` says which), whatever happened to them: a declaration
    /// that uses one of theirs that failed waits for it, and each file
    /// says so once per failed name (`E-USES-FAILED`), but the rest is
    /// checked (D3524).
    pub fn check_project_namespace(
        &mut self,
        analysis: &Analysis,
        ns: &Namespace,
    ) -> (Vec<Diagnostic>, NamespaceOutcome) {
        let name = &ns.name;
        let dependencies = dependencies(analysis, name);
        let names: Vec<String> = ns
            .files
            .iter()
            .map(|id| self.sources.get(*id).name.clone())
            .collect();
        let units: Vec<SourceUnit> = names
            .iter()
            .zip(&ns.files)
            .zip(&ns.modules)
            .map(|((name, id), module)| SourceUnit {
                file: Some(*id),
                name,
                module,
            })
            .collect();
        // The rewind test's hook: check it, rewind, check it again.
        if self.elab.options.recheck_namespaces {
            let mark = self.mark();
            let _ = self
                .elab
                .elaborate_namespace(Some(name), &units, Some(&dependencies));
            self.rewind(&mark);
            self.release(mark);
        }
        let first_new_def = self.elab.kernel.env.defs().len();
        let mut found = self
            .elab
            .elaborate_namespace(Some(name), &units, Some(&dependencies));
        self.check_exports(first_new_def, true, &mut found);
        // The declarations that parsed are checked even when others
        // didn't, so one run reports every error; the namespace still
        // counts as failed.
        let found = if ns.parse_errors.is_empty() {
            found
        } else {
            crate::driver::merge_recovered(ns.parse_errors.clone(), found)
        };
        let outcome = if found.iter().any(|d| d.severity == Severity::Error) {
            NamespaceOutcome::Failed
        } else {
            NamespaceOutcome::Checked
        };
        (found, outcome)
    }

    /// For `search --at` in a project's file (SW-915): checks every
    /// namespace of `analysis` except those that use `ns` (directly or not,
    /// so they can't be imported by it), in canonical order but with `ns`
    /// last, and stays in `ns`'s scope. Returns `ns`'s diagnostics (goals
    /// included), those of the namespaces before it, the order, and a mark
    /// taken just before `ns` was checked, to check it again with other
    /// text ([`Session::recheck_for_goal`]).
    pub fn load_for_goal(
        &mut self,
        project: &str,
        analysis: &Analysis,
        ns: &str,
    ) -> Result<GoalLoad, Vec<Diagnostic>> {
        if !analysis.diagnostics.is_empty() {
            return Err(analysis.diagnostics.clone());
        }
        let users: BTreeSet<String> = (analysis.namespaces.iter())
            .filter(|m| {
                m.name != ns
                    && closure(analysis, std::slice::from_ref(&m.name))
                        .iter()
                        .any(|n| n == ns)
            })
            .map(|m| m.name.clone())
            .collect();
        let needed: BTreeSet<String> = (analysis.namespaces.iter())
            .map(|m| m.name.clone())
            .filter(|m| !users.contains(m))
            .collect();
        self.load_namespaces_for(project, analysis, ns, &needed)
    }

    /// [`Session::load_for_goal`], checking before `ns` only what it uses,
    /// directly or not, rather than every namespace that doesn't use it:
    /// what the editor's probes need (the context at a position, the
    /// members after a dot), in the time of a few namespaces' replay from
    /// the check cache instead of the whole project's (0.6 s instead of
    /// 3.5 for AoC 2020 day 11). `ns` is checked as the language server
    /// checks the namespace being edited, after only what it uses; a
    /// namespace written out in full (`Proj.Other.`) is among those, by
    /// [`closure`]'s edges.
    pub fn load_for_probe(
        &mut self,
        project: &str,
        analysis: &Analysis,
        ns: &str,
    ) -> Result<GoalLoad, Vec<Diagnostic>> {
        if !analysis.diagnostics.is_empty() {
            return Err(analysis.diagnostics.clone());
        }
        let needed: BTreeSet<String> = closure(analysis, &[ns.to_string()]).into_iter().collect();
        self.load_namespaces_for(project, analysis, ns, &needed)
    }

    /// Checks `needed` (which has `ns`, and nothing that uses it) in
    /// canonical order but with `ns` last, and stays in `ns`'s scope.
    fn load_namespaces_for(
        &mut self,
        project: &str,
        analysis: &Analysis,
        ns: &str,
        needed: &BTreeSet<String>,
    ) -> Result<GoalLoad, Vec<Diagnostic>> {
        let mut order = canonical_order(analysis, needed).map_err(|cycles| {
            (cycles.iter())
                .map(|c| cycle_diagnostic(analysis, c))
                .collect::<Vec<_>>()
        })?;
        // Nothing among these uses `ns`, so it can go last.
        order.retain(|m| m != ns);
        order.push(ns.to_string());
        if self.elab.uses_check_cache() {
            let sources = self.namespace_sources(project, analysis);
            self.elab.set_namespace_sources(sources);
        }
        let mut before = Vec::new();
        let mut outcomes: BTreeMap<String, NamespaceOutcome> = BTreeMap::new();
        for name in &order[..order.len() - 1] {
            let namespace = analysis.namespace(name).expect("a namespace");
            let (found, outcome) = self.check_project_namespace(analysis, namespace);
            outcomes.insert(name.clone(), outcome);
            before.extend(found);
        }
        let mark = self.mark();
        let namespace = analysis.namespace(ns).expect("a namespace");
        let (diagnostics, _) = self.check_project_namespace(analysis, namespace);
        Ok(GoalLoad {
            diagnostics,
            before,
            order,
            outcomes,
            mark,
        })
    }

    /// Checks namespace `ns` again, from `load.mark`, with the file at
    /// `path` (one of its files) now `text`; `parsed` are the project's
    /// files as first read (before the mark). Stays in its scope: its
    /// diagnostics, and the file's new id.
    pub fn recheck_for_goal(
        &mut self,
        project: &str,
        parsed: &[ParsedFile],
        (path, text): (&str, &str),
        ns: &str,
        load: &GoalLoad,
    ) -> (Vec<Diagnostic>, FileId) {
        self.rewind(&load.mark);
        let changed = parse_file(self, project, path.to_string(), text.to_string());
        let id = changed.id;
        let files: Vec<ParsedFile> = (parsed.iter())
            .map(|f| {
                if f.path == path {
                    changed.clone()
                } else {
                    f.clone()
                }
            })
            .collect();
        let analysis = analyse_parsed(&mut self.elab, project, files);
        (self.recheck_analysed(project, &analysis, ns, load), id)
    }

    fn recheck_analysed(
        &mut self,
        project: &str,
        analysis: &Analysis,
        ns: &str,
        load: &GoalLoad,
    ) -> Vec<Diagnostic> {
        if !analysis.diagnostics.is_empty() {
            return analysis.diagnostics.clone();
        }
        if self.elab.uses_check_cache() {
            let sources = self.namespace_sources(project, analysis);
            self.elab.set_namespace_sources(sources);
        }
        let Some(namespace) = analysis.namespace(ns) else {
            return vec![Diagnostic::error(
                "E-SEARCH-AT",
                format!("namespace {ns} is gone"),
            )];
        };
        let outcomes = &load.outcomes;
        // A namespace it uses now that wasn't checked (it uses `ns`).
        if let Some(edge) = (namespace.edges.iter()).find(|e| !outcomes.contains_key(&e.target)) {
            return vec![
                Diagnostic::error("E-NAMESPACE-CYCLE", format!("{} uses {ns}", edge.target))
                    .with_label(edge.span, "used here"),
            ];
        }
        let (diagnostics, _) = self.check_project_namespace(analysis, namespace);
        diagnostics
    }

    /// For the check cache (docs/proposals/check-cache.md §4.2): a hash of
    /// each namespace's own sources (its name, and each file's name and
    /// text), the names of all the project's namespaces, and
    /// `stitchwort.yaml`. The elaborator adds the rest of the key.
    fn namespace_sources(
        &self,
        project: &str,
        analysis: &Analysis,
    ) -> stitchwort_core::collections::HashMap<String, stitchwort_elab::cache::Key> {
        let config_name = format!("{project}/{CONFIG}");
        let config = self
            .sources
            .iter()
            .filter(|(_, f)| f.name == config_name)
            .last()
            .map(|(_, f)| f.text.as_str());
        let namespaces: Vec<NamespaceSources> = analysis
            .namespaces
            .iter()
            .map(|ns| NamespaceSources {
                name: ns.name.as_str(),
                parsed: ns.parse_errors.is_empty(),
                files: ns
                    .files
                    .iter()
                    .map(|id| {
                        let file = self.sources.get(*id);
                        (file.name.clone(), file.text.as_str())
                    })
                    .collect(),
            })
            .collect();
        namespace_keys(config, &namespaces)
    }
}

/// What [`Session::load_for_goal`] checked.
pub struct GoalLoad {
    /// The goal's namespace's diagnostics, its goals among them.
    pub diagnostics: Vec<Diagnostic>,
    /// Those of the namespaces checked before it.
    pub before: Vec<Diagnostic>,
    /// The namespaces checked, the goal's last.
    pub order: Vec<String>,
    /// How each before the goal's went.
    pub outcomes: BTreeMap<String, NamespaceOutcome>,
    /// Just before the goal's namespace was checked.
    pub mark: crate::rewind::Mark,
}

/// How checking one namespace of a project went.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NamespaceOutcome {
    Checked,
    /// It has errors.
    Failed,
}

/// What a namespace's check cache key is made from.
pub struct NamespaceSources<'a> {
    pub name: &'a str,
    /// Whether all its files parsed.
    pub parsed: bool,
    /// Its files: display name, text.
    pub files: Vec<(String, &'a str)>,
}

/// [`Session::namespace_sources`]' hashes, from `config` (the text of
/// `stitchwort.yaml`) and each namespace's sources.
pub fn namespace_keys(
    config: Option<&str>,
    namespaces: &[NamespaceSources],
) -> stitchwort_core::collections::HashMap<String, stitchwort_elab::cache::Key> {
    let mut common = blake3::Hasher::new();
    let part = |h: &mut blake3::Hasher, bytes: &[u8]| {
        h.update(&(bytes.len() as u64).to_le_bytes());
        h.update(bytes);
    };
    part(&mut common, b"namespaces");
    let mut names: Vec<&str> = namespaces.iter().map(|n| n.name).collect();
    names.sort_unstable();
    for name in &names {
        part(&mut common, name.as_bytes());
    }
    match config {
        Some(text) => {
            part(&mut common, b"config");
            part(&mut common, text.as_bytes());
        }
        None => part(&mut common, b"no config"),
    }
    // A namespace with syntax errors is checked without its broken
    // declarations, so its result is never cached.
    namespaces
        .iter()
        .filter(|ns| ns.parsed)
        .map(|ns| {
            let mut h = common.clone();
            part(&mut h, ns.name.as_bytes());
            for (file, text) in &ns.files {
                part(&mut h, file.as_bytes());
                part(&mut h, text.as_bytes());
            }
            (ns.name.to_string(), *h.finalize().as_bytes())
        })
        .collect()
}

/// The namespace that a name of a project's `run` is in: the longest
/// namespace `P` with the name starting with `P.`.
pub fn namespace_of<'a>(analysis: &'a Analysis, name: &str) -> Option<&'a str> {
    analysis
        .namespaces
        .iter()
        .filter(|ns| name.starts_with(&format!("{}.", ns.name)))
        .max_by_key(|ns| ns.name.len())
        .map(|ns| ns.name.as_str())
}

/// `E-RUN-UNKNOWN` for a name that's in no namespace of the project.
pub fn run_unknown_namespace(project: &str, name: &str, analysis: &Analysis) -> Diagnostic {
    let mut d = Diagnostic::error(
        "E-RUN-UNKNOWN",
        format!("there's no `{name}` in project {project}/"),
    );
    if analysis.namespace(name).is_some() {
        return d.with_note(format!(
            "write the function's full name, as in `{name}.main`"
        ));
    }
    let parts: Vec<&str> = name.split('.').collect();
    let nearest = analysis
        .namespaces
        .iter()
        .filter_map(|ns| {
            let width = ns.name.split('.').count();
            if width >= parts.len() {
                return None;
            }
            let distance = stitchwort_elab::edit_distance(&parts[..width].join("."), &ns.name);
            (distance <= 2).then(|| (distance, &ns.name, parts[width..].join(".")))
        })
        .min();
    if let Some((_, namespace, rest)) = nearest {
        d = d.with_note(format!("did you mean `{namespace}.{rest}`?"));
    }
    d
}

/// `E-NAMESPACE-UNKNOWN`: a command named a namespace the project doesn't
/// have.
pub fn unknown_namespace(project: &str, name: &str, known: &BTreeSet<String>) -> Diagnostic {
    let mut d = Diagnostic::error(
        "E-NAMESPACE-UNKNOWN",
        format!("there's no namespace `{name}` in project {project}/"),
    );
    let nearest = known
        .iter()
        .map(|k| (stitchwort_elab::edit_distance(name, k), k))
        .filter(|(distance, _)| *distance <= 2)
        .min();
    if let Some((_, near)) = nearest {
        d = d.with_note(format!("did you mean `{near}`?"));
    }
    d
}

/// What reading a project's files finds.
pub struct Analysis {
    /// By name.
    pub namespaces: Vec<Namespace>,
    /// Problems that stop everything: files with no namespace, names that
    /// can't be namespaces, namespaces that clash.
    pub diagnostics: Vec<Diagnostic>,
}

pub struct Namespace {
    pub name: String,
    /// Its files, by display name.
    pub files: Vec<FileId>,
    /// Parsed, in the same order; a file with syntax errors keeps the
    /// declarations that parsed (`parse_errors` has the errors).
    pub modules: Vec<Module>,
    pub parse_errors: Vec<Diagnostic>,
    /// The namespaces it uses directly.
    pub edges: Vec<Edge>,
}

impl Analysis {
    pub fn namespace(&self, name: &str) -> Option<&Namespace> {
        self.namespaces.iter().find(|n| n.name == name)
    }
}

/// Reads the namespaces of a project's files: `files` are (path within the
/// project, text); `project` is the project's name for display (`aoc`).
pub fn analyse(session: &mut Session, project: &str, files: Vec<(String, String)>) -> Analysis {
    let parsed = parse_files(session, project, files);
    analyse_parsed(&mut session.elab, project, parsed)
}

/// Adds a project's files to the session's sources and parses them, sorted
/// by path: what [`analyse`] reads, for a caller that keeps them.
pub fn parse_files(
    session: &mut Session,
    project: &str,
    mut files: Vec<(String, String)>,
) -> Vec<ParsedFile> {
    files.sort();
    files
        .into_iter()
        .map(|(path, text)| parse_file(session, project, path, text))
        .collect()
}

/// One file of a project, added to the session's sources and parsed.
pub fn parse_file(session: &mut Session, project: &str, path: String, text: String) -> ParsedFile {
    let display = format!("{project}/{path}");
    let id = session.sources.add(display.clone(), text.clone());
    session.elab.set_include_location(id, path.clone());
    let (module, errors) = parse_module_recovering(id, &text, session.elab.options.limits.stack);
    ParsedFile {
        path,
        display,
        id,
        text,
        module,
        errors,
    }
}

/// A file of a project, parsed.
#[derive(Clone)]
pub struct ParsedFile {
    /// Its path within the project.
    pub path: String,
    /// Its name in messages (`aoc/src/Aoc/Year2025/Day01/Day01.sw`).
    pub display: String,
    pub id: FileId,
    pub text: String,
    /// The declarations that parsed, and the errors of those that didn't.
    pub module: Module,
    pub errors: Vec<Diagnostic>,
}

/// [`analyse`], for files already parsed (sorted by path): tells `elab` the
/// project's namespaces and what each declares, and finds what each uses.
pub fn analyse_parsed(
    elab: &mut stitchwort_elab::Elaborator,
    project: &str,
    files: Vec<ParsedFile>,
) -> Analysis {
    let mut diagnostics = Vec::new();
    // Each namespace's files: id, then parse result.
    struct Found {
        files: Vec<FileId>,
        displays: Vec<String>,
        modules: Vec<Module>,
        parse_errors: Vec<Diagnostic>,
    }
    let mut found: BTreeMap<String, Found> = BTreeMap::new();
    for file in files {
        let ParsedFile {
            path,
            display,
            id,
            text,
            module: parsed,
            errors,
        } = file;
        let (namespace, errors, module) = match errors {
            errors if errors.is_empty() => (parsed.namespace.clone(), errors, Some(parsed)),
            errors => {
                if let Some(not_first) = errors.iter().find(|d| d.code == "E-NAMESPACE-NOT-FIRST") {
                    diagnostics.push(not_first.clone());
                    continue;
                }
                match parse_namespace_line(id, &text) {
                    Ok(line) => (line, errors, Some(parsed)),
                    Err(d) => {
                        // The namespace line itself is the trouble.
                        diagnostics.push(d);
                        continue;
                    }
                }
            }
        };
        let Some(line) = namespace else {
            diagnostics.push(no_namespace(project, &path, &display));
            continue;
        };
        if let Err(d) = elab.check_namespace_name(&line) {
            diagnostics.push(d);
            continue;
        }
        let entry = found
            .entry(line.path.text.clone())
            .or_insert_with(|| Found {
                files: Vec::new(),
                displays: Vec::new(),
                modules: Vec::new(),
                parse_errors: Vec::new(),
            });
        entry.files.push(id);
        entry.displays.push(display);
        // A file with syntax errors keeps the declarations that parsed.
        entry.modules.extend(module);
        entry.parse_errors.extend(errors);
    }
    let mut display_names: Vec<Vec<String>> = Vec::new();
    let mut namespaces: Vec<Namespace> = found
        .into_iter()
        .map(|(name, f)| {
            display_names.push(f.displays);
            Namespace {
                name,
                files: f.files,
                modules: f.modules,
                parse_errors: f.parse_errors,
                edges: Vec::new(),
            }
        })
        .collect();
    diagnostics.extend(clashes(&namespaces));
    // A namespace that lost a declaration to a syntax error says so where
    // one of its importers names it, rather than there being no such name
    // (docs/proposals/tests-with-errors.md §4.2).
    let syntax_errors: BTreeMap<String, Option<Span>> = (namespaces.iter())
        .filter(|n| !n.parse_errors.is_empty())
        .map(|n| {
            let at = (n.parse_errors.iter()).find_map(|d| d.primary_span());
            (n.name.clone(), at)
        })
        .collect();
    elab.set_project_syntax_errors(syntax_errors);
    elab.set_project_namespaces(namespaces.iter().map(|n| n.name.clone()));
    // Every namespace's names first, since an import of everything from one
    // is read while another's edges are found.
    let syntax_of = |i: usize| {
        let ns = &namespaces[i];
        NamespaceSyntax {
            name: ns.name.clone(),
            files: display_names[i]
                .iter()
                .zip(&ns.files)
                .zip(&ns.modules)
                .map(|((name, id), module)| SourceUnit {
                    file: Some(*id),
                    name,
                    module,
                })
                .collect(),
        }
    };
    let names: BTreeMap<String, BTreeSet<String>> = (0..namespaces.len())
        .filter(|i| namespaces[*i].parse_errors.is_empty())
        .map(|i| (namespaces[i].name.clone(), direct_names(&syntax_of(i))))
        .collect();
    elab.set_project_names(names);
    let edges: Vec<Vec<Edge>> = (0..namespaces.len())
        .map(|i| {
            if namespaces[i].modules.is_empty() {
                Vec::new()
            } else {
                elab.namespace_edges(&syntax_of(i))
            }
        })
        .collect();
    for (ns, edges) in namespaces.iter_mut().zip(edges) {
        ns.edges = edges;
    }
    Analysis {
        namespaces,
        diagnostics,
    }
}

/// `E-NO-NAMESPACE`: a file in a project that doesn't start with a
/// namespace line.
fn no_namespace(project: &str, path: &str, display: &str) -> Diagnostic {
    let stem = path
        .rsplit('/')
        .next()
        .unwrap_or(path)
        .trim_end_matches(".sw");
    let word: String = stem
        .chars()
        .take_while(char::is_ascii_alphanumeric)
        .collect();
    let guess = match word.chars().next() {
        Some(c) if c.is_ascii_alphabetic() => {
            format!("{}{}", c.to_ascii_uppercase(), &word[1..])
        }
        _ => "Name".to_string(),
    };
    Diagnostic::error(
        "E-NO-NAMESPACE",
        format!("`{display}` is in the project {project}/ but doesn't say its namespace"),
    )
    .with_note(format!(
        "start the file with `namespace Name`, such as `namespace {guess}`"
    ))
}

/// `E-NAMESPACE-CLASH`: a declaration of namespace `P` that is, or is
/// inside, the namespace `Q` that is also nested in `P`.
fn clashes(namespaces: &[Namespace]) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for q in namespaces {
        for p in namespaces {
            if p.name == q.name || !q.name.starts_with(&format!("{}.", p.name)) {
                continue;
            }
            for module in &p.modules {
                for decl in &module.decls {
                    let (name, what) = match decl {
                        Decl::Data { name, .. } => (name, "type"),
                        Decl::Ability { name, .. } => (name, "ability"),
                        Decl::Signature { name, .. } => (name, "definition"),
                        _ => continue,
                    };
                    let full = format!("{}.{}", p.name, name.text);
                    let message = if full == q.name {
                        format!(
                            "`{}` is both the {what} `{}` in namespace {} and a namespace of its own",
                            q.name, name.text, p.name
                        )
                    } else if full.starts_with(&format!("{}.", q.name)) {
                        format!(
                            "`{}` is both a namespace inside {} (from `{}`) and a namespace of its own",
                            q.name, p.name, name.text
                        )
                    } else {
                        continue;
                    };
                    out.push(
                        Diagnostic::error("E-NAMESPACE-CLASH", message)
                            .with_label(name.span, "declared here")
                            .with_note("rename one of them"),
                    );
                }
            }
        }
    }
    out
}

/// The namespaces `name` uses, directly or not, in canonical order.
fn dependencies(analysis: &Analysis, name: &str) -> Vec<String> {
    let deps: BTreeSet<String> = closure(analysis, &[name.to_string()])
        .into_iter()
        .filter(|n| n != name)
        .collect();
    canonical_order(analysis, &deps).expect("a part of an acyclic closure is acyclic")
}

/// Whether a plain `check` may leave out the namespaces it doesn't need
/// ([`Load::Diagnostics`]): unless `STITCHWORT_SKIP_UNNEEDED` is `0`, to
/// compare with loading everything.
fn skip_unneeded_enabled() -> bool {
    std::env::var_os("STITCHWORT_SKIP_UNNEEDED").is_none_or(|v| v != "0")
}

/// `roots` and every namespace they use, directly or not, by name.
pub fn closure(analysis: &Analysis, roots: &[String]) -> Vec<String> {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut queue: VecDeque<String> = roots.iter().cloned().collect();
    while let Some(name) = queue.pop_front() {
        if !seen.insert(name.clone()) {
            continue;
        }
        if let Some(ns) = analysis.namespace(&name) {
            queue.extend(ns.edges.iter().map(|e| e.target.clone()));
        }
    }
    seen.into_iter().collect()
}

/// `root` and every namespace that uses it, directly or not (by importing
/// from it or writing a name that resolves into it: the same edges
/// [`closure`] follows, the other way), by name.
pub fn dependents(analysis: &Analysis, root: &str) -> Vec<String> {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut queue: VecDeque<String> = VecDeque::from([root.to_string()]);
    while let Some(name) = queue.pop_front() {
        if !seen.insert(name.clone()) {
            continue;
        }
        queue.extend(
            (analysis.namespaces.iter())
                .filter(|ns| ns.edges.iter().any(|e| e.target == name))
                .map(|ns| ns.name.clone()),
        );
    }
    seen.into_iter().collect()
}

/// The order to check the namespaces `among` in (which must be closed under
/// what they use): each after everything it uses, and of those ready, the
/// first by name. If there's a cycle, the cycles instead: each a chain of
/// namespaces, starting at its smallest name, that use each other.
pub fn canonical_order(
    analysis: &Analysis,
    among: &BTreeSet<String>,
) -> Result<Vec<String>, Vec<Vec<String>>> {
    let uses = |name: &str| -> Vec<String> {
        analysis
            .namespace(name)
            .map(|ns| {
                ns.edges
                    .iter()
                    .map(|e| e.target.clone())
                    .filter(|t| among.contains(t) && t != name)
                    .collect()
            })
            .unwrap_or_default()
    };
    let mut waiting: BTreeMap<&str, usize> =
        among.iter().map(|n| (n.as_str(), uses(n).len())).collect();
    let mut users: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for name in among {
        for target in uses(name) {
            if let Some(t) = among.get(&target) {
                users.entry(t.as_str()).or_default().push(name.as_str());
            }
        }
    }
    let mut ready: BinaryHeap<Reverse<&str>> = waiting
        .iter()
        .filter(|(_, n)| **n == 0)
        .map(|(name, _)| Reverse(*name))
        .collect();
    let mut order = Vec::new();
    while let Some(Reverse(name)) = ready.pop() {
        order.push(name.to_string());
        for user in users.get(name).into_iter().flatten() {
            let n = waiting.get_mut(user).expect("a namespace");
            *n -= 1;
            if *n == 0 {
                ready.push(Reverse(user));
            }
        }
    }
    if order.len() == among.len() {
        return Ok(order);
    }
    let left: BTreeSet<String> = among
        .iter()
        .filter(|n| !order.contains(n))
        .cloned()
        .collect();
    // Strongly connected components of the rest: u and v are together when
    // each reaches the other.
    let reach = |from: &str| -> BTreeSet<String> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![from.to_string()];
        while let Some(n) = stack.pop() {
            for t in uses(&n) {
                if left.contains(&t) && seen.insert(t.clone()) {
                    stack.push(t);
                }
            }
        }
        seen
    };
    let reaches: BTreeMap<&String, BTreeSet<String>> = left.iter().map(|n| (n, reach(n))).collect();
    let mut cycles = Vec::new();
    let mut done: BTreeSet<&String> = BTreeSet::new();
    for start in &left {
        if done.contains(start) {
            continue;
        }
        let component: BTreeSet<&String> = left
            .iter()
            .filter(|v| reaches[start].contains(*v) && reaches[*v].contains(start))
            .collect();
        done.extend(component.iter().copied());
        if component.len() < 2 {
            continue;
        }
        // The shortest way back to `start`, by breadth-first search with
        // neighbours in name order.
        let mut parent: BTreeMap<String, String> = BTreeMap::new();
        let mut queue = VecDeque::from([start.clone()]);
        let mut last = None;
        'search: while let Some(n) = queue.pop_front() {
            let mut next = uses(&n);
            next.sort();
            for t in next {
                if !component.contains(&t) {
                    continue;
                }
                if &t == start {
                    last = Some(n);
                    break 'search;
                }
                if !parent.contains_key(&t) {
                    parent.insert(t.clone(), n.clone());
                    queue.push_back(t);
                }
            }
        }
        let mut chain = vec![last.expect("a cycle returns to its start")];
        while let Some(p) = parent.get(chain.last().expect("non-empty")) {
            chain.push(p.clone());
        }
        chain.reverse();
        if chain.first() != Some(start) {
            chain.insert(0, start.clone());
        }
        cycles.push(chain);
    }
    Err(cycles)
}

/// `E-NAMESPACE-CYCLE` for a chain from [`canonical_order`]: one label per
/// link, where the first uses the next.
pub fn cycle_diagnostic(analysis: &Analysis, chain: &[String]) -> Diagnostic {
    let mut shown = chain.to_vec();
    shown.push(chain[0].clone());
    let mut d = Diagnostic::error(
        "E-NAMESPACE-CYCLE",
        format!("these namespaces use each other: {}", shown.join(" → ")),
    );
    for (i, from) in chain.iter().enumerate() {
        let to = &chain[(i + 1) % chain.len()];
        let span: Option<Span> = analysis
            .namespace(from)
            .and_then(|ns| ns.edges.iter().find(|e| &e.target == to))
            .map(|e| e.span);
        if let Some(span) = span {
            d = d.with_label(span, format!("`{from}` uses `{to}` here"));
        }
    }
    d.with_note("put what both need into one namespace, or into a third that both use")
}

// ---- stitchwort.yaml --------------------------------------------------

#[derive(serde::Deserialize, Default)]
#[serde(deny_unknown_fields)]
struct RawConfig {
    sources: Option<Vec<String>>,
    audit: Option<RawAudit>,
    check: Option<RawCheck>,
}

/// `check:` in `stitchwort.yaml` (SW-2762).
#[derive(serde::Deserialize, Default)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
struct RawCheck {
    open_goals: Option<String>,
}

/// `audit:` in `stitchwort.yaml` (SW-912).
#[derive(serde::Deserialize, Default)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
struct RawAudit {
    allowed_axioms: Option<Vec<String>>,
}

/// What `stitchwort.yaml` says (docs/proposals/multi-file.md §5).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Config {
    /// Normalised, relative to the project folder; "" is the project folder.
    pub sources: Vec<String>,
    /// The axioms `stitchwort audit` allows (`audit: allowed-axioms:`), if
    /// the project lists them; `None` means the default
    /// (`audit::DEFAULT_ALLOWED`).
    pub allowed_axioms: Option<Vec<String>>,
    /// What `stitchwort check` does with an open goal (`check: open-goals:`).
    pub open_goals: OpenGoals,
}

/// How `stitchwort check` treats an open goal (`?`), per project
/// (D3489, D3494). `audit` fails unfinished theorems either way.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum OpenGoals {
    /// An open goal fails the check.
    #[default]
    Fail,
    /// An open goal is reported as a warning, and the check can still pass.
    Warn,
}

fn config_error(display: &str, what: impl std::fmt::Display) -> Diagnostic {
    Diagnostic::error("E-PROJECT-CONFIG", format!("`{display}`: {what}"))
}

/// Reads `stitchwort.yaml`. `display` is its name for messages
/// (`aoc/stitchwort.yaml`). An empty file, or one with only comments, means
/// the defaults.
pub fn parse_config(file: FileId, display: &str, text: &str) -> Result<Config, Diagnostic> {
    // `Options` is `#[non_exhaustive]`, so its fields are set one by one.
    let mut options = serde_saphyr::Options::default();
    options.strict_booleans = true;
    options.no_schema = true;
    options.duplicate_keys = serde_saphyr::DuplicateKeyPolicy::Error;
    let only_comments = text
        .lines()
        .all(|l| l.trim().is_empty() || l.trim_start().starts_with('#'));
    let raw: RawConfig = if only_comments {
        RawConfig::default()
    } else {
        serde_saphyr::from_str_with_options::<Option<RawConfig>>(text, options)
            .map_err(|e| yaml_error(file, display, text, &e))?
            .unwrap_or_default()
    };
    let sources = match raw.sources {
        None => vec!["src".to_string()],
        Some(list) if list.is_empty() => {
            return Err(config_error(display, "`sources` lists no folders"));
        }
        Some(list) => list,
    };
    let mut normalised = Vec::new();
    for source in sources {
        let outside = source.starts_with('/') || source.split('/').any(|c| c == "..");
        if outside {
            return Err(config_error(
                display,
                format!("the source folder `{source}` is outside the project folder"),
            )
            .with_note("source folders are relative to the folder holding `stitchwort.yaml`"));
        }
        let parts: Vec<&str> = source
            .split('/')
            .filter(|c| !c.is_empty() && *c != ".")
            .collect();
        let path = parts.join("/");
        if !normalised.contains(&path) {
            normalised.push(path);
        }
    }
    let open_goals = match raw.check.and_then(|c| c.open_goals).as_deref() {
        None | Some("fail") => OpenGoals::Fail,
        Some("warn") => OpenGoals::Warn,
        Some(other) => {
            return Err(config_error(
                display,
                format!("`check: open-goals:` is `{other}`, which isn't a setting"),
            )
            .with_note("the settings are `warn` and `fail` (the default)"));
        }
    };
    let allowed_axioms = raw.audit.and_then(|a| a.allowed_axioms);
    if let Some(unknown) = allowed_axioms
        .iter()
        .flat_map(crate::audit::unknown_axioms)
        .next()
    {
        return Err(config_error(
            display,
            format!("`audit: allowed-axioms:` lists `{unknown}`, which isn't an axiom"),
        )
        .with_note(format!(
            "the axioms are {}",
            crate::audit::AXIOMS.join(", ")
        )));
    }
    Ok(Config {
        sources: normalised,
        allowed_axioms,
        open_goals,
    })
}

/// A YAML error as an `E-PROJECT-CONFIG`, with one line of what's wrong.
fn yaml_error(file: FileId, display: &str, text: &str, e: &serde_saphyr::Error) -> Diagnostic {
    let full = e.to_string();
    let first = full.lines().next().unwrap_or("").trim().to_string();
    let mut note = None;
    let what = if first.contains("unknown field")
        && let Some(key) = first.split('`').nth(1)
    {
        // The message names the fields it expected after `expected`; those
        // say which struct the unknown key was in.
        let expected = first.split_once("expected ").map_or("", |(_, rest)| rest);
        if expected.contains("allowed-axioms") {
            note = Some("the known key under `audit:` is `allowed-axioms`");
        } else if expected.contains("open-goals") {
            note = Some("the known key under `check:` is `open-goals`");
        } else if expected.contains("sources") || expected.contains("audit") {
            note = Some("the known keys are `sources`, `audit` and `check`");
        }
        format!("unknown key `{key}`")
    } else {
        // The library's message starts with where the error is, which the
        // label says, and a few mention its own types.
        let mut msg = first.strip_prefix("error: ").unwrap_or(&first);
        if msg.starts_with("line ")
            && let Some(i) = msg.find(": ")
        {
            msg = &msg[i + 2..];
        }
        if let Some(rest) = msg.strip_prefix("duplicate mapping key: ") {
            format!(
                "`{}` is written twice",
                rest.split(',').next().unwrap_or(rest)
            )
        } else if msg == "expected sequence start" {
            "expected a list".to_string()
        } else if msg == "expected mapping start" {
            "expected `sources: …`".to_string()
        } else {
            msg.to_string()
        }
    };
    let mut d = config_error(display, what);
    if let Some(location) = e.location() {
        let offset = location
            .span()
            .byte_offset()
            .map(|o| o as usize)
            .or_else(|| {
                let (line, column) = (location.line() as usize, location.column() as usize);
                let start: usize = text
                    .split_inclusive('\n')
                    .take(line.saturating_sub(1))
                    .map(str::len)
                    .sum();
                Some(start + column.saturating_sub(1))
            });
        if let Some(start) = offset.filter(|o| *o <= text.len()) {
            let mut end = (start + 1).min(text.len());
            while !text.is_char_boundary(end) {
                end += 1;
            }
            let start = (0..=start)
                .rev()
                .find(|i| text.is_char_boundary(*i))
                .unwrap_or(0);
            d = d.with_label(
                Span {
                    file,
                    start: start as u32,
                    end: end as u32,
                },
                "here",
            );
        }
    }
    match note {
        Some(note) => d.with_note(note),
        None => d,
    }
}

// ---- files ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntryKind {
    File,
    Dir,
    Other,
}

pub struct Entry {
    pub name: String,
    pub kind: EntryKind,
}

/// A project's files, by path within the project ("" is the project folder;
/// components joined by `/`).
pub trait Files {
    fn entries(&self, dir: &str) -> std::io::Result<Vec<Entry>>;
    fn read(&self, path: &str) -> std::io::Result<String>;

    /// Whether `path` is a file, so a source entry that is a file is not
    /// reported as a folder that doesn't exist.
    fn is_file(&self, path: &str) -> bool {
        self.read(path).is_ok()
    }

    /// The same files for `include` to read (`Session::load_project` hands
    /// them over), if `include` can read them.
    fn include_files(&self) -> Option<std::rc::Rc<dyn stitchwort_elab::project::IncludeFiles>> {
        None
    }

    /// Parses the project's configuration, `text` (what `read` gives for
    /// `stitchwort.yaml`), adding it to `sources` as `display` so that its
    /// errors show their line. Files whose configuration is known already
    /// (the playground's) override this, which keeps the YAML parser out of
    /// a build that never reads a `stitchwort.yaml`.
    fn config(
        &self,
        text: &str,
        display: &str,
        sources: &mut SourceMap,
    ) -> Result<Config, Diagnostic> {
        let id = sources.add(display, text);
        parse_config(id, display, text)
    }
}

/// A project on disk.
pub struct DiskFiles {
    pub root: PathBuf,
}

impl DiskFiles {
    fn path(&self, path: &str) -> PathBuf {
        let mut full = self.root.clone();
        full.extend(path.split('/').filter(|c| !c.is_empty()));
        full
    }
}

impl Files for DiskFiles {
    fn include_files(&self) -> Option<std::rc::Rc<dyn stitchwort_elab::project::IncludeFiles>> {
        Some(std::rc::Rc::new(DiskFiles {
            root: self.root.clone(),
        }))
    }

    fn entries(&self, dir: &str) -> std::io::Result<Vec<Entry>> {
        let mut out = Vec::new();
        for entry in std::fs::read_dir(self.path(dir))? {
            let entry = entry?;
            let Some(name) = entry.file_name().to_str().map(str::to_string) else {
                continue;
            };
            // Symlinks are skipped (docs/proposals/multi-file.md §5).
            let kind = match std::fs::symlink_metadata(entry.path()) {
                Ok(m) if m.is_dir() => EntryKind::Dir,
                Ok(m) if m.is_file() => EntryKind::File,
                _ => EntryKind::Other,
            };
            out.push(Entry { name, kind });
        }
        Ok(out)
    }

    fn read(&self, path: &str) -> std::io::Result<String> {
        std::fs::read_to_string(self.path(path))
    }

    fn is_file(&self, path: &str) -> bool {
        self.path(path).is_file()
    }
}

/// A project in memory: for tests. `reversed` lists directories in the
/// opposite order, to show that order never matters.
pub struct MemoryFiles {
    pub files: BTreeMap<String, String>,
    pub reversed: bool,
}

impl Files for MemoryFiles {
    fn include_files(&self) -> Option<std::rc::Rc<dyn stitchwort_elab::project::IncludeFiles>> {
        Some(std::rc::Rc::new(MemoryFiles {
            files: self.files.clone(),
            reversed: self.reversed,
        }))
    }

    fn entries(&self, dir: &str) -> std::io::Result<Vec<Entry>> {
        let prefix = if dir.is_empty() {
            String::new()
        } else {
            format!("{dir}/")
        };
        let mut found: BTreeMap<String, EntryKind> = BTreeMap::new();
        for path in self.files.keys() {
            let Some(rest) = path.strip_prefix(&prefix) else {
                continue;
            };
            match rest.split_once('/') {
                Some((name, _)) => {
                    found.insert(name.to_string(), EntryKind::Dir);
                }
                None => {
                    found.insert(rest.to_string(), EntryKind::File);
                }
            }
        }
        if found.is_empty() && !dir.is_empty() {
            return Err(std::io::ErrorKind::NotFound.into());
        }
        let mut entries: Vec<Entry> = found
            .into_iter()
            .map(|(name, kind)| Entry { name, kind })
            .collect();
        if self.reversed {
            entries.reverse();
        }
        Ok(entries)
    }

    fn read(&self, path: &str) -> std::io::Result<String> {
        self.files
            .get(path)
            .cloned()
            .ok_or_else(|| std::io::ErrorKind::NotFound.into())
    }
}

const CONFIG: &str = "stitchwort.yaml";

/// The project folder that holds `start`: `start` or the nearest folder
/// above it that contains a file `stitchwort.yaml`.
pub fn find_project(start: &Path) -> Option<PathBuf> {
    start
        .ancestors()
        .find(|dir| dir.join(CONFIG).is_file())
        .map(Path::to_path_buf)
}

/// Reads a project's configuration and every `.sw` file under its source
/// folders: (path within the project, text), sorted by path. The config is
/// added to `sources` as `{project}/stitchwort.yaml`, so its errors show
/// their line.
pub fn project_sources(
    files: &dyn Files,
    project: &str,
    sources: &mut SourceMap,
) -> Result<Vec<(String, String)>, Vec<Diagnostic>> {
    let display = format!("{project}/{CONFIG}");
    let text = files.read(CONFIG).map_err(|e| {
        vec![Diagnostic::error(
            "E-IO",
            format!("can't read `{display}`: {e}"),
        )]
    })?;
    let config = files
        .config(&text, &display, sources)
        .map_err(|d| vec![d])?;
    let mut found: BTreeMap<String, String> = BTreeMap::new();
    let mut errors = Vec::new();
    for root in &config.sources {
        if let Err(e) = files.entries(root) {
            let shown = if root.is_empty() { "." } else { root };
            if files.is_file(root) {
                errors.push(config_error(
                    &display,
                    format!("`{shown}` is a file; `sources` lists folders"),
                ));
            } else if e.kind() == std::io::ErrorKind::NotFound {
                errors.push(
                    config_error(
                        &display,
                        format!("the source folder `{shown}` doesn't exist"),
                    )
                    .with_note(
                        "create it, or list your folders under `sources` in `stitchwort.yaml`",
                    ),
                );
            } else {
                errors.push(Diagnostic::error(
                    "E-IO",
                    format!("can't read the folder `{project}/{shown}`: {e}"),
                ));
            }
            continue;
        }
        walk(files, project, root, &mut found, &mut errors);
    }
    if errors.is_empty() {
        Ok(found.into_iter().collect())
    } else {
        Err(errors)
    }
}

fn walk(
    files: &dyn Files,
    project: &str,
    dir: &str,
    found: &mut BTreeMap<String, String>,
    errors: &mut Vec<Diagnostic>,
) {
    let mut entries = match files.entries(dir) {
        Ok(entries) => entries,
        Err(e) => {
            let shown = if dir.is_empty() { "." } else { dir };
            errors.push(Diagnostic::error(
                "E-IO",
                format!("can't read the folder `{project}/{shown}`: {e}"),
            ));
            return;
        }
    };
    // Errors are found in name order, not the directory's.
    entries.sort_by(|a, b| a.name.cmp(&b.name));
    if !dir.is_empty()
        && entries
            .iter()
            .any(|e| e.name == CONFIG && e.kind == EntryKind::File)
    {
        errors.push(
            Diagnostic::error(
                "E-PROJECT-CONFIG",
                format!("`{dir}/` is a project inside the project {project}/"),
            )
            .with_note("move it out of the source folders, or delete its `stitchwort.yaml`"),
        );
        return;
    }
    let join = |name: &str| {
        if dir.is_empty() {
            name.to_string()
        } else {
            format!("{dir}/{name}")
        }
    };
    for entry in entries {
        if entry.name.starts_with('.') {
            continue;
        }
        match entry.kind {
            EntryKind::Dir => walk(files, project, &join(&entry.name), found, errors),
            EntryKind::File if entry.name.ends_with(".sw") => {
                let path = join(&entry.name);
                match files.read(&path) {
                    Ok(text) => {
                        found.insert(path, text);
                    }
                    Err(e) => errors.push(Diagnostic::error(
                        "E-IO",
                        format!("can't read `{project}/{path}`: {e}"),
                    )),
                }
            }
            _ => {}
        }
    }
}

impl Session {
    /// Reads and checks the project in `files` (`project` is its name for
    /// display): the namespaces `target` needs.
    pub fn load_project(
        &mut self,
        files: &dyn Files,
        project: &str,
        target: &Target,
    ) -> Result<Loaded, Vec<Diagnostic>> {
        if let Some(include) = files.include_files() {
            self.include_from(include);
        }
        let sources = project_sources(files, project, &mut self.sources)?;
        self.load_project_sources(project, sources, target)
    }

    /// [`Session::load_project`], for a command that does `load` with the
    /// result.
    pub fn load_project_for(
        &mut self,
        files: &dyn Files,
        project: &str,
        target: &Target,
        load: Load,
    ) -> Result<Loaded, Vec<Diagnostic>> {
        if let Some(include) = files.include_files() {
            self.include_from(include);
        }
        let sources = project_sources(files, project, &mut self.sources)?;
        self.load_project_sources_for(project, sources, target, load)
    }
}

impl stitchwort_elab::project::IncludeFiles for DiskFiles {
    /// Reads `path`, unless it resolves (through symlinks) to somewhere
    /// outside the root: that is `PermissionDenied`, which `include`
    /// reports as `E-INCLUDE-OUTSIDE`.
    fn read(&self, path: &str) -> std::io::Result<String> {
        let full = std::fs::canonicalize(self.path(path))?;
        let root = std::fs::canonicalize(&self.root)?;
        if !full.starts_with(&root) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                "resolves outside the project folder",
            ));
        }
        std::fs::read_to_string(full)
    }
}

impl stitchwort_elab::project::IncludeFiles for MemoryFiles {
    fn read(&self, path: &str) -> std::io::Result<String> {
        Files::read(self, path)
    }
}
