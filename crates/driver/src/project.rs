//! Projects of several files (docs/proposals/multi-file.md §4): which
//! namespaces the files make, what each uses, and the order to check them
//! in. Nothing here checks a declaration.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, VecDeque};

use stitchwort_elab::project::{Edge, NamespaceSyntax, SourceUnit};
use stitchwort_syntax::ast::{Decl, Module};
use stitchwort_syntax::{
    Diagnostic, FileId, Severity, Span, parse_module_within, parse_namespace_line,
};

use crate::driver::Session;

/// Which namespaces a command needs.
pub enum Target {
    Everything,
    Namespaces(Vec<String>),
}

/// What loading a project checked.
pub struct Loaded {
    pub project: String,
    /// The namespaces checked, in canonical order.
    pub checked: Vec<String>,
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
        let analysis = analyse(self, project, files);
        if !analysis.diagnostics.is_empty() {
            return Err(analysis.diagnostics);
        }
        let known: BTreeSet<String> = analysis.namespaces.iter().map(|n| n.name.clone()).collect();
        let needed: BTreeSet<String> = match target {
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
        let mut diagnostics: Vec<Diagnostic> = Vec::new();
        let mut failed: BTreeSet<&str> = BTreeSet::new();
        let mut skipped: BTreeSet<&str> = BTreeSet::new();
        for name in &order {
            let ns = analysis.namespace(name).expect("a namespace");
            // The first dependency, in canonical order, that has errors or
            // wasn't checked.
            let blocker = order
                .iter()
                .filter(|m| failed.contains(m.as_str()) || skipped.contains(m.as_str()))
                .find_map(|m| ns.edges.iter().find(|e| &e.target == m));
            if let Some(edge) = blocker {
                let m = &edge.target;
                let why = if failed.contains(m.as_str()) {
                    format!("namespace {m} has errors, so {name} isn't checked")
                } else {
                    format!("namespace {m} isn't checked, so neither is {name}")
                };
                diagnostics.push(
                    Diagnostic::error("E-NAMESPACE-FAILED", why)
                        .with_label(edge.span, format!("`{name}` uses `{m}` here")),
                );
                skipped.insert(name);
                continue;
            }
            if !ns.parse_errors.is_empty() {
                diagnostics.extend(ns.parse_errors.iter().cloned());
                failed.insert(name);
                continue;
            }
            let deps: BTreeSet<String> = closure(&analysis, std::slice::from_ref(name))
                .into_iter()
                .filter(|n| n != name)
                .collect();
            let dependencies =
                canonical_order(&analysis, &deps).expect("a part of an acyclic closure is acyclic");
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
            let first_new_def = self.elab.globals.defs.len();
            let mut found = self
                .elab
                .elaborate_namespace(Some(name), &units, Some(&dependencies));
            self.check_exports(first_new_def, true, &mut found);
            if found.iter().any(|d| d.severity == Severity::Error) {
                failed.insert(name);
            }
            diagnostics.extend(found);
        }
        self.elab.leave_namespace();
        if diagnostics.iter().any(|d| d.severity == Severity::Error) {
            return Err(diagnostics);
        }
        self.warnings.extend(diagnostics);
        Ok(Loaded {
            project: project.to_string(),
            checked: order,
        })
    }
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
    /// Parsed, in the same order; empty if any file failed to parse.
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
pub fn analyse(session: &mut Session, project: &str, mut files: Vec<(String, String)>) -> Analysis {
    files.sort();
    let mut diagnostics = Vec::new();
    // Each namespace's files: id, then parse result.
    struct Found {
        files: Vec<FileId>,
        modules: Vec<Module>,
        parse_errors: Vec<Diagnostic>,
        broken: bool,
    }
    let mut found: BTreeMap<String, Found> = BTreeMap::new();
    for (path, text) in &files {
        let display = format!("{project}/{path}");
        let id = session.sources.add(display.clone(), text.clone());
        let parsed = parse_module_within(id, text, session.elab.limits.stack);
        let (namespace, errors, module) = match parsed {
            Ok(module) => (module.namespace.clone(), Vec::new(), Some(module)),
            Err(errors) => match parse_namespace_line(id, text) {
                Ok(line) => (line, errors, None),
                Err(d) => {
                    // The namespace line itself is the trouble.
                    diagnostics.push(d);
                    continue;
                }
            },
        };
        let Some(line) = namespace else {
            diagnostics.push(no_namespace(project, path, &display));
            continue;
        };
        if let Err(d) = session.elab.check_namespace_name(&line) {
            diagnostics.push(d);
            continue;
        }
        let entry = found
            .entry(line.path.text.clone())
            .or_insert_with(|| Found {
                files: Vec::new(),
                modules: Vec::new(),
                parse_errors: Vec::new(),
                broken: false,
            });
        entry.files.push(id);
        match module {
            Some(module) => entry.modules.push(module),
            None => {
                entry.broken = true;
                entry.parse_errors.extend(errors);
            }
        }
    }
    let mut namespaces: Vec<Namespace> = found
        .into_iter()
        .map(|(name, f)| Namespace {
            name,
            files: f.files,
            modules: if f.broken { Vec::new() } else { f.modules },
            parse_errors: f.parse_errors,
            edges: Vec::new(),
        })
        .collect();
    diagnostics.extend(clashes(&namespaces));
    session
        .elab
        .set_project_namespaces(namespaces.iter().map(|n| n.name.clone()));
    for ns in &mut namespaces {
        if ns.modules.is_empty() {
            continue;
        }
        let names: Vec<String> = ns
            .files
            .iter()
            .map(|id| session.sources.get(*id).name.clone())
            .collect();
        let syntax = NamespaceSyntax {
            name: ns.name.clone(),
            files: names
                .iter()
                .zip(&ns.files)
                .zip(&ns.modules)
                .map(|((name, id), module)| SourceUnit {
                    file: Some(*id),
                    name,
                    module,
                })
                .collect(),
        };
        ns.edges = session.elab.namespace_edges(&syntax);
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
