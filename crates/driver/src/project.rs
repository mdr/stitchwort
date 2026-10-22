//! Projects of several files (docs/proposals/multi-file.md §4): which
//! namespaces the files make, what each uses, and the order to check them
//! in. Nothing here checks a declaration.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, VecDeque};
use std::path::{Path, PathBuf};

use stitchwort_elab::project::{Edge, NamespaceSyntax, SourceUnit, direct_names};
use stitchwort_syntax::ast::{Decl, Module};
use stitchwort_syntax::{
    Diagnostic, FileId, Severity, SourceMap, Span, parse_module_within, parse_namespace_line,
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
        self.load_analysis(project, analysis, target)
    }

    /// [`Session::load_project_sources`], from the files already read
    /// (`analyse`).
    pub fn load_analysis(
        &mut self,
        project: &str,
        analysis: Analysis,
        target: &Target,
    ) -> Result<Loaded, Vec<Diagnostic>> {
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
        if self.elab.uses_check_cache() {
            let sources = self.namespace_sources(project, &analysis);
            self.elab.set_namespace_sources(sources);
        }
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

    /// For the check cache (docs/proposals/check-cache.md §4.2): a hash of
    /// each namespace's own sources (its name, and each file's name and
    /// text), the names of all the project's namespaces, and
    /// `stitchwort.yaml`. The elaborator adds the rest of the key.
    fn namespace_sources(
        &self,
        project: &str,
        analysis: &Analysis,
    ) -> std::collections::HashMap<String, stitchwort_elab::cache::Key> {
        let config_name = format!("{project}/{CONFIG}");
        let config = self
            .sources
            .iter()
            .filter(|(_, f)| f.name == config_name)
            .last()
            .map(|(_, f)| f.text.as_str());
        let mut common = blake3::Hasher::new();
        let part = |h: &mut blake3::Hasher, bytes: &[u8]| {
            h.update(&(bytes.len() as u64).to_le_bytes());
            h.update(bytes);
        };
        part(&mut common, b"namespaces");
        let mut names: Vec<&str> = analysis
            .namespaces
            .iter()
            .map(|n| n.name.as_str())
            .collect();
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
        analysis
            .namespaces
            .iter()
            .map(|ns| {
                let mut h = common.clone();
                part(&mut h, ns.name.as_bytes());
                for id in &ns.files {
                    let file = self.sources.get(*id);
                    part(&mut h, file.name.as_bytes());
                    part(&mut h, file.text.as_bytes());
                }
                (ns.name.clone(), *h.finalize().as_bytes())
            })
            .collect()
    }
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
        session.elab.set_include_location(id, path.clone());
        let parsed = parse_module_within(id, text, session.elab.limits.stack);
        let (namespace, errors, module) = match parsed {
            Ok(module) => (module.namespace.clone(), Vec::new(), Some(module)),
            Err(errors) => {
                if let Some(not_first) = errors.iter().find(|d| d.code == "E-NAMESPACE-NOT-FIRST") {
                    diagnostics.push(not_first.clone());
                    continue;
                }
                match parse_namespace_line(id, text) {
                    Ok(line) => (line, errors, None),
                    Err(d) => {
                        // The namespace line itself is the trouble.
                        diagnostics.push(d);
                        continue;
                    }
                }
            }
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
    // Every namespace's names first, since an import of everything from one
    // is read while another's edges are found.
    let display_names: Vec<Vec<String>> = namespaces
        .iter()
        .map(|ns| {
            ns.files
                .iter()
                .map(|id| session.sources.get(*id).name.clone())
                .collect()
        })
        .collect();
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
        .filter(|i| !namespaces[*i].modules.is_empty())
        .map(|i| (namespaces[i].name.clone(), direct_names(&syntax_of(i))))
        .collect();
    session.elab.set_project_names(names);
    let edges: Vec<Vec<Edge>> = (0..namespaces.len())
        .map(|i| {
            if namespaces[i].modules.is_empty() {
                Vec::new()
            } else {
                session.elab.namespace_edges(&syntax_of(i))
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

// ---- stitchwort.yaml --------------------------------------------------

#[derive(serde::Deserialize, Default)]
#[serde(deny_unknown_fields)]
struct RawConfig {
    sources: Option<Vec<String>>,
}

/// What `stitchwort.yaml` says (docs/proposals/multi-file.md §5).
#[derive(Debug, PartialEq, Eq)]
pub struct Config {
    /// Normalised, relative to the project folder; "" is the project folder.
    pub sources: Vec<String>,
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
    Ok(Config {
        sources: normalised,
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
        note = Some("the known key is `sources`");
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

    /// The same files for `include` to read (`Session::load_project` hands
    /// them over), if `include` can read them.
    fn include_files(&self) -> Option<std::rc::Rc<dyn stitchwort_elab::project::IncludeFiles>> {
        None
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
    let id = sources.add(display.clone(), text.clone());
    let config = parse_config(id, &display, &text).map_err(|d| vec![d])?;
    let mut found: BTreeMap<String, String> = BTreeMap::new();
    let mut errors = Vec::new();
    for root in &config.sources {
        if files.entries(root).is_err() {
            let shown = if root.is_empty() { "." } else { root };
            errors.push(
                config_error(
                    &display,
                    format!("the source folder `{shown}` doesn't exist"),
                )
                .with_note("create it, or list your folders under `sources` in `stitchwort.yaml`"),
            );
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
    let Ok(mut entries) = files.entries(dir) else {
        return;
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
