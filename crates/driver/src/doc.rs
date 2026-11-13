//! `stitchwort doc NAME` (SW-1019, docs/proposals/documentation.md §5.3 to
//! §5.5, stage 1b): what a declaration does, in one place: its header as
//! written, its doc, the examples attached to it by name and the theorems
//! about it.
//!
//! Everything but the elaborated type and the theorem list comes from
//! parsing alone (D2143, D2152): [`Decls`] parses the library's files and
//! the program's and keeps the names they declare, so a name is resolved,
//! and its header, doc and examples are found, without a check. The theorems
//! come from [`Session::search`] through [`Session::theorems_about`].

mod coverage;
pub use coverage::{Coverage, NamespaceCoverage, render_coverage};

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;
use stitchwort_core::{DataId, DefId, Ev, Term};
use stitchwort_syntax::ast::{Decl, Expr, Import, Module};
use stitchwort_syntax::docs::{
    Doc, docs, file_doc, file_doc_namespace, file_imports, link_candidates_with_imports,
    link_ranges,
};
use stitchwort_syntax::{
    DEFAULT_STACK, FileId, SourceMap, Tok, Token, decl_ranges, lex_recovering,
    parse_module_recovering,
};

use crate::driver::Session;
use crate::search::{Kinds, Options, Scope};

/// What a declaration is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Definition,
    Theorem,
    Instance,
    Type,
    Interface,
    Ability,
    Constructor,
    Field,
    Operation,
}

impl Kind {
    pub fn name(self) -> &'static str {
        match self {
            Kind::Definition => "definition",
            Kind::Theorem => "theorem",
            Kind::Instance => "instance",
            Kind::Type => "type",
            Kind::Interface => "interface",
            Kind::Ability => "ability",
            Kind::Constructor => "constructor",
            Kind::Field => "field",
            Kind::Operation => "operation",
        }
    }

    /// Listed by a namespace (§5.3): not theorems, instances or members.
    fn is_listed(self) -> bool {
        matches!(
            self,
            Kind::Definition | Kind::Type | Kind::Interface | Kind::Ability
        )
    }
}

/// A source file the declarations come from.
struct File {
    /// As shown: `std/List/Toolkit.sw`, `aoc/src/Aoc/Common/Common.sw`.
    display: String,
    id: FileId,
    /// A library file's path under `std/` (`core/Data.sw` is the core's).
    std: Option<String>,
    /// A program's file: its namespace.
    namespace: Option<String>,
    /// Byte offsets of the starts of its lines.
    lines: Vec<u32>,
}

/// A program's source file, to be parsed.
pub struct Input {
    pub display: String,
    pub text: String,
    /// The namespace its `namespace` line names, if it has one.
    pub namespace: Option<String>,
}

/// One declared name.
pub struct Entry {
    /// The full name: `Std.List.filterMap`, `Aoc.Common.Grid.at`.
    pub path: String,
    pub kind: Kind,
    file: usize,
    /// The byte offset of the name, which keys the declaration's doc.
    name_at: u32,
    /// The byte offset of the declaration's keyword (of the name, for a
    /// member): its line is the location.
    start: u32,
    /// The declaration as written, up to `:=` or its first equation.
    pub header: String,
    /// The type, interface or ability a member belongs to.
    container: Option<usize>,
    /// A definition whose type is a function's: a test named after it
    /// without a qualifier is about it (D2144).
    function: bool,
}

/// A `test "…"` declaration.
struct TestDecl {
    description: String,
    file: usize,
    start: u32,
    source: String,
}

/// An example's source, and where it is.
struct ExampleDecl {
    kind: &'static str,
    name: String,
    file: usize,
    start: u32,
    source: String,
}

/// The declared names of the library and a program, found by parsing
/// (D2143, D2152).
pub struct Decls {
    sources: SourceMap,
    files: Vec<File>,
    entries: Vec<Entry>,
    tests: Vec<TestDecl>,
    /// The program's namespaces, as the files declare them.
    project: BTreeSet<String>,
    by_path: BTreeMap<String, Vec<usize>>,
    /// Every namespace a name can be listed under, and so named as one.
    namespaces: BTreeSet<String>,
    /// Docs by file, read once.
    docs: RefCell<BTreeMap<usize, BTreeMap<u32, Doc>>>,
    /// Each file's `import` lines, read when a link in it is resolved.
    imports: RefCell<BTreeMap<usize, Vec<Import>>>,
}

/// Where examples and theorems are looked for (D2146): the files of these
/// namespaces of the program, the library, or both.
#[derive(Clone, Debug)]
pub struct Within {
    pub std: bool,
    pub project: bool,
    /// With `project`: only these namespaces' files; none: all of them.
    pub namespaces: Option<BTreeSet<String>>,
}

/// What a name resolved to (§5.3).
#[derive(Debug, Default)]
pub struct Resolution {
    /// The declarations the name is, by index into [`Decls`].
    pub entries: Vec<usize>,
    /// The namespaces it is, in full.
    pub namespaces: Vec<String>,
}

impl Decls {
    /// Parses the library and `inputs`, a program's files.
    pub fn new(inputs: Vec<Input>) -> Decls {
        let mut decls = Decls {
            sources: SourceMap::new(),
            files: Vec::new(),
            entries: Vec::new(),
            tests: Vec::new(),
            project: BTreeSet::new(),
            by_path: BTreeMap::new(),
            namespaces: BTreeSet::new(),
            docs: RefCell::new(BTreeMap::new()),
            imports: RefCell::new(BTreeMap::new()),
        };
        let std = stitchwort_elab::std_text();
        // The core's files are joined in the prelude: each is read alone.
        let mut at = 0;
        for (path, len) in std.core_layout {
            let text = &std.prelude[at..at + len];
            at += len;
            let path = path.to_string();
            decls.add_file(std.shown_path(&path), text, Some(path), None);
        }
        for (path, text) in std.library {
            decls.add_file(std.shown_path(path), text, Some(path.to_string()), None);
        }
        for input in inputs {
            if let Some(ns) = &input.namespace {
                decls.project.insert(ns.clone());
            }
            decls.add_file(input.display, &input.text, None, input.namespace);
        }
        for (i, entry) in decls.entries.iter().enumerate() {
            decls.by_path.entry(entry.path.clone()).or_default().push(i);
        }
        decls.namespaces = decls.project.clone();
        for entry in decls.entries.iter().filter(|e| e.kind.is_listed()) {
            if decls.files[entry.file].std.is_some() {
                let mut path = entry.path.as_str();
                while let Some((rest, _)) = path.rsplit_once('.') {
                    decls.namespaces.insert(rest.to_string());
                    path = rest;
                }
            }
        }
        decls
    }

    fn add_file(&mut self, display: String, text: &str, std: Option<String>, ns: Option<String>) {
        let id = self.sources.add(display.clone(), text);
        let mut lines = vec![0u32];
        lines.extend(text.match_indices('\n').map(|(i, _)| i as u32 + 1));
        let file = self.files.len();
        self.files.push(File {
            display,
            id,
            std: std.clone(),
            namespace: ns.clone(),
            lines,
        });
        let (module, _) = parse_module_recovering(id, text, DEFAULT_STACK);
        let tokens = lex_recovering(id, text).tokens;
        let groups = decl_ranges(&tokens).unwrap_or_default();
        // A file with no `namespace` line is in `Main`, as in file mode.
        let prefix = match (&std, &module.namespace, &ns) {
            (Some(_), ..) => "Std.".to_string(),
            (None, _, Some(ns)) => format!("{ns}."),
            (None, Some(line), None) => format!("{}.", line.path.text),
            (None, None, None) => "Main.".to_string(),
        };
        self.add_decls(file, text, &module, &tokens, &groups, &prefix);
    }

    fn add_decls(
        &mut self,
        file: usize,
        text: &str,
        module: &Module,
        tokens: &[Token],
        groups: &[std::ops::Range<usize>],
        prefix: &str,
    ) {
        for decl in &module.decls {
            let Some(group) = group_of(tokens, groups, decl.span().start) else {
                continue;
            };
            let Some(first) = first_token(tokens, &group) else {
                continue;
            };
            let start = tokens[first].span.start;
            let source = || text[start as usize..group_end(tokens, &group)].to_string();
            match decl {
                Decl::Signature {
                    name,
                    theorem,
                    synonym,
                    instance,
                    ty,
                    ..
                } => {
                    let kind = if *theorem {
                        Kind::Theorem
                    } else if *instance {
                        Kind::Instance
                    } else if *synonym {
                        Kind::Type
                    } else {
                        Kind::Definition
                    };
                    let function =
                        kind == Kind::Definition && matches!(ty, Expr::Pi { .. } | Expr::Arrow(..));
                    self.entries.push(Entry {
                        path: format!("{prefix}{}", name.text),
                        kind,
                        file,
                        name_at: name.span.start,
                        start,
                        header: header(text, tokens, &group, first, kind),
                        container: None,
                        function,
                    });
                }
                Decl::Data {
                    name,
                    ctors,
                    record,
                    interface,
                    ..
                } => {
                    let kind = if *interface {
                        Kind::Interface
                    } else {
                        Kind::Type
                    };
                    let container = self.entries.len();
                    let path = format!("{prefix}{}", name.text);
                    self.entries.push(Entry {
                        path: path.clone(),
                        kind,
                        file,
                        name_at: name.span.start,
                        start,
                        header: header(text, tokens, &group, first, kind),
                        container: None,
                        function: false,
                    });
                    for ctor in ctors {
                        let members: Vec<(&str, u32, Kind)> = if *record {
                            (ctor.fields.iter())
                                .flat_map(|b| &b.names)
                                .map(|n| (n.text.as_str(), n.span.start, Kind::Field))
                                .collect()
                        } else {
                            vec![(
                                ctor.name.text.as_str(),
                                ctor.name.span.start,
                                Kind::Constructor,
                            )]
                        };
                        for (member, at, kind) in members {
                            self.add_member(file, text, &path, container, member, at, kind);
                        }
                    }
                }
                Decl::Ability { name, ops, .. } => {
                    let container = self.entries.len();
                    let path = format!("{prefix}{}", name.text);
                    self.entries.push(Entry {
                        path: path.clone(),
                        kind: Kind::Ability,
                        file,
                        name_at: name.span.start,
                        start,
                        header: header(text, tokens, &group, first, Kind::Ability),
                        container: None,
                        function: false,
                    });
                    for (op, _) in ops {
                        let (name, at) = (op.text.as_str(), op.span.start);
                        self.add_member(file, text, &path, container, name, at, Kind::Operation);
                    }
                }
                Decl::Test { name, .. } => self.tests.push(TestDecl {
                    description: name.clone(),
                    file,
                    start,
                    source: source(),
                }),
                Decl::Equation { .. } => {}
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn add_member(
        &mut self,
        file: usize,
        text: &str,
        container_path: &str,
        container: usize,
        name: &str,
        at: u32,
        kind: Kind,
    ) {
        // The line the member is on, if it has it to itself: that is how it
        // is shown. One sharing a line shows its name.
        let line = line_at(text, at);
        let begin = text[..at as usize].rfind('\n').map_or(0, |i| i + 1);
        let first_here = text[begin..at as usize]
            .chars()
            .all(|c| c.is_whitespace() || matches!(c, '|' | ',' | '{' | '('));
        let rest = line.trim_start_matches(|c: char| c.is_whitespace() || "|,{(".contains(c));
        let alone = first_here && line.starts_with(char::is_whitespace) && !rest.contains(" | ");
        let header = if alone {
            (rest.trim_end().trim_end_matches([',', '}']))
                .trim_end()
                .to_string()
        } else {
            name.to_string()
        };
        self.entries.push(Entry {
            path: format!("{container_path}.{name}"),
            kind,
            file,
            name_at: at,
            start: at,
            header,
            container: Some(container),
            function: false,
        });
    }

    pub fn entry(&self, i: usize) -> &Entry {
        &self.entries[i]
    }

    /// The line of `at` in file `file`, from 1.
    fn line_of(&self, file: usize, at: u32) -> usize {
        self.files[file].lines.partition_point(|&l| l <= at)
    }

    /// Where the declaration is: its file as shown, and the line of its
    /// keyword (of its name, for a member).
    pub fn location(&self, i: usize) -> (String, usize) {
        let e = &self.entries[i];
        (
            self.files[e.file].display.clone(),
            self.line_of(e.file, e.start),
        )
    }

    /// The doc of a declaration, read from its file's comments.
    pub fn doc(&self, i: usize) -> Option<Doc> {
        let e = &self.entries[i];
        let mut cache = self.docs.borrow_mut();
        let file = &self.files[e.file];
        let docs = cache
            .entry(e.file)
            .or_insert_with(|| docs(file.id, &self.sources.get(file.id).text));
        docs.get(&e.name_at).cloned()
    }

    /// The namespace of file `file`: a library folder's, or a program's
    /// `namespace` line's.
    fn file_namespace(&self, file: usize) -> Option<String> {
        let file = &self.files[file];
        let text = &self.sources.get(file.id).text;
        file_doc_namespace(file.id, text, file.std.as_deref())
            .or_else(|| file.namespace.clone().filter(|_| file.std.is_none()))
    }

    /// The links of `doc`, which is in file `file`, and what each names (§7,
    /// D2153): a name in the file's namespace, a full name, or a library
    /// name without `Std.`, or a name the file's `import` lines bring in
    /// (read from the syntax, as `doc` doesn't elaborate, D2152: SW-1045).
    pub fn links(&self, file: usize, doc: &Doc) -> Vec<LinkReport> {
        let namespace = self.file_namespace(file);
        let mut cache = self.imports.borrow_mut();
        let f = &self.files[file];
        let imports = cache
            .entry(file)
            .or_insert_with(|| file_imports(f.id, &self.sources.get(f.id).text));
        doc.links
            .iter()
            .map(|link| {
                let mut report = LinkReport {
                    text: link.name.clone(),
                    status: "unresolved",
                    target: None,
                    file: None,
                    line: None,
                };
                let hit = link_candidates_with_imports(&link.name, namespace.as_deref(), imports)
                    .into_iter()
                    .find(|c| self.by_path.contains_key(c) || self.is_namespace(c));
                if let Some(path) = hit {
                    match self.by_path.get(&path).map(Vec::as_slice) {
                        Some([i]) => {
                            let (file, line) = self.location(*i);
                            report.status = "resolved";
                            report.file = Some(file);
                            report.line = Some(line);
                        }
                        Some(_) => {
                            report.status = "ambiguous";
                            return report;
                        }
                        None => report.status = "resolved",
                    }
                    report.target = Some(path);
                }
                report
            })
            .collect()
    }

    /// The names a user may write for `name`: as written, without `Std.`,
    /// or as `import N (..)` sees it for each namespace of the program.
    fn candidates(&self, name: &str) -> Vec<String> {
        let mut out = vec![name.to_string()];
        if !name.starts_with("Std.") {
            out.push(format!("Std.{name}"));
        }
        out.extend(self.project.iter().map(|ns| format!("{ns}.{name}")));
        out.dedup();
        out
    }

    /// What `name` is (§5.3): a declaration, a namespace, or both.
    pub fn resolve(&self, name: &str) -> Resolution {
        let mut found = Resolution::default();
        for candidate in self.candidates(name) {
            if let Some(entries) = self.by_path.get(&candidate) {
                for &i in entries {
                    if !found.entries.contains(&i) {
                        found.entries.push(i);
                    }
                }
            }
            if self.is_namespace(&candidate) && !found.namespaces.contains(&candidate) {
                found.namespaces.push(candidate);
            }
        }
        found
    }

    /// Whether `ns` is a namespace with something to show.
    fn is_namespace(&self, ns: &str) -> bool {
        self.namespaces.contains(ns)
            && (!self.members_of(ns).is_empty() || !self.file_docs(ns).is_empty())
    }

    /// The names that look like `name`: those whose last component contains
    /// its last component, shortest first (what `doc` offers for a name it
    /// can't find).
    pub fn closest(&self, name: &str) -> Vec<usize> {
        let last = name.rsplit('.').next().unwrap_or(name).to_lowercase();
        let mut found: Vec<usize> = (0..self.entries.len())
            .filter(|&i| {
                let e = &self.entries[i];
                !last.is_empty() && !e.path.contains('%') && {
                    let l = e.path.rsplit('.').next().unwrap_or_default();
                    l.to_lowercase().contains(&last)
                }
            })
            .collect();
        found.sort_by_key(|&i| {
            let e = &self.entries[i];
            let l = e.path.rsplit('.').next().unwrap_or_default().len();
            (l, e.path.clone())
        });
        found.truncate(10);
        found
    }

    /// The declarations a namespace lists: definitions, types, interfaces
    /// and abilities, in file order, in source order.
    fn members_of(&self, ns: &str) -> Vec<usize> {
        let project = self.project.contains(ns);
        (0..self.entries.len())
            .filter(|&i| {
                let e = &self.entries[i];
                let file = &self.files[e.file];
                e.kind.is_listed()
                    && !e.path.contains('%')
                    && if project {
                        file.namespace.as_deref() == Some(ns)
                    } else {
                        file.std.is_some()
                            && e.path
                                .strip_prefix(ns)
                                .is_some_and(|rest| rest.starts_with('.'))
                    }
            })
            .collect()
    }

    /// The docs of the files of a namespace (§4): a program's files with its
    /// `namespace` line, a library folder's files.
    fn file_docs(&self, ns: &str) -> Vec<FileDoc> {
        let mut out = Vec::new();
        for file in &self.files {
            let text = &self.sources.get(file.id).text;
            let owner = file_doc_namespace(file.id, text, file.std.as_deref())
                .or_else(|| file.namespace.clone().filter(|_| file.std.is_none()));
            if owner.as_deref() != Some(ns) {
                continue;
            }
            if let Some(doc) = file_doc(file.id, text) {
                out.push(FileDoc {
                    file: file.display.clone(),
                    doc: doc.text,
                    marker: stitchwort_syntax::docs::DOC_MARKER,
                });
            }
        }
        out
    }

    /// A namespace's listing (§5.3).
    pub fn namespace(&self, ns: &str) -> NamespaceReport {
        NamespaceReport {
            namespace: ns.to_string(),
            file_docs: self.file_docs(ns),
            members: (self.members_of(ns).into_iter())
                .map(|i| self.member(i))
                .collect(),
        }
    }

    /// A declaration as a line of a listing.
    fn member(&self, i: usize) -> Member {
        let e = &self.entries[i];
        let (file, line) = self.location(i);
        let doc = self.doc(i);
        Member {
            name: e.path.clone(),
            kind: e.kind.name(),
            header: Some(e.header.clone()),
            file,
            line,
            summary: doc.map(|d| d.summary),
        }
    }

    /// The examples of declaration `i` (§5.4, D2144): the `test`s whose
    /// description names it, and the `…Example` theorems named after it.
    fn examples(&self, i: usize, within: &Within) -> Vec<Example> {
        self.example_decls(i, within, true)
            .into_iter()
            .map(|x| Example {
                kind: x.kind,
                name: x.name,
                line: self.line_of(x.file, x.start),
                file: self.files[x.file].display.clone(),
                source: x.source,
            })
            .collect()
    }

    /// [`Decls::examples`] as found; `with_source` false leaves each
    /// source empty (counting examples doesn't need it).
    fn example_decls(&self, i: usize, within: &Within, with_source: bool) -> Vec<ExampleDecl> {
        let e = &self.entries[i];
        let allowed = |file: usize| {
            let f = &self.files[file];
            match &f.namespace {
                _ if f.std.is_some() => within.std,
                Some(ns) => {
                    within.project && within.namespaces.as_ref().is_none_or(|s| s.contains(ns))
                }
                None => within.project,
            }
        };
        let mut found: Vec<ExampleDecl> = Vec::new();
        let components: Vec<&str> = e.path.split('.').collect();
        let qualified: Vec<String> = (0..components.len().saturating_sub(1))
            .map(|k| components[k..].join("."))
            .collect();
        let last = components.last().copied().unwrap_or_default();
        for t in &self.tests {
            if !allowed(t.file) {
                continue;
            }
            let d = t.description.as_str();
            let qualified_match = qualified.iter().any(|q| {
                d == q
                    || d.strip_prefix(q.as_str())
                        .is_some_and(|rest| rest.starts_with([' ', ',', ':']))
            });
            let bare_match = e.function && d == last && t.file == e.file;
            if qualified_match || bare_match {
                found.push(ExampleDecl {
                    kind: "test",
                    name: d.to_string(),
                    file: t.file,
                    start: t.start,
                    source: t.source.clone(),
                });
            }
        }
        if matches!(e.kind, Kind::Definition | Kind::Theorem) {
            for (j, other) in self.entries.iter().enumerate() {
                if other.kind != Kind::Theorem || !allowed(other.file) {
                    continue;
                }
                let Some(rest) = other.path.strip_prefix(&e.path) else {
                    continue;
                };
                let Some(digits) = rest.strip_prefix("Example") else {
                    continue;
                };
                if digits.chars().all(|c| c.is_ascii_digit()) {
                    found.push(ExampleDecl {
                        kind: "theorem",
                        name: other.path.clone(),
                        file: other.file,
                        start: other.start,
                        source: if with_source {
                            self.source_of(j)
                        } else {
                            String::new()
                        },
                    });
                }
            }
        }
        found.sort_by_key(|x| (x.file, x.start));
        found
    }

    /// The source of a declaration: from its keyword to the end of its
    /// last line (its proof included).
    fn source_of(&self, i: usize) -> String {
        let e = &self.entries[i];
        let file = &self.files[e.file];
        let text = &self.sources.get(file.id).text;
        let tokens = lex_recovering(file.id, text).tokens;
        let groups = decl_ranges(&tokens).unwrap_or_default();
        match group_of(&tokens, &groups, e.start) {
            Some(group) => text[e.start as usize..group_end(&tokens, &group)].to_string(),
            None => e.header.clone(),
        }
    }

    /// The report for declaration `i`: everything but the elaborated type
    /// and the theorems, which the caller adds if it checked.
    pub fn report(&self, i: usize, within: &Within) -> Report {
        let e = &self.entries[i];
        let (file, line) = self.location(i);
        let doc = self.doc(i);
        let members: Vec<Member> = (0..self.entries.len())
            .filter(|&j| self.entries[j].container == Some(i))
            .map(|j| self.member(j))
            .collect();
        Report {
            version: 1,
            name: e.path.clone(),
            kind: e.kind.name(),
            header: Some(e.header.clone()),
            ty: None,
            file,
            line,
            import: import_line(&e.path, self.files[e.file].namespace.as_deref()),
            container: e.container.map(|c| self.entries[c].path.clone()),
            summary: doc.as_ref().map(|d| d.summary.clone()),
            doc_marker: doc.as_ref().map(|_| stitchwort_syntax::docs::DOC_MARKER),
            links: doc
                .as_ref()
                .map(|d| self.links(e.file, d))
                .unwrap_or_default(),
            doc: doc.map(|d| d.text),
            members,
            examples: self.examples(i, within),
            theorems: None,
            equations: None,
            namespace: None,
            warnings: Vec::new(),
        }
    }

    /// A match, for the list of several or of the closest.
    pub fn found(&self, i: usize) -> Found {
        let e = &self.entries[i];
        let (file, line) = self.location(i);
        Found {
            name: e.path.clone(),
            kind: e.kind.name(),
            file,
            line,
        }
    }

    /// The program's namespace of declaration `i`; `None` for the library's.
    pub fn namespace_of(&self, i: usize) -> Option<&str> {
        self.files[self.entries[i].file].namespace.as_deref()
    }

    /// Whether declaration `i` is the library's.
    pub fn is_std(&self, i: usize) -> bool {
        self.files[self.entries[i].file].std.is_some()
    }
}

/// The import line that brings a declaration into scope as written without
/// `Std.` (as `search` shows it): `import Std (List)`, or `import Lib
/// (Range)` for a program's `Lib.Range.size`.
fn import_line(path: &str, namespace: Option<&str>) -> Option<String> {
    // A built-in is always in scope, and `Builtins.sw` only documents it
    // (SW-1146): no import brings it in (SW-1148).
    if let Some(name) = path.strip_prefix("Std.")
        && stitchwort_elab::is_builtin(name)
    {
        return None;
    }
    let (ns, rest) = match (path.strip_prefix("Std."), namespace) {
        (Some(rest), None) => ("Std", rest),
        (_, Some(ns)) => (ns, path.strip_prefix(&format!("{ns}."))?),
        _ => return None,
    };
    let first = rest.split('.').next()?;
    Some(format!("import {ns} ({first})"))
}

/// The line of `text` that `at` is on, without its newline.
fn line_at(text: &str, at: u32) -> &str {
    let at = (at as usize).min(text.len());
    let begin = text[..at].rfind('\n').map_or(0, |i| i + 1);
    let end = text[at..].find('\n').map_or(text.len(), |i| at + i);
    &text[begin..end]
}

/// The group of tokens (`decl_ranges`) the declaration at byte `at` is in.
fn group_of(
    tokens: &[Token],
    groups: &[std::ops::Range<usize>],
    at: u32,
) -> Option<std::ops::Range<usize>> {
    let i = groups.partition_point(|g| tokens[g.start].span.start <= at);
    groups.get(i.checked_sub(1)?).cloned()
}

/// The first token of the declaration in a group: after its attributes.
fn first_token(tokens: &[Token], group: &std::ops::Range<usize>) -> Option<usize> {
    let mut i = group.start;
    // `@[name args]`: an `@` and its brackets.
    while i < group.end && tokens[i].tok == Tok::At {
        let mut depth = 0;
        i += 1;
        while i < group.end {
            match tokens[i].tok {
                Tok::LBracket => depth += 1,
                Tok::RBracket => depth -= 1,
                _ => {}
            }
            i += 1;
            if depth <= 0 {
                break;
            }
        }
    }
    (i < group.end).then_some(i)
}

/// Where a group's last token ends.
fn group_end(tokens: &[Token], group: &std::ops::Range<usize>) -> usize {
    tokens[group.end - 1].span.end as usize
}

/// A declaration as written, up to `:=` or its first equation (a
/// definition, a theorem), `=` (a type, an interface) or `where` (an
/// ability).
fn header(
    text: &str,
    tokens: &[Token],
    group: &std::ops::Range<usize>,
    first: usize,
    kind: Kind,
) -> String {
    let mut depth = 0i32;
    let mut end = group.end;
    for (i, t) in tokens.iter().enumerate().take(group.end).skip(first) {
        match &t.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace => depth -= 1,
            _ if depth > 0 || i == first => {}
            Tok::ColonEq if matches!(kind, Kind::Definition | Kind::Theorem | Kind::Instance) => {
                end = i;
                break;
            }
            Tok::Pipe if t.line_start && !matches!(kind, Kind::Type | Kind::Interface) => {
                end = i;
                break;
            }
            Tok::Equals if matches!(kind, Kind::Type | Kind::Interface) => {
                end = i;
                break;
            }
            Tok::KwWhere if kind == Kind::Ability => {
                end = i;
                break;
            }
            _ => {}
        }
    }
    let to = tokens[end.max(first + 1) - 1].span.end as usize;
    text[tokens[first].span.start as usize..to].to_string()
}

/// The words of a name's last component, lower-cased: `filterMapAppend` is
/// `filter`, `map`, `append`.
fn words(name: &str) -> Vec<String> {
    let last = name.rsplit('.').next().unwrap_or(name);
    let chars: Vec<char> = last.chars().collect();
    let mut out: Vec<String> = Vec::new();
    for (i, &c) in chars.iter().enumerate() {
        if matches!(c, '_' | '\'' | '%') {
            out.push(String::new());
            continue;
        }
        let new = out.last().is_none_or(String::is_empty)
            || (c.is_uppercase()
                && i > 0
                && (!chars[i - 1].is_uppercase()
                    || chars.get(i + 1).is_some_and(|n| n.is_lowercase())));
        if new {
            out.push(String::new());
        }
        out.last_mut().expect("a word").extend(c.to_lowercase());
    }
    out.retain(|w| !w.is_empty());
    out
}

/// Whether theorem `theorem` is named after `target` (§5.5): its last
/// component contains the target's as whole camel-case words, whatever the
/// case of the first letter.
pub fn named_after(theorem: &str, target: &str) -> bool {
    let (t, x) = (words(theorem), words(target));
    !x.is_empty() && t.windows(x.len()).any(|w| w == x.as_slice())
}

// ---- The report --------------------------------------------------------

/// The JSON contract of `doc` for a declaration, version 1 (§5.3).
#[derive(Serialize, Debug)]
pub struct Report {
    pub version: u32,
    pub name: String,
    pub kind: &'static str,
    /// The declaration as written, up to `:=` or its first equation.
    pub header: Option<String>,
    /// The elaborated type; absent when `doc` didn't check (D2152) or the
    /// declaration has none to show.
    #[serde(rename = "type", skip_serializing_if = "Option::is_none")]
    pub ty: Option<String>,
    pub file: String,
    pub line: usize,
    pub import: Option<String>,
    /// For a constructor, field or operation: what it belongs to.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub container: Option<String>,
    pub doc: Option<String>,
    pub summary: Option<String>,
    #[serde(rename = "docMarker")]
    pub doc_marker: Option<&'static str>,
    /// The links in the doc (`--|` docs only), in the order written.
    pub links: Vec<LinkReport>,
    /// A type's constructors or fields, an interface's fields, an ability's
    /// operations.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub members: Vec<Member>,
    pub examples: Vec<Example>,
    /// `null` when not asked for (`--theorems 0`) or not a definition's.
    pub theorems: Option<Theorems>,
    /// The generated equations of a definition with arms, and what wasn't
    /// generated (function-equations §3.4); absent for the others.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub equations: Option<Equations>,
    /// A name that is a type and a namespace: the namespace's listing.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub namespace: Option<NamespaceReport>,
    pub warnings: Vec<String>,
}

/// A doc link and what it names (§7).
#[derive(Serialize, Debug)]
pub struct LinkReport {
    /// The name written between the backticks.
    pub text: String,
    /// `resolved`, `unresolved` or `ambiguous`.
    pub status: &'static str,
    /// The full name of what it names; `null` unless resolved.
    pub target: Option<String>,
    /// Where the target is declared; `null` for a namespace or no target.
    pub file: Option<String>,
    pub line: Option<usize>,
}

/// A doc's text with its links printed as their names: a link that names
/// nothing, or more than one thing, is marked.
fn linked(doc: &str, links: &[LinkReport]) -> String {
    let mut links = links.iter();
    let mut out = String::new();
    for (n, line) in doc.lines().enumerate() {
        if n > 0 {
            out.push('\n');
        }
        let mut at = 0;
        for (start, end, name) in link_ranges(line) {
            out.push_str(&line[at..start]);
            out.push_str(&format!("`{name}`"));
            match links.next().map(|l| l.status) {
                Some("unresolved") => out.push_str(" (unresolved link)"),
                Some("ambiguous") => out.push_str(" (ambiguous link)"),
                _ => {}
            }
            at = end;
        }
        out.push_str(&line[at..]);
    }
    out
}

/// A line of a listing: a member of a type, or a declaration of a namespace.
#[derive(Serialize, Debug)]
pub struct Member {
    pub name: String,
    pub kind: &'static str,
    /// As written (a member's line, a declaration's header).
    pub header: Option<String>,
    pub file: String,
    pub line: usize,
    pub summary: Option<String>,
}

#[derive(Serialize, Debug)]
pub struct Example {
    /// `test` or `theorem`.
    pub kind: &'static str,
    pub name: String,
    pub file: String,
    pub line: usize,
    pub source: String,
}

/// A namespace's file docs, then its declarations (§5.3).
#[derive(Serialize, Debug)]
pub struct NamespaceReport {
    pub namespace: String,
    #[serde(rename = "fileDocs")]
    pub file_docs: Vec<FileDoc>,
    pub members: Vec<Member>,
}

#[derive(Serialize, Debug)]
pub struct FileDoc {
    pub file: String,
    pub doc: String,
    #[serde(rename = "docMarker")]
    pub marker: &'static str,
}

/// A name that is several declarations or namespaces: the matches, or with
/// none the closest names.
#[derive(Serialize, Debug)]
pub struct Matches {
    pub version: u32,
    pub matches: Vec<Found>,
    /// Namespaces the name is, besides.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub namespaces: Vec<String>,
    /// With no match: names that look like it.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub closest: Vec<Found>,
}

#[derive(Serialize, Debug)]
pub struct Found {
    pub name: String,
    pub kind: &'static str,
    pub file: String,
    pub line: usize,
}

/// The theorems about a declaration (§5.5).
#[derive(Serialize, Debug)]
pub struct Theorems {
    /// How many mention it.
    pub total: usize,
    /// The first `--theorems N` of them, by group and then by search's rank.
    pub shown: Vec<TheoremJson>,
    /// The `search` command that lists all of them.
    pub command: String,
}

/// The equations generated for a definition's arms, and the ones that
/// weren't (function-equations §3.4).
#[derive(Serialize, Debug)]
pub struct Equations {
    /// How many were generated, not counting `f.induct`.
    pub total: usize,
    /// The first of them, in the order of the arms.
    pub shown: Vec<EquationJson>,
    /// `f.induct` (stage 2a), when it was generated: not an equation, so
    /// neither counted in `total` nor in `shown`.
    pub induct: Option<EquationJson>,
    /// The implied equations that weren't generated, with the reason.
    pub skipped: Vec<SkippedEquation>,
    /// The `search` command that lists all of them.
    pub command: String,
}

#[derive(Serialize, Debug)]
pub struct EquationJson {
    pub name: String,
    /// The statement without the leading parameters that only later ones use.
    pub statement: String,
    /// The line of the arm it came from.
    pub line: usize,
    pub file: String,
    /// The left side doesn't compute: `rewrite` can use the equation, where
    /// for the others the goal has already computed the call (§7.3).
    pub stuck: bool,
}

#[derive(Serialize, Debug)]
pub struct SkippedEquation {
    pub name: String,
    pub reason: String,
}

/// How many equations `doc` lists before counting the rest.
const EQUATIONS_SHOWN: usize = 16;

#[derive(Serialize, Debug)]
pub struct TheoremJson {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    /// The statement without the leading parameters that only later ones
    /// use, as the text shows it.
    pub statement: String,
    pub file: String,
    pub line: usize,
    pub summary: Option<String>,
    /// `rewrite`, `named` or `other`.
    pub group: &'static str,
}

// ---- Theorems and the elaborated type ----------------------------------

impl Session {
    /// The full name's elaborated type, if the session has it: a
    /// definition's or theorem's, a constructor's.
    pub fn declared_type(&self, path: &str) -> Option<String> {
        let g = &self.elab.ev();
        let ty = match def_named(g, path) {
            Some(id) => g.def(id).ty().clone(),
            None => {
                let (data, ctor) = path.rsplit_once('.')?;
                let d = (0..g.env.datas().len())
                    .map(DataId)
                    .find(|d| &**g.data(*d).path() == data)?;
                let c = g.data(d).ctors().iter().position(|c| &*c.name == ctor)?;
                stitchwort_elab::search::Item::Ctor(d, c).ty(g)
            }
        };
        Some(stitchwort_core::pretty::term(g, &[], &ty))
    }

    /// The theorems whose statement mentions `path`, a definition (§5.5):
    /// found by `search`, `…Example` theorems left out, grouped (`rewrite`,
    /// `named`, `other`) and capped at `cap`. `within` are the namespaces
    /// looked in (empty: all); `command_extra` is added to the command that
    /// lists all of them. A file's names are searched as the file writes
    /// them, so if `path` doesn't elaborate, `bare` (without its namespace)
    /// is tried.
    pub fn theorems_about(
        &mut self,
        path: &str,
        bare: Option<&str>,
        within: &[String],
        scope: &Scope,
        cap: usize,
        command_extra: &str,
    ) -> Result<(Theorems, Vec<String>), stitchwort_syntax::Diagnostic> {
        let options = Options {
            kinds: Kinds {
                theorems: true,
                definitions: false,
                constructors: false,
            },
            limit: usize::MAX,
            within: within.to_vec(),
            ..Options::default()
        };
        let (query, report) = match self.search(path, &options, scope) {
            Ok(report) => (path, report),
            Err(d) => match bare {
                Some(bare) => (bare, self.search(bare, &options, scope).map_err(|_| d)?),
                None => return Err(d),
            },
        };
        let g = &self.elab.ev();
        let target = def_named(g, path);
        let iff = (0..g.env.datas().len())
            .map(DataId)
            .find(|d| &**g.data(*d).path() == "Std.Iff");
        let mut seen = BTreeSet::new();
        let mut groups: [Vec<TheoremJson>; 3] = Default::default();
        for r in &report.results {
            let last = r.name.rsplit('.').next().unwrap_or_default();
            let example = last
                .trim_end_matches(|c: char| c.is_ascii_digit())
                .ends_with("Example");
            // Generated equations have their own section.
            if example || r.generated || !seen.insert(r.name.clone()) {
                continue;
            }
            let ty = def_named(g, &r.name).map(|id| g.def(id).ty().clone());
            let named = named_after(&r.name, path);
            let group = match (&ty, target) {
                (Some(ty), Some(x)) if named && rewrites(ty, x, iff) => 0,
                _ if named => 1,
                _ => 2,
            };
            let statement = match &ty {
                Some(ty) => statement(g, ty),
                None => r.ty.clone(),
            };
            groups[group].push(TheoremJson {
                name: r.name.clone(),
                ty: r.ty.clone(),
                statement,
                file: r.file.clone(),
                line: r.line,
                summary: r.summary.clone(),
                group: ["rewrite", "named", "other"][group],
            });
        }
        let total: usize = groups.iter().map(Vec::len).sum();
        let shown: Vec<TheoremJson> = groups.into_iter().flatten().take(cap).collect();
        let name = query.strip_prefix("Std.").unwrap_or(query);
        let command = format!(
            "stitchwort search '{name}' --theorems --limit {}{command_extra}",
            report.total.max(total)
        );
        Ok((
            Theorems {
                total,
                shown,
                command,
            },
            report.warnings,
        ))
    }
}

impl Session {
    /// The equations generated for definition `path`'s arms, and the implied
    /// ones that weren't (function-equations §3.4); `None` for a definition
    /// with neither. The library's and the core's are made on demand, so
    /// this makes them first. `command_extra` is added to the `search`
    /// command that lists all of them.
    pub fn equations_of(
        &mut self,
        path: &str,
        command_extra: &str,
    ) -> Result<Option<Equations>, stitchwort_syntax::Diagnostic> {
        self.elab.generate_deferred_equations()?;
        let g = &self.elab.ev();
        let Some(f) = def_named(g, path) else {
            return Ok(None);
        };
        // `f.eq2`, `f.eq2.or1`: the owner's path, then the reserved suffix.
        let found = generated_equations(g).remove(path).unwrap_or_default();
        let transparent_tree =
            def_named(g, &format!("{path}.%step")).is_none() && !g.def(f).opaque();
        let shown_name = |p: &str| shown(p).to_string();
        let mut induct = None;
        let mut equations: Vec<EquationJson> = Vec::new();
        for (_, id) in &found {
            let json = {
                let d = g.def(*id);
                let (file, line) = crate::render::location(&self.sources, d.span());
                EquationJson {
                    name: shown_name(d.path()),
                    statement: statement(g, d.ty()),
                    line,
                    file,
                    stuck: !stitchwort_elab::is_function_induct(g, d.name())
                        && (!transparent_tree || has_overlap_hypothesis(d.ty())),
                }
            };
            if stitchwort_elab::is_function_induct(g, g.def(*id).name()) {
                induct = Some(json);
            } else {
                equations.push(json);
            }
        }
        // What the source implies and elaboration skipped, once for each
        // suffix (the latest reason), unless it was made since.
        let mut skipped: Vec<SkippedEquation> = Vec::new();
        for (owner, suffix, why) in self.elab.equation_skips().iter().rev() {
            if *owner != f || g.def(*owner).path().as_ref() != path {
                continue;
            }
            let name = format!("{path}.{suffix}");
            if def_named(g, &name).is_some() || skipped.iter().any(|s| s.name == shown_name(&name))
            {
                continue;
            }
            skipped.push(SkippedEquation {
                name: shown_name(&name),
                reason: why.clone(),
            });
        }
        skipped.reverse();
        if equations.is_empty() && induct.is_none() && skipped.is_empty() {
            return Ok(None);
        }
        let name = path.strip_prefix("Std.").unwrap_or(path);
        let command = format!(
            "stitchwort search '{name}' --theorems --limit {}{command_extra}",
            found.len().max(EQUATIONS_SHOWN)
        );
        let total = equations.len();
        Ok(Some(Equations {
            total,
            shown: equations.into_iter().take(EQUATIONS_SHOWN).collect(),
            induct,
            skipped,
            command,
        }))
    }
}

/// Every generated equation made so far, by its definition's full path, in
/// the order of the arms (`f.eq2` before `f.eq2.or1` before `f.eq3`).
pub(crate) fn generated_equations(g: &Ev) -> BTreeMap<String, Vec<(Vec<usize>, DefId)>> {
    let mut by_owner: BTreeMap<String, Vec<(Vec<usize>, DefId)>> = BTreeMap::new();
    let generated = crate::audit::Generated::new(g);
    for id in (0..g.env.defs().len()).map(DefId) {
        let d = g.def(id);
        // Not the hidden lemmas branches use (`f.%match1.eq2`).
        if !d.theorem() || !generated.contains(g, id) || d.path().contains('%') {
            continue;
        }
        // The owner is what precedes the first `.eqK` (or `.eq`, below a
        // `:=` body: `gcd.eq.ifTrue`).
        let mut at = 0;
        let mut owner_end = None;
        // `f.induct`, before the equations (stage 2a): listed first, never cut.
        if stitchwort_elab::is_function_induct(g, d.name())
            && let Some(owner) = d.path().strip_suffix(".induct")
        {
            by_owner
                .entry(owner.to_string())
                .or_default()
                .push((Vec::new(), id));
            continue;
        }
        let parts = d.path().split('.').count();
        for (i, part) in d.path().split('.').enumerate() {
            let digits = part.strip_prefix("eq");
            if at > 0
                && digits.is_some_and(|n| {
                    (!n.is_empty() || i + 1 < parts) && n.bytes().all(|b| b.is_ascii_digit())
                })
            {
                owner_end = Some(at - 1);
                break;
            }
            at += part.len() + 1;
        }
        let Some(end) = owner_end else { continue };
        let order = d.path()[end + 1..]
            .split('.')
            .map(|p| p.trim_start_matches(|c: char| c.is_ascii_alphabetic()))
            .filter_map(|n| n.parse().ok())
            .collect();
        by_owner
            .entry(d.path()[..end].to_string())
            .or_default()
            .push((order, id));
    }
    for list in by_owner.values_mut() {
        list.sort();
    }
    by_owner
}

/// A definition's generated equations as hover shows them: the count and
/// the first few (function-equations §3.4), in markdown.
pub(crate) fn equations_hover(g: &Ev, ids: &[(Vec<usize>, DefId)]) -> String {
    const HOVER_SHOWN: usize = 4;
    // `f.induct`, listed first, isn't an equation: not counted (SW-1073).
    let inducts = (ids.iter())
        .filter(|(_, id)| stitchwort_elab::is_function_induct(g, g.def(*id).name()))
        .count();
    let and_induct = if inducts > 0 { " and `f.induct`" } else { "" };
    let mut out = format!(
        "Equations ({}){and_induct}, listed by `stitchwort doc`:",
        ids.len() - inducts
    );
    for (_, id) in ids.iter().take(HOVER_SHOWN) {
        let d = g.def(*id);
        out.push_str(&format!("\n- `{}`: `{}`", d.name(), statement(g, d.ty())));
    }
    if ids.len() > HOVER_SHOWN {
        out.push_str(&format!("\n- … and {} more", ids.len() - HOVER_SHOWN));
    }
    out
}

/// Whether `ty`, an equation's statement, takes an overlap hypothesis
/// (`notArm1`, `notListed`, …): its left side then has a variable where an
/// earlier arm has a pattern, so the call doesn't compute (§7.3).
fn has_overlap_hypothesis(ty: &Term) -> bool {
    // A branch's (`f.eq2.ifTrue`, `f.eq.some`): a hypothesis or a lifted
    // `match`'s pattern variable is a parameter its left side doesn't
    // mention, and the call is stuck on the condition it stands for.
    let mut n = 0;
    let mut t = ty.strip_loc();
    while let Term::Pi(_, _, _, cod) = t {
        n += 1;
        t = cod.strip_loc();
    }
    if let Term::Eq(_, lhs, _) = t
        && (0..n).any(|ix| !lhs.mentions(ix))
    {
        return true;
    }
    let mut t = ty.strip_loc();
    while let Term::Pi(name, _, _, cod) = t {
        if let Some(rest) = name.strip_prefix("not")
            && ["Arm", "Alt", "Or", "Listed"]
                .iter()
                .any(|p| rest.starts_with(p))
        {
            return true;
        }
        t = cod.strip_loc();
    }
    false
}

/// The definition with full name `path`.
fn def_named(g: &Ev, path: &str) -> Option<DefId> {
    (0..g.env.defs().len())
        .map(DefId)
        .find(|id| &**g.def(*id).path() == path)
}

/// Whether `ty`, after its parameters, is an equation or an `Iff` whose left
/// side is headed by definition `x`.
fn rewrites(ty: &Term, x: DefId, iff: Option<DataId>) -> bool {
    let mut t = ty.strip_loc();
    while let Term::Pi(_, _, _, cod) = t {
        t = cod.strip_loc();
    }
    let lhs = match t {
        Term::Eq(_, lhs, _) => lhs,
        Term::Data(d, args) if Some(*d) == iff && args.len() == 2 => &args[0],
        _ => return false,
    };
    matches!(lhs.spine().0, Term::Def(d) if *d == x)
}

/// A theorem's statement without its leading parameters that only later ones
/// use (`[a: Type] → (xs: List a) → …`): the premises and the conclusion.
fn statement(g: &Ev, ty: &Term) -> String {
    let mut names = Vec::new();
    let mut t = ty.strip_loc();
    while let Term::Pi(name, _, _, cod) = t
        && cod.mentions(0)
    {
        names.push(name.clone());
        t = cod.strip_loc();
    }
    stitchwort_core::pretty::term(g, &names, t)
}

// ---- Text --------------------------------------------------------------

/// `Std.List.map` as a user writes it: without `Std.`.
fn shown(path: &str) -> &str {
    path.strip_prefix("Std.").unwrap_or(path)
}

/// A declaration's text: the first lines, as `doc` prints them.
pub fn render_text(r: &Report, show_theorems: bool) -> String {
    let mut out = String::new();
    out.push_str(&format!("{}  {}\n", r.name, r.kind));
    if let Some(container) = &r.container {
        out.push_str(&format!("  in {container}\n"));
    }
    if let Some(header) = &r.header {
        for line in header.lines() {
            out.push_str(&format!("  {line}\n"));
        }
    }
    let import = (r.import.as_ref())
        .map(|i| format!("  ({i})"))
        .unwrap_or_default();
    out.push_str(&format!("  {}:{}{import}\n", r.file, r.line));
    out.push('\n');
    match &r.doc {
        Some(doc) => {
            for line in linked(doc, &r.links).lines() {
                if line.is_empty() {
                    out.push('\n');
                } else {
                    out.push_str(&format!("  {line}\n"));
                }
            }
        }
        None => out.push_str("  (no doc)\n"),
    }
    if !r.members.is_empty() {
        out.push_str("\nMembers:\n");
        for m in &r.members {
            let header = m.header.as_deref().unwrap_or(&m.name);
            match &m.summary {
                Some(s) => out.push_str(&format!("  {header}\n      {s}\n")),
                None => out.push_str(&format!("  {header}\n")),
            }
        }
    }
    out.push('\n');
    if r.examples.is_empty() {
        if matches!(r.kind, "definition" | "theorem") {
            out.push_str(&format!(
                "Examples: none (a `test \"{}\"` or `theorem {}Example` would be one)\n",
                shown(&r.name),
                shown(&r.name)
            ));
        } else {
            out.push_str("Examples: none\n");
        }
    } else {
        out.push_str("Examples:\n");
        for e in &r.examples {
            let lines: Vec<&str> = e.source.lines().collect();
            if lines.len() == 1 {
                out.push_str(&format!("  {}     {}:{}\n", lines[0], e.file, e.line));
            } else {
                for line in lines.iter().take(6) {
                    out.push_str(&format!("  {line}\n"));
                }
                if lines.len() > 6 {
                    out.push_str("  …\n");
                }
                out.push_str(&format!("    ({}:{})\n", e.file, e.line));
            }
        }
    }
    if show_theorems && let Some(q) = &r.equations {
        out.push('\n');
        out.push_str(&render_equations(q));
    }
    if show_theorems && let Some(t) = &r.theorems {
        out.push('\n');
        let verb = if t.total == 1 { "mentions" } else { "mention" };
        if t.total == 0 {
            out.push_str("Theorems: none mention it\n");
        } else if t.total > t.shown.len() {
            out.push_str(&format!(
                "Theorems: {} {verb} it; {} shown\n",
                t.total,
                t.shown.len()
            ));
        } else {
            out.push_str(&format!("Theorems: {} {verb} it\n", t.total));
        }
        let width = t.shown.iter().map(|x| shown(&x.name).len()).max();
        for x in &t.shown {
            out.push_str(&format!(
                "  {:width$}  {}\n",
                shown(&x.name),
                x.statement,
                width = width.unwrap_or(0)
            ));
        }
        if t.total > t.shown.len() {
            out.push_str(&format!("  all {}: {}\n", t.total, t.command));
        }
    }
    if let Some(ns) = &r.namespace {
        out.push('\n');
        out.push_str(&render_namespace(ns));
    }
    for w in &r.warnings {
        out.push_str(&format!("warning: {w}\n"));
    }
    out
}

/// The Equations section: the generated equations with the line of their
/// arm, the stuck ones marked, then what wasn't generated.
fn render_equations(q: &Equations) -> String {
    let mut out = String::new();
    let verb = if q.total == 1 {
        "equation"
    } else {
        "equations"
    };
    // `f.induct` isn't an equation: named beside the count (SW-1073).
    let and_induct = if q.induct.is_some() {
        " and f.induct"
    } else {
        ""
    };
    if q.total == 0 && q.induct.is_none() {
        out.push_str("Equations: none generated\n");
    } else if q.total == 0 {
        out.push_str("Equations: none generated; f.induct\n");
    } else if q.total > q.shown.len() {
        out.push_str(&format!(
            "Equations: {} generated {verb}{and_induct}; {} shown\n",
            q.total,
            q.shown.len()
        ));
    } else {
        out.push_str(&format!(
            "Equations: {} generated {verb}{and_induct}\n",
            q.total
        ));
    }
    let listed: Vec<&EquationJson> = q.induct.iter().chain(&q.shown).collect();
    let width = listed.iter().map(|x| x.name.len()).max().unwrap_or(0);
    for x in listed {
        let stuck = if x.stuck { "  [stuck]" } else { "" };
        out.push_str(&format!(
            "  {:width$}  {}{stuck}   ({}:{})\n",
            x.name, x.statement, x.file, x.line
        ));
    }
    if q.total > q.shown.len() {
        out.push_str(&format!("  all {}: {}\n", q.total, q.command));
    }
    if q.shown.iter().any(|x| x.stuck) {
        out.push_str(
            "  [stuck]: the left side doesn't compute (an overlap hypothesis, a branch's \
             condition, or a `decreasing` or `opaque` definition), so `rewrite` uses the \
             equation; the others state what \
             the goal has already computed, which `rfl` proves\n",
        );
    }
    if !q.skipped.is_empty() {
        out.push_str("Not generated:\n");
        for s in &q.skipped {
            out.push_str(&format!("  {}  {}\n", s.name, s.reason));
        }
    }
    out
}

/// A namespace's file docs, then its declarations with their summaries,
/// grouped by file.
pub fn render_namespace(ns: &NamespaceReport) -> String {
    let mut out = format!("namespace {}\n", ns.namespace);
    for d in &ns.file_docs {
        out.push_str(&format!("\n{}\n", d.file));
        for line in d.doc.lines() {
            if line.is_empty() {
                out.push('\n');
            } else {
                out.push_str(&format!("  {line}\n"));
            }
        }
    }
    let width = ns.members.iter().map(|m| shown(&m.name).len()).max();
    let mut file = None;
    for m in &ns.members {
        if file != Some(&m.file) {
            out.push_str(&format!("\n{}\n", m.file));
            file = Some(&m.file);
        }
        let summary = m.summary.as_deref().unwrap_or("");
        out.push_str(
            format!(
                "  {:width$}  {:10}  {summary}\n",
                shown(&m.name),
                m.kind,
                width = width.unwrap_or(0)
            )
            .trim_end(),
        );
        out.push('\n');
    }
    if ns.members.is_empty() {
        out.push_str("\n(no definitions, types, interfaces or abilities)\n");
    }
    out
}

/// The matches of an ambiguous name, or the closest names to one that
/// isn't found.
pub fn render_matches(name: &str, m: &Matches) -> String {
    let mut out = String::new();
    let list = |out: &mut String, found: &[Found]| {
        let width = found
            .iter()
            .map(|f| shown(&f.name).len())
            .max()
            .unwrap_or(0);
        for f in found {
            out.push_str(&format!(
                "  {:width$}  {:11}  {}:{}\n",
                shown(&f.name),
                f.kind,
                f.file,
                f.line
            ));
        }
    };
    if m.matches.is_empty() && m.namespaces.is_empty() {
        out.push_str(&format!(
            "error: no declaration or namespace named `{name}`\n"
        ));
        if !m.closest.is_empty() {
            out.push_str("names that look like it:\n");
            list(&mut out, &m.closest);
        }
    } else {
        out.push_str(&format!(
            "`{name}` is more than one name: write one in full\n"
        ));
        list(&mut out, &m.matches);
        for ns in &m.namespaces {
            out.push_str(&format!("  {ns}  namespace\n"));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_are_after_a_name_by_whole_words() {
        assert!(named_after(
            "Std.List.filterMapAppend",
            "Std.List.filterMap"
        ));
        assert!(named_after(
            "Std.List.memFilterMapElim",
            "Std.List.filterMap"
        ));
        assert!(named_after("Std.List.lengthMap", "Std.List.map"));
        assert!(named_after("Std.List.filterMapSome", "Std.List.map"));
        assert!(!named_after("Std.List.mapping", "Std.List.map"));
        assert!(!named_after("Std.Char.toTextDigits", "Std.List.filterMap"));
        assert!(named_after("Std.Nat.addComm", "Std.Nat.add"));
        assert!(!named_after("Std.Nat.addrOf", "Std.Nat.add"));
    }

    #[test]
    fn every_header_is_a_declaration_up_to_its_body() {
        let decls = Decls::new(Vec::new());
        for e in &decls.entries {
            let h = e.header.trim_start();
            assert!(!h.is_empty(), "{}", e.path);
            assert!(!h.starts_with('|'), "{}: {h}", e.path);
            if matches!(e.kind, Kind::Definition | Kind::Theorem | Kind::Instance) {
                // The header ends before a body, whose arms start a line at
                // the declaration's own indent (a `match` in a hypothesis is
                // inside brackets and stays).
                let last = h.lines().last().unwrap_or_default();
                assert!(!last.trim_start().starts_with('|'), "{}: {h}", e.path);
            }
        }
    }

    #[test]
    fn a_library_name_resolves_with_or_without_std() {
        let decls = Decls::new(Vec::new());
        for name in ["List.filterMap", "Std.List.filterMap"] {
            let found = decls.resolve(name);
            assert_eq!(found.entries.len(), 1, "{name}");
            let e = decls.entry(found.entries[0]);
            assert_eq!(e.path, "Std.List.filterMap");
            assert_eq!(e.kind, Kind::Definition);
            assert!(e.header.starts_with("def List.filterMap:"), "{}", e.header);
            assert!(!e.header.contains('|'), "{}", e.header);
        }
        // A type that is a namespace too.
        let list = decls.resolve("List");
        assert_eq!(list.entries.len(), 1);
        assert_eq!(list.namespaces, ["Std.List"]);
    }
}
