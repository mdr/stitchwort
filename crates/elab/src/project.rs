//! The pieces of a module that is more than one file, and of a project of
//! several modules (docs/proposals/multi-file.md §4.4, §4.6): the files
//! [`Elaborator::elaborate_namespace`] takes, and the pre-pass that finds
//! which namespaces a namespace uses.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use stitchwort_syntax::ast::{Decl, Module};
use stitchwort_syntax::{FileId, Span};

use crate::Elaborator;
use crate::module::{Ref, decl_refs};
use crate::scope::{Qualifier, QualifierLevels, STD, WildcardSource, import_target, qualifier};

/// One file of a module: its display name (project-relative path, for
/// messages) and its syntax.
pub struct SourceUnit<'a> {
    /// `None` only from `elaborate_module`, which isn't told its file.
    pub file: Option<FileId>,
    pub name: &'a str,
    pub module: &'a Module,
}

/// What a single file loaded from inside a project needs to know to say
/// why it can't use the project (`E-FILE-MODE`,
/// docs/proposals/multi-file.md §4.3, §7).
#[derive(Clone, Debug)]
pub struct FileModeContext {
    /// The file's display name.
    pub file: String,
    /// What's being done to it: "run", "checked", "tested" or "built".
    pub verb: &'static str,
    /// The project's name.
    pub project: String,
    /// The project's namespaces.
    pub namespaces: std::collections::BTreeSet<String>,
    /// The file's own namespace, if it has a namespace line: a name in it
    /// is the file's, not the project's.
    pub own: Option<String>,
    /// What to do instead.
    pub note: String,
}

impl FileModeContext {
    /// The namespace of the project that `path` is, or starts with (by
    /// components), if any: the longest.
    fn namespace_of(&self, path: &str) -> Option<&str> {
        self.namespaces
            .iter()
            .filter(|ns| path == ns.as_str() || path.starts_with(&format!("{ns}.")))
            .max_by_key(|ns| ns.len())
            .map(String::as_str)
    }

    /// `E-FILE-MODE` for the name or path `written` at `span`, if it is of
    /// the project.
    pub(crate) fn diagnostic(
        &self,
        written: &str,
        span: Span,
    ) -> Option<stitchwort_syntax::Diagnostic> {
        let namespace = self.namespace_of(written)?;
        if self.own.as_deref() == Some(namespace) {
            return None;
        }
        Some(
            stitchwort_syntax::Diagnostic::error(
                "E-FILE-MODE",
                format!(
                    "`{}` is {} as a single file, so it can use only the standard library",
                    self.file, self.verb
                ),
            )
            .with_label(
                span,
                format!(
                    "`{namespace}` is a namespace of the project {}/",
                    self.project
                ),
            )
            .with_note(self.note.clone()),
        )
    }
}

/// A namespace's files, as syntax.
pub struct NamespaceSyntax<'a> {
    pub name: String,
    pub files: Vec<SourceUnit<'a>>,
}

/// A use of another namespace: which, and the first place that uses it.
#[derive(Clone, Debug)]
pub struct Edge {
    pub target: String,
    pub span: Span,
}

impl Elaborator {
    /// Tells the elaborator which namespaces the project has (call before
    /// the pre-pass and before checking).
    pub fn set_project_namespaces(&mut self, names: impl IntoIterator<Item = String>) {
        self.project_namespaces = names.into_iter().collect();
        self.project_prefixes = self
            .project_namespaces
            .iter()
            .flat_map(|name| {
                name.match_indices('.')
                    .map(|(i, _)| name[..i].to_string())
                    .chain(std::iter::once(name.clone()))
                    .collect::<Vec<_>>()
            })
            .collect();
    }

    /// What `import N (..)` brings from each project namespace (call after
    /// [`Self::set_project_namespaces`], before the pre-pass and checking).
    /// A namespace whose files didn't parse has no entry.
    pub fn set_project_names(&mut self, names: BTreeMap<String, BTreeSet<String>>) {
        self.project_names = names;
    }

    /// What the project pre-pass says `import N (..)` brings from namespace
    /// `ns`, if its files parsed.
    pub fn project_names(&self, ns: &str) -> Option<&BTreeSet<String>> {
        self.project_names.get(ns)
    }

    /// The project namespaces `ns` uses directly, each with the first place
    /// (by file, then position) that uses it. Never `ns` itself. Sorted by
    /// target.
    pub fn namespace_edges(&self, ns: &NamespaceSyntax) -> Vec<Edge> {
        // What each file of the namespace declares and imports.
        let mut declared: HashSet<&str> = HashSet::new();
        // Qualified declarations: the first component of the written name,
        // and the file.
        let mut qualified: Vec<(&str, usize)> = Vec::new();
        for (f, unit) in ns.files.iter().enumerate() {
            for decl in &unit.module.decls {
                let text = written(decl);
                if text.is_empty() {
                    continue;
                }
                match text.split_once('.') {
                    None => {
                        declared.insert(text);
                    }
                    Some((first, _)) => qualified.push((first, f)),
                }
            }
        }
        let imported: Vec<HashSet<&str>> = ns
            .files
            .iter()
            .map(|unit| {
                unit.module
                    .imports
                    .iter()
                    .flat_map(|i| i.items.iter().map(|n| n.text.as_str()))
                    .collect()
            })
            .collect();

        // What each file's `(..)` imports bring: read like checking does,
        // from the import's path (found without any imports) and the same
        // names routine. A file that imports everything from a namespace
        // whose files didn't parse is blind: its names are unknown.
        let none: Vec<HashSet<String>> = Vec::new();
        let own_root = format!("{}.", ns.name);
        let mut wildcard: Vec<HashSet<String>> = vec![HashSet::new(); ns.files.len()];
        let mut blind = vec![false; ns.files.len()];
        for (f, unit) in ns.files.iter().enumerate() {
            let path_levels = PrePass {
                e: self,
                declared: &declared,
                qualified: &qualified,
                imported: &imported,
                wildcard: &none,
                file: f,
                imports: false,
                ns: &ns.name,
            };
            for import in unit
                .module
                .imports
                .iter()
                .filter(|i| i.everything.is_some())
            {
                let Some(k) = import_target(&path_levels, &import.path.text, &own_root) else {
                    continue;
                };
                match self.wildcard_source(&k, Some(&ns.name)) {
                    Some(WildcardSource::Names(names)) => wildcard[f].extend(names),
                    Some(WildcardSource::Unknown) => blind[f] = true,
                    Some(WildcardSource::Refused(_)) | None => {}
                }
            }
        }

        let mut edges: BTreeMap<String, Span> = BTreeMap::new();
        for (f, unit) in ns.files.iter().enumerate() {
            let levels = PrePass {
                e: self,
                declared: &declared,
                qualified: &qualified,
                imported: &imported,
                wildcard: &wildcard,
                file: f,
                imports: true,
                ns: &ns.name,
            };
            // An import's path is read without the file's imports.
            let path_levels = PrePass {
                imports: false,
                ..levels
            };
            let mut found = |target: String, span: Span| {
                edges.entry(target).or_insert(span);
            };
            for import in &unit.module.imports {
                let first = import.path.text.split('.').next().unwrap_or("");
                if matches!(qualifier(&path_levels, first), Qualifier::Project)
                    && let Some(q) = self.longest_namespace(&import.path.text, true)
                    && q != ns.name
                {
                    found(q, import.path.span);
                }
            }
            if blind[f] {
                continue;
            }
            for (decl, equations) in grouped(&unit.module.decls) {
                for (r, _) in decl_refs(decl, equations) {
                    let Ref::Name(n) = r else { continue };
                    let Some((first, _)) = n.text.split_once('.') else {
                        continue;
                    };
                    if matches!(qualifier(&levels, first), Qualifier::Project)
                        && let Some(q) = self.longest_namespace(&n.text, false)
                        && q != ns.name
                    {
                        found(q, n.span);
                    }
                }
            }
        }
        edges
            .into_iter()
            .map(|(target, span)| Edge { target, span })
            .collect()
    }

    /// The longest project namespace `Q` with `path == Q` (if `equal`) or
    /// `path` starting with `Q.`.
    pub(crate) fn longest_namespace(&self, path: &str, equal: bool) -> Option<String> {
        self.project_namespaces
            .iter()
            .filter(|q| (equal && q.as_str() == path) || path.starts_with(&format!("{q}.")))
            .max_by_key(|q| q.len())
            .cloned()
    }
}

/// The names `import N (..)` brings from namespace `ns`: what its files
/// declare without a qualifier (types, abilities, definitions, theorems,
/// synonyms), sorted. A qualified declaration such as `def Range.size` lands
/// under `Range`, never directly in `ns`; tests and equations declare no
/// name.
pub fn direct_names(ns: &NamespaceSyntax) -> BTreeSet<String> {
    ns.files
        .iter()
        .flat_map(|unit| unit.module.decls.iter())
        .map(written)
        .filter(|text| !text.is_empty() && !text.contains('.'))
        .map(str::to_string)
        .collect()
}

/// The text of the name a declaration declares, as written.
fn written(decl: &Decl) -> &str {
    match decl {
        Decl::Data { name, .. } | Decl::Ability { name, .. } | Decl::Signature { name, .. } => {
            &name.text
        }
        Decl::Test { .. } | Decl::Equation { .. } => "",
    }
}

/// A file's declarations, each signature with its equations.
fn grouped(decls: &[Decl]) -> Vec<(&Decl, &[Decl])> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < decls.len() {
        match &decls[i] {
            Decl::Signature { name, .. } => {
                let mut end = i + 1;
                while let Some(Decl::Equation { name: n, .. }) = decls.get(end)
                    && n.text == name.text
                {
                    end += 1;
                }
                out.push((&decls[i], &decls[i + 1..end]));
                i = end;
            }
            Decl::Equation { .. } => i += 1,
            decl => {
                out.push((decl, &decls[..0]));
                i += 1;
            }
        }
    }
    out
}

/// What the pre-pass knows about names, reading one file of a namespace
/// (docs/proposals/multi-file.md §4.6): the same routine as checking, over
/// what can be known before anything is checked.
struct PrePass<'e, 'a> {
    e: &'e Elaborator,
    /// The unqualified names the namespace declares, in any file.
    declared: &'e HashSet<&'a str>,
    /// The first component and file of each qualified declaration.
    qualified: &'e [(&'a str, usize)],
    /// The names each file imports.
    imported: &'e [HashSet<&'a str>],
    /// The names each file's `(..)` imports bring.
    wildcard: &'e [HashSet<String>],
    file: usize,
    /// Whether the file's imports count: not for an import's own path.
    imports: bool,
    /// The namespace being read.
    ns: &'e str,
}

impl PrePass<'_, '_> {
    fn short_in(&self, first: &str, file: usize) -> bool {
        self.declared.contains(first)
            || (self.imports
                && (self.imported[file].contains(first) || self.wildcard[file].contains(first)))
            || self.e.scope.is_std_root(first)
    }
}

impl QualifierLevels for PrePass<'_, '_> {
    type Short = ();

    fn short(&self, first: &str) -> Option<()> {
        self.short_in(first, self.file).then_some(())
    }

    fn own_namespace(&self, first: &str) -> bool {
        first != STD
            && !self.e.project_prefixes.contains(first)
            && !self.library_namespace(first)
            && self
                .qualified
                .iter()
                .any(|(q, file)| *q == first && !self.short_in(first, *file))
    }

    fn project_namespace(&self, first: &str) -> bool {
        self.e.project_prefixes.contains(first)
    }

    fn library_namespace(&self, first: &str) -> bool {
        self.e.scope.is_namespace(&format!("Std.{first}"))
    }

    fn short_key(&self, first: &str, _: &()) -> Option<String> {
        if self.declared.contains(first) {
            Some(format!("{}.{first}", self.ns))
        } else {
            self.e.scope.std_root_key(first).map(str::to_string)
        }
    }
}
