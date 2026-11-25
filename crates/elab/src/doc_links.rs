//! `W-DOC-LINK` (docs/proposals/documentation.md §7, D2149, D2153): a doc
//! link, ``[`Name`]`` in a `--|` comment, that names nothing or names more
//! than one thing.
//!
//! Links are resolved once a namespace is checked, as its file resolves
//! names (its imports and namespace), so a link may point forward, or at the
//! declaration it is on. Failing that, a full name (`Std.List.map`), a
//! library name without `Std.` (`List.map`) or a name in the file's own
//! namespace resolves, whatever the file imports, so a link never forces an
//! `import`. A link adds no dependency: nothing here is read by the check
//! cache's key. So the warnings are not cached (SW-1045): they are worked
//! out again each time, after a namespace is checked or replayed, against the
//! names as they are now. A file's `import` lines count by their syntax
//! (`link_candidates_with_imports`), as they do in `doc` and the index, since
//! a replayed namespace has not had its imports applied. A plain `check`
//! that would replay a namespace only for its links leaves it out when
//! they surely all resolve (`doc_links_resolve_unloaded`, SW-4827).

use stitchwort_core::collections::HashSet;
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{Decl, Import, Module};
use stitchwort_syntax::docs::{DocLink, link_candidates_with_imports};

use crate::Elaborator;
use crate::module::declared_names;
use crate::project::SourceUnit;
use crate::scope::{Resolved, display, edit_distance, short};

pub(crate) const CODE: &str = "W-DOC-LINK";

/// What a link means.
enum Meaning {
    Found,
    Ambiguous(Vec<String>),
    Missing,
}

impl Elaborator {
    /// The warnings for the doc links of a module's files, each in the
    /// context of its file, in source order. Run once every declaration of
    /// the module is checked.
    pub(crate) fn doc_link_warnings(&mut self, files: &[SourceUnit]) -> Vec<Diagnostic> {
        let mut out = Vec::new();
        for (file, unit) in files.iter().enumerate() {
            if unit.module.doc_links.is_empty() {
                continue;
            }
            let saved = self.unit.module.file.replace(file);
            for link in &unit.module.doc_links {
                match self.link_meaning(&link.name, &unit.module.imports) {
                    Meaning::Found => {}
                    Meaning::Ambiguous(keys) => out.push(
                        Diagnostic::warning(
                            CODE,
                            format!("the doc link `{}` is ambiguous", link.name),
                        )
                        .with_label(link.span, "this link")
                        .with_note(format!(
                            "it could be {}; write the full name",
                            keys.iter()
                                .map(|k| format!("`{}`", display(k)))
                                .collect::<Vec<_>>()
                                .join(" or ")
                        )),
                    ),
                    Meaning::Missing => out.push(self.unresolved_link(link)),
                }
            }
            self.unit.module.file = saved;
        }
        out
    }

    fn link_meaning(&self, name: &str, imports: &[Import]) -> Meaning {
        match self.resolve(name) {
            Resolved::Found { rest, .. } if rest.is_empty() => return Meaning::Found,
            // A type and its constructor of the same name are one thing to
            // a reader: the link is to the type.
            Resolved::Ambiguous(keys, _) if is_type_and_constructor(&keys) => {
                return Meaning::Found;
            }
            Resolved::Ambiguous(keys, _) => return Meaning::Ambiguous(keys),
            Resolved::Found { .. } | Resolved::Missing => {}
        }
        if self
            .doc_link_target(name, self.unit.module.namespace.as_deref(), imports)
            .is_some()
        {
            Meaning::Found
        } else {
            Meaning::Missing
        }
    }

    fn unresolved_link(&self, link: &DocLink) -> Diagnostic {
        let mut d =
            Diagnostic::warning(CODE, format!("the doc link `{}` names nothing", link.name))
                .with_label(link.span, "no such declaration or namespace");
        if let Some(near) = self.nearest_name(&link.name) {
            d = d.with_note(format!("did you mean `{near}`?"));
        }
        d
    }

    /// The name closest to `written` (within two edits), as it would be
    /// written in a link: among the keys' library names without `Std.`, and
    /// the names in the file's own namespace without it.
    fn nearest_name(&self, written: &str) -> Option<String> {
        let near = |candidate: &str| {
            let distance = edit_distance(candidate, written);
            (distance <= 2 && distance < written.chars().count()).then_some(distance)
        };
        let own = self
            .unit
            .module
            .namespace
            .as_deref()
            .map(|ns| format!("{ns}."));
        let mut best: Option<(usize, String)> = None;
        for key in self.scope.keys() {
            if key.contains('%') || short(key).is_empty() {
                continue;
            }
            let shown = if near(display(key)).is_some() {
                display(key)
            } else if let Some(rest) = own.as_deref().and_then(|p| key.strip_prefix(p))
                && near(rest).is_some()
            {
                rest
            } else {
                continue;
            };
            let distance = edit_distance(shown, written);
            let better = match &best {
                None => true,
                Some((d, s)) => (distance, shown.len(), shown) < (*d, s.len(), s.as_str()),
            };
            if better {
                best = Some((distance, shown.to_string()));
            }
        }
        best.map(|(_, name)| name)
    }

    /// What a doc link `name` means, through the file's `imports` if given
    /// (as `doc` and the index show it): the full name of the declaration or
    /// namespace it names, trying `namespace` (the namespace of the file the doc is in),
    /// then the name as written, then the library's. `None` if it names
    /// nothing.
    pub fn doc_link_target(
        &self,
        name: &str,
        namespace: Option<&str>,
        imports: &[Import],
    ) -> Option<String> {
        link_candidates_with_imports(name, namespace, imports)
            .into_iter()
            .find(|key| self.is_known_key(key))
    }

    /// Whether `key` is declared, or is a namespace, or is declared in a
    /// project namespace that isn't checked yet (the pre-pass has its names):
    /// so a link doesn't depend on the order namespaces are checked in, and
    /// adds no dependency.
    fn is_known_key(&self, key: &str) -> bool {
        self.scope.get(key).is_some()
            || self.scope.is_namespace(key)
            || self.session.project_prefixes.contains(key)
            || self.session.core_link_names.as_ref().is_some_and(|index| {
                index.owner(key).is_some()
                    || index
                        .names()
                        .any(|(k, _)| k.strip_prefix(key).is_some_and(|r| r.starts_with('.')))
            })
            || key
                .rsplit_once('.')
                .is_some_and(|(ns, name)| self.project_names(ns).is_some_and(|n| n.contains(name)))
    }
}

impl Elaborator {
    /// Makes the library's names known to doc links while the core is
    /// checked (`None` afterwards): the core's docs may link to library
    /// declarations, which aren't loaded yet (documentation.md §7: a name
    /// defined anywhere in std counts).
    pub fn set_core_link_names(&mut self, index: Option<std::sync::Arc<crate::LibraryIndex>>) {
        self.session.core_link_names = index;
    }
}

/// Whether `keys` are a type's and its own constructor's (`T`, `T.T`).
fn is_type_and_constructor(keys: &[String]) -> bool {
    let [a, b] = keys else {
        return false;
    };
    let (outer, inner) = if a.len() < b.len() { (a, b) } else { (b, a) };
    inner.strip_prefix(outer.as_str()) == Some(&format!(".{}", short(outer)))
}

/// The keys the declarations of namespace `ns`'s files `modules` put in
/// scope that a doc link may name, as far as their syntax tells: each
/// declaration's own, its constructors, operations and interface methods,
/// and a record's fields. A declaration written with a qualifier
/// (`Rules.rule`, or a function for another namespace's type) has the key
/// `ns.` and the name as written, unless the qualifier is an import's
/// local name for something else (`import N (T as U)`), whose keys are
/// left out. For [`Elaborator::doc_links_resolve_unloaded`]; a key
/// may be missing from here, never wrongly present, in a namespace that
/// checks.
pub fn declared_keys(ns: &str, modules: &[&Module]) -> HashSet<String> {
    let mut out = HashSet::default();
    for module in modules {
        let renamed: HashSet<&str> = (module.imports.iter())
            .flat_map(|i| &i.items)
            .filter(|item| item.local().text != item.name.text)
            .map(|item| item.local().text.as_str())
            .collect();
        for decl in &module.decls {
            let (Some(main), members) = declared_names(decl) else {
                continue;
            };
            let key = format!("{ns}.{}", main.text);
            if let Some((first, _)) = main.text.split_once('.') {
                if !renamed.contains(first) {
                    out.insert(key);
                }
                continue;
            }
            for (member, _) in &members {
                if !member.text.starts_with('%') {
                    out.insert(format!("{key}.{}", member.text));
                }
            }
            if let Decl::Data {
                ctors,
                record: true,
                ..
            } = decl
            {
                for field in ctors.iter().flat_map(|c| &c.fields) {
                    out.insert(format!("{key}.{}", field.name.text));
                }
            }
            out.insert(key);
        }
    }
    out
}

impl Elaborator {
    /// Whether no doc link of project namespace `ns` (its files'
    /// `modules`) warns when `ns` is replayed from its cache entry, as far
    /// as can be told without loading anything (SW-4827): what lets a
    /// plain `check` leave a namespace with doc links out. `declared` says
    /// whether a key is declared by a namespace `ns` uses
    /// ([`declared_keys`] of theirs, which it may work out only when
    /// asked); those are loaded before `ns` whatever else is.
    ///
    /// A link [`Self::doc_link_warnings`] finds is one that names
    /// something and isn't ambiguous. Named: one of its candidates is known
    /// now, from the library's index, the core, the project's namespaces
    /// and the pre-pass's names, all of which loading only adds to, or is
    /// declared in `ns` or a namespace it uses. Ambiguous: a replay applies
    /// no imports, so a name with a qualifier can't be (its qualifier is
    /// looked up without constructors, at most one key at each level), and
    /// a short name only if two of the constructors and declarations
    /// `ns` declares at its root have it, or failing those, two of the
    /// prelude's and the library root's constructors (as the lookup goes
    /// level by level, the first with any decides). A type and its own
    /// constructor of the same name count as one. Anything else, such as a
    /// local definition (`t.go`), an instance, a function another
    /// namespace adds to a type, or a link that names nothing, says no, and
    /// the namespace is loaded as before.
    pub fn doc_links_resolve_unloaded(
        &self,
        ns: &str,
        modules: &[&Module],
        declared: &mut dyn FnMut(&str) -> bool,
    ) -> bool {
        let own = declared_keys(ns, modules);
        for module in modules {
            for link in &module.doc_links {
                let named = link_candidates_with_imports(&link.name, Some(ns), &module.imports)
                    .iter()
                    .any(|key| self.is_known_key(key) || own.contains(key) || declared(key));
                if !named
                    || (!link.name.contains('.') && self.may_be_ambiguous(&link.name, ns, modules))
                {
                    return false;
                }
            }
        }
        true
    }

    /// Whether the short name `x`, written in namespace `ns` (its files'
    /// `modules`), may resolve to two different things in a replay of
    /// `ns`: see [`Self::doc_links_resolve_unloaded`].
    fn may_be_ambiguous(&self, x: &str, ns: &str, modules: &[&Module]) -> bool {
        let mut own: Vec<String> = Vec::new();
        for decl in modules.iter().flat_map(|m| &m.decls) {
            let (Some(main), members) = declared_names(decl) else {
                continue;
            };
            if main.text.contains('.') {
                continue;
            }
            if main.text == x {
                own.push(format!("{ns}.{x}"));
            }
            for (member, follower) in &members {
                if *follower && member.text == x {
                    own.push(format!("{ns}.{}.{x}", main.text));
                }
            }
        }
        let found = if own.is_empty() {
            self.scope.default_candidates(x)
        } else {
            own
        };
        found.len() > 1 && !is_type_and_constructor(&found)
    }
}
