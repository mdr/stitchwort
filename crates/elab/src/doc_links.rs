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

use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{Import, Module};
use stitchwort_syntax::docs::{DocLink, link_candidates_with_imports};

use crate::Elaborator;
use crate::module::declared_names;
use crate::project::SourceUnit;
use crate::scope::{PRELUDE, Resolved, display, edit_distance, short};

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
        let home = self.link_home();
        match self.resolve(name) {
            Resolved::Found { key, rest, .. }
                if rest.is_empty() && self.seen_by_links(key, home.as_ref()) =>
            {
                return Meaning::Found;
            }
            // A type and its constructor of the same name are one thing to
            // a reader: the link is to the type.
            Resolved::Ambiguous(keys, _) if is_type_and_constructor(&keys) => {
                return Meaning::Found;
            }
            Resolved::Ambiguous(keys, _) => return Meaning::Ambiguous(keys),
            Resolved::Found { .. } | Resolved::Missing => {}
        }
        let named = link_candidates_with_imports(name, home.as_ref().map(|h| h.ns), imports)
            .iter()
            .any(|key| self.is_known_key(key, home.as_ref()));
        if named {
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
    /// the names in the file's own namespace without it. A project
    /// namespace the file's doesn't use counts by what its files declare
    /// (SW-4836), so the answer doesn't depend on whether a check loaded
    /// it.
    fn nearest_name(&self, written: &str) -> Option<String> {
        let near = |candidate: &str| {
            let distance = edit_distance(candidate, written);
            (distance <= 2 && distance < written.chars().count()).then_some(distance)
        };
        let home = self.link_home();
        let own = home.as_ref().map(|h| format!("{}.", h.ns));
        let mut best: Option<(usize, String)> = None;
        let mut consider = |key: &str| {
            if key.contains('%') || short(key).is_empty() {
                return;
            }
            let shown = if near(display(key)).is_some() {
                display(key)
            } else if let Some(rest) = own.as_deref().and_then(|p| key.strip_prefix(p))
                && near(rest).is_some()
            {
                rest
            } else {
                return;
            };
            let distance = edit_distance(shown, written);
            let better = match &best {
                None => true,
                Some((d, s)) => (distance, shown.len(), shown) < (*d, s.len(), s.as_str()),
            };
            if better {
                best = Some((distance, shown.to_string()));
            }
        };
        let unused = |ns: &str| home.as_ref().is_some_and(|h| !h.uses(ns));
        for key in self.scope.keys() {
            if !self.project_owner(key).is_some_and(unused) {
                consider(key);
            }
        }
        if home.is_some() {
            for (ns, keys) in self.session.project_declared.iter() {
                if unused(ns) {
                    keys.iter().for_each(|key| consider(key));
                }
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
            .find(|key| self.is_known_key(key, None))
    }

    /// Where the doc links being worked out are: the namespace being
    /// checked, if it is a project's, and what it uses.
    fn link_home(&self) -> Option<Home<'_>> {
        Some(Home {
            ns: self.unit.module.namespace.as_deref()?,
            closure: self.unit.module.closure.as_deref().unwrap_or(&[]),
        })
    }

    /// The project namespace whose declaration `key` is: the longest whose
    /// name and a `.` start it.
    fn project_owner<'k>(&self, key: &'k str) -> Option<&'k str> {
        let mut end = key.len();
        while let Some(dot) = key[..end].rfind('.') {
            if self.session.project_namespaces.contains(&key[..dot]) {
                return Some(&key[..dot]);
            }
            end = dot;
        }
        None
    }

    /// Whether `key`, which a lookup found, counts for the links of
    /// `home`: any key of the library's or of a namespace `home` uses, and
    /// another project namespace's only if its files declare it
    /// ([`crate::project::declared_in`]), whether or not it is loaded.
    fn seen_by_links(&self, key: &str, home: Option<&Home>) -> bool {
        match self.project_owner(key) {
            Some(ns) if home.is_some_and(|h| !h.uses(ns)) => {
                self.declares(ns, key) || is_lemma_key(key)
            }
            _ => true,
        }
    }

    /// Whether project namespace `ns`'s files declare `key`, or a key
    /// under it (`key` is then a namespace, a type's say).
    fn declares(&self, ns: &str, key: &str) -> bool {
        self.session.project_declared.get(ns).is_some_and(|keys| {
            keys.contains(key)
                || keys
                    .iter()
                    .any(|k| k.strip_prefix(key).is_some_and(|r| r.starts_with('.')))
        })
    }

    /// Whether `key` is declared, or is a namespace, for the links of
    /// `home`. A project namespace `home` doesn't use counts by what its
    /// files declare, loaded or not: so a link doesn't depend on the order
    /// namespaces are checked in, nor on which a check loads (SW-4827),
    /// and adds no dependency. Without a `home` (`doc`, the index), what
    /// is loaded counts too.
    fn is_known_key(&self, key: &str, home: Option<&Home>) -> bool {
        if self.session.project_prefixes.contains(key) {
            return true;
        }
        if let Some(ns) = self.project_owner(key) {
            return self.declares(ns, key)
                || ((home.is_none_or(|h| h.uses(ns)) || is_lemma_key(key))
                    && (self.scope.get(key).is_some() || self.scope.is_namespace(key)));
        }
        self.scope.get(key).is_some()
            || self.scope.is_namespace(key)
            || self.session.core_link_names.as_ref().is_some_and(|index| {
                index.owner(key).is_some()
                    || index
                        .names()
                        .any(|(k, _)| k.strip_prefix(key).is_some_and(|r| r.starts_with('.')))
            })
    }
}

/// The namespace whose doc links are worked out, and the namespaces it
/// uses: loaded before its links are, whatever else a check loads.
struct Home<'a> {
    ns: &'a str,
    closure: &'a [String],
}

impl Home<'_> {
    fn uses(&self, ns: &str) -> bool {
        self.ns == ns || self.closure.iter().any(|c| c == ns)
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

/// Whether `key` may be an equation lemma or an induction principle that
/// elaboration makes (`f.eq2`, `f.eq3.or1.ifTrue`, `f.induct`), which a
/// file's syntax doesn't settle.
fn is_lemma_key(key: &str) -> bool {
    crate::equations::reserved_suffix(key).is_some()
}

/// Whether `keys` are a type's and its own constructor's (`T`, `T.T`).
fn is_type_and_constructor(keys: &[String]) -> bool {
    let [a, b] = keys else {
        return false;
    };
    let (outer, inner) = if a.len() < b.len() { (a, b) } else { (b, a) };
    inner.strip_prefix(outer.as_str()) == Some(&format!(".{}", short(outer)))
}

impl Elaborator {
    /// Whether no doc link of project namespace `ns` (its files'
    /// `modules`, using the namespaces `closure`) warns when `ns` is
    /// replayed from its cache entry, as far as can be told without
    /// loading anything (SW-4827): what lets a plain `check` leave a
    /// namespace with doc links out.
    ///
    /// A link [`Self::doc_link_warnings`] finds is one that names
    /// something and isn't ambiguous. Named: one of its candidates is known
    /// now ([`Self::is_known_key`]: the library's index, the core, and the
    /// project's namespaces by what their files declare, none of which
    /// loading takes away), or it is a short name the defaults find once
    /// (`Some`). Ambiguous: a replay applies no imports, so a name with a
    /// qualifier can't be (its qualifier is looked up without
    /// constructors, at most one key at each level), and a short name only
    /// if two of the constructors and declarations `ns` declares at its
    /// root have it, or failing those, two of the prelude's and the library
    /// root's constructors (as the lookup goes level by level, the first
    /// with any decides). A type and its own constructor of the same name
    /// count as one. Anything else, such as a local definition (`t.go`)
    /// or a link that names nothing, says no, and the namespace is loaded
    /// as before.
    pub fn doc_links_resolve_unloaded(
        &self,
        ns: &str,
        closure: &[String],
        modules: &[&Module],
    ) -> bool {
        let home = Home { ns, closure };
        for module in modules {
            for link in &module.doc_links {
                let short = !link.name.contains('.');
                let found = if short {
                    self.short_link_lookup(&link.name, ns, modules)
                } else {
                    Lookup::Missing
                };
                if matches!(found, Lookup::Ambiguous) {
                    return false;
                }
                let candidates =
                    link_candidates_with_imports(&link.name, Some(ns), &module.imports);
                let named = matches!(found, Lookup::Found)
                    || (candidates.iter()).any(|key| self.is_known_key(key, Some(&home)));
                if !named || candidates.iter().any(|key| is_lemma_key(key)) {
                    return false;
                }
            }
        }
        true
    }

    /// The project namespaces other than `ns` and those it uses (`closure`)
    /// whose equation lemmas a doc link of `ns`'s files `modules` may name
    /// (`Other.f.eq2`). Such a lemma counts by what is loaded
    /// ([`crate::project::declared_in`] can't list them), so a plain
    /// `check` that leaves namespaces out loads these whenever it loads
    /// `ns`, as a check that loads everything does.
    pub fn doc_link_lemma_owners(
        &self,
        ns: &str,
        closure: &[String],
        modules: &[&Module],
    ) -> Vec<String> {
        let home = Home { ns, closure };
        let mut out: Vec<String> = Vec::new();
        for module in modules {
            for link in &module.doc_links {
                for key in link_candidates_with_imports(&link.name, Some(ns), &module.imports) {
                    if is_lemma_key(&key)
                        && let Some(owner) = self.project_owner(&key)
                        && !home.uses(owner)
                        && !out.iter().any(|o| o == owner)
                    {
                        out.push(owner.to_string());
                    }
                }
            }
        }
        out
    }

    /// What the short name `x`, written in namespace `ns` (its files'
    /// `modules`), may find in a replay of `ns`: see
    /// [`Self::doc_links_resolve_unloaded`]. `Found` only for one of the
    /// defaults, which a replay surely finds; `Missing` when it may find
    /// nothing, or one of `ns`'s own (the candidates say whether that
    /// counts).
    fn short_link_lookup(&self, x: &str, ns: &str, modules: &[&Module]) -> Lookup {
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
        if !own.is_empty() {
            return if own.len() > 1 && !is_type_and_constructor(&own) {
                Lookup::Ambiguous
            } else {
                Lookup::Missing
            };
        }
        let found = self.scope.default_candidates(x);
        match found.as_slice() {
            [] => Lookup::Missing,
            [key] if self.default_surely_visible(key, ns) => Lookup::Found,
            [_] => Lookup::Missing,
            _ if is_type_and_constructor(&found) => Lookup::Missing,
            _ => Lookup::Ambiguous,
        }
    }

    /// Whether `key`, the one default a short link may find, is surely
    /// found in a replay of `ns`: a prelude name, or a constructor of a
    /// prelude type whose short name `ns` doesn't declare itself (which
    /// would hide the type, and so its constructors).
    fn default_surely_visible(&self, key: &str, ns: &str) -> bool {
        let Some(owner) = key.strip_prefix("Std.") else {
            return false;
        };
        let ty = match owner.rsplit_once('.') {
            None => return PRELUDE.contains(&owner),
            Some((ty, _)) => ty,
        };
        PRELUDE.contains(&ty)
            && self.scope.std_root_key(ty) == Some(&format!("Std.{ty}"))
            && !self.declares(ns, &format!("{ns}.{ty}"))
    }
}

/// What [`Elaborator::short_link_lookup`] tells.
enum Lookup {
    Found,
    Ambiguous,
    Missing,
}
