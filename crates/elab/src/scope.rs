//! Names (docs/proposals/namespaces.md §4): what a name written in a
//! program means.
//!
//! Every declaration has a **key**, its full name: `Std.List.length` for the
//! library's (the prelude's root is `Std`), and the path from the program's
//! root for a program's own (`area`, `Geometry.Shape.area`). A type or
//! ability owns the namespace of the same name, which holds its
//! constructors or operations, and anything declared in it.
//!
//! A short name is looked up at five levels, and the first level where it's
//! found decides (§4.4): local variables (the caller's), then the module's
//! own top-level declarations, then the file's imports by name, then what its
//! `import N (..)` bring, then the default set: what `Std` declares at its
//! root. Constructors and operations come with their
//! type or ability, at the same level, but only while that binding of their
//! type is the one visible. Two different things at one level are
//! ambiguous, which is an error only where the name is used.
//!
//! A qualified name `A.b.c` resolves `A` the same way, or as a namespace (the
//! program's, then the library's), and looks the rest up inside it. `Std.…`
//! always means the library.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use stitchwort_syntax::ast::{self, Import};
use stitchwort_syntax::{Diagnostic, Span};

use crate::{Elaborator, Global, Result, error};

/// The library's root.
pub const STD: &str = "Std";

/// Default names that are aliases of declarations in namespaces: the alias's
/// path under `Std`, and its target's (§4.6).
pub const ALIASES: &[(&str, &str)] = &[("not", "Bool.not")];

/// Which level a name was found at.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    /// Written in full, or with a qualifier.
    Qualified,
    /// The module's own top-level declarations.
    Module,
    /// This file's `import N (a, b)`.
    Import,
    /// This file's `import N (..)`.
    Wildcard,
    Default,
}

/// What a written name means. Looking a name up allocates nothing unless
/// it's qualified, ambiguous or followed by field accesses.
pub enum Resolved<'a> {
    Found {
        global: Global,
        span: Span,
        key: &'a str,
        level: Level,
        /// Components after the longest prefix that names a declaration:
        /// field accesses on it (`Origin.x`).
        rest: Vec<String>,
    },
    /// Two or more different things at the same level: their keys, and
    /// the level.
    Ambiguous(Vec<String>, Level),
    Missing,
}

/// The names the program sees, and the library's.
#[derive(Default)]
pub struct Scope {
    /// Every declaration, by key.
    pub entries: HashMap<String, (Global, Span)>,
    /// Constructors and operations, which are visible by their short names
    /// wherever their type's or ability's short name is: by short name.
    followers: HashMap<String, Vec<String>>,
    /// Every proper prefix of a key: the namespaces.
    namespaces: HashSet<String>,
    /// Each file of the current module's imports: short name to keys.
    imports: Vec<HashMap<String, Vec<(String, Span)>>>,
    /// Each file's `import N (..)`: short name to keys, each with the span
    /// of the import that brought it. Empty for a program without `(..)`.
    wildcards: Vec<BTreeMap<String, Vec<(String, Span)>>>,
    /// The files (of the current module) with a `(..)` import that failed
    /// with an error of its own, so the uses of names in them aren't
    /// reported again as unknown.
    pub(crate) wildcard_failed: BTreeSet<usize>,
    /// The names of imports that failed with an error of their own, so the
    /// uses of them aren't reported again as unknown.
    pub(crate) import_failed: HashSet<String>,
    /// What `Std` declares at its root, and its aliases: short name to key.
    std_root: HashMap<String, String>,
}

/// What the first component of a qualified name means, in order
/// (docs/proposals/multi-file.md §4.5, §4.6): `Std`; a short name (a local
/// variable is the caller's business); a namespace of the module's own; a
/// project namespace; a library namespace.
pub(crate) enum Qualifier<S> {
    Std,
    Short(S),
    Own,
    Project,
    Library,
    Missing,
}

/// The tests [`qualifier`] makes, so that checking and the project
/// analysis decide with one routine.
pub(crate) trait QualifierLevels {
    type Short;
    /// Levels 2-4 (own declarations, this file's imports, the defaults),
    /// without constructors or operations.
    fn short(&self, first: &str) -> Option<Self::Short>;
    fn own_namespace(&self, first: &str) -> bool;
    fn project_namespace(&self, first: &str) -> bool;
    fn library_namespace(&self, first: &str) -> bool;
    /// The key a short name found by `short` means, if it's known.
    fn short_key(&self, first: &str, found: &Self::Short) -> Option<String>;
}

pub(crate) fn qualifier<L: QualifierLevels>(levels: &L, first: &str) -> Qualifier<L::Short> {
    if first == STD {
        return Qualifier::Std;
    }
    if let Some(s) = levels.short(first) {
        return Qualifier::Short(s);
    }
    if levels.own_namespace(first) {
        return Qualifier::Own;
    }
    if levels.project_namespace(first) {
        return Qualifier::Project;
    }
    if levels.library_namespace(first) {
        return Qualifier::Library;
    }
    Qualifier::Missing
}

/// Checking's meaning of each test. The flag says whether this file's imports
/// count (a name being resolved), or not (an import's path, which is never
/// read through another import).
struct CheckingLevels<'e>(&'e Elaborator, bool);

impl<'e> QualifierLevels for CheckingLevels<'e> {
    type Short = Resolved<'e>;

    fn short(&self, first: &str) -> Option<Resolved<'e>> {
        match self.0.resolve_short_in(first, false, self.1) {
            Resolved::Missing => None,
            found => Some(found),
        }
    }

    fn own_namespace(&self, first: &str) -> bool {
        let key = format!("{}{first}", self.0.root());
        // A project namespace below this one is reached by its full name
        // only (nesting is by name, not by scope): it isn't "own".
        let nested = !self.0.root().is_empty() && self.0.project_prefixes.contains(&key);
        !nested && self.0.scope.is_namespace(&key)
    }

    fn project_namespace(&self, first: &str) -> bool {
        !self.0.loading_prelude && !self.0.root().is_empty() && self.0.scope.is_namespace(first)
    }

    fn library_namespace(&self, first: &str) -> bool {
        self.0.scope.is_namespace(&format!("Std.{first}"))
    }

    fn short_key(&self, _: &str, found: &Resolved<'e>) -> Option<String> {
        match found {
            Resolved::Found { key, .. } => Some(key.to_string()),
            _ => None,
        }
    }
}

/// The namespace key an import's path names, resolved like a qualifier
/// without the file's imports (docs/proposals/multi-file.md §4.5). `own_root`
/// is the file's namespace as a key prefix (`Day05.`, or nothing). `None` if
/// the path's first component names nothing. One routine for checking and the
/// project pre-pass.
pub(crate) fn import_target<L: QualifierLevels>(
    levels: &L,
    path: &str,
    own_root: &str,
) -> Option<String> {
    if path == STD {
        return Some(STD.to_string());
    }
    let (first, rest) = match path.split_once('.') {
        Some((f, r)) => (f, Some(r)),
        None => (path, None),
    };
    let base = match qualifier(levels, first) {
        Qualifier::Std => STD.to_string(),
        Qualifier::Short(found) => levels.short_key(first, &found)?,
        Qualifier::Missing => return None,
        Qualifier::Own => format!("{own_root}{first}"),
        Qualifier::Project => first.to_string(),
        Qualifier::Library => format!("Std.{first}"),
    };
    Some(match rest {
        Some(rest) => format!("{base}.{rest}"),
        None => base,
    })
}

/// What `import K (..)` brings, for a file of namespace `own` (docs/proposals/
/// multi-file.md §4.5, §4.6). Shared by checking and the project pre-pass.
pub(crate) enum WildcardSource {
    /// The short names, sorted, deduplicated.
    Names(Vec<String>),
    /// A project namespace whose files didn't parse: names unknown.
    Unknown,
    Refused(Refusal),
}

/// Why `import K (..)` is refused.
pub(crate) enum Refusal {
    /// `Std` itself.
    StdRoot,
    /// The file's own namespace.
    Own,
    /// Something inside the file's own namespace (a type, say).
    PartOfOwn,
    /// Something inside another project namespace.
    PartOf(String),
    /// Only the start of project namespace names.
    Prefix,
}

/// `key`'s last component.
pub fn short(key: &str) -> &str {
    key.rsplit('.').next().unwrap_or(key)
}

/// `key`'s namespace, if it has one.
fn parent(key: &str) -> Option<&str> {
    key.rfind('.').map(|i| &key[..i])
}

/// How a key is written from the program's root: the library's without
/// `Std.`. For messages, and for declarations' names in the kernel.
pub fn display(key: &str) -> &str {
    key.strip_prefix("Std.").unwrap_or(key)
}

impl Scope {
    /// Declares `key`. A constructor or operation is a follower.
    pub fn insert(&mut self, key: &str, global: Global, span: Span, follower: bool) {
        if !self.entries.contains_key(key) {
            let mut prefix = key;
            while let Some(p) = parent(prefix) {
                self.namespaces.insert(p.to_string());
                prefix = p;
            }
            if follower && !short(key).starts_with('%') {
                self.followers
                    .entry(short(key).to_string())
                    .or_default()
                    .push(key.to_string());
            }
            if let Some(path) = key.strip_prefix("Std.") {
                if !path.contains('.') {
                    self.std_root.insert(path.to_string(), key.to_string());
                }
                for (alias, target) in ALIASES {
                    if path == *target {
                        self.std_root.insert(alias.to_string(), key.to_string());
                    }
                }
            }
        }
        self.entries.insert(key.to_string(), (global, span));
    }

    /// The key `key` as stored, and what it names.
    fn entry(&self, key: &str) -> Option<(&str, Global, Span)> {
        self.entries
            .get_key_value(key)
            .map(|(k, (g, s))| (k.as_str(), *g, *s))
    }

    pub fn get(&self, key: &str) -> Option<(Global, Span)> {
        self.entries.get(key).copied()
    }

    pub fn is_namespace(&self, key: &str) -> bool {
        self.namespaces.contains(key)
    }

    /// Whether `x` is a name at the library's root (or an alias of one).
    pub(crate) fn is_std_root(&self, x: &str) -> bool {
        self.std_root.contains_key(x)
    }

    pub fn clear_imports(&mut self) {
        self.imports.clear();
        self.wildcards.clear();
        self.import_failed.clear();
        self.wildcard_failed.clear();
    }

    /// The key of the library's root name `x`, or of the alias.
    pub(crate) fn std_root_key(&self, x: &str) -> Option<&str> {
        self.std_root.get(x).map(String::as_str)
    }

    /// Every key, for suggestions.
    pub fn keys(&self) -> impl Iterator<Item = &String> {
        self.entries.keys()
    }
}

impl Elaborator {
    /// The current module's root, as a key prefix: `Std.` for the prelude,
    /// `Day05.` for a program in namespace `Day05`, nothing for a program
    /// without a namespace line.
    pub(crate) fn root(&self) -> &str {
        if self.loading_prelude {
            "Std."
        } else {
            &self.namespace_root
        }
    }

    /// A data type's or definition's kernel name (its key, without `Std.`)
    /// as it's written in this module: without the module's root. For source
    /// the elaborator generates itself, which is read like the program's.
    pub(crate) fn relative_to_root(&self, name: &str) -> String {
        if self.loading_prelude {
            name.to_string()
        } else {
            name.strip_prefix(self.root()).unwrap_or(name).to_string()
        }
    }

    /// The namespace of the module last elaborated (its root without the
    /// trailing `.`), if it has one.
    pub fn current_namespace(&self) -> Option<&str> {
        self.root().strip_suffix('.')
    }

    /// Whether a file's namespace line may be used: not the library's, and
    /// not starting with the name of one of the library's namespaces.
    pub fn check_namespace_name(&self, decl: &ast::NamespaceDecl) -> Result<()> {
        let first = decl.path.text.split('.').next().unwrap_or("");
        if first == STD {
            return Err(Diagnostic::error(
                "E-STD-NAMESPACE",
                "`Std` is the standard library's namespace, which a program can't add to",
            )
            .with_label(decl.path.span, "`Std` always means the standard library")
            .with_note("choose another name for this file's namespace"));
        }
        if first == "Main" {
            return Err(Diagnostic::error(
                "E-NAMESPACE-RESERVED",
                "`Main` is the name of a file without a namespace line",
            )
            .with_label(decl.path.span, "`Main` is reserved")
            .with_note("choose another name for this file's namespace"));
        }
        let std = format!("Std.{first}");
        if self.scope.get(&std).is_some() || self.scope.is_namespace(&std) {
            return Err(Diagnostic::error(
                "E-NAMESPACE-RESERVED",
                format!("`{first}` is a namespace of the standard library"),
            )
            .with_label(decl.path.span, format!("`{first}.…` always means the library's"))
            .with_note(
                "choose another name: a program's namespace can't start with the name of one of the library's",
            ));
        }
        Ok(())
    }

    /// What a written name means, apart from local variables (the caller's).
    pub(crate) fn resolve(&self, written: &str) -> Resolved<'_> {
        let Some((first, after)) = written.split_once('.') else {
            return self.resolve_short(written, true);
        };
        let rest: Vec<&str> = after.split('.').collect();
        let base: String = match qualifier(&CheckingLevels(self, true), first) {
            Qualifier::Std => STD.to_string(),
            Qualifier::Short(Resolved::Found { key, .. }) => key.to_string(),
            Qualifier::Short(Resolved::Ambiguous(keys, level)) => {
                return Resolved::Ambiguous(keys, level);
            }
            Qualifier::Short(Resolved::Missing) | Qualifier::Missing => return Resolved::Missing,
            Qualifier::Own => format!("{}{first}", self.root()),
            Qualifier::Project => first.to_string(),
            Qualifier::Library => format!("Std.{first}"),
        };
        // The longest prefix that names a declaration.
        for k in (0..rest.len()).rev() {
            let key = format!("{base}.{}", rest[..=k].join("."));
            let key = alias_target(&key).unwrap_or(key);
            if let Some((key, global, span)) = self.scope.entry(&key) {
                return Resolved::Found {
                    global,
                    span,
                    key,
                    level: Level::Qualified,
                    rest: rest[k + 1..].iter().map(|s| s.to_string()).collect(),
                };
            }
        }
        match self.scope.entry(&base) {
            Some((key, global, span)) => Resolved::Found {
                global,
                span,
                key,
                level: Level::Qualified,
                rest: rest.iter().map(|s| s.to_string()).collect(),
            },
            None => Resolved::Missing,
        }
    }

    /// A short name, at the first level that has it. Constructors and
    /// operations are found only with `followers`.
    fn resolve_short(&self, x: &str, followers: bool) -> Resolved<'_> {
        self.resolve_short_in(x, followers, true)
    }

    /// [`resolve_short`](Self::resolve_short), with or without this file's
    /// imports: an import's own path is read without them.
    fn resolve_short_in(&self, x: &str, followers: bool, imports: bool) -> Resolved<'_> {
        if x.starts_with('%') {
            return Resolved::Missing;
        }
        for level in [
            Level::Module,
            Level::Import,
            Level::Wildcard,
            Level::Default,
        ] {
            if !imports && matches!(level, Level::Import | Level::Wildcard) {
                continue;
            }
            // The first candidate, and any others that are different things
            // (the same thing reached twice isn't ambiguous).
            let mut first: Option<(&str, Global, Span)> = None;
            let mut others: Vec<&str> = Vec::new();
            self.candidates(level, x, followers, &mut |key| {
                let Some((key, global, span)) = self.scope.entry(key) else {
                    return;
                };
                match first {
                    None => first = Some((key, global, span)),
                    Some((_, g, _)) if g == global => {}
                    Some(_) => {
                        if !others
                            .iter()
                            .any(|k| self.scope.entry(k).is_some_and(|(_, g, _)| g == global))
                        {
                            others.push(key);
                        }
                    }
                }
            });
            match first {
                None => continue,
                Some((key, global, span)) if others.is_empty() => {
                    return Resolved::Found {
                        global,
                        span,
                        key,
                        level,
                        rest: Vec::new(),
                    };
                }
                Some((key, ..)) => {
                    let mut keys: Vec<String> = std::iter::once(key)
                        .chain(others)
                        .map(str::to_string)
                        .collect();
                    keys.sort();
                    return Resolved::Ambiguous(keys, level);
                }
            }
        }
        Resolved::Missing
    }

    /// Calls `found` with the key of each candidate for short name `x` at
    /// `level`.
    fn candidates<'a>(
        &'a self,
        level: Level,
        x: &str,
        followers: bool,
        found: &mut dyn FnMut(&'a str),
    ) {
        let followed = || {
            followers
                .then(|| self.scope.followers.get(x))
                .flatten()
                .into_iter()
                .flatten()
        };
        match level {
            // The module's own: a declaration at its root, or a constructor
            // or operation of a type or ability at its root.
            Level::Module => {
                let root = self.root();
                if root.is_empty() {
                    if let Some((key, ..)) = self.scope.entry(x) {
                        found(key);
                    }
                } else if self.loading_prelude
                    && let Some(key) = self.scope.std_root.get(x)
                    && key.strip_prefix("Std.") == Some(x)
                {
                    found(key);
                } else if !self.loading_prelude
                    && let Some((key, ..)) = self.scope.entry(&format!("{root}{x}"))
                {
                    found(key);
                }
                for key in followed() {
                    let owner = parent(key).unwrap_or("");
                    if owner.strip_prefix(root).is_some_and(|p| !p.contains('.')) {
                        found(key);
                    }
                }
            }
            Level::Import => {
                let imports = self.scope.imports.get(self.current_file());
                for (key, _) in imports.and_then(|t| t.get(x)).into_iter().flatten() {
                    found(key);
                }
                for key in followed() {
                    let owner = parent(key).unwrap_or("");
                    let imported = imports
                        .and_then(|t| t.get(short(owner)))
                        .is_some_and(|v| v.iter().any(|(k, _)| k == owner));
                    if imported && self.visible_as(owner) {
                        found(key);
                    }
                }
            }
            Level::Wildcard => {
                let Some(table) = self.scope.wildcards.get(self.current_file()) else {
                    return;
                };
                if table.is_empty() {
                    return;
                }
                for (key, _) in table.get(x).into_iter().flatten() {
                    found(key);
                }
                for key in followed() {
                    let owner = parent(key).unwrap_or("");
                    let brought = table
                        .get(short(owner))
                        .is_some_and(|v| v.iter().any(|(k, _)| k == owner));
                    if brought && self.visible_as(owner) {
                        found(key);
                    }
                }
            }
            // The default set, in a program: what `Std` declares at its
            // root, and its aliases.
            Level::Default if !self.loading_prelude => {
                if let Some(key) = self.scope.std_root.get(x) {
                    found(key);
                }
                for key in followed() {
                    let owner = parent(key).unwrap_or("");
                    let at_root = owner.strip_prefix("Std.").is_some_and(|p| !p.contains('.'));
                    if at_root && self.visible_as(owner) {
                        found(key);
                    }
                }
            }
            Level::Default | Level::Qualified => {}
        }
    }

    /// Whether the type or ability `owner` is what its short name means
    /// here, so its constructors or operations are visible (decision 6).
    fn visible_as(&self, owner: &str) -> bool {
        match self.resolve_short(short(owner), false) {
            Resolved::Found { key, .. } => key == owner,
            // Constructors of each of two types that share a name are
            // ambiguous too, not unknown.
            Resolved::Ambiguous(keys, _) => keys.iter().any(|k| k == owner),
            Resolved::Missing => false,
        }
    }

    /// The key a declaration written `written` gets in the current module.
    /// Its qualifier is resolved like a name: into a type or namespace of
    /// the module's, or a new namespace. The library's namespaces can't be
    /// added to from a program (`E-STD-NAMESPACE`).
    pub(crate) fn declaration_key(&self, name: &ast::Name) -> Result<String> {
        let written = &name.text;
        let root = self.root();
        let Some((first, rest)) = written.split_once('.') else {
            return Ok(format!("{root}{written}"));
        };
        let refuse = |owner: &str| {
            let label = if owner == STD {
                "`Std` always means the standard library".to_string()
            } else {
                format!("`{first}` here means `{owner}`")
            };
            Diagnostic::error(
                "E-STD-NAMESPACE",
                format!(
                    "`{}` is a namespace of the standard library, which a program can't add to",
                    parent(written).unwrap_or(first)
                ),
            )
            .with_label(name.span, label)
            .with_note(format!(
                "define it in your own namespace, or without one: `{}`",
                short(written)
            ))
        };
        if first == STD {
            if self.loading_prelude {
                return Ok(written.clone());
            }
            return Err(refuse(STD));
        }
        // In a namespace, a declaration can't go in another's
        // (docs/proposals/multi-file.md §4.8, §11 P8), nor use its own
        // namespace's name as a qualifier.
        if !self.loading_prelude && !root.is_empty() {
            let ns = self.current_namespace().unwrap_or("");
            match self.resolve_short(first, false) {
                Resolved::Found { key, .. }
                    if !key.starts_with(root) && !key.starts_with("Std.") =>
                {
                    let owner = self
                        .project_namespaces
                        .iter()
                        .filter(|q| key.starts_with(&format!("{q}.")))
                        .max_by_key(|q| q.len())
                        .map(String::as_str)
                        .or_else(|| parent(key))
                        .unwrap_or(key);
                    return Err(Diagnostic::error(
                        "E-FOREIGN-NAMESPACE",
                        format!("`{first}` belongs to namespace {owner}, and {ns} can't add to it"),
                    )
                    .with_label(name.span, format!("`{first}` here means `{key}`"))
                    .with_note(format!(
                        "name it in {ns} without the `{first}.` prefix, e.g. `{}`",
                        short(written)
                    )));
                }
                Resolved::Missing
                    if self.project_prefixes.contains(first)
                        || ns == first
                        || ns.starts_with(&format!("{first}.")) =>
                {
                    return Err(Diagnostic::error(
                        "E-FOREIGN-NAMESPACE",
                        format!(
                            "`{first}` is a namespace {}, and {ns} can't add to it",
                            if self.project_prefixes.contains(first) {
                                "of the project"
                            } else {
                                "of this file"
                            }
                        ),
                    )
                    .with_label(
                        name.span,
                        format!("`{first}` here means the namespace `{first}`"),
                    )
                    .with_note(format!(
                        "declarations go in the file's own namespace: write `{rest}`"
                    )));
                }
                _ => {}
            }
        }
        // A library namespace is always available as a qualifier (§4.6), so
        // `Text.foo` means the library's `Text`, even without a type `Text`.
        let base = match self.resolve_short(first, false) {
            Resolved::Found { key, .. } => key.to_string(),
            _ if self.scope.is_namespace(&format!("Std.{first}")) => format!("Std.{first}"),
            _ => format!("{root}{first}"),
        };
        if !self.loading_prelude && base.starts_with("Std.") {
            return Err(refuse(&base));
        }
        Ok(format!("{base}.{rest}"))
    }

    /// The key of data type `d`.
    pub(crate) fn data_key(&self, d: stitchwort_core::DataId) -> String {
        let data = self.globals.data(d);
        if data.path.starts_with("Std.") {
            data.path.to_string()
        } else {
            data.name.to_string()
        }
    }

    /// The key of `member` (a constructor, an operation, or a generated
    /// name) of the type or ability whose key is `owner`.
    pub(crate) fn member_key(owner: &str, member: &str) -> String {
        format!("{owner}.{member}")
    }

    /// What `written` names, if it names one declaration exactly.
    pub(crate) fn named(&self, written: &str) -> Option<&(Global, Span)> {
        match self.resolve(written) {
            Resolved::Found { key, rest, .. } if rest.is_empty() => self.scope.entries.get(key),
            _ => None,
        }
    }

    /// Why `name` doesn't name one declaration: it's ambiguous, followed by
    /// something its declaration doesn't have, or unknown.
    pub(crate) fn not_found(&self, name: &ast::Name) -> Diagnostic {
        match self.resolve_exact(name) {
            Err(d) => d,
            Ok(_) => self.unknown(name),
        }
    }

    /// The meaning of `name`, which must name a declaration exactly: an
    /// error if it's unknown, ambiguous, or followed by field accesses.
    pub(crate) fn resolve_exact(&self, name: &ast::Name) -> Result<(Global, Span, String)> {
        match self.resolve(&name.text) {
            Resolved::Found {
                global,
                span,
                key,
                rest,
                ..
            } if rest.is_empty() => Ok((global, span, key.to_string())),
            Resolved::Found { key, rest, .. } => Err(error(
                "E-UNKNOWN-NAME",
                name.span,
                format!("`{}` has no `{}`", display(key), rest.join(".")),
            )),
            Resolved::Ambiguous(keys, level) => Err(self.ambiguous(name, &keys, level)),
            Resolved::Missing => Err(self.unknown(name)),
        }
    }

    /// How `key` is written here: without `Std.` unless that would mean
    /// something else.
    pub(crate) fn written(&self, key: &str) -> String {
        let short = display(key);
        match self.resolve(short) {
            Resolved::Found { key: k, rest, .. } if k == key && rest.is_empty() => {
                short.to_string()
            }
            _ => key.to_string(),
        }
    }

    /// `E-AMBIGUOUS`, where an ambiguous name is used.
    pub(crate) fn ambiguous(&self, name: &ast::Name, keys: &[String], level: Level) -> Diagnostic {
        let shown: Vec<String> = keys
            .iter()
            .map(|k| format!("`{}`", self.written(k)))
            .collect();
        let mut d = Diagnostic::error(
            "E-AMBIGUOUS",
            format!("`{}` could mean {}", name.text, or_list(&shown)),
        )
        .with_label(name.span, format!("write {} in full", or_list(&shown)));
        for key in keys {
            if let Some((_, span)) = self.scope.get(key)
                && span.file == name.span.file
            {
                d = d.with_label(span, format!("`{}` is declared here", display(key)));
            }
        }
        if level == Level::Wildcard {
            // What to import by name: the name's first component (a type
            // used as a qualifier), or the type a constructor belongs to.
            let key = keys.first().map_or("", String::as_str);
            let follower = self
                .scope
                .followers
                .get(short(key))
                .is_some_and(|f| f.iter().any(|k| k == key));
            let (namespace, item) = if follower {
                let owner = parent(key).unwrap_or("");
                (parent(owner).unwrap_or(""), short(owner))
            } else {
                (
                    parent(key).unwrap_or(""),
                    name.text.split('.').next().unwrap_or(&name.text),
                )
            };
            d = d.with_note(format!(
                "both come in through `(..)` imports; to choose one, import it by name, e.g. `import {} ({item})`",
                display(namespace),
            ));
        }
        d
    }

    /// `E-UNKNOWN-NAME`, with the library's declarations of that short name
    /// as suggestions.
    pub(crate) fn unknown(&self, name: &ast::Name) -> Diagnostic {
        if let Some(context) = &self.file_mode
            && name.text.contains('.')
            && let Some(d) = context.diagnostic(&name.text, name.span)
        {
            return d;
        }
        let mut d = Diagnostic::error("E-UNKNOWN-NAME", format!("unknown name `{}`", name.text))
            .with_label(name.span, "not in scope");
        if !name.text.contains('.') {
            let mut found: Vec<String> = self
                .scope
                .keys()
                .filter(|k| {
                    k.starts_with("Std.")
                        && short(k) == name.text
                        && parent(k).is_some_and(|p| p.contains('.'))
                })
                .map(|k| self.written(k))
                .collect();
            found.sort_unstable();
            if let Some(first) = found.first() {
                let namespace = parent(first).unwrap_or(first);
                let shown: Vec<String> = found.iter().map(|k| format!("`{k}`")).collect();
                d = d.with_note(format!(
                    "the library has {}: write it in full, or `import {namespace} ({})`",
                    or_list(&shown),
                    name.text
                ));
            }
        }
        d
    }

    /// Resolves the module's imports. An import of the library's is
    /// resolved before the module's qualified declarations are registered
    /// (`own: false`), and one of the module's own namespaces after them.
    pub(crate) fn add_imports(
        &mut self,
        imports: &[Import],
        own: bool,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        for import in imports {
            let namespace = match self.import_namespace(&import.path) {
                Some(namespace) => namespace,
                None if own => {
                    if let Some(context) = &self.file_mode
                        && let Some(d) = context.diagnostic(&import.path.text, import.path.span)
                    {
                        diagnostics.push(d);
                        self.scope
                            .import_failed
                            .extend(import.items.iter().map(|i| i.text.clone()));
                        self.wildcard_failed(import);
                        continue;
                    }
                    let mut d = error(
                        "E-IMPORT-UNKNOWN",
                        import.path.span,
                        format!("there's no namespace `{}`", import.path.text),
                    )
                    .with_note("`import` takes a namespace, such as `List` or `Text`");
                    // The first component may be a name this file imports:
                    // an import's path isn't read through another import.
                    let first = import.path.text.split('.').next().unwrap_or_default();
                    let example = import.items.first().map_or("..", |i| i.text.as_str());
                    if let Some(source) = imports
                        .iter()
                        .find(|i| i.items.iter().any(|n| n.text == first))
                    {
                        d = d.with_note(format!(
                            "`{first}` is imported in this file, but an import's namespace is never found through another import: write it in full, e.g. `import {}.{} ({example})`",
                            source.path.text, import.path.text
                        ));
                    } else if let Some(source) = imports
                        .iter()
                        .filter(|i| i.everything.is_some())
                        .find(|i| self.wildcard_brings(i, first))
                    {
                        d = d.with_note(format!(
                            "`{first}` comes in through `import {} (..)` in this file, but an import's namespace is never found through another import: write it in full, e.g. `import {}.{} ({example})`",
                            source.path.text, source.path.text, import.path.text
                        ));
                    }
                    diagnostics.push(d);
                    self.wildcard_failed(import);
                    continue;
                }
                None => continue,
            };
            // The prelude's namespaces are all its own.
            let is_own =
                self.loading_prelude || !(namespace == STD || namespace.starts_with("Std."));
            if is_own != own {
                continue;
            }
            if import.everything.is_some() {
                self.add_wildcard(import, &namespace, diagnostics);
                continue;
            }
            for item in &import.items {
                let key = format!("{namespace}.{}", item.text);
                if item.text.starts_with('%') || self.scope.get(&key).is_none() {
                    diagnostics.push(self.import_unknown(&namespace, item));
                    continue;
                }
                // A declaration of the module's own with this name would hide
                // the import completely.
                if let Resolved::Found {
                    level: Level::Module,
                    span,
                    ..
                } = self.resolve_short(&item.text, true)
                {
                    let message = match self.current_namespace() {
                        Some(namespace) if span.file != item.span.file => format!(
                            "`{}` is imported, but `{}` is also defined in another file of namespace {namespace}",
                            item.text, item.text
                        ),
                        _ => format!(
                            "`{}` is imported, but this file also defines `{}`",
                            item.text, item.text
                        ),
                    };
                    diagnostics.push(
                        error("E-IMPORT-CLASH", item.span, message)
                            .with_label(span, "defined here, which would hide the import")
                            .with_note(format!(
                                "remove the import, and write `{}` where you mean that one",
                                display(&key)
                            )),
                    );
                    continue;
                }
                let file = self.current_file();
                if self.scope.imports.len() <= file {
                    self.scope.imports.resize_with(file + 1, HashMap::new);
                }
                let entry = self.scope.imports[file]
                    .entry(item.text.clone())
                    .or_default();
                if entry.iter().any(|(k, _)| *k == key) {
                    diagnostics.push(
                        Diagnostic::warning(
                            "W-IMPORT-TWICE",
                            format!("`{}` is imported twice", display(&key)),
                        )
                        .with_label(item.span, "imported again here"),
                    );
                    continue;
                }
                entry.push((key, item.span));
            }
        }
    }

    /// The namespace an import's path names, resolved like a qualifier.
    /// Read without this file's imports, so import order never matters
    /// (docs/proposals/multi-file.md §4.5).
    fn import_namespace(&self, path: &ast::Name) -> Option<String> {
        import_target(&CheckingLevels(self, false), &path.text, self.root())
            .filter(|k| k == STD || self.scope.is_namespace(k))
    }

    /// Records that `import`, if it's a `(..)`, failed with an error of its
    /// own.
    fn wildcard_failed(&mut self, import: &Import) {
        if import.everything.is_some() {
            let file = self.current_file();
            self.scope.wildcard_failed.insert(file);
        }
    }

    /// Whether the `(..)` import `wildcard` brings the short name `x`.
    fn wildcard_brings(&self, wildcard: &Import, x: &str) -> bool {
        let Some(k) = self.import_namespace(&wildcard.path) else {
            return false;
        };
        matches!(
            self.wildcard_source(&k, self.current_namespace()),
            Some(WildcardSource::Names(names)) if names.iter().any(|n| n == x)
        )
    }

    /// Adds what `import K (..)` brings to this file's wildcard table.
    fn add_wildcard(&mut self, import: &Import, k: &str, diagnostics: &mut Vec<Diagnostic>) {
        let own = self.current_namespace().map(str::to_string);
        let file = self.current_file();
        let dots = import.everything.unwrap_or(import.span);
        match self.wildcard_source(k, own.as_deref()) {
            Some(WildcardSource::Names(names)) => {
                if self.scope.wildcards.len() <= file {
                    self.scope.wildcards.resize_with(file + 1, BTreeMap::new);
                }
                let table = &mut self.scope.wildcards[file];
                let twice = names.first().is_some_and(|x| {
                    let key = format!("{k}.{x}");
                    table
                        .get(x)
                        .is_some_and(|v| v.iter().any(|(k, _)| *k == key))
                });
                if twice {
                    diagnostics.push(
                        Diagnostic::warning(
                            "W-IMPORT-TWICE",
                            format!("`import {} (..)` is written twice", display(k)),
                        )
                        .with_label(dots, "written again here"),
                    );
                    return;
                }
                for x in names {
                    let key = format!("{k}.{x}");
                    if self.scope.entries.contains_key(&key) {
                        let keys = self.scope.wildcards[file].entry(x).or_default();
                        if let Err(at) = keys.binary_search_by(|(k, _)| k.as_str().cmp(&key)) {
                            keys.insert(at, (key, import.span));
                        }
                    }
                }
            }
            Some(WildcardSource::Refused(refusal)) => {
                diagnostics.push(self.refused_wildcard(&refusal, k, &import.path));
                self.scope.wildcard_failed.insert(file);
            }
            // The namespace didn't parse: it isn't checked either.
            Some(WildcardSource::Unknown) => {}
            None => {
                diagnostics.push(
                    error(
                        "E-IMPORT-UNKNOWN",
                        import.path.span,
                        format!("there's no namespace `{}`", import.path.text),
                    )
                    .with_note("`import` takes a namespace, such as `List` or `Text`"),
                );
                self.scope.wildcard_failed.insert(file);
            }
        }
    }

    /// What `import k (..)` brings, for a file of namespace `own`. `None` if
    /// `k` is no namespace this can import from at all.
    pub(crate) fn wildcard_source(&self, k: &str, own: Option<&str>) -> Option<WildcardSource> {
        if k == STD {
            return Some(WildcardSource::Refused(Refusal::StdRoot));
        }
        if k.starts_with("Std.") && self.scope.is_namespace(k) {
            let prefix = format!("{k}.");
            let mut names: Vec<String> = self
                .scope
                .keys()
                .filter_map(|key| key.strip_prefix(&prefix))
                .filter(|x| !x.contains('.') && !x.starts_with('%'))
                .map(str::to_string)
                .collect();
            names.sort_unstable();
            names.dedup();
            return Some(WildcardSource::Names(names));
        }
        if own == Some(k) {
            return Some(WildcardSource::Refused(Refusal::Own));
        }
        if self.project_namespaces.contains(k) {
            return Some(match self.project_names.get(k) {
                Some(names) => WildcardSource::Names(names.iter().cloned().collect()),
                None => WildcardSource::Unknown,
            });
        }
        let in_own = match own {
            None => !k.starts_with("Std."),
            Some(own) => k.starts_with(&format!("{own}.")),
        };
        if in_own {
            return Some(WildcardSource::Refused(Refusal::PartOfOwn));
        }
        if let Some(q) = self.longest_namespace(k, false) {
            return Some(WildcardSource::Refused(Refusal::PartOf(q)));
        }
        if self.project_prefixes.contains(k) {
            return Some(WildcardSource::Refused(Refusal::Prefix));
        }
        None
    }

    /// `E-IMPORT-WILDCARD`: `import k (..)` names something that can't be
    /// imported whole.
    fn refused_wildcard(&self, refusal: &Refusal, k: &str, path: &ast::Name) -> Diagnostic {
        let shown = display(k);
        // A name inside `k` to use as an example, if there is one.
        let example = || {
            let prefix = format!("{k}.");
            self.scope
                .keys()
                .filter_map(|key| key.strip_prefix(&prefix))
                .filter(|x| !x.contains('.') && !x.starts_with('%'))
                .min()
        };
        let (message, label, note) = match refusal {
            Refusal::StdRoot => (
                "`Std`'s own names are visible already".to_string(),
                "`import Std (..)` would add nothing".to_string(),
                "import one of the library's namespaces instead, such as `import List (..)`"
                    .to_string(),
            ),
            Refusal::Own => (
                format!("`{shown}` is this file's own namespace, so its names are visible already"),
                format!("`import {shown} (..)` would add nothing"),
                "remove this import".to_string(),
            ),
            Refusal::PartOfOwn => {
                let rel = k.strip_prefix(self.root()).unwrap_or(k);
                let note = match example() {
                    Some(x) => format!(
                        "write its names in full, `{rel}.{x}`, or import them by name: `import {rel} ({x})`"
                    ),
                    None => format!(
                        "write its names in full, or import them by name: `import {rel} (…)`"
                    ),
                };
                (
                    format!(
                        "`(..)` imports a whole namespace, and `{rel}` is part of this file's namespace"
                    ),
                    format!("`{rel}` is declared in this file's namespace"),
                    note,
                )
            }
            Refusal::PartOf(q) => {
                let owner = short(k);
                let note = match example() {
                    Some(x) => format!(
                        "import the names you need, `import {shown} ({x})`, or import `{owner}` from {q} and write `{owner}.{x}`"
                    ),
                    None => format!(
                        "import the names you need, `import {shown} (…)`, or import `{owner}` from {q} and write its names after `{owner}.`"
                    ),
                };
                (
                    format!(
                        "`(..)` imports a whole namespace, and `{shown}` is part of namespace {q}"
                    ),
                    format!("`{shown}` is declared in {q}"),
                    note,
                )
            }
            Refusal::Prefix => {
                let prefix = format!("{k}.");
                let mut inside: Vec<String> = self
                    .project_namespaces
                    .iter()
                    .filter(|q| q.starts_with(&prefix))
                    .take(4)
                    .map(|q| format!("`{q}`"))
                    .collect();
                let more = inside.len() > 3;
                inside.truncate(3);
                let mut list = inside.join(", ");
                if more {
                    list.push_str(", …");
                }
                (
                    format!(
                        "`{shown}` declares nothing itself: it's only the start of namespace names"
                    ),
                    format!("there's no namespace `{shown}` of its own"),
                    format!("import from one of its namespaces: {list}"),
                )
            }
        };
        Diagnostic::error("E-IMPORT-WILDCARD", message)
            .with_label(path.span, label)
            .with_note(note)
    }

    fn import_unknown(&self, namespace: &str, item: &ast::Name) -> Diagnostic {
        let mut d = error(
            "E-IMPORT-UNKNOWN",
            item.span,
            format!("`{}` has no `{}`", display(namespace), item.text),
        );
        let prefix = format!("{namespace}.");
        let mut near: Vec<&str> = self
            .scope
            .keys()
            .filter_map(|k| k.strip_prefix(&prefix))
            .filter(|m| !m.contains('.') && !m.starts_with('%'))
            .filter(|m| edit_distance(m, &item.text) <= 2)
            .collect();
        near.sort_unstable();
        if let Some(m) = near.first() {
            d = d.with_note(format!("did you mean `{m}`?"));
        }
        d
    }
}

/// The target of the alias `key`, if it is one.
fn alias_target(key: &str) -> Option<String> {
    let path = key.strip_prefix("Std.")?;
    ALIASES
        .iter()
        .find(|(alias, _)| *alias == path)
        .map(|(_, target)| format!("Std.{target}"))
}

fn or_list(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [one] => one.clone(),
        [init @ .., last] => format!("{} or {last}", init.join(", ")),
    }
}

pub fn edit_distance(a: &str, b: &str) -> usize {
    let b: Vec<char> = b.chars().collect();
    let mut row: Vec<usize> = (0..=b.len()).collect();
    for (i, ca) in a.chars().enumerate() {
        let mut prev = row[0];
        row[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let cur = row[j + 1];
            row[j + 1] = if ca == *cb {
                prev
            } else {
                1 + prev.min(row[j]).min(cur)
            };
            prev = cur;
        }
    }
    row[b.len()]
}
