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

use std::collections::{BTreeMap, BTreeSet};

use stitchwort_core::DefId;
use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::pretty::{Declaration, NameScope};
use stitchwort_syntax::ast::{self, Import};
use stitchwort_syntax::{Diagnostic, Span};

use crate::state::{Logged, LoggedSet, Logs, Parts};
use crate::{Elaborator, Global, Result, error};

/// The library's root.
pub const STD: &str = "Std";

/// Default names that are aliases of declarations in namespaces: the alias's
/// path under `Std`, and its target's (§4.6).
pub const ALIASES: &[(&str, &str)] = &[("not", "Bool.not")];

/// The prelude: the library's root names a program sees without an import
/// (docs/proposals/prelude-slim.md §3, D266). The types built-in syntax
/// needs, `Option`, the interfaces behind operators and `deriving`, `IO`,
/// and the alias `not`. A prelude type's own declaration comes with it
/// (constructors, record fields, an ability's operations, an interface's
/// methods); the rest of its namespace (`List.map`, `Nat.addComm`) needs
/// `import Std (List)` (D260). Dot notation needs no import (D261).
pub const PRELUDE: &[&str] = &[
    "Nat",
    "Int",
    "Bool",
    "Char",
    "Text",
    "List",
    "Pair",
    "Unit",
    "Void",
    "Not",
    "And",
    "Or",
    "Exists",
    "Decidable",
    "Option",
    "Result",
    "Ordering",
    "DecEq",
    "Ord",
    "Add",
    "Mul",
    "Show",
    "Finite",
    "IO",
    "not",
];

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
/// Before a declaration's key, a name that means exactly that declaration,
/// whatever is in scope: the compiler writes one into code it generates at
/// a use site, where the declaration's own name may mean something else.
/// No one can write it (`%` isn't in names).
pub(crate) const EXACT_KEY: &str = "%key:";

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
///
/// The tables that outlive a module are [`Logged`]: a rewind's
/// checkpoint puts them back from their logs (`crate::rewind`; the
/// scope's [`Logs`]), and every write goes through their methods
/// (docs/proposals/elaborator-state.md §4.8.5). The current module's
/// imports, and the flags of a load, are copied by a mark ([`Mark`]).
#[derive(Default)]
pub struct Scope {
    /// Every declaration, by key.
    entries: Logged<String, (Global, Span)>,
    /// Constructors and operations, which are visible by their short names
    /// wherever their type's or ability's short name is: by short name.
    followers: Logged<String, Vec<String>>,
    /// Every proper prefix of a key: the namespaces.
    namespaces: LoggedSet<String>,
    /// Each file of the current module's imports: short name to keys.
    imports: Vec<HashMap<String, Vec<(String, Span)>>>,
    /// Each file's imported qualifiers: an item that is a namespace and
    /// not a declaration (`import Shop (Spec)`, `import Std (Eq)`), by its
    /// short name, to the namespaces' keys. Such an item brings none of the
    /// namespace's names: `Spec.total` means `Shop.Spec.total`.
    qualifiers: Vec<HashMap<String, Vec<(String, Span)>>>,
    /// Each file's items imported under another name (`import M (x as
    /// y)`): the key, to the names this file gives it. Also in `imports`
    /// or `qualifiers`, under those names.
    renamed: Vec<HashMap<String, Vec<String>>>,
    /// Each file's `import N (..)`: short name to keys, each with the span
    /// of the import that brought it. Empty for a program without `(..)`.
    wildcards: Vec<BTreeMap<String, Vec<(String, Span)>>>,
    /// Each file's `(..)` imports of project namespaces: the namespaces
    /// whose extensions it sees.
    extenders: Vec<BTreeSet<String>>,
    /// The files (of the current module) with a `(..)` import that failed
    /// with an error of its own, each with the namespace it names and where
    /// that is written, so the uses of names in them aren't
    /// reported again as unknown.
    pub(crate) wildcard_failed: BTreeMap<usize, (String, Span)>,
    /// The names of imports that failed with an error of their own, so the
    /// uses of them aren't reported again as unknown.
    pub(crate) import_failed: HashSet<String>,
    /// What `Std` declares at its root, and its aliases: short name to key.
    std_root: Logged<String, String>,
    /// The members of a type's, ability's or interface's own declaration:
    /// constructors, operations, record fields and interface methods. A
    /// prelude type's are usable through its default name (D260).
    members: LoggedSet<String>,
    /// Extensions: functions one project namespace adds to another's type
    /// (`def Grid.probe` in `P.Spec`, for `P.Grid`). By the key each would
    /// have in the type's namespace (`P.Grid.probe`), the extensions' own
    /// keys (`P.Spec.Grid.probe`).
    extensions: Logged<String, Vec<String>>,
    /// The reverse: an extension's key to the key it extends.
    extended: Logged<String, String>,
    /// While a library file loads: its own index entries are out of the way,
    /// so it can declare the names the index promised.
    pub(crate) loading: Option<usize>,
    /// While the core's equations are made on demand: what the core
    /// declared, so the library's names (`Std.Empty`) are out of the way,
    /// as they were while the core loaded (SW-1068).
    pub(crate) core_only: Option<CoreExtent>,
    /// While a library file loads for the check cache: each key declared
    /// for the first time, in order, and each member marked (`cache`).
    pub(crate) log: Option<Vec<ScopeOp>>,
}

/// How many definitions, data types and abilities the core declared: those
/// before the library was installed.
#[derive(Clone, Copy, Default)]
pub(crate) struct CoreExtent {
    pub defs: usize,
    pub datas: usize,
    pub abilities: usize,
    /// The definitions from here on are new: the equations being made.
    pub fresh: usize,
}

impl CoreExtent {
    /// Whether `global` is the core's (or one of the equations being made).
    fn has(&self, global: &Global) -> bool {
        match *global {
            Global::Def(d) => d.0 < self.defs || d.0 >= self.fresh,
            Global::Data(d) | Global::Ctor(d, _) => d.0 < self.datas,
            Global::Ability(a) | Global::Op(a, _) => a < self.abilities,
            Global::Unchecked(_) | Global::Failed | Global::Pending(..) => false,
        }
    }
}

/// A change [`Scope::log`] records.
#[derive(Clone)]
pub(crate) enum ScopeOp {
    /// A new key, and whether it was declared as a follower.
    New(String, bool),
    Member(String),
}

/// A file's imports, set aside while a library file loads in the middle of
/// checking a module (`library.rs`).
#[derive(Default, Clone)]
pub(crate) struct SavedImports {
    imports: Vec<HashMap<String, Vec<(String, Span)>>>,
    qualifiers: Vec<HashMap<String, Vec<(String, Span)>>>,
    renamed: Vec<HashMap<String, Vec<String>>>,
    wildcards: Vec<BTreeMap<String, Vec<(String, Span)>>>,
    extenders: Vec<BTreeSet<String>>,
    wildcard_failed: BTreeMap<usize, (String, Span)>,
    import_failed: HashSet<String>,
}

/// What the first component of a qualified name means, in order
/// (docs/proposals/multi-file.md §4.5, §4.6): `Std`; a short name (a local
/// variable is the caller's business); a namespace of the module's own; a
/// project namespace; a library namespace. A namespace this file imports
/// as an item (`import Shop (Spec)`) is its own kind of binding: below the
/// module's own declarations and namespaces, and ambiguous with any other
/// meaning the qualifier has here (docs/proposals/import-aliases.md, D2072).
pub(crate) enum Qualifier<S> {
    Std,
    Short(S),
    Own,
    Project,
    Library,
    /// A namespace imported as an item: its key.
    Imported(String),
    /// An imported namespace and some other meaning, or two imported
    /// namespaces: each meaning's key (a namespace's, or a declaration's),
    /// sorted. `None` for a meaning the pre-pass can't name.
    Ambiguous(Vec<Option<String>>),
    Missing,
}

/// The tests [`qualifier`] makes, so that checking and the project
/// analysis decide with one routine.
pub(crate) trait QualifierLevels {
    type Short;
    /// Levels 2-4 (own declarations, this file's imports, the defaults),
    /// without constructors or operations.
    fn short(&self, first: &str) -> Option<Self::Short>;
    /// Whether `found` is one of the module's own declarations.
    fn own_declaration(&self, found: &Self::Short) -> bool;
    fn own_namespace(&self, first: &str) -> bool;
    fn project_namespace(&self, first: &str) -> bool;
    fn library_namespace(&self, first: &str) -> bool;
    /// The namespaces this file imports as items under the name `first`,
    /// without repeats.
    fn imported_namespaces(&self, first: &str) -> Vec<String>;
    /// The key a short name found by `short` means, if it's known.
    fn short_key(&self, first: &str, found: &Self::Short) -> Option<String>;
    /// Every key a short name found by `short` means (several if it's
    /// ambiguous); `None` for one that isn't known.
    fn short_keys(&self, first: &str, found: &Self::Short) -> Vec<Option<String>> {
        vec![self.short_key(first, found)]
    }
}

pub(crate) fn qualifier<L: QualifierLevels>(levels: &L, first: &str) -> Qualifier<L::Short> {
    if first == STD {
        return Qualifier::Std;
    }
    let short = levels.short(first);
    let imported = levels.imported_namespaces(first);
    if imported.is_empty() {
        if let Some(s) = short {
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
        return Qualifier::Missing;
    }
    // The module's own names come first, as for any import (an import that
    // they hide is refused where it's written).
    if let Some(s) = short {
        if levels.own_declaration(&s) {
            return Qualifier::Short(s);
        }
        let mut all: Vec<Option<String>> = imported.into_iter().map(Some).collect();
        for key in levels.short_keys(first, &s) {
            if !all.contains(&key) {
                all.push(key);
            }
        }
        return imported_or_ambiguous(levels, first, all);
    }
    if levels.own_namespace(first) {
        return Qualifier::Own;
    }
    imported_or_ambiguous(levels, first, imported.into_iter().map(Some).collect())
}

/// [`qualifier`] for a name some import brings as a namespace: the meanings
/// found so far are `all`, to which a project or library namespace of that
/// name adds one.
fn imported_or_ambiguous<L: QualifierLevels>(
    levels: &L,
    first: &str,
    mut all: Vec<Option<String>>,
) -> Qualifier<L::Short> {
    for (here, key) in [
        (levels.project_namespace(first), first.to_string()),
        (levels.library_namespace(first), format!("{STD}.{first}")),
    ] {
        if here && !all.contains(&Some(key.clone())) {
            all.push(Some(key));
        }
    }
    if let [Some(key)] = all.as_slice() {
        return Qualifier::Imported(key.clone());
    }
    all.sort();
    Qualifier::Ambiguous(all)
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
        let nested = !self.0.root().is_empty() && self.0.session.project_prefixes.contains(&key);
        !nested && self.0.scope.is_namespace(&key)
    }

    fn project_namespace(&self, first: &str) -> bool {
        !self.0.unit.loading_prelude
            && !self.0.root().is_empty()
            && self.0.scope.is_namespace(first)
    }

    fn own_declaration(&self, found: &Resolved<'e>) -> bool {
        matches!(
            found,
            Resolved::Found {
                level: Level::Module,
                ..
            } | Resolved::Ambiguous(_, Level::Module)
        )
    }

    fn library_namespace(&self, first: &str) -> bool {
        // Elsewhere a library namespace is a qualifier only if it is
        // imported, which `imported_namespaces` finds.
        self.0.unit.loading_prelude && self.0.scope.is_namespace(&format!("{STD}.{first}"))
    }

    fn imported_namespaces(&self, first: &str) -> Vec<String> {
        if !self.1 {
            return Vec::new();
        }
        self.0.imported_namespaces(first)
    }

    fn short_key(&self, _: &str, found: &Resolved<'e>) -> Option<String> {
        match found {
            Resolved::Found { key, .. } => Some(key.to_string()),
            _ => None,
        }
    }

    fn short_keys(&self, _: &str, found: &Resolved<'e>) -> Vec<Option<String>> {
        match found {
            Resolved::Found { key, .. } => vec![Some(key.to_string())],
            Resolved::Ambiguous(keys, _) => keys.iter().cloned().map(Some).collect(),
            Resolved::Missing => Vec::new(),
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
        Qualifier::Missing | Qualifier::Ambiguous(_) => return None,
        Qualifier::Imported(key) => key,
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
            if let Some(log) = &mut self.log {
                log.push(ScopeOp::New(key.to_string(), follower));
            }
            let mut prefix = key;
            while let Some(p) = parent(prefix) {
                if !self.namespaces.contains_key(p) {
                    self.namespaces.add(p.to_string());
                }
                prefix = p;
            }
            if follower && !self.members.contains_key(key) {
                self.members.add(key.to_string());
            }
            if follower && !short(key).starts_with('%') {
                let short = short(key);
                if !self
                    .followers
                    .update(short, |keys| keys.push(key.to_string()))
                {
                    self.followers
                        .insert(short.to_string(), vec![key.to_string()]);
                }
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

    /// The key `key` as stored, and what it names. (Not a name the library
    /// file being loaded declares, which isn't declared until it is.)
    pub(crate) fn entry(&self, key: &str) -> Option<(&str, Global, Span)> {
        self.entries
            .get_key_value(key)
            .filter(|(_, (g, _))| !self.is_hidden(g))
            .map(|(k, (g, s))| (k.as_str(), *g, *s))
    }

    pub fn get(&self, key: &str) -> Option<(Global, Span)> {
        self.entries
            .get(key)
            .copied()
            .filter(|(g, _)| !self.is_hidden(g))
    }

    /// Whether `global` is out of the way: an index entry of the file being
    /// loaded, or, while the core's equations are made, a name the core
    /// didn't declare.
    fn is_hidden(&self, global: &Global) -> bool {
        matches!(global, Global::Pending(f, _) if self.loading == Some(*f))
            || self.core_only.is_some_and(|c| !c.has(global))
    }

    /// Sets the file's imports aside, for a nested load.
    pub(crate) fn take_imports(&mut self) -> SavedImports {
        SavedImports {
            imports: std::mem::take(&mut self.imports),
            qualifiers: std::mem::take(&mut self.qualifiers),
            renamed: std::mem::take(&mut self.renamed),
            wildcards: std::mem::take(&mut self.wildcards),
            extenders: std::mem::take(&mut self.extenders),
            wildcard_failed: std::mem::take(&mut self.wildcard_failed),
            import_failed: std::mem::take(&mut self.import_failed),
        }
    }

    pub(crate) fn restore_imports(&mut self, saved: SavedImports) {
        self.imports = saved.imports;
        self.qualifiers = saved.qualifiers;
        self.renamed = saved.renamed;
        self.wildcards = saved.wildcards;
        self.extenders = saved.extenders;
        self.wildcard_failed = saved.wildcard_failed;
        self.import_failed = saved.import_failed;
    }

    pub fn is_namespace(&self, key: &str) -> bool {
        self.namespaces.contains_key(key)
    }

    /// Whether `x` is a name at the library's root (or an alias of one).
    pub(crate) fn is_std_root(&self, x: &str) -> bool {
        self.std_root.contains_key(x)
    }

    /// Whether `x` is a default name in a program: a prelude name the
    /// library declares (D266).
    pub(crate) fn is_prelude(&self, x: &str) -> bool {
        PRELUDE.contains(&x) && self.std_root.contains_key(x)
    }

    /// A unit's write-set of the declarations' rows and of the members, in
    /// these parts of their logs, as each table's positions pick from them
    /// (for the check cache, §4.8.3): each key logged, with its row before.
    pub(crate) fn writes(&self, parts: impl Fn(fn(&Positions) -> usize) -> Parts) -> Writes<'_> {
        Writes {
            entries: self.entries.changed_in(&parts(|p| p.0[0])),
            members: self.members.changed_in(&parts(|p| p.0[4])),
        }
    }

    /// `key`'s row as stored, even if it is out of the way
    /// ([`Scope::get`] isn't).
    pub(crate) fn stored(&self, key: &str) -> Option<&(Global, Span)> {
        self.entries.get(key)
    }

    /// Forgets the rows whose global `drop` picks, as [`Scope::remove`].
    pub(crate) fn remove_where(&mut self, mut drop: impl FnMut(&Global) -> bool) {
        self.entries.retain(|_, (g, _)| !drop(g));
    }

    /// Every row, in no particular order, out of the way or not.
    pub(crate) fn rows(&self) -> impl Iterator<Item = (&String, &(Global, Span))> {
        self.entries.iter()
    }

    /// Whether `key` has a row, even one out of the way.
    pub(crate) fn has(&self, key: &str) -> bool {
        self.entries.contains_key(key)
    }

    /// Changes what `key` names, keeping its span, if it is declared;
    /// whether it is.
    pub(crate) fn set_global(&mut self, key: &str, f: impl FnOnce(&mut Global)) -> bool {
        self.entries.update(key, |(global, _)| f(global))
    }

    /// Forgets `key`'s row (not the namespaces, members or followers it
    /// added): a name declared and then withdrawn.
    pub(crate) fn remove(&mut self, key: &str) -> bool {
        self.entries.remove(key)
    }

    /// Where `key` is among the followers of its short name, if it is one
    /// (for the check cache, which must add them in the same order).
    pub(crate) fn follower_position(&self, key: &str) -> Option<usize> {
        self.followers
            .get(short(key))
            .and_then(|keys| keys.iter().position(|k| k == key))
    }

    /// Records that `key` belongs to its type's own declaration (a record
    /// field, an interface method), like a constructor.
    pub(crate) fn mark_member(&mut self, key: &str) {
        if let Some(log) = &mut self.log {
            log.push(ScopeOp::Member(key.to_string()));
        }
        if !self.members.contains_key(key) {
            self.members.add(key.to_string());
        }
    }

    /// Whether `key` belongs to its type's own declaration.
    pub(crate) fn is_member(&self, key: &str) -> bool {
        self.members.contains_key(key)
    }

    pub fn clear_imports(&mut self) {
        self.imports.clear();
        self.qualifiers.clear();
        self.renamed.clear();
        self.wildcards.clear();
        self.extenders.clear();
        self.import_failed.clear();
        self.wildcard_failed.clear();
    }

    /// The key of the library's root name `x`, or of the alias.
    pub(crate) fn std_root_key(&self, x: &str) -> Option<&str> {
        self.std_root.get(x).map(String::as_str)
    }

    /// Records that `key` is an extension standing for `target`, a key in
    /// another namespace's type's namespace.
    pub(crate) fn add_extension(&mut self, key: &str, target: &str) {
        if self.extended.contains_key(key) {
            return;
        }
        self.extended.insert(key.to_string(), target.to_string());
        if !self
            .extensions
            .update(target, |keys| keys.push(key.to_string()))
        {
            self.extensions
                .insert(target.to_string(), vec![key.to_string()]);
        }
    }

    /// The extensions of `target`, by key.
    pub(crate) fn extensions_of(&self, target: &str) -> &[String] {
        self.extensions.get(target).map_or(&[], Vec::as_slice)
    }

    /// The key the extension `key` stands for, if it is one.
    pub(crate) fn extended(&self, key: &str) -> Option<&str> {
        self.extended.get(key).map(String::as_str)
    }

    /// Every extension and the key it stands for (for the check cache).
    pub(crate) fn all_extended(&self) -> impl Iterator<Item = (&String, &String)> {
        self.extended.iter()
    }

    /// Every key, for suggestions.
    pub fn keys(&self) -> impl Iterator<Item = &String> {
        self.entries.keys()
    }

    /// Everything that outlives a module, in a canonical order: for the
    /// check cache's differential test (`cache::dump`).
    pub(crate) fn dump(&self, out: &mut String) {
        use std::fmt::Write;
        let mut lines: Vec<String> = self
            .entries
            .iter()
            .map(|(k, (g, s))| format!("scope {k} {g:?} @{}:{}-{}", s.file.index(), s.start, s.end))
            .collect();
        lines.extend(
            self.followers
                .iter()
                .map(|(k, v)| format!("followers {k} {v:?}")),
        );
        lines.extend(self.namespaces.keys().map(|k| format!("namespace {k}")));
        lines.extend(
            self.std_root
                .iter()
                .map(|(k, v)| format!("std_root {k} {v}")),
        );
        lines.extend(self.members.keys().map(|k| format!("member {k}")));
        lines.extend(
            self.extended
                .iter()
                .map(|(k, target)| format!("extension {k} {target}")),
        );
        lines.sort();
        for line in lines {
            let _ = writeln!(out, "{line}");
        }
    }
}

/// What a rewind mark copies of a [`Scope`]: the current module's imports
/// and a load's flags. Its tables are logged instead ([`Scope`]'s [`Logs`]).
pub(crate) struct Mark {
    imports: SavedImports,
    loading: Option<usize>,
    core_only: Option<CoreExtent>,
    log: Option<Vec<ScopeOp>>,
}

/// Where each of a [`Scope`]'s logged tables' log is, in
/// [`Scope::logged`]'s order.
pub(crate) struct Positions([usize; 7]);

/// A unit's write-set of a [`Scope`] ([`Scope::writes`]).
pub(crate) struct Writes<'a> {
    pub(crate) entries: Vec<(&'a String, Option<&'a (Global, Span)>)>,
    pub(crate) members: Vec<(&'a String, Option<&'a ()>)>,
}

impl Scope {
    pub(crate) fn mark(&self) -> Mark {
        let Scope {
            imports,
            qualifiers,
            renamed,
            wildcards,
            extenders,
            wildcard_failed,
            import_failed,
            loading,
            core_only,
            log,
            // Logged.
            entries: _,
            followers: _,
            namespaces: _,
            std_root: _,
            members: _,
            extensions: _,
            extended: _,
        } = self;
        Mark {
            imports: SavedImports {
                imports: imports.clone(),
                qualifiers: qualifiers.clone(),
                renamed: renamed.clone(),
                wildcards: wildcards.clone(),
                extenders: extenders.clone(),
                wildcard_failed: wildcard_failed.clone(),
                import_failed: import_failed.clone(),
            },
            loading: *loading,
            core_only: *core_only,
            log: log.clone(),
        }
    }

    /// Back to `m`; the tables are put back by the journal.
    pub(crate) fn rewind(&mut self, m: &Mark) {
        self.restore_imports(m.imports.clone());
        self.loading = m.loading;
        self.core_only = m.core_only;
        self.log = m.log.clone();
    }

    /// The logged tables, with what each does in [`Logs`]'s methods.
    fn logged(&mut self) -> [&mut dyn Logs<Positions = usize>; 7] {
        let Scope {
            entries,
            followers,
            namespaces,
            std_root,
            members,
            extensions,
            extended,
            // Copied by a mark.
            imports: _,
            qualifiers: _,
            renamed: _,
            wildcards: _,
            extenders: _,
            wildcard_failed: _,
            import_failed: _,
            loading: _,
            core_only: _,
            log: _,
        } = self;
        [
            entries, followers, namespaces, std_root, members, extensions, extended,
        ]
    }

    fn logged_ref(&self) -> [&dyn Logs<Positions = usize>; 7] {
        [
            &self.entries,
            &self.followers,
            &self.namespaces,
            &self.std_root,
            &self.members,
            &self.extensions,
            &self.extended,
        ]
    }
}

/// The names a language server's checkpoints cover: a copy of them at
/// each mark cost 3 MB and a millisecond on the AoC project (§4.8.7).
impl Logs for Scope {
    type Positions = Positions;

    fn positions(&self) -> Positions {
        Positions(self.logged_ref().map(|t| t.positions()))
    }

    fn undo_to(&mut self, at: &Positions) -> usize {
        self.logged()
            .into_iter()
            .zip(&at.0)
            .map(|(t, at)| t.undo_to(at))
            .sum()
    }

    fn set_generation(&mut self, g: Option<u32>) {
        self.logged().into_iter().for_each(|t| t.set_generation(g));
    }

    fn entries(&self) -> usize {
        self.logged_ref().iter().map(|t| t.entries()).sum()
    }

    fn bytes(&self) -> usize {
        self.logged_ref().iter().map(|t| t.bytes()).sum()
    }

    fn distinct_keys(&self) -> usize {
        self.logged_ref().iter().map(|t| t.distinct_keys()).sum()
    }
}

impl Elaborator {
    /// Whether `first` is a library namespace usable as a qualifier here
    /// without being a default name: inside the library itself, or because
    /// this file imports it (`import Std (Eq)`). The default names are
    /// found as short names instead (docs/proposals/namespaces.md §4.6, D50).
    pub(crate) fn library_namespace(&self, first: &str, imports: bool) -> bool {
        let key = format!("Std.{first}");
        self.scope.is_namespace(&key)
            && (self.unit.loading_prelude
                || (imports && self.imported_namespaces(first).contains(&key)))
    }

    /// The namespaces this file imports as items under the name `first`
    /// (`import Shop (Spec)`: `Shop.Spec`), without repeats.
    pub(crate) fn imported_namespaces(&self, first: &str) -> Vec<String> {
        let mut keys: Vec<String> = Vec::new();
        for (key, _) in self
            .scope
            .qualifiers
            .get(self.current_file())
            .and_then(|m| m.get(first))
            .into_iter()
            .flatten()
        {
            if !keys.contains(key) {
                keys.push(key.clone());
            }
        }
        keys
    }

    /// The `import` items that bring `first` as a namespace here, as
    /// `import P (S)`, with their spans.
    fn qualifier_imports(&self, first: &str) -> Vec<(String, Span)> {
        self.scope
            .qualifiers
            .get(self.current_file())
            .and_then(|m| m.get(first))
            .cloned()
            .unwrap_or_default()
    }

    /// The current module's root, as a key prefix: `Std.` for the prelude,
    /// `Day05.` for a program in namespace `Day05`, nothing for a program
    /// without a namespace line.
    pub(crate) fn root(&self) -> &str {
        if self.unit.loading_prelude {
            "Std."
        } else {
            &self.unit.namespace_root
        }
    }

    /// A data type's or definition's kernel name (its key, without `Std.`)
    /// as it's written in this module: without the module's root. For source
    /// the elaborator generates itself, which is read like the program's.
    pub(crate) fn relative_to_root(&self, name: &str) -> String {
        if self.unit.loading_prelude {
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
    /// Outside the library, the library-internal declarations
    /// ([`Elaborator::is_internal`]) aren't found.
    pub(crate) fn resolve(&self, written: &str) -> Resolved<'_> {
        match self.resolve_any(written) {
            Resolved::Found { global, .. }
                if !self.unit.loading_prelude && self.is_internal(global) =>
            {
                Resolved::Missing
            }
            Resolved::Found { global, .. }
                if !self.unit.loading_prelude
                    && self.is_proof_only(global)
                    && self.unit.module.phase == crate::module::Phase::Body
                    && !matches!(self.body_erased(), Ok(Some(true))) =>
            {
                Resolved::Missing
            }
            found => found,
        }
    }

    /// Whether `global` may be named only in the library: the constructors
    /// of `Effect.Effects` and the definitions that take a row apart, so that a
    /// program can't build, inspect, compare or branch on an effect-row
    /// parameter (docs/proposals/effect-polymorphism.md §5.C.2, D1122; not
    /// parametricity in the strong sense, as computation differs at the empty
    /// row by design). The type `Effect.Effects` itself can be named, to declare a type
    /// with a row parameter: without its constructors nothing can be done
    /// with a row but pass it on.
    pub(crate) fn is_internal(&self, global: Global) -> bool {
        use stitchwort_core::registry::Builtin;
        let registry = &self.kernel.env.registry();
        match global {
            Global::Ctor(d, _) => {
                registry.is_data(Builtin::Row, d) || registry.is_data(Builtin::Divergence, d)
            }
            // Whether a bare row may be partial is the elaborator's to say
            // (docs/proposals/partial-stage-3.md).
            Global::Data(d) => registry.is_data(Builtin::Divergence, d),
            Global::Def(id) => [
                Builtin::CompD,
                Builtin::DoneD,
                Builtin::BindDv,
                Builtin::LiftD,
                Builtin::DelayD,
                Builtin::FoldCompD,
                Builtin::TranslateD,
                Builtin::CallD,
                Builtin::RowOp,
                Builtin::RowRes,
                Builtin::CompIn,
                Builtin::DoneIn,
                Builtin::BindIn,
                Builtin::LiftIn,
                Builtin::LowerIn,
                Builtin::WidenIn,
            ]
            .into_iter()
            .any(|b| registry.is_def(b, id)),
            _ => false,
        }
    }

    /// Whether `global` takes a computation apart: the constructors of
    /// `Effect.Comp` and the definitions that match on them. Outside the
    /// library they may be named only in a declaration whose result is erased
    /// (a proof or a type), so that no program depends on how a computation
    /// is represented (docs/proposals/proof-reification.md, D1145, stage R2).
    pub(crate) fn is_proof_only(&self, global: Global) -> bool {
        use stitchwort_core::registry::Builtin;
        let registry = &self.kernel.env.registry();
        match global {
            Global::Ctor(d, _) => registry.is_data(Builtin::Comp, d),
            Global::Def(id) => [
                Builtin::FoldComp,
                Builtin::Bind,
                Builtin::Translate,
                Builtin::RunPure,
            ]
            .into_iter()
            .any(|b| registry.is_def(b, id)),
            _ => false,
        }
    }

    /// [`Elaborator::resolve`], finding library-internal declarations too.
    pub(crate) fn resolve_any(&self, written: &str) -> Resolved<'_> {
        // A name the compiler wrote for a declaration it has already found
        // (a shared-field update's constructors): exactly that key.
        if let Some(key) = written.strip_prefix(EXACT_KEY) {
            return match self.scope.entry(key) {
                Some((key, global, span)) => Resolved::Found {
                    global,
                    span,
                    key,
                    level: Level::Qualified,
                    rest: Vec::new(),
                },
                None => Resolved::Missing,
            };
        }
        let Some((first, after)) = written.split_once('.') else {
            return self.resolve_short(written, true);
        };
        let rest: Vec<&str> = after.split('.').collect();
        // A prelude type found as a default name, not imported: only its
        // own declaration's members are reached through it (D260).
        let mut members_only = false;
        let base: String = match qualifier(&CheckingLevels(self, true), first) {
            Qualifier::Std => STD.to_string(),
            Qualifier::Short(Resolved::Found { key, level, .. }) => {
                members_only = level == Level::Default;
                key.to_string()
            }
            Qualifier::Short(Resolved::Ambiguous(keys, level)) => {
                return Resolved::Ambiguous(keys, level);
            }
            Qualifier::Short(Resolved::Missing) | Qualifier::Missing => return Resolved::Missing,
            Qualifier::Own => format!("{}{first}", self.root()),
            Qualifier::Project => first.to_string(),
            Qualifier::Library => format!("Std.{first}"),
            Qualifier::Imported(key) => key,
            // Each meaning of the qualifier, with the rest of the name.
            Qualifier::Ambiguous(keys) => {
                let keys = keys
                    .into_iter()
                    .flatten()
                    .map(|k| format!("{k}.{after}"))
                    .collect();
                return Resolved::Ambiguous(keys, Level::Import);
            }
        };
        // The longest prefix that names a declaration.
        for k in (0..rest.len()).rev() {
            let key = format!("{base}.{}", rest[..=k].join("."));
            let key = alias_target(&key).unwrap_or(key);
            if let Some((key, global, span)) = self.scope.entry(&key) {
                if members_only && (k > 0 || !self.scope.is_member(key)) {
                    return Resolved::Missing;
                }
                return Resolved::Found {
                    global,
                    span,
                    key,
                    level: Level::Qualified,
                    rest: rest[k + 1..].iter().map(|s| s.to_string()).collect(),
                };
            }
            // A function another namespace adds to the type, as `x.f` finds
            // it.
            match self.visible_extension(&key) {
                Extension::Found(ext) => {
                    if let Some((key, global, span)) = self.scope.entry(&ext) {
                        return Resolved::Found {
                            global,
                            span,
                            key,
                            level: Level::Qualified,
                            rest: rest[k + 1..].iter().map(|s| s.to_string()).collect(),
                        };
                    }
                }
                Extension::Ambiguous(keys) => return Resolved::Ambiguous(keys, Level::Qualified),
                Extension::Missing => {}
            }
        }
        // Nor a namespace inside it (`Nat.Divides…`).
        if members_only && self.scope.is_namespace(&format!("{base}.{}", rest[0])) {
            return Resolved::Missing;
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
                } else if self.unit.loading_prelude
                    && let Some(key) = self.scope.std_root.get(x)
                    && key.strip_prefix("Std.") == Some(x)
                {
                    found(key);
                } else if !self.unit.loading_prelude
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
                let renamed = self.scope.renamed.get(self.current_file());
                for key in followed() {
                    let owner = parent(key).unwrap_or("");
                    let imported = imports
                        .and_then(|t| t.get(short(owner)))
                        .is_some_and(|v| v.iter().any(|(k, _)| k == owner));
                    // A type imported under another name brings its
                    // constructors under their own names.
                    let renamed = || {
                        renamed.and_then(|r| r.get(owner)).is_some_and(|locals| {
                            locals.iter().any(|l| self.visible_as_named(owner, l))
                        })
                    };
                    if (imported && self.visible_as(owner)) || renamed() {
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
            Level::Default if !self.unit.loading_prelude => {
                if let Some(key) = self.scope.std_root.get(x)
                    && PRELUDE.contains(&x)
                {
                    found(key);
                }
                for key in followed() {
                    let owner = parent(key).unwrap_or("");
                    let at_root = owner.strip_prefix("Std.").is_some_and(|p| !p.contains('.'));
                    // A library ability's operations aren't default: they
                    // are written `IO.print`, or imported (SW-134).
                    let is_op = matches!(
                        self.scope.get(key),
                        Some((
                            Global::Op(..) | Global::Pending(_, crate::library::PendingKind::Op),
                            _
                        ))
                    );
                    if at_root && !is_op && self.visible_as(owner) {
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
        self.visible_as_named(owner, short(owner))
    }

    /// Whether the type or ability `owner` is what `local` means here.
    fn visible_as_named(&self, owner: &str, local: &str) -> bool {
        match self.resolve_short(local, false) {
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
            if self.unit.loading_prelude {
                return Ok(written.clone());
            }
            return Err(refuse(STD));
        }
        // A function for another project namespace's type is an extension,
        // declared in this namespace under the type's short name.
        if let Some(target) = self.extension_target(name) {
            let ty = &target[..target.len() - rest.len() - 1];
            return Ok(format!("{root}{}.{rest}", short(ty)));
        }
        // In a namespace, a declaration can't go in another's
        // (docs/proposals/multi-file.md §4.8, §11 P8), nor use its own
        // namespace's name as a qualifier.
        if !self.unit.loading_prelude && !root.is_empty() {
            let ns = self.current_namespace().unwrap_or("");
            match self.resolve_short(first, false) {
                Resolved::Found { key, .. }
                    if !key.starts_with(root) && !key.starts_with("Std.") =>
                {
                    let owner = self
                        .session
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
                    if self.session.project_prefixes.contains(first)
                        || ns == first
                        || ns.starts_with(&format!("{first}.")) =>
                {
                    return Err(Diagnostic::error(
                        "E-FOREIGN-NAMESPACE",
                        format!(
                            "`{first}` is a namespace {}, and {ns} can't add to it",
                            if self.session.project_prefixes.contains(first) {
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
                    .with_note(self.unqualified_advice(written, rest)));
                }
                _ => {}
            }
        }
        // A library namespace is always available as a qualifier (§4.6), so
        // `Text.foo` means the library's `Text`, even without a type `Text`.
        let base = match self.resolve_short(first, false) {
            Resolved::Found { key, .. } => key.to_string(),
            _ if self.library_namespace(first, true) => format!("Std.{first}"),
            _ => format!("{root}{first}"),
        };
        if !self.unit.loading_prelude && base.starts_with("Std.") {
            return Err(refuse(&base));
        }
        Ok(format!("{base}.{rest}"))
    }

    /// For a declaration written with a namespace's full name (`def
    /// P.Grid.probe` in `P.Spec`), how to write it instead: for a function
    /// on a type, the type's short name and the function's (imported first
    /// if this file doesn't see the type by that name); otherwise without
    /// the namespace.
    fn unqualified_advice(&self, written: &str, rest: &str) -> String {
        let Some((within, last)) = rest.rsplit_once('.') else {
            return format!("declarations go in the file's own namespace: write `{rest}`");
        };
        let ty_written = &written[..written.len() - last.len() - 1];
        if let Resolved::Found {
            key, global, rest, ..
        } = self.resolve(ty_written)
            && rest.is_empty()
            && self.is_type_former(global)
        {
            let ty = short(key);
            let owner = self.longest_namespace(key, false);
            let sees = matches!(
                self.resolve_short(ty, false),
                Resolved::Found { key: k, .. } if k == key
            );
            return match owner {
                Some(owner)
                    if !sees && owner.as_str() != self.current_namespace().unwrap_or("") =>
                {
                    format!(
                        "to add `{last}` to `{key}`, import the type with `import {owner} ({ty})` \
                         and write `{ty}.{last}`"
                    )
                }
                _ => format!("write `{ty}.{last}`"),
            };
        }
        if self.scope.is_namespace(&format!("{}{within}", self.root())) {
            return format!("declarations go in the file's own namespace: write `{rest}`");
        }
        format!("declarations go in the file's own namespace: write `{last}`")
    }

    /// The key that a declaration written `T.f` stands for, if it adds `f`
    /// to a type `T` of another project namespace (docs/proposals/
    /// extending-types.md §6): `T.f`'s key in `T`'s namespace. Such a
    /// declaration is an extension, declared in this file's namespace.
    pub(crate) fn extension_target(&self, name: &ast::Name) -> Option<String> {
        if self.unit.loading_prelude || self.root().is_empty() {
            return None;
        }
        let (first, rest) = name.text.split_once('.')?;
        let Resolved::Found { key, global, .. } = self.resolve_short(first, false) else {
            return None;
        };
        if key.starts_with("Std.") || !self.is_type_former(global) {
            return None;
        }
        let owner = self.longest_namespace(key, false)?;
        (Some(owner.as_str()) != self.current_namespace()).then(|| format!("{key}.{rest}"))
    }

    /// Whether `decl`, written `name`, may add `target` to another project
    /// namespace's type: it's a function or theorem, and the type's own
    /// namespace has no `f` (that one always wins, so the clash is an error
    /// here, where the type's namespace is already checked).
    pub(crate) fn check_extension(
        &self,
        decl: &ast::Decl,
        name: &ast::Name,
        target: &str,
    ) -> Result<()> {
        let ns = self.current_namespace().unwrap_or("");
        let (first, _) = name.text.split_once('.').unwrap_or((&name.text, ""));
        let ty = &target[..target.len() - (name.text.len() - first.len())];
        let owner = self.longest_namespace(ty, false).unwrap_or_default();
        if !matches!(decl, ast::Decl::Signature { .. }) {
            return Err(Diagnostic::error(
                "E-FOREIGN-NAMESPACE",
                format!(
                    "`{first}` belongs to namespace {owner}, and {ns} can add only functions to it"
                ),
            )
            .with_label(name.span, format!("`{first}` here means `{ty}`"))
            .with_note(format!(
                "a namespace can add functions and theorems to another namespace's type, \
                 but not types; name it in {ns} without the `{first}.` prefix, e.g. `{}`",
                short(&name.text)
            )));
        }
        if let Some((_, span)) = self.scope.get(target) {
            let mut d = Diagnostic::error(
                "E-EXTENSION-CLASH",
                format!("`{ty}` already has a `{}`", short(target)),
            )
            .with_label(
                name.span,
                format!("this would add a second `{first}.{}`", short(target)),
            )
            .with_note(format!(
                "`{target}` is declared in namespace {owner}, and a type's own functions come \
                 first: give this one another name"
            ));
            if span.file == name.span.file {
                d = d.with_label(span, "declared here");
            }
            return Err(d);
        }
        Ok(())
    }

    /// The extension `T.f` means here, `target` being `T.f`'s key in `T`'s
    /// namespace (docs/proposals/extending-types.md §6): this namespace's
    /// own, else the one from a namespace this file imports with `(..)`
    /// (imports aren't passed on). Two of those are ambiguous.
    pub(crate) fn visible_extension(&self, target: &str) -> Extension {
        let all = self.scope.extensions_of(target);
        if all.is_empty() || self.unit.loading_prelude {
            return Extension::Missing;
        }
        let own = self.current_namespace();
        let extender = |key: &str| self.longest_namespace(key, false);
        if let Some(key) = all
            .iter()
            .find(|k| own.is_some() && extender(k).as_deref() == own)
        {
            return Extension::Found(key.clone());
        }
        let Some(imported) = self.scope.extenders.get(self.current_file()) else {
            return Extension::Missing;
        };
        let mut seen: Vec<String> = all
            .iter()
            .filter(|k| extender(k).is_some_and(|ns| imported.contains(&ns)))
            .cloned()
            .collect();
        match seen.len() {
            0 => Extension::Missing,
            1 => Extension::Found(seen.remove(0)),
            _ => {
                seen.sort();
                Extension::Ambiguous(seen)
            }
        }
    }

    /// The namespaces that add `target` to its type and that this file
    /// doesn't see, for suggesting an import.
    pub(crate) fn hidden_extenders(&self, target: &str) -> Vec<String> {
        let mut out: Vec<String> = self
            .scope
            .extensions_of(target)
            .iter()
            .filter_map(|k| self.longest_namespace(k, false))
            .collect();
        out.sort();
        out.dedup();
        out
    }
}

/// What `T.f` means as an extension ([`Elaborator::visible_extension`]).
pub(crate) enum Extension {
    Found(String),
    Ambiguous(Vec<String>),
    Missing,
}

impl Elaborator {
    /// The key of data type `d`.
    pub(crate) fn data_key(&self, d: stitchwort_core::DataId) -> String {
        let data = self.kernel.data(d);
        if data.path().starts_with("Std.") {
            data.path().to_string()
        } else {
            data.name().to_string()
        }
    }

    /// The key of `member` (a constructor, an operation, or a generated
    /// name) of the type or ability whose key is `owner`.
    pub(crate) fn member_key(owner: &str, member: &str) -> String {
        format!("{owner}.{member}")
    }

    /// Whether `global` is a type, a function returning one (`List`, a
    /// `def Grid: Type`), or an ability. A value of one has no fields, so
    /// `T.f` after it names a member of its namespace, not a field access.
    pub(crate) fn is_type_former(&self, global: Global) -> bool {
        match global {
            Global::Data(_) | Global::Ability(_) => true,
            Global::Def(id) => {
                let mut ty = self.kernel.def(id).ty().strip_loc();
                while let stitchwort_core::Term::Pi(_, _, _, cod) = ty {
                    ty = cod.strip_loc();
                }
                matches!(ty, stitchwort_core::Term::Sort(_))
            }
            _ => false,
        }
    }

    /// `E-UNKNOWN-NAME` for `T.member` where the type (or namespace) `key`
    /// has no `member`, with near misses among its members as suggestions.
    /// (One that exists but needs an import never gets here: `resolve`
    /// doesn't find the type's prefix for it, and `unknown` says what to
    /// import.)
    pub(crate) fn no_member(&self, name: &ast::Name, key: &str, member: &str) -> Diagnostic {
        let shown = self.written(key);
        let mut d = Diagnostic::error(
            "E-UNKNOWN-NAME",
            format!("no function `{member}` in `{shown}`"),
        )
        .with_label(name.span, format!("`{shown}` has no `{member}`"));
        let prefix = format!("{key}.");
        let mut near: Vec<(usize, &str)> = self
            .scope
            .keys()
            .filter_map(|k| k.strip_prefix(&prefix))
            .filter(|m| !m.contains('.') && !m.starts_with('%'))
            .map(|m| (edit_distance(m, member), m))
            .filter(|&(distance, _)| distance <= 2 && distance < member.len())
            .collect();
        near.sort_unstable();
        near.dedup();
        let meant = meaning_suggestions(key, member, |full| self.scope.get(full).is_some());
        let near: Vec<String> = if meant.is_empty() {
            near.iter().take(3).map(|(_, m)| format!("`{m}`")).collect()
        } else {
            meant.iter().map(|m| format!("`{shown}.{m}`")).collect()
        };
        if !near.is_empty() {
            d = d.with_note(format!("did you mean {}?", or_list(&near)));
        }
        d
    }

    /// What `written` names, if it names one declaration exactly.
    pub(crate) fn named(&self, written: &str) -> Option<&(Global, Span)> {
        match self.resolve(written) {
            Resolved::Found { key, rest, .. } if rest.is_empty() => self.scope.stored(key),
            _ => None,
        }
    }

    /// Which declaration `written` found, where, and the other
    /// declarations of that short name (a library one it hides, or
    /// constructors of other types).
    pub(crate) fn hiding_note(&self, written: &str) -> Option<String> {
        let Resolved::Found { key, .. } = self.resolve(written) else {
            return None;
        };
        let x = short(key);
        let library = self.scope.std_root_key(x).filter(|other| *other != key);
        let mut others: Vec<String> = self
            .scope
            .followers
            .get(x)
            .into_iter()
            .flatten()
            .filter(|other| *other != key)
            .map(|other| format!("`{}`", display(other)))
            .collect();
        others.dedup();
        if library.is_none() && others.is_empty() {
            return None;
        }
        let place = match parent(key) {
            Some(namespace) => format!(", declared in `{}`", display(namespace)),
            None => String::new(),
        };
        let mut note = format!("`{written}` here means `{}`{place}", display(key));
        if let Some(library) = library {
            note.push_str(&format!(
                "; it hides the library's `{}`, which is written `Std.{}`",
                display(library),
                display(library)
            ));
        }
        if !others.is_empty() {
            note.push_str(&format!(
                "; other constructors named `{x}`: {}",
                others.join(", ")
            ));
        }
        Some(note)
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
            Resolved::Found {
                global, key, rest, ..
            } if self.is_type_former(global) => Err(self.no_member(name, key, &rest[0])),
            Resolved::Found { key, rest, .. } => Err(error(
                "E-UNKNOWN-NAME",
                name.span,
                format!("`{}` has no `{}`", display(key), rest.join(".")),
            )),
            Resolved::Ambiguous(keys, level) => Err(self.ambiguous(name, &keys, level)),
            Resolved::Missing => Err(self.unknown(name)),
        }
    }

    /// How `key` is written here: by the name this file imports it under,
    /// if it has one (`import M (x as y)`); else without `Std.` unless that
    /// would mean something else.
    pub(crate) fn written(&self, key: &str) -> String {
        for alias in self.aliases(key) {
            if matches!(
                self.resolve_any(&alias),
                Resolved::Found { key: k, rest, .. } if k == key && rest.is_empty()
            ) {
                return alias;
            }
        }
        self.written_in_full(key)
    }

    /// [`Self::written`], ignoring the names this file gives imports: for
    /// saying where a declaration is.
    fn written_in_full(&self, key: &str) -> String {
        let short = display(key);
        match self.resolve_any(short) {
            Resolved::Found { key: k, rest, .. } if k == key && rest.is_empty() => {
                short.to_string()
            }
            _ => key.to_string(),
        }
    }

    /// The key of `declaration`: its kernel name, with `Std.` for the
    /// library's.
    fn declaration_key_of(&self, declaration: Declaration) -> String {
        let (name, path) = match declaration {
            Declaration::Def(id) => {
                let def = self.kernel.def(id);
                (def.name(), def.path())
            }
            Declaration::Data(d) => {
                let data = self.kernel.data(d);
                (data.name(), data.path())
            }
        };
        if path.starts_with("Std.") {
            path.to_string()
        } else {
            name.to_string()
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
        // A qualifier that an import brings as a namespace, and that means
        // something else here too.
        if let Some((first, after)) = name.text.split_once('.')
            && level == Level::Import
            && !self.qualifier_imports(first).is_empty()
        {
            let imported = self.imported_namespaces(first);
            let meanings: Vec<String> = keys
                .iter()
                .filter_map(|k| k.strip_suffix(&format!(".{after}")))
                .map(|k| {
                    if imported.iter().any(|i| i == k) {
                        format!("the namespace `{k}` (imported by name)")
                    } else if self.scope.get(k).is_some() {
                        format!("`{k}`")
                    } else {
                        format!("the namespace `{k}`")
                    }
                })
                .collect();
            d = d.with_note(format!(
                "`{first}` here could be {}; an imported namespace never hides another meaning, \
                 so write the full name, or import only one `{first}`",
                or_list(&meanings)
            ));
            for (_, span) in self.qualifier_imports(first) {
                if span.file == name.span.file {
                    d = d.with_label(span, format!("`{first}` imported here"));
                }
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
        if let Resolved::Found { global, key, .. } = self.resolve_any(&name.text)
            && !self.unit.loading_prelude
            && self.is_internal(global)
        {
            return Diagnostic::error(
                "E-STD-INTERNAL",
                format!("`{}` is internal to the standard library", display(key)),
            )
            .with_label(name.span, "only the standard library can name this")
            .with_note(
                "effect rows are made by the compiler from `{e}` and `{A | e}` in types; a program \
                 can pass an effect-row parameter on, but not build or inspect one",
            );
        }
        if let Resolved::Found { global, key, .. } = self.resolve_any(&name.text)
            && !self.unit.loading_prelude
            && self.is_proof_only(global)
        {
            return Diagnostic::error(
                "E-PROOF-ONLY",
                format!(
                    "`{}` takes a computation apart, so it can only be used in a proof",
                    display(key)
                ),
            )
            .with_label(
                name.span,
                "this declaration computes data, so this would run",
            )
            .with_note(
                "`Effect.Comp`'s constructors and eliminators may be used in a `theorem`, or a \
                 `def` whose type ends in `Prop` or a type: what it computes is never run",
            )
            .with_note(
                "a program passes computations as thunks `() -> {Fail} a` and observes them \
                 with a handler such as `Fail.toResult` or `Fail.orElse`",
            );
        }
        if let Some(context) = &self.unit.file_mode
            && name.text.contains('.')
            && let Some(d) = context.diagnostic(&name.text, name.span)
        {
            return d;
        }
        let mut d = Diagnostic::error("E-UNKNOWN-NAME", format!("unknown name `{}`", name.text))
            .with_label(name.span, "not in scope");
        // A constructor followed by a member of its type (`BirthYear.valid`
        // for `Key.valid`): neither reading finds a name, so give the two
        // forms that do.
        if let Some((prefix, member)) = name.text.split_once('.')
            && !member.contains('.')
            && let Resolved::Found {
                global: Global::Ctor(data, _),
                rest,
                ..
            } = self.resolve(prefix)
            && rest.is_empty()
        {
            let owner = self.data_key(data);
            if self
                .scope
                .entry(&Self::member_key(&owner, member))
                .is_some()
            {
                let owner = self.written(&owner);
                d = d.with_note(format!(
                    "`{prefix}` is a `{owner}`: write `{owner}.{member} {prefix}` or `{prefix} |> .{member}`"
                ));
            }
        }
        // A library namespace that isn't a default name needs an import (D50),
        // and so does a prelude type's namespace beyond its own declaration
        // (D260).
        if let Some((first, member)) = name.text.split_once('.')
            && !self.unit.loading_prelude
            && first != STD
            && self.scope.is_namespace(&format!("Std.{first}"))
        {
            let imported = self.imported_namespaces(first);
            if !imported.is_empty() {
                // The namespace is already here, so the name is what's wrong:
                // suggest its near misses instead of the import it has.
                let mut near: Vec<(usize, String)> = Vec::new();
                for key in &imported {
                    let prefix = format!("{key}.");
                    for m in self.scope.keys().filter_map(|k| k.strip_prefix(&prefix)) {
                        if m.contains('.') || m.starts_with('%') {
                            continue;
                        }
                        let distance = edit_distance(m, member);
                        if distance <= 2 && distance < member.len() {
                            near.push((distance, format!("{first}.{m}")));
                        }
                    }
                }
                near.sort_unstable();
                near.dedup();
                let meant: Vec<String> = imported
                    .iter()
                    .flat_map(|key| {
                        meaning_suggestions(key, member, |full| self.scope.get(full).is_some())
                    })
                    .map(|m| format!("`{first}.{m}`"))
                    .collect();
                let near: Vec<String> = if meant.is_empty() {
                    near.iter().take(3).map(|(_, m)| format!("`{m}`")).collect()
                } else {
                    meant
                };
                if !near.is_empty() {
                    d = d.with_note(format!("did you mean {}?", or_list(&near)));
                }
            } else {
                let full = format!("Std.{}", name.text);
                let prelude = matches!(
                    self.resolve_short(first, false),
                    Resolved::Found { level: Level::Default, key, .. } if key == format!("Std.{first}")
                );
                d = if prelude
                    && (self.scope.get(&full).is_some() || self.scope.is_namespace(&full))
                {
                    d.with_note(format!(
                        "`{}` needs `import Std ({first})`, or write it in full: `{full}`",
                        name.text
                    ))
                    // Why `IO.print` works without the import and `IO.simulate`
                    // doesn't (D260, docs/proposals/prelude-slim.md §3).
                    .with_note(format!(
                        "the prelude's `{first}` comes with its own constructors, fields and \
                         operations; the functions and theorems in its namespace need the import"
                    ))
                    .with_import(STD, first)
                } else {
                    d.with_note(format!(
                        "`{first}` is `Std.{first}`; add `import Std ({first})`, or write `{full}`"
                    ))
                    .with_import(STD, first)
                };
            }
        }
        // The name of something this file imports under another name.
        if !self.unit.loading_prelude
            && let Some(renamed) = self.scope.renamed.get(self.current_file())
        {
            let (first, rest) = match name.text.split_once('.') {
                Some((first, rest)) => (first, format!(".{rest}")),
                None => (name.text.as_str(), String::new()),
            };
            let mut keys: Vec<(&String, &Vec<String>)> =
                renamed.iter().filter(|(k, _)| short(k) == first).collect();
            keys.sort();
            let shown: Vec<String> = keys
                .iter()
                .map(|(key, locals)| format!("`{}{rest}` as `{}{rest}`", display(key), locals[0]))
                .collect();
            if !shown.is_empty() {
                d = d.with_note(format!(
                    "this file imports {}: write the name it has here",
                    or_list(&shown).replacen(" or ", " and ", 1)
                ));
            }
        }
        // A namespace imported as a qualifier names nothing on its own.
        if !name.text.contains('.') && !self.unit.loading_prelude {
            let imported = self.imported_namespaces(&name.text);
            if let Some(key) = imported.first() {
                d = d.with_note(format!(
                    "`{}` is the namespace `{}`, imported as a qualifier: write `{}.x` for a name `x` in it",
                    name.text,
                    key,
                    name.text
                ));
            }
        }
        // A project namespace written by its last name, not imported.
        if let Some((first, _)) = name.text.split_once('.')
            && !self.unit.loading_prelude
            && matches!(
                qualifier(&CheckingLevels(self, true), first),
                Qualifier::Missing
            )
        {
            let suffix = format!(".{first}");
            let own = self.current_namespace().unwrap_or("");
            // Those sharing the most leading components with this one first.
            let mut found: Vec<(usize, &String)> = self
                .session
                .project_namespaces
                .iter()
                .filter(|q| q.ends_with(&suffix))
                .map(|q| {
                    let shared = q
                        .split('.')
                        .zip(own.split('.'))
                        .take_while(|(a, b)| a == b)
                        .count();
                    (usize::MAX - shared, q)
                })
                .collect();
            found.sort();
            if let Some((_, q)) = found.first() {
                let parent = &q[..q.len() - suffix.len()];
                let mut note = format!(
                    "`{first}` is the namespace `{q}`: add `import {parent} ({first})`, or write `{q}.{}`",
                    &name.text[first.len() + 1..]
                );
                if found.len() > 1 {
                    let others: Vec<String> = found[1..]
                        .iter()
                        .take(2)
                        .map(|(_, q)| format!("`{q}`"))
                        .collect();
                    note.push_str(&format!(
                        " (other namespaces named `{first}`: {})",
                        others.join(", ")
                    ));
                }
                d = d.with_note(note).with_import(parent, first);
            }
        }
        // A library type outside the prelude (D266).
        if !name.text.contains('.')
            && !self.unit.loading_prelude
            && self.scope.is_std_root(&name.text)
            && !self.scope.is_prelude(&name.text)
        {
            d = d.with_note(format!(
                "`{0}` is `Std.{0}`, which isn't in the prelude; add `import Std ({0})`, or write `Std.{0}`",
                name.text
            ))
            .with_import(STD, name.text.clone());
        }
        if !name.text.contains('.') {
            let mut keys: Vec<&String> = self
                .scope
                .keys()
                .filter(|k| {
                    k.starts_with("Std.")
                        && short(k) == name.text
                        && parent(k).is_some_and(|p| p.contains('.'))
                })
                .collect();
            keys.sort_by_key(|k| self.written_in_full(k));
            let found: Vec<String> = keys.iter().map(|k| self.written_in_full(k)).collect();
            if let Some(first_key) = keys.first() {
                // The import path names the namespace in full: `written`
                // may drop the `Std.` that it needs (SW-403).
                let namespace = parent(first_key).unwrap_or(first_key);
                let first = &found[0];
                let shown: Vec<String> = found.iter().map(|k| format!("`{k}`")).collect();
                // A constructor of a library type outside the prelude comes
                // with its type (D266).
                let ty = namespace.strip_prefix("Std.").filter(|t| {
                    found.len() == 1
                        && !t.contains('.')
                        && !self.scope.is_prelude(t)
                        && self.scope.is_member(first)
                });
                if found.len() == 1 {
                    d = d.with_import(namespace, name.text.clone());
                }
                d = d.with_note(match ty {
                    Some(t) => format!(
                        "the library has {}: write it in full, or `import Std ({t})`, or `import {namespace} ({})`",
                        or_list(&shown),
                        name.text
                    ),
                    None => format!(
                        "the library has {}: write it in full, or `import {namespace} ({})`",
                        or_list(&shown),
                        name.text
                    ),
                });
            }
        }
        d
    }

    /// Whether `key` names a data type (including one this module declares
    /// and hasn't checked yet).
    fn is_data_key(&self, key: &str) -> bool {
        match self.scope.get(key) {
            Some((Global::Data(..) | Global::Pending(_, crate::library::PendingKind::Data), _)) => {
                true
            }
            Some((Global::Unchecked(i), _)) => {
                self.unit
                    .module
                    .items
                    .get(i)
                    .is_some_and(|item| item.kind == crate::module::Kind::Data)
                    && !self.scope.is_member(key)
            }
            _ => false,
        }
    }

    /// Whether `key` names a constructor (including one this module declares
    /// and hasn't checked yet).
    fn is_ctor_key(&self, key: &str) -> bool {
        match self.scope.get(key) {
            Some((Global::Ctor(..), _)) => true,
            Some((Global::Pending(_, crate::library::PendingKind::Ctor), _)) => true,
            Some((Global::Unchecked(i), _)) => {
                self.unit
                    .module
                    .items
                    .get(i)
                    .is_some_and(|item| item.kind == crate::module::Kind::Data)
                    && self.scope.is_member(key)
            }
            _ => false,
        }
    }

    /// The constructors of types declared directly in `namespace` whose short
    /// name is `name`, sorted: what `import N (name)` imports when no
    /// declaration of `namespace` has that name (D3503).
    fn constructors_named(&self, namespace: &str, name: &str) -> Vec<String> {
        let prefix = format!("{namespace}.");
        let suffix = format!(".{name}");
        let mut keys: Vec<String> = self
            .scope
            .keys()
            .filter_map(|key| {
                let owner = key.strip_prefix(&prefix)?.strip_suffix(&suffix)?;
                (!owner.contains('.') && self.is_ctor_key(key)).then_some(key)
            })
            .cloned()
            .collect();
        keys.sort_unstable();
        keys
    }

    /// `E-AMBIGUOUS`: `import N (x)` names a constructor `x` of more than one
    /// type in `N`, so it names no one thing.
    fn ambiguous_import_ctor(&self, item: &ast::Name, keys: &[String]) -> Diagnostic {
        let shown: Vec<String> = keys.iter().map(|k| format!("`{}`", display(k))).collect();
        let types: Vec<String> = keys
            .iter()
            .filter_map(|k| parent(k))
            .map(short)
            .map(|t| format!("`{t}`"))
            .collect();
        let namespace = keys
            .first()
            .and_then(|k| parent(k))
            .and_then(parent)
            .map(display)
            .unwrap_or_default();
        Diagnostic::error(
            "E-AMBIGUOUS",
            format!("`{}` could mean {}", item.text, or_list(&shown)),
        )
        .with_label(item.span, "it is a constructor of more than one type")
        .with_note(format!(
            "`{}` is a constructor of {}: import the type you mean, as in `import {namespace} ({})`",
            item.text,
            or_list(&types),
            short(parent(&keys[0]).unwrap_or(&keys[0])),
        ))
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
                    if let Some(context) = &self.unit.file_mode
                        && let Some(d) = context.diagnostic(&import.path.text, import.path.span)
                    {
                        diagnostics.push(d);
                        self.scope
                            .import_failed
                            .extend(import.items.iter().map(|i| i.local().text.clone()));
                        self.wildcard_failed(import);
                        continue;
                    }
                    // A namespace with syntax errors may have lost every
                    // name it declares, so the path itself isn't in scope:
                    // say why, once per imported name, rather than that
                    // there is no such namespace (§4.2).
                    if let Some(found) = self.import_unparsed_path(import) {
                        diagnostics.extend(found);
                        self.scope
                            .import_failed
                            .extend(import.items.iter().map(|i| i.local().text.clone()));
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
                    let example = import.items.first().map_or("..", |i| i.name.text.as_str());
                    if !self.unit.loading_prelude
                        && first != STD
                        && self.scope.is_namespace(&format!("Std.{first}"))
                    {
                        d = d.with_note(format!(
                            "`{first}` is `Std.{first}`, which isn't a default name: write `import Std.{} ({example})`",
                            import.path.text
                        ));
                    } else if let Some(source) = imports
                        .iter()
                        .find(|i| i.items.iter().any(|n| n.local().text == first))
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
                self.unit.loading_prelude || !(namespace == STD || namespace.starts_with("Std."));
            if is_own != own {
                // A library namespace imported as a qualifier was added
                // before the module's qualified declarations: now that they
                // are, one of the module's own namespaces may hide it.
                if own {
                    self.own_namespace_clashes(import, &namespace, diagnostics);
                }
                continue;
            }
            if import.everything.is_some() {
                self.add_wildcard(import, &namespace, diagnostics);
                continue;
            }
            // The types this import names: each brings its constructors, so
            // naming one beside its type is accepted and adds nothing.
            let types: Vec<String> = import
                .items
                .iter()
                .filter_map(|whole| {
                    let key = format!("{namespace}.{}", whole.name.text);
                    self.is_data_key(&key).then_some(key)
                })
                .collect();
            for whole in &import.items {
                let (name, item) = (&whole.name, whole.local());
                let mut key = format!("{namespace}.{}", name.text);
                // An item may be a namespace that declares no name of its
                // own (`import Std (Eq)`).
                if name.text.starts_with('%') {
                    diagnostics.push(self.import_unknown(&namespace, name));
                    continue;
                }
                if self.scope.get(&key).is_none() && !self.scope.is_namespace(&key) {
                    // A constructor by its short name, as a type brings its
                    // constructors: `import N (S)` imports just `S` (D3503).
                    match self.constructors_named(&namespace, &name.text).as_slice() {
                        [] => {
                            match self.import_unparsed_at(&namespace, name) {
                                Some(d) => {
                                    diagnostics.push(d);
                                    // What uses the name waits for the
                                    // syntax error, so it isn't reported
                                    // again as unknown (§4.2).
                                    self.scope.import_failed.insert(item.text.clone());
                                    self.scope.import_failed.insert(name.text.clone());
                                }
                                None => diagnostics.push(self.import_unknown(&namespace, name)),
                            }
                            continue;
                        }
                        [only] => {
                            let owner = parent(only).unwrap_or("");
                            if types.iter().any(|t| t == owner) {
                                // The type, named in this import, already
                                // brings it.
                                self.note_import(name, only);
                                continue;
                            }
                            key = only.clone();
                        }
                        many => {
                            diagnostics.push(self.ambiguous_import_ctor(name, many));
                            continue;
                        }
                    }
                }
                // A declaration of the module's own with this name would hide
                // the import completely.
                if let Resolved::Found {
                    level: Level::Module,
                    span,
                    ..
                } = self.resolve_short(&item.text, true)
                {
                    let imported = match &whole.alias {
                        Some(_) => format!("`{}` is imported as `{}`", name.text, item.text),
                        None => format!("`{}` is imported", item.text),
                    };
                    let message = match self.current_namespace() {
                        Some(namespace) if span.file != item.span.file => format!(
                            "{imported}, but `{}` is also defined in another file of namespace {namespace}",
                            item.text
                        ),
                        _ => format!("{imported}, but this file also defines `{}`", item.text),
                    };
                    // Written in full (`Std.List.length`): a full name works
                    // whatever the file imports, where `List.length` needs
                    // `import Std (List)`.
                    let write = if self.scope.get(&key).is_none() {
                        format!("`{key}.x` for a name `x` in that namespace")
                    } else {
                        format!("`{key}` where you mean that one")
                    };
                    diagnostics.push(
                        error("E-IMPORT-CLASH", item.span, message)
                            .with_label(span, "defined here, which would hide the import")
                            .with_note(format!("remove the import, and write {write}")),
                    );
                    continue;
                }
                // A namespace and not a declaration: a qualifier
                // (docs/proposals/import-aliases.md, D2072).
                let qualifier = self.scope.get(&key).is_none();
                if qualifier && own && self.own_namespace_clash(item, &key, diagnostics) {
                    continue;
                }
                self.note_import(name, &key);
                let file = self.current_file();
                if let Some(alias) = &whole.alias {
                    self.note_import(alias, &key);
                    if alias.text != name.text {
                        if self.scope.renamed.len() <= file {
                            self.scope.renamed.resize_with(file + 1, HashMap::default);
                        }
                        let locals = self.scope.renamed[file].entry(key.clone()).or_default();
                        if !locals.contains(&alias.text) {
                            locals.push(alias.text.clone());
                        }
                    }
                }
                let table = if qualifier {
                    &mut self.scope.qualifiers
                } else {
                    &mut self.scope.imports
                };
                if table.len() <= file {
                    table.resize_with(file + 1, HashMap::default);
                }
                let entry = table[file].entry(item.text.clone()).or_default();
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

    /// `E-IMPORT-CLASH` if the namespace `key`, imported as the qualifier
    /// `item`, is hidden by a namespace of the module's own of that name
    /// (from `def Spec.f` in this module): the module's own names come
    /// first, as for any import.
    fn own_namespace_clash(
        &self,
        item: &ast::Name,
        key: &str,
        diagnostics: &mut Vec<Diagnostic>,
    ) -> bool {
        if self.unit.loading_prelude || !CheckingLevels(self, true).own_namespace(&item.text) {
            return false;
        }
        let own = format!("{}{}", self.root(), item.text);
        let mut d = error(
            "E-IMPORT-CLASH",
            item.span,
            format!(
                "`{}` is imported as a namespace, but this module has its own `{}.…`",
                item.text, item.text
            ),
        );
        // Where the module's own namespace comes from: a declaration in it.
        let prefix = format!("{own}.");
        if let Some(span) = self
            .scope
            .entries
            .iter()
            .filter(|(k, _)| k.starts_with(&prefix))
            .map(|(_, (_, span))| *span)
            .min_by_key(|s| (s.file.index(), s.start))
        {
            d = d.with_label(
                span,
                format!(
                    "declared in `{}`, which would hide the import",
                    display(&own)
                ),
            );
        }
        diagnostics.push(d.with_note(format!(
            "`{0}.x` here means `{1}.x`; remove the import and write `{2}.x` for the imported one",
            item.text,
            display(&own),
            key
        )));
        true
    }

    /// [`Self::own_namespace_clash`] for the namespace items of a library
    /// import, which were added before the module's own namespaces were
    /// known: a clashing one is taken out again.
    fn own_namespace_clashes(
        &mut self,
        import: &Import,
        namespace: &str,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        let file = self.current_file();
        for whole in &import.items {
            let item = whole.local();
            let key = format!("{namespace}.{}", whole.name.text);
            if !self.imported_namespaces(&item.text).contains(&key)
                || !self.own_namespace_clash(item, &key, diagnostics)
            {
                continue;
            }
            if let Some(entry) = self
                .scope
                .qualifiers
                .get_mut(file)
                .and_then(|t| t.get_mut(&item.text))
            {
                entry.retain(|(k, _)| *k != key);
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
            (self.scope.wildcard_failed.entry(file))
                .or_insert_with(|| (import.path.text.clone(), import.path.span));
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
                if self.session.project_namespaces.contains(k) {
                    if self.scope.extenders.len() <= file {
                        self.scope.extenders.resize_with(file + 1, BTreeSet::new);
                    }
                    self.scope.extenders[file].insert(k.to_string());
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
                    if self.scope.has(&key) {
                        let keys = self.scope.wildcards[file].entry(x).or_default();
                        if let Err(at) = keys.binary_search_by(|(k, _)| k.as_str().cmp(&key)) {
                            keys.insert(at, (key, import.span));
                        }
                    }
                }
            }
            Some(WildcardSource::Refused(refusal)) => {
                diagnostics.push(self.refused_wildcard(&refusal, k, &import.path));
                (self.scope.wildcard_failed.entry(file))
                    .or_insert_with(|| (import.path.text.clone(), import.path.span));
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
                (self.scope.wildcard_failed.entry(file))
                    .or_insert_with(|| (import.path.text.clone(), import.path.span));
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
        if self.session.project_namespaces.contains(k) {
            return Some(match self.session.project_names.get(k) {
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
        if self.session.project_prefixes.contains(k) {
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
                // A record's generated `ext` lemma is a poor example of its
                // names: prefer anything else.
                .min_by_key(|x| (*x == "ext", *x))
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
                    .session
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

    /// `E-USES-FAILED` for an import whose namespace isn't in scope at all
    /// (it lost every declaration): one per item, or one for the whole
    /// namespace when it imports `(..)`.
    fn import_unparsed_path(&self, import: &Import) -> Option<Vec<Diagnostic>> {
        if import.everything.is_some() {
            let error_at = *self.session.project_syntax_errors.get(&import.path.text)?;
            let mut d = Diagnostic::error(
                "E-USES-FAILED",
                format!(
                    "`{}` has a syntax error, so its names can't be found",
                    import.path.text
                ),
            )
            .with_label(import.path.span, "its declarations are missing");
            if let Some(span) = error_at {
                d = d.with_label(span, "the syntax error is here");
            }
            return Some(vec![d]);
        }
        let found: Vec<Diagnostic> = (import.items.iter())
            .filter_map(|whole| self.import_unparsed_at(&import.path.text, &whole.name))
            .collect();
        (!found.is_empty()).then_some(found)
    }

    /// `E-USES-FAILED` for an import of `item` from `namespace`, which no
    /// longer declares it because its file has a syntax error
    /// (docs/proposals/tests-with-errors.md §4.2): `None` when the
    /// namespace has no syntax error, so the name is simply unknown.
    fn import_unparsed_at(&self, namespace: &str, item: &ast::Name) -> Option<Diagnostic> {
        let error_at = *self.session.project_syntax_errors.get(namespace)?;
        let mut d = Diagnostic::error(
            "E-USES-FAILED",
            format!(
                "`{}` has a syntax error, so `{}` can't be found",
                display(namespace),
                item.text
            ),
        )
        .with_label(item.span, format!("`{}` can't be found here", item.text));
        if let Some(span) = error_at {
            d = d.with_label(span, "the syntax error is here");
        }
        Some(d)
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

/// Printed terms name declarations as the module being checked would write
/// them, from its namespace and the current file's imports.
impl NameScope for Elaborator {
    fn names(&self, written: &str, declaration: Declaration) -> bool {
        let Resolved::Found {
            global, key, rest, ..
        } = self.resolve_any(written)
        else {
            return false;
        };
        if !rest.is_empty() {
            return false;
        }
        match (global, declaration) {
            (Global::Def(a), Declaration::Def(b)) => a == b,
            (Global::Data(a), Declaration::Data(b)) => a == b,
            (Global::Def(_) | Global::Data(_), _) => false,
            // Not checked yet, or not loaded: by key.
            _ => key == self.declaration_key_of(declaration),
        }
    }

    fn full_name(&self, declaration: Declaration) -> String {
        self.declaration_key_of(declaration)
    }

    fn aliases(&self, full: &str) -> Vec<String> {
        Elaborator::aliases(self, full)
    }

    fn method(&self, projection: DefId) -> Option<(DefId, String)> {
        Elaborator::method_of(self, projection)
    }
}

impl Elaborator {
    /// How the key `full` can be written through a name this file imports
    /// under another name: `y` for `M.x` after `import M (x as y)`, `T.f`
    /// for `M.Tree.f` after `import M (Tree as T)`. Nothing checks here that
    /// the spelling means `full`.
    pub(crate) fn aliases(&self, full: &str) -> Vec<String> {
        let Some(renamed) = self.scope.renamed.get(self.current_file()) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for (key, locals) in renamed {
            let rest = if full == key {
                Some("")
            } else {
                full.strip_prefix(key.as_str())
                    .filter(|r| r.starts_with('.'))
            };
            if let Some(rest) = rest {
                out.extend(locals.iter().map(|local| format!("{local}{rest}")));
            }
        }
        out.sort();
        out
    }

    /// Every short name the current file can write, with the key it
    /// resolves to, what that is and the level that decides it: the
    /// candidates for completing a name. A name that is ambiguous here is
    /// left out, as is one only the compiler writes (`%…`).
    pub(crate) fn short_names_visible(&self) -> Vec<(String, String, Global, Level)> {
        let mut shorts: BTreeSet<&str> = BTreeSet::new();
        let root = self.root();
        for key in self.scope.entries.keys() {
            let rest = if root.is_empty() {
                Some(key.as_str())
            } else {
                key.strip_prefix(root)
            };
            if let Some(rest) = rest.filter(|r| !r.contains('.')) {
                shorts.insert(rest);
            }
        }
        let file = self.current_file();
        if let Some(table) = self.scope.imports.get(file) {
            shorts.extend(table.keys().map(String::as_str));
        }
        if let Some(table) = self.scope.wildcards.get(file) {
            shorts.extend(table.keys().map(String::as_str));
        }
        shorts.extend(
            PRELUDE
                .iter()
                .copied()
                .filter(|x| self.scope.std_root.contains_key(*x)),
        );
        shorts.extend(self.scope.followers.keys().map(String::as_str));
        shorts
            .into_iter()
            .filter(|x| !x.is_empty() && !x.starts_with('%'))
            .filter_map(|x| match self.resolve_short(x, true) {
                Resolved::Found {
                    global, key, level, ..
                } => Some((x.to_string(), key.to_string(), global, level)),
                _ => None,
            })
            .collect()
    }
}

impl Elaborator {
    /// The library's names one import would bring here, by short name, as
    /// the unknown-name error suggests them: a root name outside the
    /// prelude (`import Std (Map)`), or the one declaration of the
    /// library's namespaces with that short name (`import Std.List
    /// (replicate)`). Each with its key, what it is, and the import's path.
    pub(crate) fn importable_names(&self) -> Vec<(String, String, Global, String)> {
        if self.unit.loading_prelude {
            return Vec::new();
        }
        let mut by_short: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for key in self.scope.entries.keys() {
            let Some(path) = key.strip_prefix("Std.") else {
                continue;
            };
            let name = short(key);
            if name.starts_with('%') {
                continue;
            }
            if !path.contains('.') {
                if !self.scope.is_prelude(name) {
                    by_short.entry(name).or_default().insert(0, STD);
                }
            } else if parent(key).is_some_and(|p| p.contains('.')) {
                by_short.entry(name).or_default().push(key);
            }
        }
        by_short
            .into_iter()
            .filter_map(|(name, keys)| {
                let (path, key) = match keys.as_slice() {
                    [STD, ..] => (STD.to_string(), format!("{STD}.{name}")),
                    [key] => (parent(key)?.to_string(), key.to_string()),
                    _ => return None,
                };
                let (global, _) = self.scope.get(&key)?;
                Some((name.to_string(), key, global, path))
            })
            .collect()
    }

    /// The members of the namespace written `written` (`List`, `Std`,
    /// `Shop.Spec`) that it reaches here: each as written after it, with
    /// its key and what it is, then the namespaces under it that are no
    /// declaration (`(name, key, None)`). Empty if `written` isn't a
    /// namespace here.
    pub(crate) fn namespace_members(&self, written: &str) -> Vec<(String, String, Option<Global>)> {
        let (first, rest) = match written.split_once('.') {
            Some((first, rest)) => (first, format!(".{rest}")),
            None => (written, String::new()),
        };
        let mut prefixes: BTreeSet<String> = [
            format!("{}{written}.", self.root()),
            format!("{written}."),
            format!("{STD}.{written}."),
        ]
        .into_iter()
        .collect();
        prefixes.extend(
            self.imported_namespaces(first)
                .into_iter()
                .map(|q| format!("{q}{rest}.")),
        );
        let mut out: Vec<(String, String, Option<Global>)> = Vec::new();
        for key in self.scope.entries.keys() {
            for prefix in &prefixes {
                let Some(member) = key.strip_prefix(prefix.as_str()) else {
                    continue;
                };
                if member.contains('.') || member.starts_with('%') {
                    continue;
                }
                if let Resolved::Found {
                    key: found,
                    global,
                    rest,
                    ..
                } = self.resolve_any(&format!("{written}.{member}"))
                    && found == key
                    && rest.is_empty()
                    && !out.iter().any(|(m, ..)| m == member)
                {
                    out.push((member.to_string(), key.clone(), Some(global)));
                }
            }
        }
        for ns in self.scope.namespaces.keys() {
            for prefix in &prefixes {
                if let Some(member) = ns.strip_prefix(prefix.as_str())
                    && !member.contains('.')
                    && !out.iter().any(|(m, ..)| m == member)
                {
                    out.push((member.to_string(), ns.clone(), None));
                }
            }
        }
        out
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

/// Names other languages use for what std calls something else, per
/// namespace: `(namespace, [aliases], [std names])`. Aliases compare
/// ignoring case; a std name is only ever suggested when it exists.
const MEANING_TABLE: &[(&str, &[&str], &[&str])] = &[
    (
        "Char",
        &["isLower", "isLowerCase", "isLowercase"],
        &["isAsciiLowercase"],
    ),
    (
        "Char",
        &["isUpper", "isUpperCase", "isUppercase"],
        &["isAsciiUppercase"],
    ),
    (
        "Char",
        &["isAlpha", "isLetter", "isAlphabetic"],
        &["isAsciiLetter"],
    ),
    (
        "Char",
        &["isSpace", "isBlank"],
        &["isWhitespace", "isAsciiSpace"],
    ),
    (
        "Char",
        &["isAlphaNum", "isAlnum", "isAlphanumeric"],
        &["isAsciiAlphanumeric"],
    ),
    ("Char", &["ord", "code", "toInt", "toCode"], &["toNat"]),
    ("Char", &["chr", "ofNat"], &["fromNat"]),
    ("List", &["size", "len", "count"], &["length"]),
    (
        "List",
        &["includes", "has", "member", "isMember"],
        &["contains"],
    ),
    ("List", &["fold", "foldl", "reduce"], &["foldLeft"]),
    ("List", &["foldr"], &["foldRight"]),
    ("List", &["flatten"], &["concat"]),
    ("List", &["each", "foreach", "for_each"], &["forEach"]),
    ("List", &["first", "car"], &["head"]),
    ("List", &["reversed"], &["reverse"]),
    ("List", &["uniq", "nub", "distinct"], &["dedup", "unique"]),
    ("List", &["max"], &["maximum"]),
    ("List", &["min"], &["minimum"]),
    ("List", &["exists", "some"], &["any"]),
    ("List", &["forall", "every"], &["all"]),
    ("List", &["empty", "null", "isNull"], &["isEmpty"]),
    ("List", &["push", "add", "concatenate"], &["append"]),
    ("Text", &["size", "len"], &["length"]),
    ("Text", &["includes", "has"], &["contains"]),
    ("Text", &["strip"], &["trim"]),
    ("Text", &["parseInt"], &["toInt", "toNat"]),
    ("Text", &["parseNat"], &["toNat"]),
    ("Text", &["concat"], &["append"]),
    ("Text", &["empty", "null"], &["isEmpty"]),
    ("Text", &["splitBy"], &["split"]),
    ("Text", &["chars"], &["toList"]),
    ("Text", &["startswith", "hasPrefix"], &["startsWith"]),
    ("Text", &["hasSuffix"], &["endsWith"]),
    ("Option", &["isDefined", "isPresent"], &["isSome"]),
    ("Option", &["isEmpty"], &["isNone"]),
    (
        "Option",
        &["unwrapOr", "getOr", "withDefault", "valueOr"],
        &["getOrElse"],
    ),
    ("Option", &["bind", "andThen", "then"], &["flatMap"]),
    ("Map", &["length", "len", "count"], &["size"]),
    (
        "Map",
        &["has", "containsKey", "hasKey", "member"],
        &["contains"],
    ),
    ("Map", &["put", "set", "add"], &["insert"]),
    ("Map", &["delete", "erase"], &["remove"]),
    ("Map", &["entries", "items", "toArray"], &["toList"]),
    ("Map", &["getOrDefault", "findWithDefault"], &["getOr"]),
    ("Nat", &["plus", "sum"], &["add"]),
    ("Nat", &["minus", "subtract"], &["sub"]),
    ("Nat", &["times", "multiply"], &["mul"]),
    ("Nat", &["divide"], &["div"]),
    ("Nat", &["modulo", "rem", "remainder"], &["mod"]),
    ("Nat", &["power", "exp"], &["pow"]),
    ("Nat", &["maximum"], &["max"]),
    ("Nat", &["minimum"], &["min"]),
    ("Nat", &["toString"], &["toText"]),
];

/// The members of namespace `key` (written `Std.Char` or `Char`) that
/// `member` is another language's name for, as std spells them. `exists`
/// says whether `key.name` is declared, so only real names come back.
pub fn meaning_suggestions(key: &str, member: &str, exists: impl Fn(&str) -> bool) -> Vec<String> {
    let namespace = key.rsplit('.').next().unwrap_or(key);
    let mut found: Vec<String> = Vec::new();
    for (ns, aliases, targets) in MEANING_TABLE {
        if *ns == namespace && aliases.iter().any(|a| a.eq_ignore_ascii_case(member)) {
            for t in *targets {
                if exists(&format!("{key}.{t}")) && !found.iter().any(|f| f == t) {
                    found.push((*t).to_string());
                }
            }
        }
    }
    found
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
