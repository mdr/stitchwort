//! The standard library's files, its name index, and loading it on demand
//! (docs/proposals/std-library.md).
//!
//! The always-loaded **core** is the files of `std/core/`, joined (`PRELUDE`). Everything else is a
//! **library file** under `std/`, checked only when a program uses
//! something in it. Lazy loading is an implementation detail (§4.0): a
//! program resolves and elaborates exactly as if every file were loaded.
//! That is by construction:
//!
//! - **The index is part of name resolution.** [`LibraryIndex`] lists every
//!   name each file declares, the generated ones too, and
//!   [`Elaborator::install_library`] enters each as a [`Global::Pending`]
//!   in the one name table. Resolution, imports, the namespace tree,
//!   ambiguity, dot notation and suggestions all read that table, so none of
//!   them can depend on what is loaded, and none of them loads anything.
//!   When a file loads, its names' entries are replaced in place.
//! - **Loading is driven by references.** Before a module is checked, every
//!   reference it makes that resolves to a pending name names a file to
//!   load. A dot call `x.f` names every file with an `f` in a namespace
//!   whose type is in the core, loaded, or loading with it ([`DotTarget`]):
//!   only those can be `x`'s type. A file's own references name the files
//!   it needs, found the same way, once, when the index is built. Files
//!   load in a canonical order (dependency order, ties by path).
//! - **A request for a file that is loading is a cycle**, reported as an
//!   internal error naming both files, never a hang or a silent skip.
//!
//! Library files are elaborated as the prelude is: names are written as in
//! `std/core/`, in the namespace they declare into.

use std::cmp::Reverse;
use std::collections::{BTreeSet, BinaryHeap, HashMap};
use std::sync::{Arc, OnceLock};

use stitchwort_syntax::ast::{Decl, Expr, Module};
use stitchwort_syntax::{Diagnostic, FileId, Severity, SourceMap, Span, parse_module_within};

use crate::module::{ModuleState, Ref, decl_refs, declared_names, expr_refs};
use crate::project::{SourceUnit, grouped};
use crate::scope::{self, Resolved};
use crate::{Elaborator, Global, PRELUDE};

/// The library files, `(path under std/, text)`, sorted by path. A test
/// checks this lists every `.sw` file under `std/`.
pub const LIBRARY_FILES: &[(&str, &str)] = &[
    ("Abort/Abort.sw", include_str!("std/Abort/Abort.sw")),
    ("Bool/Bool.sw", include_str!("std/Bool/Bool.sw")),
    (
        "Decidable/Decidable.sw",
        include_str!("std/Decidable/Decidable.sw"),
    ),
    ("Each/Each.sw", include_str!("std/Each/Each.sw")),
    ("Fin/Fin.sw", include_str!("std/Fin/Fin.sw")),
    ("Int/Basics.sw", include_str!("std/Int/Basics.sw")),
    ("Int/Int.sw", include_str!("std/Int/Int.sw")),
    ("List/Attach.sw", include_str!("std/List/Attach.sw")),
    ("List/Grid.sw", include_str!("std/List/Grid.sw")),
    ("List/Index.sw", include_str!("std/List/Index.sw")),
    ("List/Sort.sw", include_str!("std/List/Sort.sw")),
    ("List/Toolkit.sw", include_str!("std/List/Toolkit.sw")),
    ("List/Unfold.sw", include_str!("std/List/Unfold.sw")),
    ("Logic/Logic.sw", include_str!("std/Logic/Logic.sw")),
    ("Map/Map.sw", include_str!("std/Map/Map.sw")),
    ("Mod/Mod.sw", include_str!("std/Mod/Mod.sw")),
    ("Nat/Arith.sw", include_str!("std/Nat/Arith.sw")),
    ("Nat/Digits.sw", include_str!("std/Nat/Digits.sw")),
    ("Nat/Divides.sw", include_str!("std/Nat/Divides.sw")),
    ("Nat/Iterate.sw", include_str!("std/Nat/Iterate.sw")),
    ("Omega/Omega.sw", include_str!("std/Omega/Omega.sw")),
    ("Omega/Sound.sw", include_str!("std/Omega/Sound.sw")),
    ("Option/Option.sw", include_str!("std/Option/Option.sw")),
    ("Ord/Ord.sw", include_str!("std/Ord/Ord.sw")),
    ("Set/Set.sw", include_str!("std/Set/Set.sw")),
    ("Text/Basics.sw", include_str!("std/Text/Basics.sw")),
    ("Text/Text.sw", include_str!("std/Text/Text.sw")),
    ("Vec/Grid.sw", include_str!("std/Vec/Grid.sw")),
    ("Vec/Vec.sw", include_str!("std/Vec/Vec.sw")),
];

/// What a name the index promises is, as far as resolution cares.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PendingKind {
    Def,
    Data,
    Ctor,
    /// An ability's operation: not a default name (SW-134).
    Op,
    Other,
}

/// One name a file declares.
#[derive(Clone, Debug)]
pub struct IndexedName {
    pub key: String,
    pub kind: PendingKind,
    /// A constructor or operation: visible wherever its type or ability is.
    pub follower: bool,
    /// A definition declared with a function type (`W-LAMBDA-SHADOW` asks
    /// before the file is loaded).
    pub function: bool,
    pub span: Span,
}

/// One file of the library, parsed once.
pub struct IndexedFile {
    /// Its path under `std/` (`core` for the core).
    pub path: String,
    pub id: FileId,
    pub text: String,
    pub module: Module,
    /// Every name it declares, generated ones included.
    pub names: Vec<IndexedName>,
    /// The files it needs, by index: every reference resolved to its owning
    /// file (dot notation: every file with a function of that name). Never
    /// itself or the core.
    pub edges: Vec<usize>,
}

/// Every name the core and the library files declare, with the file that
/// owns it. Built once per process ([`LibraryIndex::standard`]).
pub struct LibraryIndex {
    /// The core first, then the library files by path.
    pub files: Vec<IndexedFile>,
    owner: HashMap<String, usize>,
    /// What a dot call `x.name` might mean in the library: every function
    /// whose last name component is the key, as the file it's in and the
    /// file that declares its namespace.
    dots_by_short: HashMap<String, Vec<DotTarget>>,
}

/// A library function `T.f` that a dot call `x.f` might mean.
///
/// `x.f` means `T.f` only when `x`'s type has `T` at its head (or unfolds
/// to one that does, `dot.rs`), and a type can only be built from `T` once
/// the file declaring `T` is loaded: a pending name never reaches the
/// checker. So `x.f` needs `T.f`'s file only when `T`'s file is loaded or
/// is being loaded with it. That is how a `List` program's `xs.size` stays
/// clear of `Mod.size`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DotTarget {
    /// The file declaring `T`: `None` if no file declares a name `T` (the
    /// built-in `Eq`, say), and then the target counts as always reachable.
    pub namespace: Option<usize>,
    /// The file declaring `T.f`.
    pub file: usize,
}

/// What a module's or an expression's references need from the library:
/// files by name, and the fields of its dot calls, which need files only
/// depending on what else loads ([`LibraryIndex::resolve_needs`]).
#[derive(Clone, Debug, Default)]
pub(crate) struct Needs {
    pub files: BTreeSet<usize>,
    pub dots: BTreeSet<String>,
}

static STANDARD: OnceLock<Result<Arc<LibraryIndex>, String>> = OnceLock::new();

impl LibraryIndex {
    /// The index of the standard library, built the first time it's asked
    /// for. `stack` bounds the parser's recursion.
    pub fn standard(stack: usize) -> Result<Arc<LibraryIndex>, String> {
        STANDARD
            .get_or_init(|| LibraryIndex::build(PRELUDE, LIBRARY_FILES, stack).map(Arc::new))
            .clone()
    }

    /// The index of a core and library files given as text, for tests of
    /// the index and of the loader. Rejects a name declared twice.
    pub fn build(core: &str, files: &[(&str, &str)], stack: usize) -> Result<LibraryIndex, String> {
        let mut sorted: Vec<(&str, &str)> = files.to_vec();
        sorted.sort_by_key(|(path, _)| *path);
        let mut sources = SourceMap::new();
        let mut parsed: Vec<IndexedFile> = Vec::new();
        for (path, text) in std::iter::once(("core", core)).chain(sorted) {
            let id = sources.add(path, text);
            let module = parse_module_within(id, text, stack).map_err(|errors| {
                let mut report = format!("the library file `{path}` doesn't parse:");
                for d in errors {
                    report.push_str(&format!("\n  {}: {}", d.code, d.message));
                }
                report
            })?;
            parsed.push(IndexedFile {
                path: path.to_string(),
                id,
                text: text.to_string(),
                module,
                names: Vec::new(),
                edges: Vec::new(),
            });
        }

        // The names, from a scratch elaborator that reads declarations the
        // way loading them does.
        let mut scratch = Elaborator::new();
        scratch.loading_prelude = true;
        let mut owner: HashMap<String, usize> = HashMap::new();
        for f in 0..parsed.len() {
            let names = file_names(&scratch, &parsed[f])?;
            for name in &names {
                if let Some(&first) = owner.get(&name.key) {
                    return Err(format!(
                        "`{}` is declared twice: in `{}` and in `{}`",
                        name.key, parsed[first].path, parsed[f].path
                    ));
                }
                owner.insert(name.key.clone(), f);
            }
            parsed[f].names = names;
        }
        let mut dots_by_short: HashMap<String, Vec<DotTarget>> = HashMap::new();
        for (f, file) in parsed.iter().enumerate().skip(1) {
            for name in file.names.iter().filter(|n| n.kind == PendingKind::Def) {
                let namespace = name
                    .key
                    .rsplit_once('.')
                    .and_then(|(ns, _)| owner.get(ns).copied());
                let target = DotTarget { namespace, file: f };
                let targets = dots_by_short.entry(scope::short(&name.key).to_string());
                let targets = targets.or_default();
                if !targets.contains(&target) {
                    targets.push(target);
                }
            }
        }
        let mut index = LibraryIndex {
            files: parsed,
            owner,
            dots_by_short,
        };

        // The edges: each reference resolved to the file that owns it, by
        // the resolver itself, in a scratch scope where every name is
        // pending.
        for (f, file) in index.files.iter().enumerate() {
            for name in &file.names {
                scratch.scope.insert(
                    &name.key,
                    Global::Pending(f, name.kind),
                    name.span,
                    name.follower,
                );
            }
        }
        let mut needs: Vec<Needs> = Vec::new();
        for (f, file) in index.files.iter().enumerate() {
            let mut n = Needs::default();
            for (decl, equations) in grouped(&file.module.decls) {
                for (r, _) in decl_refs(decl, equations) {
                    scratch.note_library_use(&index, &r, &mut n);
                }
            }
            n.files.remove(&f);
            n.files.remove(&0);
            needs.push(n);
        }
        for (file, n) in index.files.iter_mut().zip(&needs) {
            file.edges = n.files.iter().copied().collect();
        }
        // A file's dot calls need what they can reach given what the file
        // itself needs: the values it makes have types from those files
        // only. Adding an edge can make more reachable, so until nothing
        // changes. The result is fixed per file, whatever else is loaded,
        // so the check cache's keys and the load order can read `edges`.
        loop {
            let mut changed = false;
            for (f, n) in needs.iter().enumerate().skip(1) {
                let reach = index.closure(&BTreeSet::from([f]), &|_| false);
                let mut add = Vec::new();
                for field in &n.dots {
                    for t in index.dot_targets(field) {
                        // Not a file that already needs `f`: `f` can't use
                        // it, and the edge would be a cycle. `[1, 2].span p`
                        // in `List/Toolkit.sw` has the target `Nat.span` in
                        // `List/Sort.sw` (the core's `Nat` is always
                        // reachable), and Sort needs the Toolkit (SW-254).
                        if t.file != f
                            && !index
                                .closure(&BTreeSet::from([t.file]), &|_| false)
                                .contains(&f)
                            && !index.files[f].edges.contains(&t.file)
                            && !add.contains(&t.file)
                            && t.namespace.is_none_or(|ns| ns == 0 || reach.contains(&ns))
                        {
                            add.push(t.file);
                        }
                    }
                }
                if !add.is_empty() {
                    changed = true;
                    let edges = &mut index.files[f].edges;
                    edges.extend(add);
                    edges.sort_unstable();
                }
            }
            if !changed {
                break;
            }
        }
        Ok(index)
    }

    /// The files `roots` need that aren't `loaded`, themselves included,
    /// following the edges.
    fn closure(&self, roots: &BTreeSet<usize>, loaded: &dyn Fn(usize) -> bool) -> BTreeSet<usize> {
        let mut set = BTreeSet::new();
        let mut stack: Vec<usize> = roots.iter().copied().filter(|f| !loaded(*f)).collect();
        while let Some(f) = stack.pop() {
            if !set.insert(f) {
                continue;
            }
            stack.extend(self.files[f].edges.iter().copied().filter(|d| !loaded(*d)));
        }
        set
    }

    /// The files to load for `needs`, given the files already `loaded`:
    /// the files it names, and the target of each dot call whose namespace
    /// is declared in the core, in a loaded file, or in a file loading now
    /// (these, until nothing more is added). When a dot call's namespace
    /// can't be told, its file is loaded.
    pub(crate) fn resolve_needs(
        &self,
        needs: &Needs,
        loaded: &dyn Fn(usize) -> bool,
    ) -> BTreeSet<usize> {
        let mut roots: BTreeSet<usize> = needs
            .files
            .iter()
            .copied()
            .filter(|f| !loaded(*f))
            .collect();
        loop {
            let reach = self.closure(&roots, loaded);
            let before = roots.len();
            for field in &needs.dots {
                for t in self.dot_targets(field) {
                    let reachable = t
                        .namespace
                        .is_none_or(|ns| ns == 0 || loaded(ns) || reach.contains(&ns));
                    if reachable && !loaded(t.file) {
                        roots.insert(t.file);
                    }
                }
            }
            if roots.len() == before {
                return roots;
            }
        }
    }

    /// The file that declares `key`, if any (the core is file 0).
    pub fn owner(&self, key: &str) -> Option<usize> {
        self.owner.get(key).copied()
    }

    /// Every full name the index holds, with its file.
    pub fn names(&self) -> impl Iterator<Item = (&str, usize)> {
        self.owner.iter().map(|(k, f)| (k.as_str(), *f))
    }

    /// The library functions with this last name component.
    pub fn dot_targets(&self, field: &str) -> &[DotTarget] {
        self.dots_by_short.get(field).map_or(&[], Vec::as_slice)
    }

    /// The order to load `roots` in, with everything they need that isn't
    /// `loaded` yet: dependencies first, and among the files ready, the
    /// first by path. It depends on the set of files only, never on the
    /// order a program mentions things. `Err` is a cycle among the files.
    pub fn load_order(
        &self,
        roots: &BTreeSet<usize>,
        loaded: &dyn Fn(usize) -> bool,
    ) -> Result<Vec<usize>, Vec<usize>> {
        let set = self.closure(roots, loaded);
        let mut waiting: HashMap<usize, usize> = set
            .iter()
            .map(|&f| {
                let n = self.files[f]
                    .edges
                    .iter()
                    .filter(|d| set.contains(d))
                    .count();
                (f, n)
            })
            .collect();
        let mut ready: BinaryHeap<Reverse<usize>> = waiting
            .iter()
            .filter(|(_, n)| **n == 0)
            .map(|(f, _)| Reverse(*f))
            .collect();
        let mut order = Vec::new();
        while let Some(Reverse(f)) = ready.pop() {
            order.push(f);
            for &user in &set {
                if self.files[user].edges.contains(&f) {
                    let n = waiting.get_mut(&user).expect("in the set");
                    *n -= 1;
                    if *n == 0 {
                        ready.push(Reverse(user));
                    }
                }
            }
        }
        if order.len() == set.len() {
            return Ok(order);
        }
        // Whatever is left has a cycle: follow dependencies until one
        // repeats.
        let left: BTreeSet<usize> = set
            .difference(&order.iter().copied().collect())
            .copied()
            .collect();
        let mut path = vec![*left.iter().next().expect("something is left")];
        loop {
            let last = *path.last().expect("not empty");
            let next = self.files[last]
                .edges
                .iter()
                .copied()
                .find(|d| left.contains(d))
                .expect("a file left over depends on another left over");
            if let Some(at) = path.iter().position(|&p| p == next) {
                return Err(path[at..].to_vec());
            }
            path.push(next);
        }
    }

    /// Words for a cycle of files: "`a` needs `b`, which needs `a`".
    pub fn cycle_message(&self, cycle: &[usize]) -> String {
        let name = |f: usize| format!("`std/{}`", self.files[f].path);
        match cycle {
            [a] => format!("the library file {} needs itself", name(*a)),
            [a, b] => format!(
                "the library files {} and {} need each other",
                name(*a),
                name(*b)
            ),
            [first, rest @ ..] => {
                let mut s = format!("the library file {}", name(*first));
                for f in rest {
                    s.push_str(&format!(" needs {}, which", name(*f)));
                }
                s.push_str(&format!(" needs {}", name(*first)));
                s
            }
            [] => String::new(),
        }
    }
}

/// Every name `file` declares: each declaration's own, the constructors,
/// operations and record fields it generates, and what an ability
/// generates.
pub(crate) fn file_names(
    scratch: &Elaborator,
    file: &IndexedFile,
) -> Result<Vec<IndexedName>, String> {
    let mut out = Vec::new();
    for (decl, _) in grouped(&file.module.decls) {
        let (main, members) = declared_names(decl);
        let Some(main) = main else { continue };
        let key = scratch
            .declaration_key(&main)
            .map_err(|d| format!("`{}`: {}", file.path, d.message))?;
        let (own, member) = match decl {
            Decl::Data { .. } => (PendingKind::Data, PendingKind::Ctor),
            Decl::Signature { .. } => (PendingKind::Def, PendingKind::Other),
            _ => (PendingKind::Other, PendingKind::Op),
        };
        out.push(IndexedName {
            key: key.clone(),
            kind: own,
            follower: false,
            function: matches!(decl, Decl::Signature { ty, .. } if crate::module::is_function_type(ty)),
            span: main.span,
        });
        // An interface's fields are its methods: definitions, listed below.
        let interface = matches!(
            decl,
            Decl::Data {
                interface: true,
                ..
            }
        );
        for (name, follower) in members {
            if interface && !follower {
                continue;
            }
            out.push(IndexedName {
                key: Elaborator::member_key(&key, &name.text),
                kind: if follower { member } else { PendingKind::Other },
                follower,
                function: follower,
                span: name.span,
            });
        }
        // A record's fields are functions in its namespace.
        if let Decl::Data {
            record: true,
            ctors,
            ..
        } = decl
        {
            for binder in ctors.iter().flat_map(|c| &c.fields) {
                for name in &binder.names {
                    out.push(IndexedName {
                        key: Elaborator::member_key(&key, &name.text),
                        kind: PendingKind::Def,
                        follower: false,
                        function: true,
                        span: name.span,
                    });
                    // An interface's own projections, beside its methods.
                    if interface {
                        out.push(IndexedName {
                            key: Elaborator::member_key(&key, &format!("%{}", name.text)),
                            kind: PendingKind::Def,
                            follower: false,
                            function: true,
                            span: name.span,
                        });
                    }
                }
            }
        }
    }
    Ok(out)
}

/// Whether a library file is loaded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LoadState {
    NotLoaded,
    Loading,
    Loaded,
}

/// What an elaborator knows about the library: the index, and the state of
/// each file.
#[derive(Clone)]
pub(crate) struct LibraryState {
    pub index: Arc<LibraryIndex>,
    pub state: Vec<LoadState>,
    /// The files being loaded, outermost first.
    pub stack: Vec<usize>,
    /// The files loaded so far, in order.
    pub order: Vec<usize>,
}

/// What a nested load sets aside and puts back.
struct Context {
    module: ModuleState,
    namespace_root: String,
    globals_module: stitchwort_core::Name,
    imports: scope::SavedImports,
    file_mode: Option<crate::project::FileModeContext>,
    loading_prelude: bool,
    warnings: Vec<Diagnostic>,
    lambda_warnings: Vec<Diagnostic>,
}

impl Elaborator {
    /// Enters every name the library files declare as pending, once the
    /// core is loaded, and starts tracking the files.
    /// Whether the library name `written`, declared by the file `file` that
    /// isn't loaded, is a definition with a function type.
    pub(crate) fn pending_is_function(&self, written: &str, file: usize) -> bool {
        let (Some(lib), scope::Resolved::Found { key, .. }) =
            (&self.library, self.resolve(written))
        else {
            return false;
        };
        lib.index.files[file]
            .names
            .iter()
            .any(|n| n.key == key && n.function)
    }

    pub fn install_library(&mut self, index: Arc<LibraryIndex>) {
        let mut state = vec![LoadState::NotLoaded; index.files.len()];
        state[0] = LoadState::Loaded;
        for (f, file) in index.files.iter().enumerate().skip(1) {
            for name in &file.names {
                // A name the core already has stays the core's; loading
                // the file then reports the clash.
                if self.scope.entries.contains_key(&name.key) {
                    continue;
                }
                self.scope.insert(
                    &name.key,
                    Global::Pending(f, name.kind),
                    name.span,
                    name.follower,
                );
            }
        }
        self.library = Some(LibraryState {
            index,
            state,
            stack: Vec::new(),
            order: Vec::new(),
        });
    }

    /// Every key in the name table, for tests of the index.
    #[doc(hidden)]
    pub fn scope_keys(&self) -> Vec<String> {
        self.scope.keys().cloned().collect()
    }

    /// The keys that name a library file's declaration that isn't loaded.
    #[doc(hidden)]
    pub fn pending_keys(&self) -> Vec<String> {
        self.scope
            .entries
            .iter()
            .filter(|(_, (g, _))| matches!(g, Global::Pending(..)))
            .map(|(k, _)| k.clone())
            .collect()
    }

    /// The definitions made since the core was loaded (the library files',
    /// when called before any program is) whose result type is a
    /// `Decidable …`: D58 says there are none, so `auto` never depends on
    /// what's loaded.
    #[doc(hidden)]
    pub fn library_decision_procedures(&self) -> Vec<String> {
        use stitchwort_core::registry::Builtin;
        use stitchwort_core::{DefId, Value};
        let g = &self.globals;
        let _op = g.budget.operation(self.limits);
        let decidable = g.registry.data(Builtin::Decidable);
        let mut found = Vec::new();
        for id in self.prelude_defs..g.defs.len() {
            let mut ty = g.def(DefId(id)).ty_value.clone();
            let mut level = 0;
            while let Value::Pi(_, _, _, cod) = &ty {
                let Ok(next) = cod
                    .apply(g, Value::var(level))
                    .and_then(|v| stitchwort_core::value::force(g, v))
                else {
                    break;
                };
                ty = next;
                level += 1;
            }
            if matches!(ty, Value::Data(d, _) if Some(d) == decidable) {
                found.push(g.def(DefId(id)).path.to_string());
            }
        }
        found
    }

    /// Whether no library file is loading.
    pub(crate) fn library_stack_is_empty(&self) -> bool {
        self.library.as_ref().is_none_or(|lib| lib.stack.is_empty())
    }

    /// The library index, if there is one.
    pub(crate) fn library_index(&self) -> Option<Arc<LibraryIndex>> {
        self.library.as_ref().map(|lib| lib.index.clone())
    }

    /// The paths of the library files loaded so far, in the order they
    /// loaded.
    pub fn loaded_library_files(&self) -> Vec<String> {
        self.library.as_ref().map_or_else(Vec::new, |lib| {
            lib.order
                .iter()
                .map(|&f| lib.index.files[f].path.clone())
                .collect()
        })
    }

    /// Notes the library files a reference needs: the file that owns the
    /// library name it resolves to, and for dot notation (whose target
    /// depends on a type the pre-pass doesn't know) the field, which
    /// [`LibraryIndex::resolve_needs`] turns into files.
    ///
    /// A file is noted whether or not it is loaded already, so what a
    /// module needs doesn't depend on what loaded before it: the check
    /// cache keeps a namespace's needs and loads them when it replays the
    /// namespace in another run, where other files may be loaded (SW-255).
    /// Loading skips the files that are loaded.
    pub(crate) fn note_library_use(&self, index: &LibraryIndex, r: &Ref<'_>, needs: &mut Needs) {
        let (n, mut fields) = match r {
            Ref::Name(n) => (n, Vec::new()),
            Ref::Dot(n, field) => (n, vec![field.clone()]),
        };
        if fields.is_empty()
            && let Resolved::Found {
                global, rest, key, ..
            } = self.resolve(&n.text)
        {
            match global {
                Global::Pending(f, _) => {
                    needs.files.insert(f);
                }
                // A library file's name that is loaded already (file 0
                // is the core).
                _ => {
                    if let Some(f) = index.owner(key).filter(|&f| f != 0) {
                        needs.files.insert(f);
                    }
                }
            }
            fields = rest;
        }
        for field in fields {
            if !index.dot_targets(&field).is_empty() {
                needs.dots.insert(field);
            }
        }
    }

    /// Loads what a program's references need (files, and the files its
    /// dot calls can reach given what will be loaded), and what those need,
    /// in canonical order.
    pub(crate) fn load_needs(&mut self, needs: &Needs) -> Result<(), Vec<Diagnostic>> {
        let Some(lib) = &self.library else {
            return Ok(());
        };
        let roots = lib
            .index
            .resolve_needs(needs, &|f| lib.state[f] == LoadState::Loaded);
        if roots.is_empty() {
            return Ok(());
        }
        self.load_libraries(&roots)
    }

    /// Loads `needs` and what they need, in canonical order.
    pub(crate) fn load_libraries(
        &mut self,
        needs: &BTreeSet<usize>,
    ) -> Result<(), Vec<Diagnostic>> {
        let Some(lib) = &self.library else {
            return Ok(());
        };
        let index = lib.index.clone();
        let order = index
            .load_order(needs, &|f| lib.state[f] == LoadState::Loaded)
            .map_err(|cycle| vec![internal(index.cycle_message(&cycle))])?;
        for f in order {
            self.load_library_file(f)?;
        }
        Ok(())
    }

    /// The error for a library file that uses files that aren't loaded: a
    /// file being loaded (a cycle), or one the dependency analysis missed.
    pub(crate) fn unloaded_needs(&self, needs: &BTreeSet<usize>) -> Vec<Diagnostic> {
        let Some(lib) = &self.library else {
            return Vec::new();
        };
        let by = lib.stack.last().copied().unwrap_or(0);
        needs
            .iter()
            .filter(|&&f| lib.state[f] != LoadState::Loaded)
            .map(|&f| {
                if lib.state[f] == LoadState::Loading {
                    internal(lib.index.cycle_message(&[by, f]))
                } else {
                    internal(format!(
                        "the library file `std/{}` uses `std/{}`, which isn't loaded",
                        lib.index.files[by].path, lib.index.files[f].path
                    ))
                    .with_note("the loader's reference analysis missed this use")
                }
            })
            .collect()
    }

    /// Loads every library file, in canonical order: the test-only "eager
    /// `Std`" mode.
    pub fn load_all_libraries(&mut self) -> Result<(), Vec<Diagnostic>> {
        let Some(lib) = &self.library else {
            return Ok(());
        };
        let all: BTreeSet<usize> = (1..lib.index.files.len()).collect();
        self.load_libraries(&all)
    }

    /// Loads the files an expression typed in needs (`eval`, the REPL).
    pub fn prepare_expr(&mut self, expr: &Expr) -> Result<(), Diagnostic> {
        let Some(lib) = &self.library else {
            return Ok(());
        };
        let index = lib.index.clone();
        let mut needs = Needs::default();
        for r in expr_refs(expr) {
            self.note_library_use(&index, &r, &mut needs);
        }
        self.load_needs(&needs).map_err(|mut ds| ds.swap_remove(0))
    }

    /// Checks one library file, as the prelude is checked, in the middle of
    /// whatever else is being elaborated.
    fn load_library_file(&mut self, f: usize) -> Result<(), Vec<Diagnostic>> {
        let lib = self.library.as_mut().expect("a library is installed");
        let index = lib.index.clone();
        let file = &index.files[f];
        match lib.state[f] {
            LoadState::Loaded => return Ok(()),
            LoadState::Loading => {
                let by = lib.stack.last().copied().unwrap_or(f);
                return Err(vec![internal(index.cycle_message(&[by, f]))]);
            }
            LoadState::NotLoaded => {}
        }
        // From the check cache, if it has the file (`cache`).
        let cached = self.cache_lookup(f);
        let timed = cached.is_some() && crate::timings::enabled();
        if timed {
            crate::timings::begin(&self.globals);
        }
        let hit = match &cached {
            Some((unit, key)) => self.load_from_cache(f, unit, key),
            None => false,
        };
        if timed {
            // A miss is timed again below, as an ordinary load.
            let label = format!(
                "std/{} ({})",
                file.path,
                if hit { "cached" } else { "cache miss" }
            );
            crate::timings::end(&self.globals, label);
        }
        if hit {
            let lib = self.library.as_mut().expect("a library is installed");
            lib.state[f] = LoadState::Loaded;
            lib.order.push(f);
            return Ok(());
        }
        let before = cached.as_ref().map(|_| self.cache_before());
        let lib = self.library.as_mut().expect("a library is installed");
        lib.state[f] = LoadState::Loading;
        lib.stack.push(f);
        let saved = Context {
            module: std::mem::take(&mut self.module),
            namespace_root: std::mem::take(&mut self.namespace_root),
            globals_module: self.globals.module.clone(),
            imports: self.scope.take_imports(),
            file_mode: self.file_mode.take(),
            loading_prelude: self.loading_prelude,
            warnings: std::mem::take(&mut self.warnings),
            lambda_warnings: self.lambda_warnings.take(),
        };
        self.loading_prelude = true;
        self.scope.loading = Some(f);
        let name = format!("std/{}", file.path);
        let unit = SourceUnit {
            file: Some(file.id),
            name: &name,
            module: &file.module,
        };
        let diagnostics = self.elaborate_namespace(None, &[unit], None);
        self.scope.loading = None;
        self.module = saved.module;
        self.namespace_root = saved.namespace_root;
        self.globals.module = saved.globals_module;
        self.scope.restore_imports(saved.imports);
        self.file_mode = saved.file_mode;
        self.loading_prelude = saved.loading_prelude;
        self.warnings = saved.warnings;
        self.lambda_warnings.replace(saved.lambda_warnings);
        let lib = self.library.as_mut().expect("a library is installed");
        lib.stack.pop();
        lib.state[f] = LoadState::Loaded;
        lib.order.push(f);
        let ok = !diagnostics.iter().any(|d| d.severity == Severity::Error);
        if let (Some(before), Some((unit, key))) = (before, &cached) {
            self.cache_after(f, before, ok, unit, key);
        }
        if !ok {
            // Running out of resources isn't a bug in the file: it's the
            // answer for the program that needed it, as for the core.
            if diagnostics.iter().any(|d| d.code == "E-RESOURCE") {
                return Err(diagnostics);
            }
            let mut all = vec![internal(format!("the library file `{name}` doesn't check"))];
            all.extend(diagnostics);
            return Err(all);
        }
        Ok(())
    }

    /// The error for a reference to a name whose library file isn't
    /// loaded: either the file is loading (a cycle), or the dependency
    /// analysis missed the reference.
    pub(crate) fn unloaded(&self, name: &stitchwort_syntax::ast::Name, file: usize) -> Diagnostic {
        let Some(lib) = &self.library else {
            return internal(format!(
                "`{}` is in a library file that isn't loaded",
                name.text
            ));
        };
        let path = format!("std/{}", lib.index.files[file].path);
        if lib.state[file] == LoadState::Loading {
            let by = lib.stack.last().copied().unwrap_or(file);
            return internal(lib.index.cycle_message(&[by, file]))
                .with_label(name.span, format!("`{}` is in `{path}`", name.text));
        }
        internal(format!(
            "`{}` is in the library file `{path}`, which isn't loaded",
            name.text
        ))
        .with_label(name.span, "used here")
        .with_note("the loader's reference analysis missed this use: a bug in the compiler")
    }
}

/// An internal error: the library is malformed, or the loader has a bug.
fn internal(message: String) -> Diagnostic {
    Diagnostic::error("E-INTERNAL", format!("internal error: {message}"))
        .with_note("this is a bug in the compiler's standard library, not in your program")
}
