//! The standard library's files, its name index, and loading it on demand
//! (docs/proposals/std-library.md).
//!
//! The always-loaded **core** is the files of `std/core/`, joined (`prelude()`). Everything else is a
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
//!   only those can be `x`'s type. Where `x` is a variable whose written
//!   type has a data type `T` at its head, `x.f` names only `T.f`'s file.
//!   A file's own references name the files it needs, found the same way,
//!   once, when the index is built. Files load in a canonical order
//!   (dependency order, ties by path).
//! - **A request for a file that is loading is a cycle**, reported as an
//!   internal error naming both files, never a hang or a silent skip.
//!
//! Library files are elaborated as the prelude is: names are written as in
//! `std/core/`, in the namespace they declare into.

use std::cmp::Reverse;
use std::collections::{BTreeSet, BinaryHeap};
use std::rc::Rc;
use std::sync::{Arc, OnceLock};

use stitchwort_core::collections::HashMap;
use stitchwort_syntax::ast::{Decl, Expr, Module};
use stitchwort_syntax::{Diagnostic, FileId, Severity, SourceMap, Span, parse_module_within};

use crate::module::{ModuleState, Ref, decl_refs, declared_names, expr_refs};
use crate::project::{SourceUnit, grouped};
use crate::scope::{self, Resolved};
use crate::state::Unit;
use crate::{Elaborator, Global};

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
    /// A data type's field every constructor has: a shared-field accessor
    /// if its types agree, which loading the file decides (docs/proposals/
    /// variant-fields.md §12.1).
    pub candidate: bool,
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
    /// The definitions (by key) whose generated equations it names: the
    /// library's and the core's are made on demand (`equations.rs`).
    pub equation_needs: BTreeSet<String>,
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
    /// The file declaring `T`: `None` for the built-in `Eq`, which no file
    /// declares, and then the target counts as always reachable.
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
    /// The definitions (by key) whose generated equations are named
    /// (`f.eq2`): the core's are put off until then (`equations.rs`).
    pub equations: BTreeSet<String>,
}

/// The namespace of the built-in equality's dot calls (`dot.rs`).
const EQ_NAMESPACE: &str = "Std.Eq";

static STANDARD: OnceLock<Result<Arc<LibraryIndex>, String>> = OnceLock::new();

impl LibraryIndex {
    /// The index of the standard library, built the first time it's asked
    /// for. `stack` bounds the parser's recursion.
    pub fn standard(stack: usize) -> Result<Arc<LibraryIndex>, String> {
        STANDARD
            .get_or_init(|| {
                LibraryIndex::build(crate::prelude(), crate::library_files(), stack).map(Arc::new)
            })
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
                equation_needs: BTreeSet::new(),
            });
        }

        // The names, from a scratch elaborator that reads declarations the
        // way loading them does.
        let mut scratch = Elaborator::new();
        scratch.unit.loading_prelude = true;
        let mut owner: HashMap<String, usize> = HashMap::default();
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
        congruence_lemmas_beside(&parsed, &owner)?;
        let mut dots_by_short: HashMap<String, Vec<DotTarget>> = HashMap::default();
        for (f, file) in parsed.iter().enumerate().skip(1) {
            // Not a definition's generated equations (`f.eq2`), which are named in
            // full, never reached by a dot call.
            for name in (file.names.iter())
                .filter(|n| n.kind == PendingKind::Def)
                .filter(|n| !(n.candidate && crate::equations::reserved_suffix(&n.key).is_some()))
            {
                let ns = name.key.rsplit_once('.').map(|(ns, _)| ns);
                let namespace = ns.and_then(|ns| owner.get(ns).copied());
                // A dot call looks in the namespace of a declared type or of
                // the built-in equality: `Ring.lookup`, in a namespace that
                // names no type, is no dot call's target.
                if namespace.is_none() && ns != Some(EQ_NAMESPACE) {
                    continue;
                }
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
        instances_beside(&index, &scratch)?;
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
            file.equation_needs = n.equations.clone();
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
    pub(crate) fn closure(
        &self,
        roots: &BTreeSet<usize>,
        loaded: &dyn Fn(usize) -> bool,
    ) -> BTreeSet<usize> {
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

    /// The file that declares the definition with full path `path`, or the
    /// declaration it was generated for (`Std.Map.decEq.%match1` is
    /// `Std.Map.decEq`'s): `None` for a path outside the library.
    pub fn owner_of_path(&self, path: &str) -> Option<usize> {
        let mut path = path;
        loop {
            if let Some(f) = self.owner(path) {
                return Some(f);
            }
            path = path.rsplit_once('.')?.0;
        }
    }

    /// Every full name the index holds, with its file.
    pub fn names(&self) -> impl Iterator<Item = (&str, usize)> {
        self.owner.iter().map(|(k, f)| (k.as_str(), *f))
    }

    /// The candidate shared-field accessors: names loading may not declare.
    pub fn candidates(&self) -> impl Iterator<Item = &str> {
        self.files
            .iter()
            .flat_map(|f| &f.names)
            .filter(|n| n.candidate)
            .map(|n| n.key.as_str())
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

/// Checks that every congruence lemma of a definition `F` (`FCong`,
/// `FCongMem`, `FCongRange`: `congruence.rs`) is declared in `F`'s own file.
///
/// `rewrite` under a binder and `decreasing` look the lemma up by name
/// once they meet a call of `F`, which is when `F`'s file is loaded; a
/// lemma in another file would be found only when something else happened
/// to load that file, so whether a program checks would depend on what
/// else is in the run (SW-1354). Beside `F`, it is loaded whenever it can
/// be asked for, as if every file were.
fn congruence_lemmas_beside(
    files: &[IndexedFile],
    owner: &HashMap<String, usize>,
) -> Result<(), String> {
    let mut misplaced = Vec::new();
    for (f, file) in files.iter().enumerate() {
        for name in file.names.iter().filter(|n| n.kind == PendingKind::Def) {
            for suffix in crate::congruence::SUFFIXES {
                let lemma = format!("{}{suffix}", name.key);
                if let Some(&g) = owner.get(&lemma)
                    && g != f
                {
                    misplaced.push(format!(
                        "`{lemma}` is declared in `{}`, but as a congruence lemma of `{}` it \
                         must be declared beside it, in `{}`: `rewrite` and `decreasing` find \
                         it only where `{}`'s file is loaded",
                        files[g].path, name.key, file.path, name.key
                    ));
                }
            }
        }
    }
    if misplaced.is_empty() {
        Ok(())
    } else {
        Err(misplaced.join("\n"))
    }
}

/// Checks that every library instance of an interface `I` for a type `T`
/// is declared in `T`'s file or `I`'s file.
///
/// Instance search reads one run-wide table keyed by interface and type,
/// and the library is one owner, so an instance elsewhere would be found
/// only in a run that happened to load its file: whether a program checks
/// would depend on what else is in the run (SW-1362, as SW-1354 for
/// congruence lemmas). `I` and `T` are both loaded wherever the instance
/// can be asked for, so an instance in either file is loaded with them. The
/// core is always loaded, so its instances are exempt; one for core types
/// and a core interface must be in the core. Decision procedures
/// (`Decidable …`) are found by their proposition, not by an interface and
/// a type, and are not checked.
///
/// `scratch` has every library name in scope as pending.
fn instances_beside(index: &LibraryIndex, scratch: &Elaborator) -> Result<(), String> {
    // The name `e` heads, if it is a type, and the file that declares it.
    let head_file = |e: &Expr| -> Option<(String, usize)> {
        let mut e = e;
        loop {
            match e {
                Expr::App(f, _) => e = f,
                Expr::Bracketed(inner, _) => e = inner,
                Expr::Var(n) => {
                    return match scratch.resolve(&n.text) {
                        Resolved::Found {
                            global: Global::Pending(_, PendingKind::Data),
                            key,
                            rest,
                            ..
                        } if rest.is_empty() => Some((key.to_string(), index.owner(key)?)),
                        _ => None,
                    };
                }
                _ => return None,
            }
        }
    };
    let mut misplaced = Vec::new();
    for (f, file) in index.files.iter().enumerate().skip(1) {
        for decl in &file.module.decls {
            let Decl::Signature {
                name,
                ty,
                instance: true,
                ..
            } = decl
            else {
                continue;
            };
            // The result `I T …`, after the parameters.
            let mut result = ty;
            while let Expr::Pi { cod, .. } | Expr::Arrow(_, cod) = result {
                result = cod;
            }
            let Expr::App(interface, arg) = result else {
                continue;
            };
            let (Some((i, fi)), Some((t, ft))) = (head_file(interface), head_file(arg)) else {
                continue;
            };
            if f != fi && f != ft {
                misplaced.push(format!(
                    "the instance `{}` of `{i}` for `{t}` is declared in `{}`, but must be in \
                     `{}` (which declares `{t}`) or in `{}` (which declares `{i}`): instance \
                     search finds it only where its file is loaded",
                    name.text, file.path, index.files[ft].path, index.files[fi].path
                ));
            }
        }
    }
    if misplaced.is_empty() {
        Ok(())
    } else {
        Err(misplaced.join("\n"))
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
    for (decl, equations) in grouped(&file.module.decls) {
        let (main, members) = declared_names(decl);
        let Some(main) = main else { continue };
        let key = scratch
            .declaration_key(&main)
            .map_err(|d| format!("`{}`: {}", file.path, d.message))?;
        // A definition's equations, one for each arm (`equations.rs`): the
        // names the source implies, each a candidate, since elaboration may
        // skip one (naming it is then `E-NO-EQUATION`).
        if let Decl::Signature {
            theorem: false,
            instance: false,
            span,
            ..
        } = decl
        {
            for suffix in crate::equations::source_suffixes(equations) {
                out.push(IndexedName {
                    key: Elaborator::member_key(&key, &suffix),
                    kind: PendingKind::Def,
                    follower: false,
                    function: false,
                    span: *span,
                    candidate: true,
                });
            }
            // `f.induct` (stage 2a), for a definition that may call itself:
            // one that names anything of its own short name, generously,
            // since it's a candidate (SW-1077).
            let short = scope::short(&key);
            let recursive = decl_refs(decl, equations).iter().any(|(r, _)| match r {
                Ref::Name(n) => scope::short(&n.text) == short,
                Ref::Dot(_, field, _) => field == short,
            });
            if recursive {
                out.push(IndexedName {
                    key: Elaborator::member_key(&key, "induct"),
                    kind: PendingKind::Def,
                    follower: false,
                    function: false,
                    span: *span,
                    candidate: true,
                });
            }
        }
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
            candidate: false,
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
                candidate: false,
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
                        candidate: false,
                    });
                    // An interface's own projections, beside its methods.
                    if interface {
                        out.push(IndexedName {
                            key: Elaborator::member_key(&key, &format!("%{}", name.text)),
                            kind: PendingKind::Def,
                            follower: false,
                            function: true,
                            span: name.span,
                            candidate: false,
                        });
                    }
                }
            }
        }
        // A data type's shared-field accessors (docs/proposals/variant-fields.md
        // §12.1): which fields are shared depends on their types, which the
        // source can't tell, so each field every constructor has explicitly
        // is a candidate, forcing the file to load like any of its names.
        // Loading it confirms the shared ones and removes the rest
        // (`Elaborator::drop_unconfirmed`). A written `T.f` in the file is
        // listed once, as itself.
        if let Decl::Data {
            record: false,
            ctors,
            ..
        } = decl
        {
            let explicit = |c: &stitchwort_syntax::ast::CtorDecl| -> Vec<String> {
                c.fields
                    .iter()
                    .enumerate()
                    .filter(|(k, _)| !c.implicit.get(*k).copied().unwrap_or(false))
                    .flat_map(|(_, b)| b.names.iter().map(|n| n.text.clone()))
                    .collect()
            };
            let Some((first, rest)) = ctors.split_first() else {
                continue;
            };
            let others: Vec<Vec<String>> = rest.iter().map(explicit).collect();
            for binder in first
                .fields
                .iter()
                .enumerate()
                .filter(|(k, _)| !first.implicit.get(*k).copied().unwrap_or(false))
                .map(|(_, b)| b)
            {
                for name in &binder.names {
                    let member = Elaborator::member_key(&key, &name.text);
                    if others.iter().all(|o| o.contains(&name.text))
                        && !out.iter().any(|n: &IndexedName| n.key == member)
                        && !declares(file, scratch, &member)
                    {
                        out.push(IndexedName {
                            key: member,
                            kind: PendingKind::Def,
                            follower: false,
                            function: true,
                            span: name.span,
                            candidate: true,
                        });
                    }
                }
            }
            // Their update lemmas `T.f.update.g` (`update_lemmas.rs`), by
            // the same rule: a candidate for each pair of candidate fields.
            let fields: Vec<&String> = first
                .fields
                .iter()
                .enumerate()
                .filter(|(k, _)| !first.implicit.get(*k).copied().unwrap_or(false))
                .flat_map(|(_, b)| b.names.iter().map(|n| &n.text))
                .filter(|f| others.iter().all(|o| o.contains(f)))
                .collect();
            for f in &fields {
                for g in &fields {
                    let member = Elaborator::member_key(&key, &format!("{f}.update.{g}"));
                    if !out.iter().any(|n: &IndexedName| n.key == member) {
                        out.push(IndexedName {
                            key: member,
                            kind: PendingKind::Def,
                            follower: false,
                            function: false,
                            span: decl.span(),
                            candidate: true,
                        });
                    }
                }
            }
        }
    }
    Ok(out)
}

/// Whether `file` declares `key` itself, other than as a field: a written
/// `def T.f` beside a type with a field `f`.
fn declares(file: &IndexedFile, scratch: &Elaborator, key: &str) -> bool {
    grouped(&file.module.decls).into_iter().any(|(decl, _)| {
        matches!(decl, Decl::Signature { .. })
            && declared_names(decl)
                .0
                .and_then(|main| scratch.declaration_key(&main).ok())
                .is_some_and(|k| k == key)
    })
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
    /// What the core declared, for making its equations in its own scope.
    pub core: scope::CoreExtent,
}

/// What a nested load sets aside and puts back: the outer unit
/// ([`Unit::nested`], [`Unit::leave`]), and the parts of its state that
/// live elsewhere so far (docs/proposals/elaborator-state.md §7: the
/// imports move with `Tables`).
struct Outer {
    unit: Unit,
    imports: scope::SavedImports,
    /// The warnings noted where only a shared reference is at hand, which
    /// are drained with [`Unit::warnings`]. In `Attempt`, for its undo
    /// (`W-NO-EFFECT` found in an attempt undone is dropped); set aside
    /// here because a nested load can come while a unit's warnings wait to
    /// be drained.
    lambda_warnings: Vec<Diagnostic>,
    /// The outer unit (`state::Session::owners`).
    unit_id: crate::state::UnitId,
}

impl Elaborator {
    /// Enters every name the library files declare as pending, once the
    /// core is loaded, and starts tracking the files.
    /// Whether the library name `written`, declared by the file `file` that
    /// isn't loaded, is a definition with a function type.
    pub(crate) fn pending_is_function(&self, written: &str, file: usize) -> bool {
        let (Some(lib), scope::Resolved::Found { key, .. }) =
            (&self.session.library, self.resolve(written))
        else {
            return false;
        };
        lib.index.files[file]
            .names
            .iter()
            .any(|n| n.key == key && n.function)
    }

    pub fn install_library(&mut self, index: Arc<LibraryIndex>) {
        stitchwort_core::registry::install_library(&mut self.kernel);
        let mut state = vec![LoadState::NotLoaded; index.files.len()];
        state[0] = LoadState::Loaded;
        for (f, file) in index.files.iter().enumerate().skip(1) {
            for name in &file.names {
                // A name the core already has stays the core's; loading
                // the file then reports the clash.
                if self.scope.has(&name.key) {
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
        self.session.library = Some(LibraryState {
            index,
            state,
            stack: Vec::new(),
            order: Vec::new(),
            core: scope::CoreExtent {
                defs: self.kernel.env.defs().len(),
                datas: self.kernel.env.datas().len(),
                abilities: self.tables.abilities.len(),
                fresh: usize::MAX,
            },
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
            .rows()
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
        let g = &self.ev();
        let _op = g.machine.budget.operation(self.options.limits);
        let decidable = g.env.registry().data(Builtin::Decidable);
        let mut found = Vec::new();
        for id in self.tables.prelude_defs..g.env.defs().len() {
            let mut ty = g.def(DefId(id)).ty_value().clone();
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
                found.push(g.def(DefId(id)).path().to_string());
            }
        }
        found
    }

    /// Whether no library file is loading.
    pub(crate) fn library_stack_is_empty(&self) -> bool {
        self.session
            .library
            .as_ref()
            .is_none_or(|lib| lib.stack.is_empty())
    }

    /// The library index, if there is one.
    pub(crate) fn library_index(&self) -> Option<Arc<LibraryIndex>> {
        self.session.library.as_ref().map(|lib| lib.index.clone())
    }

    /// Whether `auto` may try `omega` now (the unit's setting; for tests).
    #[doc(hidden)]
    pub fn omega_for_auto(&self) -> bool {
        self.unit.omega_for_auto
    }

    /// The warnings the library's own files reported as they loaded. They
    /// aren't shown to programs: a test of the library itself reads them.
    pub fn library_warnings(&self) -> &[Diagnostic] {
        &self.library_warnings
    }

    /// The paths of the library files loaded so far, in the order they
    /// loaded.
    pub fn loaded_library_files(&self) -> Vec<String> {
        self.session.library.as_ref().map_or_else(Vec::new, |lib| {
            lib.order
                .iter()
                .map(|&f| lib.index.files[f].path.clone())
                .collect()
        })
    }

    /// Notes the library files a reference needs: the file that owns the
    /// library name it resolves to, and for dot notation the file of
    /// `T.field` where the receiver's written type is the data type `T`, or
    /// else (the type isn't known before checking) the field, which
    /// [`LibraryIndex::resolve_needs`] turns into files.
    ///
    /// A file is noted whether or not it is loaded already, so what a
    /// module needs doesn't depend on what loaded before it: the check
    /// cache keeps a namespace's needs and loads them when it replays the
    /// namespace in another run, where other files may be loaded (SW-255).
    /// Loading skips the files that are loaded.
    pub(crate) fn note_library_use(&self, index: &LibraryIndex, r: &Ref<'_>, needs: &mut Needs) {
        // `f.eq2` names `f`'s equations, which the library and the core
        // make on demand (`equations.rs`); read as a field of `f` too.
        let owner = match r {
            Ref::Name(n) => crate::equations::reserved_suffix(&n.text).map(|(o, _)| o),
            Ref::Dot(n, field, _)
                if field == "induct"
                    || crate::equations::is_equation_name(&format!("f.{field}")) =>
            {
                Some(n.text.as_str())
            }
            _ => None,
        };
        if let Some(owner) = owner
            && let Resolved::Found { key, rest, .. } = self.resolve(owner)
            && rest.is_empty()
        {
            needs.equations.insert(key.to_string());
        }
        let (n, mut fields) = match r {
            Ref::Name(n) => (n, Vec::new()),
            Ref::Dot(n, field, receiver) => {
                if let Some(namespace) = receiver
                    .and_then(|r| r.written())
                    .and_then(|head| self.data_namespace(head))
                {
                    // The receiver's type is the data type `T`, whose dot
                    // calls mean `T.field` and nothing else.
                    if let Some(f) = index.owner(&format!("{namespace}.{field}"))
                        && f != 0
                    {
                        needs.files.insert(f);
                    }
                    return;
                }
                (n, vec![field.clone()])
            }
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

    /// The key of the data type `head` names, loaded or not: the namespace
    /// a dot call on a value of that type looks in. `None` for anything
    /// else, a definition of a type say, which dot calls may unfold.
    pub(crate) fn data_namespace(&self, head: &stitchwort_syntax::ast::Name) -> Option<String> {
        match self.resolve(&head.text) {
            Resolved::Found {
                global: Global::Data(_) | Global::Pending(_, PendingKind::Data),
                rest,
                key,
                ..
            } if rest.is_empty() => Some(key.to_string()),
            _ => None,
        }
    }

    /// Loads what a program's references need (files, and the files its
    /// dot calls can reach given what will be loaded), and what those need,
    /// in canonical order.
    pub(crate) fn load_needs(&mut self, needs: &Needs) -> Result<(), Vec<Diagnostic>> {
        let Some(lib) = &self.session.library else {
            return Ok(());
        };
        let roots = lib
            .index
            .resolve_needs(needs, &|f| lib.state[f] == LoadState::Loaded);
        if !roots.is_empty() {
            self.load_libraries(&roots)?;
        }
        // The equations it names, made on demand once their files load.
        self.ensure_equations(&needs.equations).map_err(|d| vec![d])
    }

    /// Sets the module's `library_reach` from its `needs`: the files they
    /// ask for, with the files those need, as if nothing were loaded, and
    /// those of the namespaces it depends on (their values can be the
    /// module's). The same set however the module is reached. A project
    /// namespace's is kept for the namespaces that depend on it.
    pub(crate) fn set_library_reach(&mut self, needs: &Needs) {
        let Some(lib) = &self.session.library else {
            self.unit.module.library_reach = None;
            return;
        };
        let index = &lib.index;
        let roots = index.resolve_needs(needs, &|_| false);
        let mut reach = index.closure(&roots, &|_| false);
        for namespace in self.unit.module.closure.iter().flatten() {
            if let Some(theirs) = self.session.library_reach.get(namespace) {
                reach.extend(theirs.iter().copied());
            }
        }
        let reach = Rc::new(reach);
        if let Some(namespace) = &self.unit.module.namespace
            && !self.unit.loading_prelude
        {
            Rc::make_mut(&mut self.session.library_reach).insert(namespace.clone(), reach.clone());
        }
        self.unit.module.library_reach = Some(reach);
    }

    /// Whether the files `needs` names, with the files those need, declare
    /// everything the proofs `omega` writes use. It depends only on the
    /// module's own needs, not on what happens to be loaded, so `auto`
    /// proves the same things however the module is reached.
    pub(crate) fn needs_reach_omega(&self, needs: &Needs) -> bool {
        let Some(lib) = &self.session.library else {
            return false;
        };
        // A module that needs no files reaches none of omega's.
        if needs.files.is_empty() {
            return false;
        }
        let index = &lib.index;
        let omega: BTreeSet<usize> = crate::omega::LIBRARY
            .iter()
            .filter_map(|name| index.owner(name).filter(|&f| f != 0))
            .collect();
        let reach = index.closure(&needs.files, &|_| false);
        !omega.is_empty() && omega.is_subset(&reach)
    }

    /// Loads `needs` and what they need, in canonical order.
    pub(crate) fn load_libraries(
        &mut self,
        needs: &BTreeSet<usize>,
    ) -> Result<(), Vec<Diagnostic>> {
        let Some(lib) = &self.session.library else {
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
        let Some(lib) = &self.session.library else {
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

    /// Whether every library file is loaded (also when the session has no
    /// library: there is nothing to load).
    pub fn all_libraries_loaded(&self) -> bool {
        self.session
            .library
            .as_ref()
            .is_none_or(|lib| (1..lib.index.files.len()).all(|f| lib.state[f] == LoadState::Loaded))
    }

    /// Loads every library file, in canonical order: the test-only "eager
    /// `Std`" mode.
    pub fn load_all_libraries(&mut self) -> Result<(), Vec<Diagnostic>> {
        let Some(lib) = &self.session.library else {
            return Ok(());
        };
        let all: BTreeSet<usize> = (1..lib.index.files.len()).collect();
        self.load_libraries(&all)
    }

    /// The library files a `check --std` target names, as indexes into the
    /// index: a path under `std/` (`Nat/Arith.sw`), a folder (`Nat`, every
    /// file below it), or a namespace spelled with dots
    /// (`Std.Nat.Arith`, `Nat.Arith`), which names the same file or folder.
    /// `Std` alone is every file. The core isn't one (it always loads).
    pub fn library_files_named(&self, target: &str) -> Result<Vec<usize>, Diagnostic> {
        let Some(lib) = &self.session.library else {
            return Ok(Vec::new());
        };
        let rest = target
            .strip_prefix("std/")
            .or_else(|| target.strip_prefix("Std."))
            .unwrap_or(target);
        let prefix = match rest.strip_suffix(".sw") {
            Some(file) => file.to_string(),
            None if rest == "Std" => String::new(),
            None => rest.replace('.', "/"),
        };
        let exact = format!("{prefix}.sw");
        let below = format!("{prefix}/");
        let found: Vec<usize> = (1..lib.index.files.len())
            .filter(|&f| {
                let path = &lib.index.files[f].path;
                prefix.is_empty() || *path == exact || path.starts_with(&below)
            })
            .collect();
        if found.is_empty() {
            return Err(Diagnostic::error(
                "E-STD-TARGET",
                format!("there's no standard library file or folder `{target}`"),
            )
            .with_note("name one as `Nat/Arith.sw`, `Nat` or `Std.Nat.Arith`"));
        }
        Ok(found)
    }

    /// Checks the library files `targets` name ([`Self::library_files_named`])
    /// and the files they need, bodies and all, in canonical order. The
    /// check cache answers for a file whose text and dependencies are
    /// unchanged. Returns the paths of the files named.
    pub fn check_library_targets(
        &mut self,
        targets: &[String],
    ) -> Result<Vec<String>, Vec<Diagnostic>> {
        let mut files = BTreeSet::new();
        for target in targets {
            files.extend(self.library_files_named(target).map_err(|d| vec![d])?);
        }
        self.load_libraries(&files)?;
        let Some(lib) = &self.session.library else {
            return Ok(Vec::new());
        };
        Ok(files
            .into_iter()
            .map(|f| lib.index.files[f].path.clone())
            .collect())
    }

    /// Loads every library file but those in `skip` (paths under `std/`,
    /// `Float/Theory.sw`) and those that need one of them, in canonical
    /// order. The files left out load when something needs them, as in a
    /// lazy session.
    pub fn load_libraries_except(
        &mut self,
        skip: &BTreeSet<String>,
    ) -> Result<(), Vec<Diagnostic>> {
        let Some(lib) = &self.session.library else {
            return Ok(());
        };
        let index = &lib.index;
        let skipped: BTreeSet<usize> = (1..index.files.len())
            .filter(|&f| skip.contains(&index.files[f].path))
            .collect();
        let wanted: BTreeSet<usize> = (1..index.files.len())
            .filter(|&f| (index.closure(&BTreeSet::from([f]), &|_| false)).is_disjoint(&skipped))
            .collect();
        self.load_libraries(&wanted)
    }

    /// Loads every library file that checks under this session's limits,
    /// in canonical order, and returns the paths of those that don't and of
    /// those that need one that doesn't: what
    /// [`Elaborator::load_libraries_except`] should leave out for a session
    /// like this one. For a host that checks the library once ahead of time
    /// into a check cache it ships (the playground's).
    pub fn load_libraries_that_check(&mut self) -> BTreeSet<String> {
        let Some(lib) = &self.session.library else {
            return BTreeSet::new();
        };
        let index = lib.index.clone();
        let all: BTreeSet<usize> = (1..index.files.len()).collect();
        let Ok(order) = index.load_order(&all, &|_| false) else {
            return all.iter().map(|&f| index.files[f].path.clone()).collect();
        };
        let mut left_out = BTreeSet::new();
        for f in order {
            // A file that failed stays loaded as far as it got: one that
            // needs it would load on top of that.
            let needs = index.closure(&BTreeSet::from([f]), &|_| false);
            if !needs.is_disjoint(&left_out) || self.load_libraries(&BTreeSet::from([f])).is_err() {
                left_out.insert(f);
            }
        }
        left_out
            .into_iter()
            .map(|f| index.files[f].path.clone())
            .collect()
    }

    /// Loads the files an expression typed in needs (`eval`, the REPL).
    pub fn prepare_expr(&mut self, expr: &Expr) -> Result<(), Diagnostic> {
        let Some(lib) = &self.session.library else {
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
        let lib = self
            .session
            .library
            .as_mut()
            .expect("a library is installed");
        let index = lib.index.clone();
        match lib.state[f] {
            LoadState::Loaded => return Ok(()),
            LoadState::Loading => {
                let by = lib.stack.last().copied().unwrap_or(f);
                return Err(vec![internal(index.cycle_message(&[by, f]))]);
            }
            LoadState::NotLoaded => {}
        }
        // A unit of its own, whether it is elaborated or replayed, for what
        // loading it does outside the file's own elaboration: replaying its
        // entry, dropping the index's entries it didn't declare. So none of
        // it is the write-set of the unit it loads in (§4.8.3), as it isn't
        // the entry's of a namespace it loads inside.
        let outer = self.session.owners.enter(self.ids());
        self.unit_changed();
        let loaded = self.load_library_file_in_unit(f);
        self.session.owners.leave(self.ids(), outer);
        self.unit_changed();
        loaded
    }

    /// [`Self::load_library_file`], once it is known to load, in the unit
    /// of its own that it begins.
    fn load_library_file_in_unit(&mut self, f: usize) -> Result<(), Vec<Diagnostic>> {
        let lib = self
            .session
            .library
            .as_mut()
            .expect("a library is installed");
        let index = lib.index.clone();
        let file = &index.files[f];
        // The equations of other files it names, before its entry is
        // looked up or written, so they are never part of it.
        let _ = self.ensure_equations(&file.equation_needs);
        // From the check cache, if it has the file (`cache`).
        let cached = self.cache_lookup(f);
        let timed = cached.is_some() && crate::timings::enabled();
        if timed {
            crate::timings::begin(&self.ev());
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
            crate::timings::end(&self.ev(), label);
        }
        if hit {
            let lib = self
                .session
                .library
                .as_mut()
                .expect("a library is installed");
            lib.state[f] = LoadState::Loaded;
            lib.order.push(f);
            self.drop_unconfirmed(f);
            return Ok(());
        }
        let before = cached.as_ref().map(|_| self.cache_before());
        let lib = self
            .session
            .library
            .as_mut()
            .expect("a library is installed");
        lib.state[f] = LoadState::Loading;
        lib.stack.push(f);
        let saved = self.enter_nested_unit();
        self.scope.loading = Some(f);
        let name = format!("std/{}", file.path);
        let unit = SourceUnit {
            file: Some(file.id),
            name: &name,
            module: &file.module,
        };
        let diagnostics = self.elaborate_namespace(None, &[unit], None);
        // Programs don't see the library's warnings, but a test of the
        // library itself must (`library_warnings`).
        self.library_warnings.extend(
            diagnostics
                .iter()
                .filter(|d| d.severity == Severity::Warning)
                .cloned(),
        );
        self.scope.loading = None;
        self.leave_nested_unit(saved);
        let lib = self
            .session
            .library
            .as_mut()
            .expect("a library is installed");
        lib.stack.pop();
        lib.state[f] = LoadState::Loaded;
        lib.order.push(f);
        // A library file with an open goal (`?`) doesn't check either, nor
        // one with a function whose main value isn't first, nor one with a
        // redundant arm, nor one with a line that does nothing: the library
        // keeps the convention it asks of programs (D306).
        let ok = !diagnostics.iter().any(|d| {
            matches!(d.severity, Severity::Error | Severity::Goal)
                || d.code == "W-RECEIVER-NOT-FIRST"
                || d.code == "W-REDUNDANT"
                || d.code == crate::no_effect::CODE
                || d.code == crate::doc_links::CODE
        });
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
        self.drop_unconfirmed(f);
        Ok(())
    }

    /// Runs `run` in the scope of library file `f` (the core for 0), loaded
    /// already: as while it loaded, its own imports and the library's
    /// names, whatever module is being checked (or none). For what is made
    /// from a file's source after it loads, the equations made on demand,
    /// so they come out the same whoever asks (SW-1068).
    pub(crate) fn in_library_file<T>(&mut self, f: usize, run: impl FnOnce(&mut Self) -> T) -> T {
        // The file loading is in its own scope already (its own proofs
        // naming its equations), with its later declarations unchecked.
        if self.scope.loading == Some(f) {
            let saved = std::mem::replace(&mut self.unit.module_path, "Std".into());
            let result = run(self);
            self.unit.module_path = saved;
            return result;
        }
        let lib = self
            .session
            .library
            .as_ref()
            .expect("a library is installed");
        let index = lib.index.clone();
        let file = &index.files[f];
        // The core loaded before the library's names were there.
        let core_only = (f == 0).then_some(scope::CoreExtent {
            fresh: self.kernel.env.defs().len(),
            ..lib.core
        });
        let saved = self.enter_nested_unit();
        self.unit.module = ModuleState {
            files: vec![crate::module::FileInfo {
                id: Some(file.id),
                name: format!("std/{}", file.path),
            }],
            file: Some(0),
            ..ModuleState::default()
        };
        // Errors were reported when the file loaded, and its imports aren't
        // the program's to navigate. (Only here: `clear_metas` flushes what
        // navigation has pending, which needs it in place.)
        let nav = self.present.nav.take();
        let mut errors = Vec::new();
        self.add_imports(&file.module.imports, false, &mut errors);
        self.add_imports(&file.module.imports, true, &mut errors);
        self.present.nav = nav;
        let saved_core_only = std::mem::replace(&mut self.scope.core_only, core_only);
        // Glued as while the file loaded (the library always is), not as the
        // caller's switch happens to be, so the result is the same whoever
        // asks.
        let was = self.kernel.machine.glue.replace(self.gluing());
        let result = run(self);
        self.kernel.machine.glue.set(was);
        self.scope.core_only = saved_core_only;
        self.leave_nested_unit(saved);
        result
    }

    /// Sets the unit being elaborated aside for a library file's, until
    /// [`Self::leave_nested_unit`].
    fn enter_nested_unit(&mut self) -> Outer {
        let inner = self.unit.nested();
        let outer = Outer {
            unit: std::mem::replace(&mut self.unit, inner),
            imports: self.scope.take_imports(),
            lambda_warnings: self.attempt.lambda_warnings.take(),
            unit_id: self.session.owners.enter(self.ids()),
        };
        self.unit_changed();
        outer
    }

    /// Back to the unit [`Self::enter_nested_unit`] set aside.
    fn leave_nested_unit(&mut self, outer: Outer) {
        let Outer {
            unit,
            imports,
            lambda_warnings,
            unit_id,
        } = outer;
        self.session.owners.leave(self.ids(), unit_id);
        self.unit_changed();
        self.unit.leave(unit);
        self.scope.restore_imports(imports);
        self.attempt.lambda_warnings.replace(lambda_warnings);
    }

    /// Removes the index's entries for file `f` that loading it didn't
    /// declare: candidate shared-field accessors that aren't shared (their
    /// fields' types differ, say), so `T.f` is then unknown, as it would be
    /// with every file loaded (docs/proposals/variant-fields.md §12.1).
    fn drop_unconfirmed(&mut self, f: usize) {
        (self.scope).remove_where(|g| matches!(g, Global::Pending(file, _) if *file == f));
    }

    /// The error for a reference to a name whose library file isn't
    /// loaded: either the file is loading (a cycle), or the dependency
    /// analysis missed the reference.
    pub(crate) fn unloaded(&self, name: &stitchwort_syntax::ast::Name, file: usize) -> Diagnostic {
        let Some(lib) = &self.session.library else {
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
