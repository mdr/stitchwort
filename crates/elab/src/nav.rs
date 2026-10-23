//! The resolution index for code navigation (docs/proposals/code-navigation.md):
//! which declaration each written name refers to, which binder each local
//! variable refers to, and the definitions themselves.
//!
//! Recording is off unless [`Elaborator::enable_navigation`] was called.
//! Then the elaborator notes, where it resolves a name to a declaration,
//! the span of the name and its target; a walk over each file's syntax
//! (before it's elaborated) finds the local variables' binders and the
//! definitions. [`Elaborator::navigation_index`] puts the two together.
//!
//! A declaration can be elaborated more than once (an attempt undone, a
//! `match` lifted), so references are kept by span, the last one noted
//! winning.

use std::cell::RefCell;
use std::collections::HashMap;

use stitchwort_core::{DefId, Icit, Name, Term, Value, pretty};
use stitchwort_syntax::ast::{self, Clause, Decl, Expr, Module, Pattern};
use stitchwort_syntax::{FileId, Span};

use crate::check::Ctx;
use crate::library::PendingKind;
use crate::scope::Resolved;
use crate::{Elaborator, Global};

/// What the elaborator noted, and the walk found.
#[derive(Clone, Default)]
pub(crate) struct Recorder {
    /// A name resolved to a declaration, by the span of the name.
    pub(crate) refs: HashMap<Span, Noted>,
    /// The types of local variables where they're used, not yet printed
    /// (the metavariables in them are solved by the end of the
    /// declaration): the span, the type, and the names of the context.
    pub(crate) pending: Vec<(Span, Value, Vec<Name>, bool)>,
    /// The printed types, by where the use starts.
    pub(crate) local_types: HashMap<(FileId, u32), String>,
    /// Local variables used, from the walk.
    pub(crate) locals: Vec<LocalUse>,
    /// Where local variables are bound (a binder refers to itself).
    pub(crate) binders: Vec<LocalUse>,
    /// The definitions of the files walked.
    pub(crate) outline: Vec<OutlineItem>,
    /// Each record field's name, by its type's declaration and its name.
    pub(crate) field_spans: HashMap<(Span, String), Span>,
    /// Whether to note the type of every elaborated expression
    /// ([`Elaborator::enable_expression_types`]).
    pub(crate) exprs: bool,
    /// More than 0 while elaborating what a declaration generates (the
    /// equality lemmas, `Show` and `Ord`): written nowhere, so nothing is
    /// noted under the declaration's span.
    pub(crate) generated: usize,
    /// The printed type of the expression written at a span (the last one
    /// elaborated there), for hovering over a selection.
    pub(crate) expr_types: HashMap<Span, String>,
}

impl Recorder {
    /// Everything recorded, in a canonical order: for the check cache's
    /// differential test (`cache::dump`). (Not the index made from it,
    /// whose symbols for two references to one span depend on a hash
    /// map's order.)
    ///
    /// A reference noted while its library file wasn't loaded yet is shown
    /// as what its name is `now`, as the index reads it: whether the file
    /// had loaded when the reference was noted depends on what else the
    /// run loaded first (SW-255).
    pub(crate) fn dump(&self, out: &mut String, now: &dyn Fn(&str) -> Option<Global>) {
        let span = |s: Span| format!("@{}:{}-{}", s.file.index(), s.start, s.end);
        let mut lines: Vec<String> = self
            .refs
            .iter()
            .map(|(at, n)| {
                let global = match n.global {
                    Global::Pending(..) => now(&n.key).unwrap_or(n.global),
                    global => global,
                };
                format!(
                    "nav ref {} {} {} {:?} {:?}",
                    span(*at),
                    n.key,
                    span(n.target),
                    global,
                    n.dot
                )
            })
            .collect();
        lines.extend(
            self.local_types
                .iter()
                .map(|((file, at), ty)| format!("nav type @{}:{at} {ty}", file.index())),
        );
        for (what, uses) in [("local", &self.locals), ("binder", &self.binders)] {
            lines.extend(uses.iter().enumerate().map(|(i, u)| {
                format!(
                    "nav {what} {i} {} {} {}",
                    span(u.span),
                    u.name,
                    span(u.binder)
                )
            }));
        }
        lines.extend(self.outline.iter().enumerate().map(|(i, o)| {
            format!(
                "nav outline {i} {} {} {} {} {} {:?}",
                o.name,
                o.key,
                o.kind,
                span(o.span),
                span(o.range),
                o.container
            )
        }));
        lines.extend(
            self.field_spans
                .iter()
                .map(|((at, name), s)| format!("nav field {} {name} {}", span(*at), span(*s))),
        );
        lines.extend(
            self.expr_types
                .iter()
                .map(|(at, ty)| format!("nav expr {} {ty}", span(*at))),
        );
        lines.push(format!("nav pending {}", self.pending.len()));
        lines.sort();
        for line in lines {
            out.push_str(&line);
            out.push('\n');
        }
    }

    /// A local variable bound at `span`.
    fn note_binder(&mut self, name: &str, span: Span) {
        if name != "_" && !name.starts_with('%') {
            self.binders.push(LocalUse {
                span,
                name: name.to_string(),
                binder: span,
            });
        }
    }
}

#[derive(Clone)]
pub(crate) struct Noted {
    pub(crate) key: String,
    /// The name of the declaration.
    pub(crate) target: Span,
    pub(crate) global: Global,
    /// The reference is the last component of a dotted written name.
    pub(crate) dot: Option<String>,
}

#[derive(Clone)]
pub(crate) struct LocalUse {
    pub(crate) span: Span,
    pub(crate) name: String,
    pub(crate) binder: Span,
}

#[derive(Clone)]
pub(crate) struct OutlineItem {
    /// The full name as the index shows it (`Main.` for a file with no
    /// namespace line, as for a project's namespaces).
    pub(crate) name: String,
    /// The name the scope binds it by.
    key: String,
    kind: &'static str,
    /// Its name.
    span: Span,
    /// The whole declaration.
    range: Span,
    container: Option<usize>,
}

/// The index: every definition of the files checked, and every reference.
pub struct NavIndex {
    pub symbols: Vec<NavSymbol>,
    pub refs: Vec<NavRef>,
    /// The type of the expression written at each span, if recorded
    /// ([`Elaborator::enable_expression_types`]), sorted by position.
    pub exprs: Vec<(Span, String)>,
}

pub struct NavSymbol {
    /// Its full name.
    pub name: String,
    pub kind: &'static str,
    /// Its name where it's declared.
    pub span: Span,
    /// The whole declaration, if known.
    pub range: Option<Span>,
    /// The symbol it's declared in (a constructor's type), by index.
    pub container: Option<usize>,
    pub ty: Option<String>,
}

pub struct NavRef {
    pub span: Span,
    /// The reference is the last component of this dotted name: the span
    /// covers more (`xs.map`).
    pub dot: Option<String>,
    pub target: NavTarget,
    pub ty: Option<String>,
}

pub enum NavTarget {
    /// A declaration: an index into [`NavIndex::symbols`].
    Symbol(usize),
    /// A local variable, by its binder.
    Binder { name: String, span: Span },
}

/// The text of an embedded library file, by its path under `std/`
/// (`core/Int.sw` is one of the core's files). Read from the library index
/// (built if it isn't yet, with `stack` for the parser): a lookup in the
/// constants the files are embedded as would copy them, which doubles their
/// size in WebAssembly. A core file is cut from the core's text, which the
/// index holds whole.
pub fn std_source(path: &str, stack: usize) -> Option<String> {
    let index = crate::LibraryIndex::standard(stack).ok()?;
    if path.starts_with("core/") {
        let start: usize = crate::CORE_LAYOUT
            .iter()
            .take_while(|(p, _)| *p != path)
            .map(|(_, len)| len)
            .sum();
        let (_, len) = crate::CORE_LAYOUT.iter().find(|(p, _)| *p == path)?;
        return index
            .files
            .first()?
            .text
            .get(start..start + len)
            .map(str::to_string);
    }
    index
        .files
        .iter()
        .skip(1)
        .find(|f| f.path == path)
        .map(|f| f.text.clone())
}

impl Elaborator {
    /// Starts recording what the index needs. Call before loading anything
    /// that should be in it.
    pub fn enable_navigation(&mut self) {
        self.nav = Some(RefCell::new(Recorder::default()));
    }

    /// Also records the type of every expression elaborated, for the
    /// language server's hover over a selection. Call right after
    /// [`Elaborator::enable_navigation`].
    pub fn enable_expression_types(&mut self) {
        if let Some(nav) = &mut self.nav {
            nav.get_mut().exprs = true;
        }
    }

    /// The expression written at `span` has type `ty` in `cx`.
    pub(crate) fn note_expr(&self, cx: &Ctx, span: Span, ty: &Value) {
        if span.start == span.end {
            return;
        }
        if let Some(nav) = &self.nav {
            let mut nav = nav.borrow_mut();
            if nav.exprs && nav.generated == 0 {
                nav.pending.push((span, ty.clone(), cx.names.clone(), true));
            }
        }
    }

    pub(crate) fn note(&self, at: Span, noted: Noted) {
        if let Some(nav) = &self.nav {
            let mut nav = nav.borrow_mut();
            if nav.generated == 0 {
                nav.refs.insert(at, noted);
            }
        }
    }

    /// Runs `f`, which elaborates what a declaration generates: nothing it
    /// notes (references, types) is kept, as the generated code is written
    /// nowhere (its spans are the declaration's).
    pub(crate) fn unnoted<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        if let Some(nav) = &self.nav {
            nav.borrow_mut().generated += 1;
        }
        let out = f(self);
        if let Some(nav) = &self.nav {
            nav.borrow_mut().generated -= 1;
        }
        out
    }

    /// `name`, written, resolved to a declaration.
    pub(crate) fn note_name(&self, name: &ast::Name) {
        if self.nav.is_none() {
            return;
        }
        if let Resolved::Found {
            global,
            span,
            key,
            rest,
            ..
        } = self.resolve(&name.text)
            && rest.is_empty()
            && !matches!(global, Global::Unchecked(_) | Global::Failed)
        {
            self.note(
                name.span,
                Noted {
                    key: key.to_string(),
                    target: span,
                    global,
                    dot: None,
                },
            );
        }
    }

    /// A name found already: by `resolve_exact`.
    pub(crate) fn note_found(&self, at: Span, key: &str, global: Global, target: Span) {
        if self.nav.is_some() && !matches!(global, Global::Unchecked(_) | Global::Failed) {
            self.note(
                at,
                Noted {
                    key: key.to_string(),
                    target,
                    global,
                    dot: None,
                },
            );
        }
    }

    /// `.field` found the definition `id` by the type of what's before it.
    pub(crate) fn note_dot(&self, field: &ast::Name, id: DefId) {
        if self.nav.is_none() {
            return;
        }
        let def = self.globals.def(id);
        // The declaration's name, as a written name finds it; a definition's
        // own span covers all of it.
        let path = def.path.to_string();
        let relative = path.strip_prefix("Main.").unwrap_or(&path);
        let target = match self.scope.get(&path).or_else(|| self.scope.get(relative)) {
            Some((Global::Def(found), span)) if found == id => span,
            _ => def.span,
        };
        self.note(
            field.span,
            Noted {
                key: def.path.to_string(),
                target,
                global: Global::Def(id),
                dot: Some(field.text.clone()),
            },
        );
    }

    /// The field `name` of record type `d`, written in a literal, update or
    /// pattern.
    pub(crate) fn note_field(&self, d: stitchwort_core::DataId, name: &ast::Name) {
        if self.nav.is_none() {
            return;
        }
        let owner = self.data_key(d);
        for hidden in ["", "%"] {
            let key = Self::member_key(&owner, &format!("{hidden}{}", name.text));
            if let Some((global, span)) = self.scope.get(&key) {
                self.note(
                    name.span,
                    Noted {
                        key,
                        target: span,
                        global,
                        dot: None,
                    },
                );
                return;
            }
        }
    }

    /// The field `name` of the constructor written at `ctor_at`, named in a
    /// pattern `C { name = … }` (docs/proposals/variant-fields.md §4.3):
    /// its target is the field's binder in the constructor's declaration.
    pub(crate) fn note_ctor_field(&self, ctor_at: Span, name: &ast::Name) {
        let Some(nav) = &self.nav else {
            return;
        };
        let noted = nav.borrow().refs.get(&ctor_at).cloned();
        if let Some(ctor) = noted
            && matches!(ctor.global, Global::Ctor(..))
        {
            self.note(
                name.span,
                Noted {
                    key: format!("{}.{}", ctor.key, name.text),
                    target: ctor.target,
                    global: ctor.global,
                    dot: None,
                },
            );
        }
    }

    /// A local variable used at `name`, of type `ty` in `cx`.
    pub(crate) fn note_local(&self, cx: &Ctx, name: &ast::Name, ty: &Value) {
        if let Some(nav) = &self.nav {
            let mut nav = nav.borrow_mut();
            if nav.generated == 0 {
                nav.pending
                    .push((name.span, ty.clone(), cx.names.clone(), false));
            }
        }
    }

    /// How many local variables' types are waiting to be printed: a
    /// [`crate::undo::Snapshot`] keeps it, to drop the ones an undone
    /// attempt noted.
    pub(crate) fn pending_local_types(&self) -> usize {
        self.nav
            .as_ref()
            .map_or(0, |nav| nav.borrow().pending.len())
    }

    /// Drops the local variables' types noted after the first `len`: their
    /// attempt was undone, and the metavariables in them with it, so they
    /// can't be printed (a later metavariable may reuse the number of one
    /// in them, with a different solution).
    pub(crate) fn drop_local_types_since(&self, len: usize) {
        if let Some(nav) = &self.nav {
            nav.borrow_mut().pending.truncate(len);
        }
    }

    /// Prints the types noted, while the metavariables in them still have
    /// their solutions.
    pub(crate) fn flush_navigation(&self) {
        let Some(nav) = &self.nav else {
            return;
        };
        let mut nav = nav.borrow_mut();
        let pending = std::mem::take(&mut nav.pending);
        for (span, ty, names, expr) in pending {
            let text = pretty::value_for_message(&self.globals, &names, &ty);
            if expr {
                nav.expr_types.insert(span, text);
            } else {
                nav.local_types.insert((span.file, span.start), text);
            }
        }
    }

    /// An import's item `item`, resolved to `key`.
    pub(crate) fn note_import(&self, item: &ast::Name, key: &str) {
        if self.nav.is_none() {
            return;
        }
        if let Some((global, span)) = self.scope.get(key) {
            self.note_found(item.span, key, global, span);
        }
    }

    /// Walks the syntax of the files of a module about to be elaborated.
    pub(crate) fn walk_for_navigation(&self, modules: &[&Module]) {
        let Some(nav) = &self.nav else {
            return;
        };
        let library = self.loading_prelude || !self.library_stack_is_empty();
        let mut nav = nav.borrow_mut();
        for module in modules {
            let mut walk = Walk {
                nav: &mut nav,
                prefix: self.namespace_root.clone(),
                outline: !library,
                display: if self.namespace_root.is_empty() {
                    "Main.".to_string()
                } else {
                    self.namespace_root.clone()
                },
            };
            walk.module(module);
        }
    }

    /// The index of what was recorded, for the references `wanted` says to include
    /// (the others' definitions are still there as targets).
    pub fn navigation_index(&self, wanted: &dyn Fn(Span, Option<&str>) -> bool) -> NavIndex {
        self.flush_navigation();
        let Some(nav) = &self.nav else {
            return NavIndex {
                symbols: Vec::new(),
                refs: Vec::new(),
                exprs: Vec::new(),
            };
        };
        let nav = nav.borrow();
        let mut symbols: Vec<NavSymbol> = Vec::new();
        let mut by_span: HashMap<Span, usize> = HashMap::new();
        for item in &nav.outline {
            by_span.insert(item.span, symbols.len());
            let key = item.key.clone();
            symbols.push(NavSymbol {
                ty: self
                    .scope
                    .get(&key)
                    .and_then(|(global, _)| self.global_type(global)),
                name: item.name.clone(),
                kind: item.kind,
                span: item.span,
                range: Some(item.range),
                container: item.container,
            });
        }
        let mut refs: Vec<NavRef> = Vec::new();
        // In source order, so that the symbols made for the library's
        // declarations (and the name and type each is shown with) don't
        // depend on the hash map's order.
        let mut noted_refs: Vec<(&Span, &Noted)> = nav.refs.iter().collect();
        noted_refs.sort_by_key(|(at, _)| (at.file.index(), at.start, at.end));
        // The symbols whose name is one a user writes (not a generated `%`
        // member's): the first such reference names the symbol.
        let mut visible: std::collections::HashSet<usize> = std::collections::HashSet::new();
        for (at, noted) in noted_refs {
            if !wanted(*at, noted.dot.as_deref()) {
                continue;
            }
            let mut global = noted.global;
            if matches!(global, Global::Pending(..))
                && let Some((now, _)) = self.scope.get(&noted.key)
            {
                global = now;
            }
            let last = noted.key.rsplit('.').next().unwrap_or_default().to_string();
            let field_span = nav
                .field_spans
                .get(&(noted.target, last.trim_start_matches('%').to_string()))
                .copied();
            let (target, kind) = match field_span {
                Some(span) => (span, "field"),
                None => (noted.target, self.global_kind(global)),
            };
            // A constructor's field named in a pattern `C { f = … }` shows
            // the field's type, not the constructor's.
            // and is named after the constructor's symbol.
            let ty_of = || match (field_span, global) {
                (Some(_), Global::Ctor(d, c)) => self.ctor_field_type(d, c, &last),
                _ => self.global_type(global),
            };
            let name = match (field_span, global) {
                (Some(_), Global::Ctor(..)) => by_span.get(&noted.target).map_or_else(
                    || noted.key.clone(),
                    |&i| format!("{}.{last}", symbols[i].name),
                ),
                _ => noted.key.clone(),
            };
            let shown = !last.starts_with('%');
            let index = *by_span.entry(target).or_insert_with(|| {
                symbols.push(NavSymbol {
                    name: name.clone(),
                    kind,
                    span: target,
                    range: None,
                    container: None,
                    ty: ty_of(),
                });
                symbols.len() - 1
            });
            if symbols[index].range.is_none() {
                // The elaborator's name is the one a reference was resolved
                // by. A field is reached both by its projection (`Ord.equal`)
                // and by its generated member (`Ord.%equal`, a different
                // type); the index shows the projection and its type.
                if shown && visible.insert(index) {
                    symbols[index].name = name.clone();
                    symbols[index].ty = ty_of();
                } else if !visible.contains(&index) {
                    symbols[index].name = name.clone();
                    if symbols[index].ty.is_none() {
                        symbols[index].ty = ty_of();
                    }
                }
            } else if symbols[index].ty.is_none() {
                symbols[index].ty = ty_of();
            }
            refs.push(NavRef {
                span: *at,
                dot: noted.dot.clone(),
                target: NavTarget::Symbol(index),
                ty: symbols[index].ty.clone(),
            });
        }
        for local in &nav.locals {
            refs.push(NavRef {
                span: local.span,
                dot: None,
                target: NavTarget::Binder {
                    name: local.name.clone(),
                    span: local.binder,
                },
                ty: nav
                    .local_types
                    .get(&(local.span.file, local.span.start))
                    .cloned(),
            });
        }
        // Each declaration's own name refers to it, for hover and definition there.
        let mut taken: std::collections::HashSet<(FileId, u32)> =
            refs.iter().map(|r| (r.span.file, r.span.start)).collect();
        for (i, item) in nav.outline.iter().enumerate() {
            if item.kind == "test" || !taken.insert((item.span.file, item.span.start)) {
                continue;
            }
            let last = item.name.rsplit('.').next().unwrap_or_default();
            refs.push(NavRef {
                span: item.span,
                dot: Some(last.to_string()),
                target: NavTarget::Symbol(i),
                ty: symbols[i].ty.clone(),
            });
        }
        // In `def Pt.sum`, the `Pt` is a reference to the type (when it's
        // one of the namespace's own).
        for item in &nav.outline {
            if item.kind == "test" || item.kind == "field" || item.kind == "ctor" {
                continue;
            }
            let Some((prefix_key, last)) = item.key.rsplit_once('.') else {
                continue;
            };
            let written = (item.span.end - item.span.start) as usize;
            let Some(prefix_len) = written.checked_sub(last.len() + 1).filter(|n| *n > 0) else {
                continue;
            };
            let Some((global, target)) = self.scope.get(prefix_key) else {
                continue;
            };
            let span = Span {
                end: item.span.start + prefix_len as u32,
                ..item.span
            };
            if !wanted(span, None) {
                continue;
            }
            let kind = self.global_kind(global);
            let index = *by_span.entry(target).or_insert_with(|| {
                symbols.push(NavSymbol {
                    name: prefix_key.to_string(),
                    kind,
                    span: target,
                    range: None,
                    container: None,
                    ty: self.global_type(global),
                });
                symbols.len() - 1
            });
            refs.push(NavRef {
                span,
                dot: None,
                target: NavTarget::Symbol(index),
                ty: symbols[index].ty.clone(),
            });
        }
        // The same for a declaration outside the outline (the library's: only
        // the ones something refers to), so that hover and references work on
        // its name when a library file is open. Not for a generated
        // declaration whose span isn't its name (a record's `ext` lemma is at
        // the whole record declaration): such a reference would contain the
        // names written inside it, and a lookup by position finds one
        // reference, which must be the innermost.
        for (i, symbol) in symbols.iter().enumerate() {
            let last = symbol.name.rsplit('.').next().unwrap_or_default();
            if symbol.range.is_some()
                || symbol.kind == "test"
                || !wanted(symbol.span, Some(last))
                || !taken.insert((symbol.span.file, symbol.span.start))
            {
                continue;
            }
            refs.push(NavRef {
                span: symbol.span,
                dot: Some(last.to_string()),
                target: NavTarget::Symbol(i),
                ty: symbol.ty.clone(),
            });
        }
        // A local variable's binder refers to itself (a record field is a declaration, above).
        for binder in &nav.binders {
            if !taken.insert((binder.span.file, binder.span.start)) {
                continue;
            }
            refs.push(NavRef {
                span: binder.span,
                dot: None,
                target: NavTarget::Binder {
                    name: binder.name.clone(),
                    span: binder.span,
                },
                ty: None,
            });
        }
        refs.sort_by_key(|r| (r.span.file.index(), r.span.start, r.span.end));
        let mut exprs: Vec<(Span, String)> = nav
            .expr_types
            .iter()
            .map(|(at, ty)| (*at, ty.clone()))
            .collect();
        exprs.sort_by_key(|(at, _)| (at.file.index(), at.start, at.end));
        NavIndex {
            symbols,
            refs,
            exprs,
        }
    }

    /// How many of a session's first files are the core and the library's
    /// (they're added to the source map first, in the index's order).
    pub fn std_file_count(&self) -> usize {
        self.library_index().map_or(1, |index| index.files.len())
    }

    fn global_kind(&self, global: Global) -> &'static str {
        match global {
            Global::Def(id) => {
                let def = self.globals.def(id);
                if def.theorem {
                    "theorem"
                } else if def.instance {
                    "instance"
                } else {
                    "def"
                }
            }
            Global::Data(d) => {
                if self.interfaces.contains_key(&d) {
                    "interface"
                } else if self.globals.data(d).record {
                    "record"
                } else {
                    "data"
                }
            }
            Global::Ctor(..) => "ctor",
            Global::Ability(_) => "ability",
            Global::Op(..) => "op",
            Global::Pending(_, PendingKind::Def) => "def",
            Global::Pending(_, PendingKind::Data) => "data",
            Global::Pending(_, PendingKind::Ctor) => "ctor",
            Global::Pending(_, PendingKind::Op) => "op",
            _ => "def",
        }
    }

    /// A declaration's type, printed.
    /// The declared type of constructor `c`'s field `name`, in terms of the
    /// type's parameters and the constructor's earlier fields.
    fn ctor_field_type(&self, d: stitchwort_core::DataId, c: usize, name: &str) -> Option<String> {
        let g = &self.globals;
        let data = g.data(d);
        let ctor = &data.ctors[c];
        let i = ctor.fields.iter().position(|(f, _)| **f == *name)?;
        let mut names: Vec<Name> = data.params.iter().map(|(n, _)| n.clone()).collect();
        names.extend(ctor.fields[..i].iter().map(|(n, _)| n.clone()));
        Some(pretty::term(g, &names, &ctor.fields[i].1))
    }

    fn global_type(&self, global: Global) -> Option<String> {
        let g = &self.globals;
        match global {
            Global::Def(id) => Some(pretty::value(g, &[], &g.def(id).ty_value)),
            Global::Data(d) => {
                let data = g.data(d);
                let mut ty = Term::Sort(data.sort);
                for (name, t) in data.indices.iter().rev() {
                    ty = Term::Pi(name.clone(), Icit::Explicit, t.clone().into(), ty.into());
                }
                for (name, t) in data.params.iter().rev() {
                    ty = Term::Pi(name.clone(), Icit::Explicit, t.clone().into(), ty.into());
                }
                Some(pretty::term(g, &[], &ty))
            }
            Global::Ctor(d, c) => {
                let data = g.data(d);
                let ctor = &data.ctors[c];
                let (np, nf) = (data.params.len(), ctor.fields.len());
                let mut args: Vec<Term> = (0..np).map(|k| Term::Var(np + nf - 1 - k)).collect();
                args.extend(ctor.result.iter().cloned());
                let mut ty = Term::data(d, args);
                for (i, (name, t)) in ctor.fields.iter().enumerate().rev() {
                    let icit = if ctor.implicit.get(i).copied().unwrap_or(false) {
                        Icit::Implicit
                    } else {
                        Icit::Explicit
                    };
                    ty = Term::Pi(name.clone(), icit, t.clone().into(), ty.into());
                }
                for (name, t) in data.params.iter().rev() {
                    ty = Term::Pi(name.clone(), Icit::Implicit, t.clone().into(), ty.into());
                }
                Some(pretty::term(g, &[], &ty))
            }
            _ => None,
        }
    }
}

// ---- The walk ------------------------------------------------------------

/// One step of the walk: as `module::free_names`, but binders keep their
/// spans.
enum Work<'a> {
    Expr(&'a Expr),
    Pattern(&'a Pattern),
    Bind(&'a ast::Name),
    Unbind(&'a str),
    Use(&'a ast::Name),
}

struct Walk<'n> {
    nav: &'n mut Recorder,
    prefix: String,
    display: String,
    /// Whether definitions go in the outline: not for library files, whose
    /// symbols are made when something refers to them.
    outline: bool,
}

impl Walk<'_> {
    fn module(&mut self, module: &Module) {
        let decls = &module.decls;
        let mut i = 0;
        while i < decls.len() {
            match &decls[i] {
                Decl::Signature {
                    name,
                    ty,
                    theorem,
                    synonym,
                    instance,
                    span,
                    ..
                } => {
                    let mut j = i + 1;
                    let mut range = *span;
                    while let Some(Decl::Equation { span, .. }) = decls.get(j) {
                        range = range.to(*span);
                        j += 1;
                    }
                    let equations = &decls[i + 1..j];
                    let kind = if *theorem {
                        "theorem"
                    } else if *instance {
                        "instance"
                    } else if *synonym {
                        "type"
                    } else {
                        "def"
                    };
                    self.item(&name.text, kind, name.span, range, None);
                    self.signature(ty, equations);
                    i = j;
                    continue;
                }
                Decl::Data {
                    name,
                    params,
                    indices,
                    sort,
                    ctors,
                    record,
                    interface,
                    span,
                    ..
                } => self.data(
                    name,
                    params,
                    indices,
                    sort.as_ref(),
                    ctors,
                    *record,
                    *interface,
                    *span,
                ),
                Decl::Ability {
                    name,
                    params,
                    ops,
                    span,
                } => {
                    let owner = self.item(&name.text, "ability", name.span, *span, None);
                    let mut work = Vec::new();
                    for binder in params {
                        work.push(Work::Expr(&binder.ty));
                        work.extend(binder.names.iter().map(Work::Bind));
                    }
                    for (op, ty) in ops {
                        self.item(
                            &format!("{}.{}", name.text, op.text),
                            "op",
                            op.span,
                            op.span,
                            Some(owner),
                        );
                        work.push(Work::Expr(ty));
                    }
                    work.extend(
                        params
                            .iter()
                            .flat_map(|b| b.names.iter().map(|n| Work::Unbind(&n.text))),
                    );
                    self.run(work);
                }
                Decl::Test { name, expr, span } => {
                    self.item(name, "test", *span, *span, None);
                    self.run(vec![Work::Expr(expr)]);
                }
                Decl::Equation { .. } => {}
            }
            i += 1;
        }
    }

    /// Adds a definition to the outline; its index.
    fn item(
        &mut self,
        name: &str,
        kind: &'static str,
        span: Span,
        range: Span,
        container: Option<usize>,
    ) -> usize {
        if !self.outline {
            return 0;
        }
        self.nav.outline.push(OutlineItem {
            name: format!("{}{name}", self.display),
            key: format!("{}{name}", self.prefix),
            kind,
            span,
            range,
            container,
        });
        self.nav.outline.len() - 1
    }

    #[allow(clippy::too_many_arguments)]
    fn data(
        &mut self,
        name: &ast::Name,
        params: &[ast::Binder],
        indices: &[(Option<ast::Name>, Expr)],
        sort: Option<&Expr>,
        ctors: &[ast::CtorDecl],
        record: bool,
        interface: bool,
        span: Span,
    ) {
        let kind = if interface {
            "interface"
        } else if record {
            "record"
        } else {
            "data"
        };
        let owner = self.item(&name.text, kind, name.span, span, None);
        let mut work = Vec::new();
        for binder in params {
            work.push(Work::Expr(&binder.ty));
            work.extend(binder.names.iter().map(Work::Bind));
        }
        work.extend(indices.iter().map(|(_, e)| Work::Expr(e)));
        work.extend(sort.map(Work::Expr));
        for ctor in ctors {
            if record {
                for binder in &ctor.fields {
                    for field in &binder.names {
                        self.item(
                            &format!("{}.{}", name.text, field.text),
                            "field",
                            field.span,
                            field.span,
                            Some(owner),
                        );
                        self.nav
                            .field_spans
                            .insert((span, field.text.clone()), field.span);
                    }
                }
            } else {
                self.item(
                    &format!("{}.{}", name.text, ctor.name.text),
                    "ctor",
                    ctor.name.span,
                    ctor.name.span,
                    Some(owner),
                );
                // For `C { f = … }` patterns: a field by its constructor.
                for binder in &ctor.fields {
                    for field in &binder.names {
                        self.nav
                            .field_spans
                            .insert((ctor.name.span, field.text.clone()), field.span);
                    }
                }
            }
            for binder in &ctor.fields {
                work.push(Work::Expr(&binder.ty));
                work.extend(binder.names.iter().map(Work::Bind));
            }
            work.extend(ctor.result.iter().map(Work::Expr));
            work.extend(
                ctor.fields
                    .iter()
                    .rev()
                    .flat_map(|b| b.names.iter().rev().map(|n| Work::Unbind(&n.text))),
            );
        }
        work.extend(
            params
                .iter()
                .rev()
                .flat_map(|b| b.names.iter().rev().map(|n| Work::Unbind(&n.text))),
        );
        self.run(work);
    }

    /// A signature and its equations.
    fn signature(&mut self, ty: &Expr, equations: &[Decl]) {
        let mut work = vec![Work::Expr(ty)];
        let binders = body_binders(ty, equations);
        for eq in equations {
            let Decl::Equation { patterns, rhs, .. } = eq else {
                continue;
            };
            work.extend(binders.iter().map(|n| Work::Bind(n)));
            let mut vars = Vec::new();
            for p in patterns {
                pattern_binders(p, &mut vars);
                work.push(Work::Pattern(p));
            }
            work.extend(rhs.iter().map(Work::Expr));
            work.extend(vars.into_iter().map(Work::Unbind));
            work.extend(binders.iter().map(|n| Work::Unbind(&n.text)));
        }
        self.run(work);
    }

    fn local_def<'a>(def: &'a ast::LocalDef) -> Vec<Work<'a>> {
        let Decl::Signature { ty, .. } = &def.signature else {
            return Vec::new();
        };
        let mut work = vec![Work::Expr(ty)];
        let binders = body_binders(ty, &def.equations);
        for eq in &def.equations {
            let Decl::Equation { patterns, rhs, .. } = eq else {
                continue;
            };
            work.extend(binders.iter().map(|n| Work::Bind(n)));
            let mut vars = Vec::new();
            for p in patterns {
                pattern_binders(p, &mut vars);
                work.push(Work::Pattern(p));
            }
            work.extend(rhs.iter().map(Work::Expr));
            work.extend(vars.into_iter().map(Work::Unbind));
            work.extend(binders.iter().map(|n| Work::Unbind(&n.text)));
        }
        work
    }

    /// Runs steps in order, with a work list (expressions nest more deeply
    /// than recursion could follow).
    fn run(&mut self, work: Vec<Work<'_>>) {
        let mut bound: HashMap<&str, Vec<Span>> = HashMap::new();
        let mut stack: Vec<Work> = work;
        stack.reverse();
        fn then<'a>(stack: &mut Vec<Work<'a>>, steps: Vec<Work<'a>>) {
            stack.extend(steps.into_iter().rev());
        }
        while let Some(step) = stack.pop() {
            let expr = match step {
                Work::Bind(n) => {
                    self.nav.note_binder(&n.text, n.span);
                    bound.entry(&n.text).or_default().push(n.span);
                    continue;
                }
                Work::Unbind(x) => {
                    if let Some(spans) = bound.get_mut(x) {
                        spans.pop();
                    }
                    continue;
                }
                Work::Use(n) => {
                    let first = n.text.split('.').next().unwrap_or_default();
                    if first.starts_with('%') {
                        continue;
                    }
                    if let Some(&binder) = bound.get(first).and_then(|s| s.last()) {
                        let end = n.span.start + u32::try_from(first.len()).unwrap_or(0);
                        let span = if first.len() == n.text.len() {
                            n.span
                        } else {
                            Span::new(n.span.file, n.span.start, end)
                        };
                        self.nav.locals.push(LocalUse {
                            span,
                            name: first.to_string(),
                            binder,
                        });
                    }
                    continue;
                }
                Work::Pattern(p) => {
                    match p {
                        Pattern::Var(x) => {
                            self.nav.note_binder(&x.text, x.span);
                            bound.entry(&x.text).or_default().push(x.span);
                        }
                        Pattern::Ctor(_, args, _) => {
                            then(&mut stack, args.iter().map(Work::Pattern).collect());
                        }
                        Pattern::Tuple(a, b, _) | Pattern::Cons(a, b, _) => {
                            then(&mut stack, vec![Work::Pattern(a), Work::Pattern(b)]);
                        }
                        Pattern::Named(_, p, _) => then(&mut stack, vec![Work::Pattern(p)]),
                        Pattern::Record { fields, .. } | Pattern::CtorFields { fields, .. } => {
                            then(
                                &mut stack,
                                fields.iter().map(|(_, p)| Work::Pattern(p)).collect(),
                            )
                        }
                        Pattern::Wildcard(_)
                        | Pattern::Absurd(_)
                        | Pattern::Nil(_)
                        | Pattern::Num(..)
                        | Pattern::NegNum(..)
                        | Pattern::Char(..) => {}
                    }
                    continue;
                }
                Work::Expr(e) => e,
            };
            match expr {
                Expr::Var(n) => stack.push(Work::Use(n)),
                Expr::Num(..)
                | Expr::Str(..)
                | Expr::Include(..)
                | Expr::Char(..)
                | Expr::Type(..)
                | Expr::Prop(_)
                | Expr::Hole(_)
                | Expr::Unit(_) => {}
                Expr::App(a, b)
                | Expr::Arrow(a, b)
                | Expr::Binary(_, a, b)
                | Expr::Pipe(a, b)
                | Expr::Seq(a, b) => then(&mut stack, vec![Work::Expr(a), Work::Expr(b)]),
                Expr::Neg(a, _) => stack.push(Work::Expr(a)),
                Expr::Lam(names, body, _) => {
                    let mut steps: Vec<Work> = names.iter().map(Work::Bind).collect();
                    steps.push(Work::Expr(body));
                    steps.extend(names.iter().map(|n| Work::Unbind(&n.text)));
                    then(&mut stack, steps);
                }
                Expr::TypedLam(name, ty, body, _) => then(
                    &mut stack,
                    vec![
                        Work::Expr(ty),
                        Work::Bind(name),
                        Work::Expr(body),
                        Work::Unbind(&name.text),
                    ],
                ),
                Expr::Pi {
                    names, dom, cod, ..
                } => {
                    let mut steps = vec![Work::Expr(dom)];
                    steps.extend(names.iter().map(Work::Bind));
                    steps.push(Work::Expr(cod));
                    steps.extend(names.iter().map(|n| Work::Unbind(&n.text)));
                    then(&mut stack, steps);
                }
                Expr::NamedArg(_, value, _) => stack.push(Work::Expr(value)),
                Expr::If {
                    binder,
                    cond,
                    then: yes,
                    otherwise,
                    ..
                } => {
                    let mut steps = vec![Work::Expr(cond)];
                    steps.extend(binder.iter().map(Work::Bind));
                    steps.extend([Work::Expr(yes), Work::Expr(otherwise)]);
                    steps.extend(binder.iter().map(|b| Work::Unbind(&b.text)));
                    then(&mut stack, steps);
                }
                Expr::Ann(e, t, _) | Expr::Tuple(e, t, _) => {
                    then(&mut stack, vec![Work::Expr(e), Work::Expr(t)]);
                }
                Expr::List(items, _) => then(&mut stack, items.iter().map(Work::Expr).collect()),
                Expr::Record { base, fields, .. } => {
                    let mut steps: Vec<Work> = base.iter().map(|b| Work::Expr(b)).collect();
                    steps.extend(fields.iter().map(|(_, e)| Work::Expr(e)));
                    then(&mut stack, steps);
                }
                Expr::Field(e, _) => stack.push(Work::Expr(e)),
                Expr::Omega { facts, .. } => {
                    then(&mut stack, facts.iter().map(Work::Expr).collect())
                }
                Expr::Calc { first, steps, .. } => {
                    let mut work = vec![Work::Expr(first)];
                    for step in steps {
                        work.push(Work::Expr(&step.rhs));
                        work.extend(step.proof.iter().map(Work::Expr));
                    }
                    then(&mut stack, work);
                }
                Expr::Rewrite {
                    rules,
                    target,
                    body,
                    ..
                } => {
                    let mut work: Vec<Work> = rules.iter().map(|r| Work::Expr(&r.proof)).collect();
                    work.extend(target.iter().map(|t| Work::Expr(t)));
                    work.extend(body.iter().map(|b| Work::Expr(b)));
                    then(&mut stack, work);
                }
                Expr::Effect(row, ty) => {
                    let mut steps: Vec<Work> = row.abilities.iter().map(Work::Expr).collect();
                    steps.push(Work::Expr(ty));
                    then(&mut stack, steps);
                }
                Expr::Let {
                    name,
                    ty,
                    value,
                    body,
                    ..
                } => {
                    let mut steps: Vec<Work> = ty.iter().map(|t| Work::Expr(t)).collect();
                    steps.extend([
                        Work::Expr(value),
                        Work::Bind(name),
                        Work::Expr(body),
                        Work::Unbind(&name.text),
                    ]);
                    then(&mut stack, steps);
                }
                Expr::Match {
                    scrutinees, alts, ..
                } => {
                    let mut steps: Vec<Work> =
                        scrutinees.iter().map(|s| Work::Expr(&s.expr)).collect();
                    let names: Vec<&ast::Name> =
                        scrutinees.iter().filter_map(|s| s.name.as_ref()).collect();
                    steps.extend(names.iter().map(|n| Work::Bind(n)));
                    for alt in alts {
                        let mut vars = Vec::new();
                        for p in &alt.patterns {
                            pattern_binders(p, &mut vars);
                            steps.push(Work::Pattern(p));
                        }
                        steps.push(Work::Expr(&alt.body));
                        steps.extend(vars.into_iter().map(Work::Unbind));
                    }
                    steps.extend(names.iter().map(|n| Work::Unbind(&n.text)));
                    then(&mut stack, steps);
                }
                Expr::LocalDefs { defs, body, .. } => {
                    let names: Vec<&ast::Name> = defs
                        .iter()
                        .filter_map(|d| match &d.signature {
                            Decl::Signature { name, .. } => Some(name),
                            _ => None,
                        })
                        .collect();
                    let mut steps: Vec<Work> = names.iter().map(|n| Work::Bind(n)).collect();
                    for def in defs {
                        steps.extend(Self::local_def(def));
                    }
                    steps.push(Work::Expr(body));
                    steps.extend(names.iter().map(|n| Work::Unbind(&n.text)));
                    then(&mut stack, steps);
                }
                Expr::Handle { body, clauses, .. } => {
                    let mut steps = vec![Work::Expr(body)];
                    for clause in clauses {
                        match clause {
                            Clause::Return { var, body } => steps.extend([
                                Work::Bind(var),
                                Work::Expr(body),
                                Work::Unbind(&var.text),
                            ]),
                            Clause::Op { arg, k, body, .. } => {
                                let mut vars = Vec::new();
                                pattern_binders(arg, &mut vars);
                                steps.push(Work::Pattern(arg));
                                steps.extend([
                                    Work::Bind(k),
                                    Work::Expr(body),
                                    Work::Unbind(&k.text),
                                ]);
                                steps.extend(vars.into_iter().map(Work::Unbind));
                            }
                        }
                    }
                    then(&mut stack, steps);
                }
            }
        }
    }
}

/// The variables a pattern binds.
fn pattern_binders<'a>(pattern: &'a Pattern, out: &mut Vec<&'a str>) {
    match pattern {
        Pattern::Var(x) => out.push(&x.text),
        Pattern::Ctor(_, args, _) => args.iter().for_each(|p| pattern_binders(p, out)),
        Pattern::Tuple(a, b, _) | Pattern::Cons(a, b, _) => {
            pattern_binders(a, out);
            pattern_binders(b, out);
        }
        Pattern::Record { fields, .. } | Pattern::CtorFields { fields, .. } => {
            fields.iter().for_each(|(_, p)| pattern_binders(p, out))
        }
        Pattern::Named(_, p, _) => pattern_binders(p, out),
        Pattern::Wildcard(_)
        | Pattern::Absurd(_)
        | Pattern::Num(..)
        | Pattern::NegNum(..)
        | Pattern::Char(..)
        | Pattern::Nil(_) => {}
    }
}

/// The names a definition's equations can use for its parameters named in
/// the signature, as `module::body_binders`, with their spans.
fn body_binders<'a>(ty: &'a Expr, equations: &[Decl]) -> Vec<&'a ast::Name> {
    let arity = match equations.first() {
        Some(Decl::Equation { patterns, .. }) => patterns.len(),
        _ => 0,
    };
    let mut names = Vec::new();
    let mut explicit = 0;
    let mut ty = ty;
    loop {
        match ty {
            Expr::Pi {
                names: ns,
                implicit: true,
                cod,
                ..
            } => {
                names.extend(ns.iter());
                ty = cod;
            }
            Expr::Pi { names: ns, cod, .. } if explicit + ns.len() <= arity => {
                explicit += ns.len();
                ty = cod;
            }
            Expr::Arrow(_, cod) if explicit < arity => {
                explicit += 1;
                ty = cod;
            }
            _ => break,
        }
    }
    names
}
