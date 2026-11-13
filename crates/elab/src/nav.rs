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

use stitchwort_core::collections::HashMap;
use stitchwort_core::registry::Builtin;
use stitchwort_core::{DefId, Ev, Icit, Name, Term, Value, pretty};
use stitchwort_syntax::ast::{self, Clause, Decl, Expr, Module, Pattern};
use stitchwort_syntax::{FileId, Span};

use crate::check::Ctx;
use crate::equations::is_generated_name;
use crate::library::PendingKind;
use crate::scope::Resolved;
use crate::state::{Logged, Logs};
use crate::{Elaborator, Global};

/// What the elaborator noted, and the walk found.
#[derive(Clone, Default)]
pub(crate) struct Recorder {
    /// A name resolved to a declaration, by the span of the name.
    pub(crate) refs: Logged<Span, Noted>,
    /// The types of local variables where they're used, not yet printed
    /// (the metavariables in them are solved by the end of the
    /// declaration): the span, the type, and the names of the context.
    pub(crate) pending: Vec<(Span, Value, Vec<Name>, bool)>,
    /// The printed types, by where the use starts.
    pub(crate) local_types: Logged<(FileId, u32), String>,
    /// Those with an outermost `Not` written as `p → Void` (`not_unfolded`).
    pub(crate) local_unfolded: Logged<(FileId, u32), String>,
    /// Local variables used, from the walk.
    pub(crate) locals: Vec<LocalUse>,
    /// Where local variables are bound (a binder refers to itself).
    pub(crate) binders: Vec<LocalUse>,
    /// The definitions of the files walked.
    pub(crate) outline: Vec<OutlineItem>,
    /// The parameters of the declarations walked, by their binders in the
    /// declaration's header (a library file loaded from the cache has its
    /// own, kept in the entry).
    pub(crate) params: Vec<ParamBinder>,
    /// The names in named arguments `(x := e)` and `[x := p]` that the walk
    /// found, to be linked to the callee's parameter in the index.
    pub(crate) named: Vec<NamedUse>,
    /// Each record field's name, by its type's declaration and its name.
    pub(crate) field_spans: Logged<(Span, String), Span>,
    /// Whether to note the type of every elaborated expression
    /// ([`Elaborator::enable_expression_types`]).
    pub(crate) exprs: bool,
    /// More than 0 while elaborating what a declaration generates (the
    /// equality lemmas, `Show` and `Ord`): written nowhere, so nothing is
    /// noted under the declaration's span.
    pub(crate) generated: usize,
    /// The printed type of the expression written at a span (the last one
    /// elaborated there), for hovering over a selection.
    pub(crate) expr_types: Logged<Span, String>,
    /// Those with an outermost `Not` written as `p → Void` (`not_unfolded`).
    pub(crate) expr_unfolded: Logged<Span, String>,
    /// For hover on the head of a call that left defaulted parameters out,
    /// by the head's span: the defaults it used; and on a term a test fact
    /// was built from, what it built (`build.rs`).
    pub(crate) call_defaults: Logged<Span, String>,
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
        lines.extend(
            self.local_unfolded
                .iter()
                .map(|((file, at), ty)| format!("nav type-unfolded @{}:{at} {ty}", file.index())),
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
        lines.extend(
            self.expr_unfolded
                .iter()
                .map(|(at, ty)| format!("nav expr-unfolded {} {ty}", span(*at))),
        );
        lines.extend(
            self.call_defaults
                .iter()
                .map(|(at, used)| format!("nav defaults {} {used:?}", span(*at))),
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

/// Where a [`Recorder`] was, to rewind it to ([`crate::rewind`]): the
/// lists' lengths (the lists only grow between marks). Its maps are
/// [`Logged`], put back by the session's journal ([`Recorder`]'s [`Logs`]).
pub(crate) struct NavMark {
    locals: usize,
    binders: usize,
    outline: usize,
    params: usize,
    named: usize,
    pending: Vec<(Span, Value, Vec<Name>, bool)>,
    exprs: bool,
    generated: usize,
}

/// Where each of a [`Recorder`]'s logged maps' log is.
pub(crate) struct Positions {
    refs: usize,
    local_types: usize,
    local_unfolded: usize,
    field_spans: usize,
    expr_types: usize,
    expr_unfolded: usize,
    call_defaults: usize,
}

impl Recorder {
    pub(crate) fn mark(&self) -> NavMark {
        NavMark {
            locals: self.locals.len(),
            binders: self.binders.len(),
            outline: self.outline.len(),
            params: self.params.len(),
            named: self.named.len(),
            pending: self.pending.clone(),
            exprs: self.exprs,
            generated: self.generated,
        }
    }

    /// Back to `mark`; the maps are put back by the journal first.
    pub(crate) fn rewind(&mut self, mark: &NavMark) {
        assert!(
            mark.locals <= self.locals.len()
                && mark.binders <= self.binders.len()
                && mark.outline <= self.outline.len(),
            "a mark from after a rewind"
        );
        self.locals.truncate(mark.locals);
        self.binders.truncate(mark.binders);
        self.outline.truncate(mark.outline);
        self.params.truncate(mark.params);
        self.named.truncate(mark.named);
        self.pending = mark.pending.clone();
        self.exprs = mark.exprs;
        self.generated = mark.generated;
    }

    /// The logged maps, with what each does in [`Logs`]'s methods.
    fn logged(&mut self) -> [&mut dyn Logs<Positions = usize>; 7] {
        let Recorder {
            refs,
            local_types,
            local_unfolded,
            field_spans,
            expr_types,
            expr_unfolded,
            call_defaults,
            // Lists, cut back by `rewind`, or put back from the mark.
            pending: _,
            locals: _,
            binders: _,
            outline: _,
            params: _,
            named: _,
            exprs: _,
            generated: _,
        } = self;
        [
            refs,
            local_types,
            local_unfolded,
            field_spans,
            expr_types,
            expr_unfolded,
            call_defaults,
        ]
    }
}

/// A language server keeps a checkpoint before each namespace it has
/// checked, and a copy of the maps in each made them quadratic in the
/// project (8 of the 13 GB of an editor session on the AoC project;
/// SW-1052): so they log what each change replaced.
impl Logs for Recorder {
    type Positions = Positions;

    fn positions(&self) -> Positions {
        Positions {
            refs: self.refs.position(),
            local_types: self.local_types.position(),
            local_unfolded: self.local_unfolded.position(),
            field_spans: self.field_spans.position(),
            expr_types: self.expr_types.position(),
            expr_unfolded: self.expr_unfolded.position(),
            call_defaults: self.call_defaults.position(),
        }
    }

    fn undo_to(&mut self, at: &Positions) -> usize {
        let Positions {
            refs,
            local_types,
            local_unfolded,
            field_spans,
            expr_types,
            expr_unfolded,
            call_defaults,
        } = at;
        let [a, b, c, d, e, f, g] = self.logged();
        a.undo_to(refs)
            + b.undo_to(local_types)
            + c.undo_to(local_unfolded)
            + d.undo_to(field_spans)
            + e.undo_to(expr_types)
            + f.undo_to(expr_unfolded)
            + g.undo_to(call_defaults)
    }

    fn set_generation(&mut self, g: Option<u32>) {
        self.logged().into_iter().for_each(|t| t.set_generation(g));
    }

    fn entries(&self) -> usize {
        self.refs.entries()
            + self.local_types.entries()
            + self.local_unfolded.entries()
            + self.field_spans.entries()
            + self.expr_types.entries()
            + self.expr_unfolded.entries()
            + self.call_defaults.entries()
    }

    fn bytes(&self) -> usize {
        self.refs.bytes()
            + self.local_types.bytes()
            + self.local_unfolded.bytes()
            + self.field_spans.bytes()
            + self.expr_types.bytes()
            + self.expr_unfolded.bytes()
            + self.call_defaults.bytes()
    }

    fn distinct_keys(&self) -> usize {
        self.refs.distinct_keys()
            + self.local_types.distinct_keys()
            + self.local_unfolded.distinct_keys()
            + self.field_spans.distinct_keys()
            + self.expr_types.distinct_keys()
            + self.expr_unfolded.distinct_keys()
            + self.call_defaults.distinct_keys()
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

/// A parameter written in a declaration's header.
#[derive(Clone)]
pub(crate) struct ParamBinder {
    /// The declaration's name where it's declared.
    pub(crate) owner: Span,
    pub(crate) name: String,
    pub(crate) binder: Span,
}

/// The name in a named argument or pattern, and the head it is for.
#[derive(Clone)]
pub(crate) struct NamedUse {
    /// The places a reference to the head may be noted: the whole written
    /// name, and its last component (`xs.foldl`).
    pub(crate) head: [Span; 2],
    pub(crate) name: String,
    pub(crate) span: Span,
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
    /// ([`Elaborator::enable_expression_types`]), sorted by position. The
    /// third is the type with an outermost `Not` written as `p → Void`
    /// (`not_unfolded`), when it has one.
    pub exprs: Vec<(Span, String, Option<String>)>,
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
    /// For a function, its parameters with their names, as
    /// `(low: Nat) -> [n: Nat] -> Nat` (the type above leaves the names of
    /// parameters nothing depends on out): for completing the names in a
    /// named argument.
    pub signature: Option<String>,
    /// For a function: its parameters as its declaration writes them, up to
    /// the first one without a name of its own, then the rest of the type,
    /// `(low: Nat) [n: Nat]: Nat → Nat`; for a hover, which puts the kind and
    /// name before it.
    pub header: Option<String>,
    /// Its type with an outermost `Not`, if it has one, written as
    /// `p → Void` (`not_unfolded`), for hover.
    pub unfolded: Option<String>,
}

/// A name a file can write unqualified ([`Elaborator::names_in_scope`]).
#[derive(Clone, Debug)]
pub struct ScopeName {
    /// As written.
    pub name: String,
    /// What it names, in full (`List.map`; the library's without `Std.`).
    pub key: String,
    pub kind: &'static str,
    /// None for a library declaration not loaded yet.
    pub ty: Option<String>,
    /// Declared by the file's own namespace (else imported or a default).
    pub own: bool,
    /// Not in scope: the import that brings it, `(path, item)` for
    /// `import path (item)`.
    pub import: Option<(String, String)>,
}

pub struct NavRef {
    pub span: Span,
    /// The reference is the last component of this dotted name: the span
    /// covers more (`xs.map`).
    pub dot: Option<String>,
    pub target: NavTarget,
    pub ty: Option<String>,
    /// The type with an outermost `Not`, if it has one, written as
    /// `p → Void` (`not_unfolded`), for hover.
    pub unfolded: Option<String>,
    /// For the head of a call that left defaulted parameters out: the
    /// defaults it used, "`step` left out: its default `1`".
    pub defaults: Option<String>,
    /// A record field punned with a variable, `{ name }`: this and another
    /// reference (the field, the variable) are written by the same text.
    pub pun: bool,
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
        let start: usize = crate::core_layout()
            .iter()
            .take_while(|(p, _)| *p != path)
            .map(|(_, len)| len)
            .sum();
        let (_, len) = crate::core_layout().iter().find(|(p, _)| *p == path)?;
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
        self.present.nav = Some(RefCell::new(Recorder::default()));
    }

    /// Also records the type of every expression elaborated, for the
    /// language server's hover over a selection. Call right after
    /// [`Elaborator::enable_navigation`].
    pub fn enable_expression_types(&mut self) {
        if let Some(nav) = &mut self.present.nav {
            nav.get_mut().exprs = true;
        }
    }

    /// The expression written at `span` has type `ty` in `cx`.
    pub(crate) fn note_expr(&self, cx: &Ctx, span: Span, ty: &Value, checked: bool) {
        self.note_probe(cx, span, ty, checked);
        if span.start == span.end {
            return;
        }
        if let Some(nav) = &self.present.nav {
            let mut nav = nav.borrow_mut();
            if nav.exprs && nav.generated == 0 {
                nav.pending.push((span, ty.clone(), cx.names.clone(), true));
            }
        }
    }

    pub(crate) fn note(&self, at: Span, noted: Noted) {
        if let Some(nav) = &self.present.nav {
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
        if let Some(nav) = &self.present.nav {
            nav.borrow_mut().generated += 1;
        }
        let out = f(self);
        if let Some(nav) = &self.present.nav {
            nav.borrow_mut().generated -= 1;
        }
        out
    }

    /// [`Self::unnoted`] in a body's context: `f` elaborates code the
    /// compiler wrote at a use site (a shared-field update's `match`).
    pub(crate) fn unnoted_in<'e, T>(
        cx: &mut crate::check::Ctx<'e>,
        f: impl FnOnce(&mut crate::check::Ctx<'e>) -> T,
    ) -> T {
        if let Some(nav) = &cx.e.present.nav {
            nav.borrow_mut().generated += 1;
        }
        let out = f(cx);
        if let Some(nav) = &cx.e.present.nav {
            nav.borrow_mut().generated -= 1;
        }
        out
    }

    /// What the term written at `at` builds (`build.rs`), for hover: kept
    /// with the defaults a call there used.
    pub(crate) fn note_build(&self, at: Span, what: String) {
        if let Some(nav) = &self.present.nav {
            let mut nav = nav.borrow_mut();
            if nav.generated == 0 {
                let text = match nav.call_defaults.get(&at) {
                    Some(defaults) if !defaults.contains(&what) => format!("{defaults}\n\n{what}"),
                    Some(defaults) => defaults.clone(),
                    None => what,
                };
                nav.call_defaults.insert(at, text);
            }
        }
    }

    /// The defaults a call whose head is written at `at` used, for hover.
    pub(crate) fn note_call_defaults(&self, at: Span, used: String) {
        if let Some(nav) = &self.present.nav {
            let mut nav = nav.borrow_mut();
            if nav.generated == 0 {
                nav.call_defaults.insert(at, used);
            }
        }
    }

    /// A built-in name (`rfl`, `J`, `Quot`, …): its reference is to the
    /// declaration `std/core/Builtins.sw` documents it with (SW-1146). It's
    /// found by its key, not by scope: the library's names aren't all in
    /// scope in a program, and these mean the built-in wherever they're written.
    pub(crate) fn note_builtin(&self, name: &ast::Name) {
        if self.present.nav.is_none() {
            return;
        }
        let key = format!("{}.{}", crate::scope::STD, name.text);
        if let Some((key, global, target)) = self.scope.entry(&key) {
            self.note_found(name.span, key, global, target);
        }
    }

    /// `name`, written, resolved to a declaration.
    pub(crate) fn note_name(&self, name: &ast::Name) {
        if self.present.nav.is_none() {
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
        if self.present.nav.is_some() && !matches!(global, Global::Unchecked(_) | Global::Failed) {
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
        if self.present.nav.is_none() {
            return;
        }
        let def = self.kernel.def(id);
        // The declaration's name, as a written name finds it; a definition's
        // own span covers all of it.
        let path = def.path().to_string();
        let relative = path.strip_prefix("Main.").unwrap_or(&path);
        let target = match self.scope.get(&path).or_else(|| self.scope.get(relative)) {
            Some((Global::Def(found), span)) if found == id => span,
            _ => def.span(),
        };
        self.note(
            field.span,
            Noted {
                key: def.path().to_string(),
                target,
                global: Global::Def(id),
                dot: Some(field.text.clone()),
            },
        );
    }

    /// The field `name` of record type `d`, written in a literal, update or
    /// pattern.
    pub(crate) fn note_field(&self, d: stitchwort_core::DataId, name: &ast::Name) {
        if self.present.nav.is_none() {
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
        let Some(nav) = &self.present.nav else {
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
        if let Some(nav) = &self.present.nav {
            let mut nav = nav.borrow_mut();
            if nav.generated == 0 {
                nav.pending
                    .push((name.span, ty.clone(), cx.names.clone(), false));
            }
        }
    }

    /// The type of the variable a `let` binds, at its binder, so that one
    /// nothing uses has a type too (for its inlay hint).
    pub(crate) fn note_let_binder(&self, cx: &Ctx, name: &ast::Name, ty: &Value) {
        if let Some(nav) = &self.present.nav {
            let mut nav = nav.borrow_mut();
            if nav.generated == 0 {
                nav.pending
                    .push((name.span, ty.clone(), cx.names.clone(), false));
            }
        }
    }

    /// The name of a parameter in a named argument (`(x := e)`), of type
    /// `ty` in a context with `names`. It's noted as a local variable that
    /// is its own binder, so hover shows the parameter's type.
    pub(crate) fn note_parameter(&self, name: &ast::Name, ty: &Value, names: Vec<Name>) {
        if let Some(nav) = &self.present.nav {
            let mut nav = nav.borrow_mut();
            if nav.generated == 0 {
                nav.pending.push((name.span, ty.clone(), names, false));
                if nav.locals.iter().any(|l| l.span == name.span) {
                    return;
                }
                let local = LocalUse {
                    span: name.span,
                    name: name.text.to_string(),
                    binder: name.span,
                };
                nav.locals.push(local);
            }
        }
    }

    /// How many local variables' types are waiting to be printed: a
    /// [`crate::undo::Snapshot`] keeps it, to drop the ones an undone
    /// attempt noted.
    pub(crate) fn pending_local_types(&self) -> usize {
        self.present
            .nav
            .as_ref()
            .map_or(0, |nav| nav.borrow().pending.len())
    }

    /// Drops the local variables' types noted after the first `len`: their
    /// attempt was undone, and the metavariables in them with it, so they
    /// can't be printed (a later metavariable may reuse the number of one
    /// in them, with a different solution).
    pub(crate) fn drop_local_types_since(&self, len: usize) {
        if let Some(nav) = &self.present.nav {
            nav.borrow_mut().pending.truncate(len);
        }
    }

    /// Prints the types noted, while the metavariables in them still have
    /// their solutions.
    pub(crate) fn flush_navigation(&self) {
        let Some(nav) = &self.present.nav else {
            return;
        };
        let mut nav = nav.borrow_mut();
        let pending = std::mem::take(&mut nav.pending);
        for (span, ty, names, expr) in pending {
            // Also called between a declaration's operations, where nothing
            // would limit the printer's evaluation or its depth (SW-1430):
            // each type is printed within limits of its own, and no deeper
            // than the operation running allows, if there is one. Running
            // out shows `…` and, unlike an attempt's, isn't passed on, so a
            // check doesn't depend on whether navigation is on.
            let budget = &self.kernel.machine.budget;
            let saved = budget.start_attempt(self.options.limits);
            let text = pretty::value_for_message(&self.ev(), &names, &ty);
            let unfolded = value_not_unfolded(&self.ev(), &names, &ty);
            budget.restore(saved);
            if expr {
                nav.expr_types.insert(span, text);
                if let Some(unfolded) = unfolded {
                    nav.expr_unfolded.insert(span, unfolded);
                }
            } else {
                nav.local_types.insert((span.file, span.start), text);
                if let Some(unfolded) = unfolded {
                    nav.local_unfolded.insert((span.file, span.start), unfolded);
                }
            }
        }
    }

    /// An import's item `item`, resolved to `key`.
    pub(crate) fn note_import(&self, item: &ast::Name, key: &str) {
        if self.present.nav.is_none() {
            return;
        }
        if let Some((global, span)) = self.scope.get(key) {
            self.note_found(item.span, key, global, span);
        }
    }

    /// Walks the syntax of the files of a module about to be elaborated.
    pub(crate) fn walk_for_navigation(&self, modules: &[&Module]) {
        let Some(nav) = &self.present.nav else {
            return;
        };
        let library = self.unit.loading_prelude || !self.library_stack_is_empty();
        let mut nav = nav.borrow_mut();
        for module in modules {
            let mut walk = Walk {
                nav: &mut nav,
                prefix: self.unit.namespace_root.clone(),
                outline: !library,
                display: if self.unit.namespace_root.is_empty() {
                    "Main.".to_string()
                } else {
                    self.unit.namespace_root.clone()
                },
            };
            walk.module(module);
        }
    }

    /// The index of what was recorded, for the references `wanted` says to include
    /// (the others' definitions are still there as targets).
    pub fn navigation_index(&self, wanted: &dyn Fn(Span, Option<&str>) -> bool) -> NavIndex {
        self.flush_navigation();
        let Some(nav) = &self.present.nav else {
            return NavIndex {
                symbols: Vec::new(),
                refs: Vec::new(),
                exprs: Vec::new(),
            };
        };
        let nav = nav.borrow();
        let mut symbols: Vec<NavSymbol> = Vec::new();
        let mut by_span: HashMap<Span, usize> = HashMap::default();
        for item in &nav.outline {
            by_span.insert(item.span, symbols.len());
            let key = item.key.clone();
            symbols.push(NavSymbol {
                ty: self
                    .scope
                    .get(&key)
                    .and_then(|(global, _)| self.global_type(global)),
                signature: self
                    .scope
                    .get(&key)
                    .and_then(|(global, _)| self.global_signature(global)),
                header: self
                    .scope
                    .get(&key)
                    .and_then(|(global, _)| self.global_header(global)),
                unfolded: self
                    .scope
                    .get(&key)
                    .and_then(|(global, _)| self.global_not_unfolded(global)),
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
        // The field of a constructor named in a named argument or pattern
        // (`VCons [n := k] …`) is a reference to the field.
        let named_fields: Vec<(Span, Noted)> = nav
            .named
            .iter()
            .filter_map(|used| {
                let ctor = used.head.iter().find_map(|at| nav.refs.get(at))?;
                (matches!(ctor.global, Global::Ctor(..))
                    && nav
                        .field_spans
                        .contains_key(&(ctor.target, used.name.clone())))
                .then(|| {
                    (
                        used.span,
                        Noted {
                            key: format!("{}.{}", ctor.key, used.name),
                            target: ctor.target,
                            global: ctor.global,
                            dot: None,
                        },
                    )
                })
            })
            .collect();
        noted_refs.extend(named_fields.iter().map(|(at, noted)| (at, noted)));
        noted_refs.sort_by_key(|(at, _)| (at.file.index(), at.start, at.end));
        // The symbols whose name is one a user writes (not a generated `%`
        // member's): the first such reference names the symbol.
        let mut visible: stitchwort_core::collections::HashSet<usize> =
            stitchwort_core::collections::HashSet::default();
        let field_binders: stitchwort_core::collections::HashSet<Span> =
            nav.field_spans.values().copied().collect();
        let mut by_name: HashMap<(Span, String), usize> = HashMap::default();
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
            // A theorem declared at a field (a shared field's update lemma,
            // `Shape.id.update.ref`, at `id`) is a symbol of its own there.
            let at_field = field_span.is_none() && field_binders.contains(&target);
            let found = if at_field {
                by_name.get(&(target, name.clone())).copied()
            } else {
                by_span.get(&target).copied()
            };
            let index = found.unwrap_or_else(|| {
                symbols.push(NavSymbol {
                    name: name.clone(),
                    kind,
                    span: target,
                    range: None,
                    container: None,
                    ty: ty_of(),
                    signature: if field_span.is_none() {
                        self.global_signature(global)
                    } else {
                        None
                    },
                    header: if field_span.is_none() {
                        self.global_header(global)
                    } else {
                        None
                    },
                    unfolded: if field_span.is_none() {
                        self.global_not_unfolded(global)
                    } else {
                        None
                    },
                });
                symbols.len() - 1
            });
            if at_field {
                by_name.insert((target, name.clone()), index);
            } else {
                by_span.insert(target, index);
            }
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
                unfolded: symbols[index].unfolded.clone(),
                defaults: nav.call_defaults.get(at).cloned(),
                pun: false,
            });
        }
        // A name taken for an implicitly bound variable (`implicit_guesses`)
        // that is a declaration's: its binder is its own first use, and a
        // reference to the declaration is noted there. The name is not a
        // local anywhere else in the declaration either (a later use in the
        // body is the declaration's, noted by the elaborator).
        let guesses: stitchwort_core::collections::HashSet<Span> = nav
            .locals
            .iter()
            .filter(|l| l.binder == l.span && nav.refs.contains_key(&l.span))
            .map(|l| l.span)
            .filter(|span| nav.binders.iter().any(|b| b.span == *span))
            .collect();
        // The name in a named argument `(x := e)` is a use of the callee's
        // parameter. (A callee that isn't known leaves the name as a variable
        // of its own.)
        let mut linked: stitchwort_core::collections::HashSet<Span> =
            stitchwort_core::collections::HashSet::default();
        for used in &nav.named {
            if named_fields.iter().any(|(at, _)| *at == used.span) {
                linked.insert(used.span);
                continue;
            }
            let Some(head) = used.head.iter().find_map(|at| nav.refs.get(at)) else {
                continue;
            };
            let Some(param) = nav
                .params
                .iter()
                .find(|p| p.owner == head.target && p.name == used.name)
            else {
                continue;
            };
            linked.insert(used.span);
            if !wanted(used.span, None) {
                continue;
            }
            refs.push(NavRef {
                span: used.span,
                dot: None,
                target: NavTarget::Binder {
                    name: used.name.clone(),
                    span: param.binder,
                },
                ty: nav
                    .local_types
                    .get(&(used.span.file, used.span.start))
                    .cloned(),
                unfolded: nav
                    .local_unfolded
                    .get(&(used.span.file, used.span.start))
                    .cloned(),
                defaults: None,
                pun: false,
            });
        }
        for local in &nav.locals {
            if guesses.contains(&local.span)
                || guesses.contains(&local.binder)
                || linked.contains(&local.span)
            {
                continue;
            }
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
                unfolded: nav
                    .local_unfolded
                    .get(&(local.span.file, local.span.start))
                    .cloned(),
                defaults: nav.call_defaults.get(&local.span).cloned(),
                pun: false,
            });
        }
        // Each declaration's own name refers to it, for hover and definition there.
        let mut taken: stitchwort_core::collections::HashSet<(FileId, u32)> =
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
                unfolded: symbols[i].unfolded.clone(),
                defaults: None,
                pun: false,
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
                    signature: self.global_signature(global),
                    header: self.global_header(global),
                    unfolded: self.global_not_unfolded(global),
                });
                symbols.len() - 1
            });
            refs.push(NavRef {
                span,
                dot: None,
                target: NavTarget::Symbol(index),
                ty: symbols[index].ty.clone(),
                unfolded: symbols[index].unfolded.clone(),
                defaults: None,
                pun: false,
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
                unfolded: symbol.unfolded.clone(),
                defaults: None,
                pun: false,
            });
        }
        // A local variable's binder refers to itself (a record field is a declaration, above).
        // (A pun `{ name }` in a pattern is both the field and the variable
        // it binds, at one span.)
        let field_refs: stitchwort_core::collections::HashSet<Span> = refs
            .iter()
            .filter(|r| {
                matches!(r.target, NavTarget::Symbol(i)
                if symbols[i].kind == "field" && symbols[i].span != r.span)
            })
            .map(|r| r.span)
            .collect();
        for binder in &nav.binders {
            if guesses.contains(&binder.span) {
                continue;
            }
            if !taken.insert((binder.span.file, binder.span.start))
                && !field_refs.contains(&binder.span)
            {
                continue;
            }
            refs.push(NavRef {
                span: binder.span,
                dot: None,
                target: NavTarget::Binder {
                    name: binder.name.clone(),
                    span: binder.span,
                },
                ty: nav
                    .local_types
                    .get(&(binder.span.file, binder.span.start))
                    .cloned(),
                unfolded: nav
                    .local_unfolded
                    .get(&(binder.span.file, binder.span.start))
                    .cloned(),
                defaults: None,
                pun: false,
            });
        }
        refs.sort_by_key(|r| (r.span.file.index(), r.span.start, r.span.end));
        // A field and a variable at one span are a pun.
        let mut start = 0;
        while start < refs.len() {
            let mut end = start + 1;
            while end < refs.len() && refs[end].span == refs[start].span {
                end += 1;
            }
            let group = &mut refs[start..end];
            let field = |r: &NavRef| {
                matches!(r.target, NavTarget::Symbol(i)
                    if symbols[i].kind == "field" && symbols[i].span != r.span)
            };
            if group.iter().any(field)
                && group
                    .iter()
                    .any(|r| matches!(r.target, NavTarget::Binder { .. }))
            {
                group
                    .iter_mut()
                    .filter(|r| field(r) || matches!(r.target, NavTarget::Binder { .. }))
                    .for_each(|r| r.pun = true);
            }
            start = end;
        }
        let mut exprs: Vec<(Span, String, Option<String>)> = nav
            .expr_types
            .iter()
            .map(|(at, ty)| (*at, ty.clone(), nav.expr_unfolded.get(at).cloned()))
            .collect();
        exprs.sort_by_key(|(at, _, _)| (at.file.index(), at.start, at.end));
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

    /// The names the file whose scope is current can write unqualified
    /// ([`Elaborator::use_file_scope`]; after a module is checked, its
    /// last file's), for completing a name: its namespace's own, then
    /// those its imports bring, then the defaults. Then the library's that
    /// one import would bring, each with that import (the one an unknown
    /// name's error suggests), and without a type, which would cost a
    /// printing of each. Local definitions and generated declarations are
    /// left out.
    pub fn names_in_scope(&self) -> Vec<ScopeName> {
        let g = &self.ev();
        let wanted =
            |key: &str| !self.tables.helper_keys.contains_key(key) && !is_generated_name(g, key);
        let mut out: Vec<ScopeName> = self
            .short_names_visible()
            .into_iter()
            .filter(|(_, key, ..)| wanted(key))
            .filter(|(_, _, global, _)| !matches!(global, Global::Failed))
            .map(|(name, key, global, level)| {
                self.scope_name(name, &key, global, level == crate::scope::Level::Module)
            })
            .collect();
        out.sort_by(|a, b| (!a.own, &a.name).cmp(&(!b.own, &b.name)));
        let visible: std::collections::BTreeSet<String> =
            out.iter().map(|n| n.name.clone()).collect();
        let mut importable: Vec<ScopeName> = self
            .importable_names()
            .into_iter()
            .filter(|(name, key, ..)| !visible.contains(name) && wanted(key))
            .map(|(name, key, global, path)| ScopeName {
                kind: self.global_kind(global),
                ty: None,
                own: false,
                key: crate::scope::display(&key).to_string(),
                import: Some((path, name.clone())),
                name,
            })
            .collect();
        importable.sort_by(|a, b| a.name.cmp(&b.name));
        out.extend(importable);
        out
    }

    /// `key`, written `name`, for completion.
    pub(crate) fn scope_name(
        &self,
        name: String,
        key: &str,
        global: Global,
        own: bool,
    ) -> ScopeName {
        ScopeName {
            name,
            kind: self.global_kind(global),
            ty: self.global_type(global),
            own,
            key: crate::scope::display(key).to_string(),
            import: None,
        }
    }

    fn global_kind(&self, global: Global) -> &'static str {
        match global {
            Global::Def(id) => {
                let def = self.kernel.def(id);
                if def.theorem() {
                    "theorem"
                } else if def.instance() {
                    "instance"
                } else {
                    "def"
                }
            }
            Global::Data(d) => {
                if self.tables.interfaces.contains_key(&d) {
                    "interface"
                } else if self.kernel.data(d).record() {
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
        let g = &self.ev();
        let data = g.data(d);
        let ctor = &data.ctors()[c];
        let i = ctor.fields.iter().position(|(f, _)| **f == *name)?;
        let mut names: Vec<Name> = data.params().iter().map(|(n, _)| n.clone()).collect();
        names.extend(ctor.fields[..i].iter().map(|(n, _)| n.clone()));
        Some(pretty::term(g, &names, &ctor.fields[i].1))
    }

    /// The parameters of a definition's type with their names (all of
    /// them, which [`Self::global_type`] doesn't print for the ones nothing
    /// depends on), `(low: Nat) -> [n: Nat] -> Nat`.
    fn global_signature(&self, global: Global) -> Option<String> {
        let Global::Def(id) = global else {
            return None;
        };
        let g = &self.ev();
        let mut names: Vec<Name> = Vec::new();
        let mut parts: Vec<String> = Vec::new();
        let mut ty = g.def(id).ty().clone();
        while let Term::Pi(name, icit, dom, cod) = ty.strip_loc() {
            let shown = pretty::term(g, &names, dom);
            // A bare row's divergence index isn't written
            // (docs/proposals/partial-stage-3.md §2.2).
            if name.starts_with("%div.") {
                names.push(name.clone());
                ty = (**cod).clone();
                continue;
            }
            let default = self
                .param_default_shown(id, names.len())
                .map(|d| format!(" := {d}"))
                .unwrap_or_default();
            parts.push(match icit {
                Icit::Explicit => format!("({name}: {shown}{default})"),
                _ => format!("[{name}: {shown}]"),
            });
            names.push(name.clone());
            let next = (**cod).clone();
            ty = next;
        }
        if parts.is_empty() {
            return None;
        }
        parts.push(pretty::term(g, &names, &ty));
        Some(parts.join(" -> "))
    }

    /// A definition's header after its name, as its declaration writes it
    /// (`(what: Text) (passes: Char → Bool): {Parse} Char`): the leading
    /// parameters that have names, then the rest of the type, which starts
    /// at the first parameter the declaration left unnamed (a type written
    /// `Nat → Nat`). None if no parameter is named.
    fn global_header(&self, global: Global) -> Option<String> {
        let Global::Def(id) = global else {
            return None;
        };
        let g = &self.ev();
        let mut names: Vec<Name> = Vec::new();
        let mut parts: Vec<String> = Vec::new();
        let mut ty = g.def(id).ty().clone();
        while let Term::Pi(name, icit, dom, cod) = ty.strip_loc() {
            if name.starts_with("%div.") {
                names.push(name.clone());
                ty = (**cod).clone();
                continue;
            }
            if name.starts_with('%') || &**name == "_" {
                break;
            }
            let shown = pretty::term(g, &names, dom);
            let default = self
                .param_default_shown(id, names.len())
                .map(|d| format!(" := {d}"))
                .unwrap_or_default();
            parts.push(match icit {
                Icit::Explicit => format!("({name}: {shown}{default})"),
                Icit::Auto => format!("[auto {name}: {shown}]"),
                _ => format!("[{name}: {shown}]"),
            });
            names.push(name.clone());
            let next = (**cod).clone();
            ty = next;
        }
        if parts.is_empty() {
            return None;
        }
        let result = pretty::term(g, &names, &ty);
        Some(format!("{}: {result}", parts.join(" ")))
    }

    /// The value of definition `id`'s parameter `i`'s default, if it has
    /// one: its helper's body, in the names of the parameters it takes.
    pub(crate) fn param_default_shown(&self, id: DefId, i: usize) -> Option<String> {
        let g = &self.ev();
        let table = self.tables.param_defaults.get(&id)?;
        let default = table.params.get(i)?.as_ref()?;
        let mut body: Term = (**g.def(default.helper).body()?).clone();
        let mut names: Vec<Name> = Vec::new();
        while let Term::Lam(x, _, inner) = body.strip_loc() {
            names.push(x.clone());
            body = (**inner).clone();
        }
        Some(pretty::term(g, &names, &body))
    }

    /// A definition with parameter defaults, as its header is written:
    /// `def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat`.
    fn defaulted_header(&self, id: DefId) -> Option<String> {
        let g = &self.ev();
        let def = g.def(id);
        let table = self.tables.param_defaults.get(&id)?;
        let mut names: Vec<Name> = Vec::new();
        let mut parts: Vec<String> = Vec::new();
        let mut ty = def.ty().clone();
        while names.len() < table.header {
            let Term::Pi(name, icit, dom, cod) = ty.strip_loc() else {
                return None;
            };
            if !name.starts_with("%div.") {
                let shown = pretty::term(g, &names, dom);
                parts.push(match (icit, self.param_default_shown(id, names.len())) {
                    (Icit::Explicit, Some(d)) => format!("({name}: {shown} := {d})"),
                    (Icit::Explicit, None) => format!("({name}: {shown})"),
                    _ => format!("[{name}: {shown}]"),
                });
            }
            names.push(name.clone());
            ty = (**cod).clone();
        }
        let kind = if def.theorem() { "theorem" } else { "def" };
        let short = def.name().rsplit('.').next().unwrap_or(def.name());
        Some(format!(
            "{kind} {short} {}: {}",
            parts.join(" "),
            pretty::term(g, &names, &ty)
        ))
    }

    /// A definition's type with an outermost `Not` written as `p → Void`
    /// ([`not_unfolded`]), for hover.
    fn global_not_unfolded(&self, global: Global) -> Option<String> {
        let Global::Def(id) = global else {
            return None;
        };
        let g = &self.ev();
        not_unfolded(g, &[], g.def(id).ty())
    }

    fn global_type(&self, global: Global) -> Option<String> {
        let g = &self.ev();
        match global {
            Global::Def(id) => {
                let ty = match self.defaulted_header(id) {
                    Some(header) => header,
                    // The type as elaborated, with calls as written
                    // (`Float.isValid a`): unfolded, it can run to megabytes.
                    None => pretty::term(g, &[], g.def(id).ty()),
                };
                // Checked with its bare row variables total (D1215,
                // docs/proposals/partial-stage-3.md §2.2): say why.
                Some(match self.tables.total_rows.contains_key(&id) {
                    true => format!(
                        "{ty}\n-- takes only total callbacks: its body runs a callback where \
                         partial code can't run"
                    ),
                    false => ty,
                })
            }
            Global::Data(d) => {
                let data = g.data(d);
                let mut ty = Term::Sort(data.sort());
                for (name, t) in data.indices().iter().rev() {
                    ty = Term::Pi(name.clone(), Icit::Explicit, t.clone().into(), ty.into());
                }
                for (name, t) in data.params().iter().rev() {
                    ty = Term::Pi(name.clone(), Icit::Explicit, t.clone().into(), ty.into());
                }
                Some(pretty::term(g, &[], &ty))
            }
            Global::Ctor(d, c) => {
                let data = g.data(d);
                let ctor = &data.ctors()[c];
                let (np, nf) = (data.params().len(), ctor.fields.len());
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
                for (name, t) in data.params().iter().rev() {
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
                    decreasing,
                    defaults,
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
                    self.params(name.span, ty);
                    self.signature(ty, defaults, decreasing.as_deref(), equations);
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
        for binder in params {
            for param in &binder.names {
                self.nav.params.push(ParamBinder {
                    owner: name.span,
                    name: param.text.clone(),
                    binder: param.span,
                });
            }
        }
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
                // For a shared field's accessor (`a.f`, `T.f`), found at the
                // type's declaration: the first constructor's field
                // (docs/proposals/variant-fields.md §9.3).
                for binder in &ctor.fields {
                    for field in &binder.names {
                        self.nav
                            .field_spans
                            .insert((ctor.name.span, field.text.clone()), field.span);
                        self.nav
                            .field_spans
                            .insert_absent((span, field.text.clone()), field.span);
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

    /// The parameters a header's type names, which a named argument of a
    /// call to the declaration `owner` may name.
    fn params(&mut self, owner: Span, ty: &Expr) {
        let mut ty = ty;
        loop {
            match ty {
                Expr::Pi { names, cod, .. } => {
                    for name in names {
                        self.nav.params.push(ParamBinder {
                            owner,
                            name: name.text.clone(),
                            binder: name.span,
                        });
                    }
                    ty = cod;
                }
                Expr::Arrow(_, cod) => ty = cod,
                _ => break,
            }
        }
    }

    /// A signature and its equations.
    fn signature(
        &mut self,
        ty: &Expr,
        defaults: &[Option<Expr>],
        decreasing: Option<&Expr>,
        equations: &[Decl],
    ) {
        let guesses = implicit_guesses(ty);
        let mut work: Vec<Work> = guesses.iter().map(|n| Work::Bind(n)).collect();
        work.push(Work::Expr(ty));
        work.extend(Self::header_work(ty, defaults, decreasing));
        let binders = body_binders(ty, equations);
        for eq in equations {
            let Decl::Equation {
                patterns,
                guard,
                rhs,
                ..
            } = eq
            else {
                continue;
            };
            work.extend(binders.iter().map(|n| Work::Bind(n)));
            let mut vars = Vec::new();
            for p in patterns {
                pattern_binders(p, &mut vars);
                work.push(Work::Pattern(p));
            }
            if let Some(guard) = guard {
                work.push(Work::Expr(&guard.cond));
                if let Some(h) = &guard.binder {
                    work.push(Work::Bind(h));
                }
            }
            work.extend(rhs.iter().map(Work::Expr));
            if let Some(h) = guard.as_ref().and_then(|g| g.binder.as_ref()) {
                work.push(Work::Unbind(&h.text));
            }
            work.extend(vars.into_iter().map(Work::Unbind));
            work.extend(binders.iter().map(|n| Work::Unbind(&n.text)));
        }
        work.extend(guesses.iter().map(|n| Work::Unbind(&n.text)));
        self.run(work);
    }

    /// The walk of a header's parameter defaults, each with the parameters
    /// before it bound, and of its `decreasing` measure, with all of them.
    fn header_work<'a>(
        ty: &'a Expr,
        defaults: &'a [Option<Expr>],
        decreasing: Option<&'a Expr>,
    ) -> Vec<Work<'a>> {
        let mut names: Vec<Option<&ast::Name>> = Vec::new();
        let mut cursor = ty;
        loop {
            match cursor {
                Expr::Pi { names: ns, cod, .. } => {
                    names.extend(ns.iter().map(Some));
                    cursor = cod;
                }
                Expr::Arrow(_, cod) => {
                    names.push(None);
                    cursor = cod;
                }
                _ => break,
            }
        }
        let mut work = Vec::new();
        for (k, default) in defaults.iter().enumerate() {
            let Some(default) = default else { continue };
            let before: Vec<&ast::Name> = names[..k.min(names.len())]
                .iter()
                .flatten()
                .copied()
                .collect();
            work.extend(before.iter().map(|n| Work::Bind(n)));
            work.push(Work::Expr(default));
            work.extend(before.iter().rev().map(|n| Work::Unbind(&n.text)));
        }
        if let Some(measure) = decreasing {
            let params = names.iter().flatten().copied().collect::<Vec<_>>();
            work.extend(params.iter().map(|n| Work::Bind(n)));
            work.push(Work::Expr(measure));
            work.extend(params.iter().rev().map(|n| Work::Unbind(&n.text)));
        }
        work
    }

    fn local_def<'a>(def: &'a ast::LocalDef) -> Vec<Work<'a>> {
        let Decl::Signature {
            ty,
            defaults,
            decreasing,
            ..
        } = &def.signature
        else {
            return Vec::new();
        };
        let mut work = vec![Work::Expr(ty)];
        work.extend(Self::header_work(ty, defaults, decreasing.as_deref()));
        let binders = body_binders(ty, &def.equations);
        for eq in &def.equations {
            let Decl::Equation {
                patterns,
                guard,
                rhs,
                ..
            } = eq
            else {
                continue;
            };
            work.extend(binders.iter().map(|n| Work::Bind(n)));
            let mut vars = Vec::new();
            for p in patterns {
                pattern_binders(p, &mut vars);
                work.push(Work::Pattern(p));
            }
            if let Some(guard) = guard {
                work.push(Work::Expr(&guard.cond));
                if let Some(h) = &guard.binder {
                    work.push(Work::Bind(h));
                }
            }
            work.extend(rhs.iter().map(Work::Expr));
            if let Some(h) = guard.as_ref().and_then(|g| g.binder.as_ref()) {
                work.push(Work::Unbind(&h.text));
            }
            work.extend(vars.into_iter().map(Work::Unbind));
            work.extend(binders.iter().map(|n| Work::Unbind(&n.text)));
        }
        work
    }

    /// Runs steps in order, with a work list (expressions nest more deeply
    /// than recursion could follow).
    fn run(&mut self, work: Vec<Work<'_>>) {
        let mut bound: HashMap<&str, Vec<Span>> = HashMap::default();
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
                        Pattern::Ctor(ctor, args, _) => {
                            for arg in args {
                                if let Pattern::Named(name, ..) = arg {
                                    self.nav.named.push(NamedUse {
                                        head: name_spans(ctor),
                                        name: name.text.clone(),
                                        span: name.span,
                                    });
                                }
                            }
                            then(&mut stack, args.iter().map(Work::Pattern).collect());
                        }
                        Pattern::Tuple(a, b, _) | Pattern::Cons(a, b, _) => {
                            then(&mut stack, vec![Work::Pattern(a), Work::Pattern(b)]);
                        }
                        Pattern::Named(_, p, _) => then(&mut stack, vec![Work::Pattern(p)]),
                        Pattern::Or(alternatives, _) => {
                            then(&mut stack, alternatives.iter().map(Work::Pattern).collect());
                        }
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
                | Expr::Float(..)
                | Expr::Str(..)
                | Expr::Include(..)
                | Expr::Char(..)
                | Expr::Type(..)
                | Expr::Prop(_)
                | Expr::Hole(_)
                | Expr::Goal(_)
                | Expr::Unit(_) => {}
                Expr::App(a, b) => {
                    if let Expr::NamedArg(name, ..) = &**b
                        && let Some(head) = head_spans(a)
                    {
                        self.nav.named.push(NamedUse {
                            head,
                            name: name.text.clone(),
                            span: name.span,
                        });
                    }
                    then(&mut stack, vec![Work::Expr(a), Work::Expr(b)]);
                }
                Expr::Arrow(a, b) | Expr::Binary(_, a, b) | Expr::Pipe(a, b) | Expr::Seq(a, b) => {
                    then(&mut stack, vec![Work::Expr(a), Work::Expr(b)])
                }
                Expr::Neg(a, _, _) | Expr::Bracketed(a, _) | Expr::Interpolated(a, _) => {
                    stack.push(Work::Expr(a))
                }
                Expr::Lam(names, body, _) => {
                    let mut steps: Vec<Work> = names.iter().map(Work::Bind).collect();
                    steps.push(Work::Expr(body));
                    steps.extend(names.iter().map(|n| Work::Unbind(&n.text)));
                    then(&mut stack, steps);
                }
                Expr::TypedLam(name, _, ty, body, _) => then(
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
                Expr::NamedArg(_, value, _, _) => stack.push(Work::Expr(value)),
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
                Expr::Spread(e, _) => then(&mut stack, vec![Work::Expr(e)]),
                Expr::Record { base, fields, .. } => {
                    let mut steps: Vec<Work> = base.iter().map(|b| Work::Expr(b)).collect();
                    steps.extend(fields.iter().map(|(_, e)| Work::Expr(e)));
                    then(&mut stack, steps);
                }
                Expr::CtorFields { ctor, fields, .. } => {
                    stack.push(Work::Use(ctor));
                    then(
                        &mut stack,
                        fields.iter().map(|(_, e)| Work::Expr(e)).collect(),
                    );
                }
                Expr::Field(e, _) => stack.push(Work::Expr(e)),
                Expr::Omega { facts, .. } | Expr::Ring { facts, .. } => {
                    then(&mut stack, facts.iter().map(Work::Expr).collect())
                }
                Expr::Cases { body, .. } => {
                    then(&mut stack, body.iter().map(|b| Work::Expr(b)).collect())
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
                        if let Some(guard) = &alt.guard {
                            steps.push(Work::Expr(&guard.cond));
                            if let Some(h) = &guard.binder {
                                steps.push(Work::Bind(h));
                                vars.push(&h.text);
                            }
                        }
                        steps.extend(alt.body.as_ref().map(Work::Expr));
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
                Expr::Induct { call, alts, .. } => {
                    let mut steps = vec![Work::Expr(call)];
                    for alt in alts {
                        steps.extend(alt.binders.iter().map(Work::Bind));
                        steps.push(Work::Expr(&alt.body));
                        steps.extend(alt.binders.iter().map(|b| Work::Unbind(&b.text)));
                    }
                    then(&mut stack, steps);
                }
                Expr::Handle { body, clauses, .. }
                | Expr::Reify {
                    thunk: body,
                    clauses,
                    ..
                } => {
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

/// Where a reference to the head of a call may be noted: the whole of a
/// written name, and its last component.
fn name_spans(name: &ast::Name) -> [Span; 2] {
    let last = name.text.rsplit('.').next().unwrap_or_default().len() as u32;
    let tail = if name.span.end - name.span.start == name.text.len() as u32 {
        Span::new(name.span.file, name.span.end - last, name.span.end)
    } else {
        name.span
    };
    [name.span, tail]
}

/// [`name_spans`] of the head of a call, if it is a name.
fn head_spans(mut head: &Expr) -> Option<[Span; 2]> {
    loop {
        match head {
            Expr::App(f, _) => head = f,
            Expr::Var(name) => return Some(name_spans(name)),
            Expr::Field(_, name) => return Some([name.span, name.span]),
            _ => return None,
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
        Pattern::Or(alternatives, _) => alternatives.iter().for_each(|p| pattern_binders(p, out)),
        Pattern::Wildcard(_)
        | Pattern::Absurd(_)
        | Pattern::Num(..)
        | Pattern::NegNum(..)
        | Pattern::Char(..)
        | Pattern::Nil(_) => {}
    }
}

/// The names a signature uses without binding them, that may be bound
/// implicitly (`k` in `List k`, `o` in `Map k v [ord := o]`): lowercase and
/// unqualified, each at its first use. Whether a name is one is for the
/// elaborator to say, which notes a reference where it isn't (a
/// declaration's name).
fn implicit_guesses(ty: &Expr) -> Vec<&ast::Name> {
    let mut out: Vec<&ast::Name> = Vec::new();
    for r in crate::module::free_names_of(ty) {
        if let crate::module::Ref::Name(n) = r
            && !n.text.contains('.')
            && n.text.starts_with(|c: char| c.is_lowercase())
            && !out.iter().any(|o| o.text == n.text)
        {
            out.push(n);
        }
    }
    out
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

/// A type with an outermost `Not` written as `p → Void` under its
/// parameters: `(n: Nat) → n + 1 ≠ 0` gives
/// `(n: Nat) → n + 1 = 0 → Void`. None unless the type after its parameters
/// is `Not p`, which is why applying a proof of it gives a `Void`.
fn not_unfolded(g: &Ev, names: &[Name], ty: &Term) -> Option<String> {
    let mut names = names.to_vec();
    let mut parts: Vec<String> = Vec::new();
    let mut ty = ty.clone();
    while let Term::Pi(name, icit, dom, cod) = ty.strip_loc() {
        if !name.starts_with('%') {
            let shown = pretty::term(g, &names, dom);
            parts.push(match icit {
                Icit::Explicit => format!("({name}: {shown})"),
                Icit::Auto => format!("[auto {name}: {shown}]"),
                _ => format!("[{name}: {shown}]"),
            });
        }
        names.push(name.clone());
        ty = (**cod).clone();
    }
    let (head, args) = ty.spine();
    let Term::Def(not) = head.strip_loc() else {
        return None;
    };
    if !g.env.registry().is_def(Builtin::Not, *not) {
        return None;
    }
    let [prop] = args.as_slice() else {
        return None;
    };
    let void = g.env.registry().data(Builtin::Void)?;
    let unfolded = Term::Pi(
        "_".into(),
        Icit::Explicit,
        (*prop).clone().into(),
        Term::data(void, Vec::new()).into(),
    );
    parts.push(pretty::term_not_unfolded(g, &names, &unfolded));
    Some(parts.join(" → "))
}

/// [`not_unfolded`] for a local's or expression's type, a value.
fn value_not_unfolded(g: &Ev, names: &[Name], value: &Value) -> Option<String> {
    let ty = stitchwort_core::value::quote_shown(g, names.len(), value).ok()?;
    not_unfolded(g, names, &ty)
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use stitchwort_core::{Limits, Sort};
    use stitchwort_syntax::SourceMap;

    use super::*;

    /// The noted types are printed after a declaration's operation has
    /// ended too, where nothing limited the printer: printing a type nested
    /// deeply enough overflowed the stack, which in the language server's
    /// worker is the engine's stack, not recoverable (SW-1430). Within the
    /// session's limits, its inner parts are shown as `…`.
    #[test]
    fn a_noted_type_is_printed_within_the_limits() {
        let mut e = Elaborator::new();
        e.enable_navigation();
        e.options.limits = Limits {
            stack: 64 * 1024,
            ..Limits::default()
        };
        // `((Type = Type) = Type) = …`, nested far deeper than a test
        // thread's stack could print.
        let mut ty = Value::Sort(Sort::Type(0));
        for _ in 0..100_000 {
            let type1 = Rc::new(Value::Sort(Sort::Type(1)));
            ty = Value::Eq(
                type1.into(),
                Rc::new(ty).into(),
                Rc::new(Value::Sort(Sort::Type(0))).into(),
            );
        }
        // Dropping it would recurse as deeply: the test keeps it.
        let kept = ty.clone();
        let mut sources = SourceMap::new();
        let at = Span::point(sources.add("test", ""), 0);
        let nav = e.present.nav.as_ref().expect("navigation on");
        nav.borrow_mut().pending.push((at, ty, Vec::new(), true));
        e.flush_navigation();
        let nav = e.present.nav.as_ref().expect("navigation on").borrow();
        let shown = nav.expr_types.get(&at).expect("the type printed");
        assert!(
            shown.contains('…') && shown.chars().count() < 300,
            "{shown}"
        );
        std::mem::forget(kept);
    }
}
