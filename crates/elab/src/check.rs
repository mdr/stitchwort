//! The elaborator's type checker: checks surface expressions while turning them
//! into core terms, inserting implicit arguments as metavariables and solving
//! them by unification. Its output is re-checked by the kernel.

use std::rc::Rc;

use crate::kernel;
use stitchwort_core::chars::{self as compact, Chars};
use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Closure, Head, apply, eval, force, quote, unused};
use stitchwort_core::{DataId, Globals, Icit, MAX_LEVEL, Name, Sort, Term, Value, pretty};
use stitchwort_syntax::ast::{BinOp, Bracket, Expr, Mode, Name as AstName, NegForm, SECTION};
use stitchwort_syntax::{Diagnostic, Span};

use crate::unify::unify;
use crate::{Elaborator, Global, effects, records, scope};

pub type Result<T> = std::result::Result<T, Diagnostic>;

/// The name the elaborator's depth guards report. Each function the
/// elaborator recurses through over syntax or terms (`infer`, `check`,
/// `may_perform`, …) checks it has stack left first
/// (docs/proposals/stack-safe-evaluation.md).
pub(crate) const PASS: &str = "elaborator";

/// How many elements of a list literal are written as one `Cons` chain when
/// it's too long to be one; then it's several chains joined by `append`s
/// (SW-62).
const LITERAL_CHUNK: usize = 64;

/// The stack a `Cons` chain costs per element, rounded up from what was
/// measured on 2026-10-22: about 1,850 bytes of the limit's stack (a limit of
/// 1.2 MB took 640 elements, 50 MB took 27,136, checking and running `main`).
/// A literal whose chain would use more than the limit's stack is chunked.
const LITERAL_BYTES: usize = 2400;

pub struct Ctx<'e> {
    pub e: &'e Elaborator,
    /// What each variable evaluates to (inside a case branch, the matched
    /// variable is the constructor value).
    pub env: Vec<Value>,
    pub types: Vec<Value>,
    /// Display names, for error messages.
    pub names: Vec<Name>,
    /// Each variable's type as written, where known: a term in the context
    /// of the variables before it. Dot notation finds a namespace from it
    /// (docs/proposals/namespaces.md §4.8), since `types` may have unfolded
    /// a nickname like `Price = Nat`.
    pub written: Vec<Option<crate::dot::Written>>,
    /// Names that can be referred to, and the level each refers to.
    scope: Vec<(String, usize)>,
    /// How each variable was bound: an implicit or `auto` parameter keeps
    /// its kind when a local definition captures it
    /// (docs/proposals/syntax-conveniences.md §2.1).
    pub kinds: Vec<Icit>,
    /// Local definitions in scope (`local.rs`), each shadowing the names
    /// bound before it and shadowed by those bound after.
    locals: Vec<LocalName>,
    /// For each variable bound by a transparent `let` ([`Ctx::define`]), its
    /// type and value as written in the core term, so a lifted helper can
    /// re-create the `let` (docs/proposals/let.md §A.4).
    pub lets: Vec<Option<Rc<LetDef>>>,
    /// The type of the definition body being checked, as written, with the
    /// number of variables in scope where it makes sense. A failed `rfl`
    /// shows the sides of an `=` as they were written, if this is the type.
    pub goal: Option<(usize, Rc<Term>)>,
    /// Set by `calc` just before it checks a step's proof that is a
    /// `rewrite`: the step's proposition as it was built (a term in the
    /// current context), which `rewrite` shows in its messages. It searches
    /// the goal as it computes, not this (docs/proposals/calc-rewrite.md,
    /// "As built"). Taken by the first `rewrite` that looks.
    pub(crate) written_goal: Option<Term>,
    /// The context's variables in the order a helper lifted here takes its
    /// captures: the header's parameters, then the pattern variables of the
    /// arm being checked as written, left to right, then the rest by level
    /// (D228; set by `check_tree` at each leaf). A level not listed comes
    /// after the listed ones.
    pub(crate) order: Vec<usize>,
    /// The first level the current case tree binds (`check_tree`).
    pub(crate) tree_start: usize,
    /// The expression scrutinees of the generalised `match`es whose
    /// alternatives are being checked: the variables in scope at the `match`,
    /// the scrutinee as types hold it, where it is written, and the level of
    /// the variable standing for it (in a branch, the branch's constructor).
    /// A mismatch that still contains one gets a hint (D230).
    pub(crate) scrutinees: Vec<(usize, Term, Span, usize)>,
    /// How to show the goal of a `?` that is a `match reify`'s `return`
    /// clause (`reify.rs`); display only.
    pub(crate) reify_display: Option<ReifyDisplay>,
    /// The `cases` whose cases are being checked (`cases.rs`): its
    /// alternatives' bodies go on splitting.
    pub(crate) cases: Option<Rc<crate::cases::Run>>,
    pub span: Span,
}

/// What `goals::hole` needs to show a `match reify` `return` clause's goal
/// in terms of what was written, instead of the handlers unfolded.
#[derive(Clone)]
pub(crate) struct ReifyDisplay {
    /// The `?` that is the clause's whole body.
    pub hole: Span,
    /// The `match`'s goal, calls kept folded, in `base` variables.
    pub folded: Term,
    pub base: usize,
    /// The computation being taken apart, as the goal holds it.
    pub computation: Term,
    /// The thunk, when it is a variable (a level below `base`).
    pub thunk: Option<usize>,
    /// The clause's variable: what the computation returns.
    pub result: String,
    /// `Comp`, whose `Done` is what the clause says the computation is.
    pub comp: stitchwort_core::DataId,
}

/// A `let`'s type and value, as terms in the context of the variables
/// before it.
pub(crate) struct LetDef {
    pub ty: Term,
    pub value: Term,
}

/// A local definition's name in scope: what it means, as a term in the
/// context of the first `base` variables, and its type.
#[derive(Clone)]
pub(crate) struct LocalName {
    pub name: String,
    /// `scope.len()` when it was bound.
    scope: usize,
    pub term: Term,
    pub base: usize,
    pub ty: Value,
}

/// A position to return to with [`Ctx::reset`].
#[derive(Clone, Copy)]
pub struct Mark {
    level: usize,
    scope: usize,
    locals: usize,
}

impl<'e> Ctx<'e> {
    pub fn new(e: &'e Elaborator, span: Span) -> Self {
        Ctx {
            e,
            env: Vec::new(),
            types: Vec::new(),
            names: Vec::new(),
            written: Vec::new(),
            scope: Vec::new(),
            kinds: Vec::new(),
            locals: Vec::new(),
            lets: Vec::new(),
            goal: None,
            written_goal: None,
            order: Vec::new(),
            tree_start: 0,
            scrutinees: Vec::new(),
            reify_display: None,
            cases: None,
            span,
        }
    }

    /// A context with the given variables in scope (none of them by name).
    pub fn from_parts(
        e: &'e Elaborator,
        env: Vec<Value>,
        types: Vec<Value>,
        names: Vec<Name>,
        span: Span,
    ) -> Self {
        let written = vec![None; env.len()];
        let kinds = vec![Icit::Explicit; env.len()];
        let lets = vec![None; env.len()];
        Ctx {
            e,
            env,
            types,
            names,
            written,
            scope: Vec::new(),
            kinds,
            locals: Vec::new(),
            lets,
            goal: None,
            written_goal: None,
            order: Vec::new(),
            tree_start: 0,
            scrutinees: Vec::new(),
            reify_display: None,
            cases: None,
            span,
        }
    }

    pub fn g(&self) -> &'e Globals {
        &self.e.globals
    }

    pub fn level(&self) -> usize {
        self.env.len()
    }

    pub fn mark(&self) -> Mark {
        Mark {
            level: self.level(),
            scope: self.scope.len(),
            locals: self.locals.len(),
        }
    }

    pub fn reset(&mut self, mark: Mark) {
        self.env.truncate(mark.level);
        self.types.truncate(mark.level);
        self.names.truncate(mark.level);
        self.written.truncate(mark.level);
        self.kinds.truncate(mark.level);
        self.lets.truncate(mark.level);
        self.scope.truncate(mark.scope);
        self.locals.truncate(mark.locals);
    }

    /// Binds a variable that can be referred to by `name`.
    pub fn bind(&mut self, name: &str, ty: Value) {
        self.scope.push((name.to_string(), self.level()));
        self.bind_hidden(name.into(), ty);
    }

    /// Binds a variable that can't be referred to by name.
    pub fn bind_hidden(&mut self, name: Name, ty: Value) {
        self.env.push(Value::var(self.level()));
        self.types.push(ty);
        self.names.push(name);
        self.written.push(None);
        self.kinds.push(Icit::Explicit);
        self.lets.push(None);
    }

    /// Binds `name` (or, with `None`, a variable that can't be referred to,
    /// shown as `shown`) as a transparent local definition `value : ty`,
    /// where `ty_term` and `value` are terms in the current context. The
    /// variable takes a slot, but what it evaluates to there is `value`'s
    /// value, never a variable of its own (docs/proposals/let.md §6.1 rule
    /// 1). So nothing computed under it mentions it, and `fresh_meta`,
    /// lifting and matching, which look for slots that are their own
    /// variable, leave it out of metavariable spines and captures.
    ///
    /// A value that's cheap to compute (`unify::cheaply`: most are, being
    /// stuck on the context's variables) is computed now, once. Otherwise,
    /// as in the kernel, it's computed only when something needs it (a type
    /// that mentions the variable is compared, printed or read back), so a
    /// `let` of a large value that no type needs, like a long list in
    /// `main`, costs nothing to check (docs/proposals/let.md §A.3, "Cost at
    /// check time"). Such a *deferred* slot holds a solved metavariable
    /// applied to the context, `?d _ x₀ … xₙ`, whose solution is
    /// `_ x₀ … xₙ => value`: forcing it, as everything that looks at a value
    /// does, computes the value, again each time. It's not the slot's own
    /// variable, so the placeholder can't be taken for one (a pending slot
    /// has its own marker, stage 2's warning), and since the context is in
    /// its spine, a case split's refinement of a variable reaches the value.
    pub(crate) fn define(
        &mut self,
        name: Option<&str>,
        shown: Name,
        ty: Value,
        ty_term: Term,
        value: Term,
    ) -> Result<()> {
        let g = self.g();
        let v = match crate::unify::cheaply(g, || eval(g, &self.env, &value)) {
            Some(v) => v,
            None => self.deferred(&value)?,
        };
        if let Some(name) = name {
            self.scope.push((name.to_string(), self.level()));
        }
        self.env.push(v);
        self.types.push(ty);
        self.names.push(shown);
        self.written.push(None);
        self.kinds.push(Icit::Explicit);
        self.lets.push(Some(Rc::new(LetDef { ty: ty_term, value })));
        Ok(())
    }

    /// `value`, a term in the context, computed when it's forced: see
    /// [`Ctx::define`].
    fn deferred(&self, value: &Term) -> Result<Value> {
        let g = self.g();
        let mut solution = value.clone();
        for x in self.names.iter().rev() {
            solution = Term::Lam(x.clone(), Icit::Explicit, Rc::new(solution));
        }
        let solution = Term::Lam("_".into(), Icit::Explicit, Rc::new(solution));
        let m = g.new_meta(self.span);
        g.solve_meta(m, eval(g, &[], &solution)?);
        let spine = std::iter::once(Value::Sort(Sort::Prop))
            .chain(self.env.iter().cloned())
            .map(|v| stitchwort_core::value::Elim::App(v, Icit::Explicit))
            .collect();
        Ok(Value::Neutral(Head::Meta(m), spine))
    }

    /// Records that the latest variable is an implicit or `auto` parameter.
    pub(crate) fn set_kind(&mut self, icit: Icit) {
        if let Some(last) = self.kinds.last_mut() {
            *last = icit;
        }
    }

    /// Makes `name` refer to a local definition: `term`, in the context of
    /// the variables now in scope, of type `ty`.
    pub(crate) fn bind_local(&mut self, name: &str, term: Term, ty: Value) {
        self.locals.push(LocalName {
            name: name.to_string(),
            scope: self.scope.len(),
            term,
            base: self.level(),
            ty,
        });
    }

    /// The local definition `name` refers to, if it does: one bound after
    /// any variable of that name. Its term (in the current context) and type.
    pub(crate) fn local(&self, name: &str) -> Result<Option<(Term, Value)>> {
        let Some(local) = self.local_entry(name) else {
            return Ok(self.decreasing_call(name));
        };
        let term = local.term.shift(self.g(), self.level() - local.base, 0)?;
        Ok(Some((term, local.ty.clone())))
    }

    /// A use of `name`, resolved by `local`: a local definition is noted as a
    /// local, but the recursive call of a definition with `decreasing` (stood
    /// in for by `%rec`) is a use of the global definition.
    pub(crate) fn note_local_use(&self, name: &AstName, ty: &Value) {
        if self.local_entry(&name.text).is_some() {
            self.e.note_local(self, name, ty);
        } else {
            self.e.note_name(name);
        }
    }

    /// Every local definition that can be referred to: its name, its term in
    /// the current context, and its type (for `omega`, which reads them as
    /// facts).
    pub(crate) fn visible_locals(&self) -> Result<Vec<(String, Term, Value)>> {
        let mut out = Vec::new();
        for local in &self.locals {
            if self
                .local_entry(&local.name)
                .is_some_and(|l| std::ptr::eq(l, local))
            {
                let term = local.term.shift(self.g(), self.level() - local.base, 0)?;
                out.push((local.name.clone(), term, local.ty.clone()));
            }
        }
        Ok(out)
    }

    /// The name `level` can be referred to by, if any.
    pub(crate) fn name_of_level(&self, level: usize) -> Option<&str> {
        self.scope
            .iter()
            .rev()
            .find(|(n, l)| *l == level && self.lookup(n) == Some(level))
            .map(|(n, _)| n.as_str())
    }

    /// Whether a local definition called `name` is in scope.
    pub(crate) fn has_local(&self, name: &str) -> bool {
        self.local_entry(name).is_some()
    }

    fn local_entry(&self, name: &str) -> Option<&LocalName> {
        let local = self.locals.iter().rev().find(|l| l.name == name)?;
        let shadowed = self.scope[local.scope..].iter().any(|(n, _)| n == name);
        (!shadowed).then_some(local)
    }

    /// Every name a variable or local definition in scope can be referred to by.
    pub(crate) fn scope_names(&self) -> Vec<String> {
        self.scope
            .iter()
            .map(|(n, _)| n.clone())
            .chain(self.locals.iter().map(|l| l.name.clone()))
            .collect()
    }

    /// Records the type the latest variable was declared with, as written: a
    /// term in the context of the variables before it.
    pub(crate) fn set_written(&mut self, ty: crate::dot::Written) {
        if let Some(last) = self.written.last_mut() {
            *last = Some(ty);
        }
    }

    /// Makes `name` refer to an existing variable.
    pub fn alias(&mut self, name: &str, level: usize) {
        self.scope.push((name.to_string(), level));
    }

    /// Makes every name that now refers to the variable at `old` refer to
    /// the one at `new` instead (a generalised `match`'s copies).
    pub(crate) fn rebind(&mut self, old: usize, new: usize) {
        let names: Vec<String> = self
            .scope
            .iter()
            .filter(|(n, level)| *level == old && self.lookup(n) == Some(old))
            .map(|(n, _)| n.clone())
            .collect();
        for n in names {
            self.scope.push((n, new));
        }
    }

    /// The variable `name` refers to, unless it's a local definition bound
    /// after it ([`Ctx::local`]).
    pub(crate) fn lookup(&self, name: &str) -> Option<usize> {
        let (position, level) = self
            .scope
            .iter()
            .enumerate()
            .rev()
            .find(|(_, (n, _))| n == name)
            .map(|(i, (_, level))| (i, *level))?;
        let shadowed = self
            .locals
            .iter()
            .any(|l| l.name == name && l.scope > position);
        (!shadowed).then_some(level)
    }

    pub fn eval(&self, term: &Term) -> Result<Value> {
        Ok(eval(self.g(), &self.env, term)?)
    }

    pub fn quote(&self, value: &Value) -> Result<Term> {
        Ok(quote(self.g(), self.level(), value)?)
    }

    /// [`Ctx::quote`] with calls written as calls, not their unfoldings
    /// (`value::quote_folded`): for terms the elaboration produces, such as
    /// annotations and helper types.
    pub fn quote_folded(&self, value: &Value) -> Result<Term> {
        Ok(stitchwort_core::value::quote_folded(
            self.g(),
            self.level(),
            value,
        )?)
    }

    /// `Ok(false)` if `a` and `b` can't be made equal; an error if it ran out
    /// of resources finding out.
    pub fn unify(&self, a: &Value, b: &Value) -> Result<bool> {
        Ok(unify(self.g(), self.level(), a, b)?)
    }

    /// Whether `a` and `b` are equal by computation, solving nothing, with
    /// an unknown solved since either was computed taken as its solution.
    /// The kernel's conversion (`value::conv`) compares unknowns by their
    /// numbers: to it, `Box ?a` with `?a` solved as `Nat` since isn't
    /// `Box Nat` (SW-862). So where it says they differ and something has
    /// been solved, both are computed again (`interfaces::refresh`) and
    /// compared once more.
    pub(crate) fn conv_now(&self, a: &Value, b: &Value) -> Result<bool> {
        let g = self.g();
        if stitchwort_core::value::conv(g, self.level(), a, b)? {
            return Ok(true);
        }
        if g.meta_trail.borrow().is_empty() {
            return Ok(false);
        }
        let a = crate::interfaces::refresh(self, a)?;
        let b = crate::interfaces::refresh(self, b)?;
        Ok(stitchwort_core::value::conv(g, self.level(), &a, &b)?)
    }

    pub fn show(&self, value: &Value) -> String {
        pretty::value_for_message_in(self.g(), self.e, &self.names, value)
    }

    /// [`Ctx::show`] for one side of an equation written `a = b`.
    pub fn show_side(&self, value: &Value) -> String {
        pretty::side_for_message_in(self.g(), self.e, &self.names, value)
    }

    /// [`Ctx::show`], but with calls unfolded: what `value` computes to,
    /// for a message that says so.
    pub fn show_unfolded(&self, value: &Value) -> String {
        match stitchwort_core::value::quote_unfolded_shown(self.g(), self.level(), value) {
            Ok(term) => pretty::term_for_message_in(self.g(), self.e, &self.names, &term),
            Err(_) => "…".into(),
        }
    }

    /// `d` with the "is opaque" notes (docs/proposals/opaque-definitions.md
    /// §6.10) for the opaque definitions left folded in `values`, the sides
    /// of a failed comparison. Error path only.
    pub fn with_opaque_notes(&self, d: Diagnostic, values: &[&Value]) -> Diagnostic {
        let g = self.g();
        if !g.defs.iter().any(|def| def.opaque) {
            return d;
        }
        let terms: Vec<Term> = values
            .iter()
            .filter_map(|v| quote(g, self.level(), v).ok())
            .collect();
        let ids = crate::opaque::declined_in(g, &terms);
        crate::opaque::opaque_notes(self.e, &ids)
            .into_iter()
            .fold(d, Diagnostic::with_note)
    }

    /// `d` with a note for each hypothesis `h: e = C` (`C` a constructor)
    /// whose `e` occurs inside a function in `values`, as they compute
    /// (SW-882): `rfl` and `cases` compute and split, but don't rewrite with
    /// `h`, so `anyRemoved (ys => ok x && …) rest` keeps its `ok x` though
    /// `step: ok x = True` is in scope. `rewrite h` reaches it, since `e`
    /// can't mention the function's parameter. If `e` is a `match`'s
    /// scrutinee, the occurrence came in after the `match` refined the goal
    /// (from a lemma's statement, or a term written in the branch). Error
    /// path only.
    pub(crate) fn with_unused_equation_notes(
        &self,
        mut d: Diagnostic,
        values: &[&Value],
    ) -> Diagnostic {
        let g = self.g();
        let level = self.level();
        let hay: Vec<Term> = values
            .iter()
            .filter_map(|v| quote(g, level, v).ok())
            .collect();
        if hay.is_empty() {
            return d;
        }
        for l in (0..level).rev() {
            let Some(name) = self.name_of_level(l) else {
                continue;
            };
            let Ok(Value::Eq(_, lhs, rhs)) = force(g, self.types[l].clone()) else {
                continue;
            };
            if !matches!(
                force(g, (*rhs).clone()),
                Ok(Value::Ctor(..) | Value::Nat(_))
            ) {
                continue;
            }
            let Ok(needle) = quote(g, level, &lhs) else {
                continue;
            };
            if matches!(needle.strip_loc(), Term::Ctor(..) | Term::Nat(_)) {
                continue;
            }
            let under_binder = |t: &Term| {
                t.subterms().any(|(sub, under)| {
                    under > 0 && crate::matching::same_shifted(&needle, sub, under, 0)
                })
            };
            if !hay.iter().any(under_binder) {
                continue;
            }
            let shown = pretty::term_for_message_in(g, self.e, &self.names, &needle);
            let ty = self.show(&self.types[l]);
            let matched = self.scrutinees.iter().any(|(base, s, _, _)| {
                s.shift(g, level - base, 0)
                    .is_ok_and(|s| crate::matching::same(&s, &needle))
            });
            let why = if matched {
                format!(
                    " This `{shown}` came in after the `match` on it (from a lemma's statement \
                     or a term written in the branch), so the `match` didn't replace it."
                )
            } else {
                String::new()
            };
            d = d.with_note(format!(
                "`{shown}` is inside a function here, where `{name}: {ty}` isn't used: `rfl` \
                 and `cases` compute, but don't rewrite with a hypothesis.{why} `rewrite \
                 {name} in …` does, as `{shown}` doesn't mention the function's parameter"
            ));
        }
        d
    }

    /// [`Ctx::show`], with the arguments the compiler fills in.
    pub fn show_hidden(&self, value: &Value) -> String {
        pretty::value_for_message_hidden_in(self.g(), self.e, &self.names, value)
    }

    /// Whether `a` and `b` differ only in arguments the compiler fills in,
    /// as shown (calls folded) or as computed. Error path only.
    pub fn differ_only_in_hidden(&self, a: &Value, b: &Value) -> bool {
        let g = self.g();
        let level = self.level();
        let folded = |v| stitchwort_core::value::quote_shown(g, level, v).ok();
        let normal = |v| quote(g, level, v).ok();
        [(folded(a), folded(b)), (normal(a), normal(b))]
            .iter()
            .any(|pair| match pair {
                (Some(x), Some(y)) => pretty::differ_only_in_hidden(g, x, y),
                _ => false,
            })
    }

    /// Where what `a` and `b` compute to first differ, as a note. Error
    /// path only.
    pub fn first_difference_note(&self, a: &Value, b: &Value) -> Option<String> {
        let g = self.g();
        let level = self.level();
        let shown = |v| stitchwort_core::value::quote_unfolded_shown(g, level, v).ok();
        let (x, y) = (shown(a)?, shown(b)?);
        let found = pretty::first_difference_in(g, self.e, &self.names, &x, &y)?;
        let within = found
            .within
            .map(|call| format!(", in `{call}`"))
            .unwrap_or_default();
        Some(format!(
            "they first differ at `{}` against `{}`{within}",
            found.left, found.right
        ))
    }

    /// `d` with a note saying the sides are different updates, for two
    /// sides that print alike but whose values, as shown or computed, call
    /// two different helpers of updates (each prints as `{ x | f = s }`).
    /// Error path only.
    pub fn with_alike_updates_note(&self, d: Diagnostic, values: &[&Value]) -> Diagnostic {
        let g = self.g();
        let level = self.level();
        let mut helpers: Vec<stitchwort_core::DefId> = Vec::new();
        for value in values {
            let terms = [
                stitchwort_core::value::quote_shown(g, level, value),
                quote(g, level, value),
            ];
            for term in terms.iter().flatten() {
                for (t, _) in term.subterms() {
                    if let Term::Def(id) = t
                        && g.def(*id).update_shown.is_some()
                        && !helpers.contains(id)
                    {
                        helpers.push(*id);
                    }
                }
            }
        }
        if helpers.len() < 2 {
            return d;
        }
        d.with_note(
            "these are different updates that print alike: each `{ x | f = s }` is made into a \
             hidden function of its own, and two are equal only when they replace the same \
             fields with the same values and neither calls the definition it's written in \
             (here they may differ in a part shown as `…`, or one may be in a recursive \
             definition); to prove something about both, name the update as a `def` and use \
             it in both places",
        )
    }

    pub fn error(
        &self,
        code: &'static str,
        message: impl Into<String>,
        label: impl Into<String>,
    ) -> Diagnostic {
        Diagnostic::error(code, message).with_label(self.span, label)
    }

    /// A new metavariable, applied to every variable in scope (except those a
    /// case branch has replaced by a constructor), so its solution may depend
    /// on them.
    pub fn fresh_meta(&self) -> Term {
        let mut term = Term::Meta(self.g().new_meta(self.span));
        for (level, value) in self.env.iter().enumerate() {
            if matches!(value, Value::Neutral(Head::Var(l, _), s) if *l == level && s.is_empty()) {
                term = Term::app(term, Term::Var(self.level() - 1 - level));
            }
        }
        term
    }

    pub(crate) fn mismatch(&self, expected: &Value, found: &Value) -> Diagnostic {
        let expected_shown = self.show(expected);
        let found_shown = self.show(found);
        if let (Ok(Value::Sort(_)), Ok(Value::Sort(_))) = (
            force(self.g(), expected.clone()),
            force(self.g(), found.clone()),
        ) {
            return self
                .error(
                    "E-UNIVERSE",
                    "universe mismatch",
                    format!("expected something of type `{expected_shown}`, but this has type `{found_shown}`"),
                )
                .with_note("`Type n` lives in `Type (n+1)`; allowing `Type: Type` would make the logic inconsistent");
        }
        // Two types that print the same may differ only in something the
        // compiler fills in (an implicit argument, a proof): show those.
        let (expected_shown, found_shown, hidden) = if expected_shown == found_shown {
            let (e, f) = (self.show_hidden(expected), self.show_hidden(found));
            if e != f && self.differ_only_in_hidden(expected, found) {
                (e, f, true)
            } else {
                (expected_shown, found_shown, false)
            }
        } else {
            (expected_shown, found_shown, false)
        };
        let d = self.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!("expected `{expected_shown}`, but this has type `{found_shown}`"),
        );
        let d = if hidden {
            d.with_note(
                "the two types differ only in arguments the compiler fills in, shown here in \
                 `[brackets]` (an implicit argument, or a proof such as `d != 0`; proofs of the \
                 same statement aren't interchangeable)",
            )
        } else if expected_shown == found_shown {
            let d = match self.first_difference_note(expected, found) {
                Some(note) => d.with_note(note),
                None => d,
            };
            self.with_alike_updates_note(d, &[expected, found])
        } else {
            d
        };
        let d = match crate::data_auto::auto_mismatch_note(self, expected, found) {
            Some(note) => d.with_note(note),
            None => d,
        };
        let d = match self.alias_note(expected, found) {
            Some(note) => d.with_note(note),
            None => d,
        };
        let d = self.with_opaque_notes(d, &[expected, found]);
        self.unrefined_hint(d, expected, found)
    }

    /// SW-832: a side that is a definition kept folded in the message (an
    /// alias, `Q` for `Quot Bool AllTrue`) hides the difference when its
    /// unfolding has the same head as the other side, which is not itself a
    /// kept call: the two then differ in arguments that only the unfolded
    /// form shows. So say what the alias is. When the heads differ
    /// (`expected Nat, but this has type MyList`), the alias isn't what the
    /// mismatch is about; and when both sides are kept calls (`b ≤ c`
    /// against `b < c`), both names are already in the message. No note
    /// then.
    fn alias_note(&self, expected: &Value, found: &Value) -> Option<String> {
        let g = self.g();
        let (fe, ff) = (
            force(g, expected.clone()).ok()?,
            force(g, found.clone()).ok()?,
        );
        if !same_type_head(&fe, &ff) {
            return None;
        }
        let (alias, unfolded) = match (expected, found) {
            (Value::Call(..), Value::Call(..)) => return None,
            (Value::Call(..), _) => (expected, &fe),
            (_, Value::Call(..)) => (found, &ff),
            _ => return None,
        };
        let (shown, full) = (self.show(alias), self.show_unfolded(unfolded));
        (shown != full).then(|| format!("`{shown}` is `{full}`"))
    }

    /// D230: inside a generalised `match`, a mismatch whose types still
    /// contain the scrutinee comes from a term written out in the branch,
    /// which the `match` didn't refine (only the goal and the variables in
    /// scope are). Only looked for here, when the error is being reported.
    fn unrefined_hint(&self, d: Diagnostic, expected: &Value, found: &Value) -> Diagnostic {
        if self.scrutinees.is_empty() {
            return d;
        }
        let g = self.g();
        let level = self.level();
        let (Ok(expected), Ok(found)) = (quote(g, level, expected), quote(g, level, found)) else {
            return d;
        };
        for (base, needle, span, var) in self.scrutinees.iter().rev() {
            let Ok(needle) = needle.shift(g, level - base, 0) else {
                continue;
            };
            let contains = |t: &Term| crate::matching::occurs(&needle, t);
            // What's expected is `found` refined by the `match`: a hypothesis
            // or `let`-bound lemma from before it, given the match's own
            // equation or another term about the unrefined scrutinee.
            if !contains(&expected)
                && contains(&found)
                && let Some(value) = self.refined_value(*var)
                && self.refines_to(&needle, *var, &found, &expected)
            {
                let mut d = d
                    .with_label(
                        *span,
                        format!(
                            "this `match` replaced its scrutinee with `{value}` in this branch"
                        ),
                    )
                    .with_note(format!(
                        "what's expected was refined by the `match`: it has `{value}` where this \
                         has the scrutinee. The goal, the hypotheses and the `let`-bound lemmas \
                         from before the `match` are refined; the `match`'s own equation and \
                         terms written in the branch aren't"
                    ));
                if let Term::Eq(_, l, r) = expected.strip_loc()
                    && crate::matching::same(l, r)
                    && let Ok(side) = self.eval(l)
                {
                    d = d.with_note(format!(
                        "both sides of what's expected are `{}`, so `rfl` proves it",
                        self.show(&side)
                    ));
                }
                return d;
            }
            if contains(&expected) || contains(&found) {
                return d
                    .with_label(*span, "the `match`'s scrutinee, still in this type")
                    .with_note(
                        "a term written out inside a branch (an explicit argument, or a type you \
                     wrote) isn't refined by the `match`: only the goal and the variables in scope \
                     are, so it still has the scrutinee in it. Write `_` for such an argument, so \
                     it is inferred from the hypothesis (docs/syntax.md, \"Proving things about a \
                     definition with an inner `match`\")",
                    );
            }
        }
        d
    }

    /// In a branch of a generalised `match`, what the variable at `var`
    /// (standing for a scrutinee) is, shown: the branch's constructor or
    /// number. `None` where it is still a variable (a catch-all arm).
    pub(crate) fn refined_value(&self, var: usize) -> Option<String> {
        let value = self.env.get(var)?;
        if matches!(value, Value::Neutral(..)) {
            return None;
        }
        Some(self.show(value))
    }

    /// Whether `term`, with `needle` replaced by the variable at `var`,
    /// computes to `refined` (quoted, as `needle` is, at the current level).
    pub(crate) fn refines_to(
        &self,
        needle: &Term,
        var: usize,
        term: &Term,
        refined: &Term,
    ) -> bool {
        let g = self.g();
        let level = self.level();
        let hook = |t: &Term, under: usize| {
            crate::matching::same_shifted(needle, t, under, 0)
                .then(|| Term::Var(level + under - 1 - var))
        };
        let Ok(replaced) =
            crate::lift::replace_with(g, term, level, &|l| Ok(Term::Var(level - 1 - l)), &hook)
        else {
            return false;
        };
        let Ok(value) = self.eval(&replaced) else {
            return false;
        };
        quote(g, level, &value).is_ok_and(|t| crate::matching::same(&t, refined))
    }
}

/// Whether two forced types are built by the same outermost former (the
/// same data type, both functions, the same stuck head, …), so that they
/// differ only in what's inside. `=` is left out: a proposition such as
/// `b <= c` (which unfolds to an equation) is printed in its own notation, and
/// naming its unfolding would only add noise.
fn same_type_head(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Sort(_), Value::Sort(_)) => true,
        (Value::Pi(..), Value::Pi(..)) => true,
        (Value::Data(x, _), Value::Data(y, _)) => x == y,
        (Value::Neutral(x, _), Value::Neutral(y, _)) => x == y,
        _ => false,
    }
}

fn with_span<T>(cx: &mut Ctx, span: Span, f: impl FnOnce(&mut Ctx) -> Result<T>) -> Result<T> {
    let saved = std::mem::replace(&mut cx.span, span);
    let result = f(cx);
    cx.span = saved;
    result
}

/// An argument in an application.
#[derive(Clone, Copy)]
pub(crate) enum Arg<'a> {
    Explicit(&'a Expr),
    /// `[x := e]`: an implicit or `auto` argument by name.
    Named(&'a AstName, &'a Expr),
    /// `(x := e)`: an explicit argument by name. `named::plan` puts it in
    /// its parameter's place, as an `Explicit`, before it's applied.
    NamedExplicit(&'a AstName, &'a Expr),
    /// The value piped in by `|>`, already elaborated (`pipe.rs`).
    Piped(&'a Piped),
    /// A parameter's default, for a call that leaves it out
    /// (`defaults::apply`): its helper applied to the arguments before it,
    /// put in its place before any later argument is elaborated.
    Default(crate::defaults::DefaultRef),
}

/// An argument as written.
pub(crate) fn arg_of(arg: &Expr) -> Arg<'_> {
    match arg {
        Expr::NamedArg(name, value, _, Bracket::Square) => Arg::Named(name, value),
        Expr::NamedArg(name, value, _, Bracket::Round) => Arg::NamedExplicit(name, value),
        other => Arg::Explicit(other),
    }
}

/// The arguments of the application `expr` as written, and its head.
pub(crate) fn spine(expr: &Expr) -> (&Expr, Vec<Arg<'_>>) {
    let mut args = Vec::new();
    let mut head = expr;
    loop {
        match head {
            Expr::App(f, a) => {
                args.push(arg_of(a));
                head = f;
            }
            Expr::Bracketed(call, _) => head = call,
            _ => break,
        }
    }
    args.reverse();
    (head, args)
}

/// `(f a) b`, where `f` has parameter defaults: the bracketed call, to be
/// finished (its defaults filled) before it's applied to the arguments
/// after it (docs/proposals/signature-defaults.md §6.3).
fn finished_call<'a>(cx: &Ctx, expr: &'a Expr) -> Option<(&'a Expr, Vec<Arg<'a>>)> {
    let mut args = Vec::new();
    let mut head = expr;
    while let Expr::App(f, a) = head {
        args.push(arg_of(a));
        head = f;
    }
    let Expr::Bracketed(call, _) = head else {
        return None;
    };
    let Expr::Var(name) = spine(call).0 else {
        return None;
    };
    crate::defaults::of_name(cx, &name.text)?;
    args.reverse();
    Some((call, args))
}

/// The left side of `x |> f`, elaborated, as `f`'s first argument.
pub(crate) struct Piped {
    pub term: Term,
    pub ty: Value,
    /// The right side's span: errors about the value not fitting point at
    /// the function it's piped into.
    pub span: Span,
    /// A dot call's receiver (`x.f`), not a value before `|>`: only the
    /// error message differs.
    pub dot: bool,
}

pub fn infer(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    cx.g().budget.nesting(PASS)?;
    let span = expr.span();
    with_span(cx, span, |cx| {
        let (term, ty) = infer_inner(cx, expr)?;
        cx.e.note_expr(cx, span, &ty);
        Ok((Term::Loc(span, Rc::new(term)), ty))
    })
}

/// [`infer`] for an expression whose own value is a computation that goes
/// to a place of computation type (a call's argument, a dot call's
/// receiver, a value piped in): its value is the computation, which isn't
/// run, though anything in it that performs is (stage 0 of
/// docs/proposals/effect-polymorphism.md).
pub(crate) fn infer_unrun(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    cx.g().budget.nesting(PASS)?;
    let span = expr.span();
    with_span(cx, span, |cx| {
        let (term, ty) = infer_value(cx, expr)?;
        cx.e.note_expr(cx, span, &ty);
        Ok((Term::Loc(span, Rc::new(term)), ty))
    })
}

fn infer_inner(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    // The pieces are elaborated under the whole literal's span, so errors
    // point at all of it; the pieces' own span is still noted.
    if let Expr::Interpolated(text, _) = expr {
        let (term, ty) = infer_inner(cx, text)?;
        cx.e.note_expr(cx, text.span(), &ty);
        return Ok((term, ty));
    }
    // Code that performs operations, in a pure context: it may only perform
    // what it handles itself.
    if effects::may_perform(cx, expr)? {
        return match pure_first(cx, expr, None, |cx| infer_value(cx, expr))? {
            PureFirst::Done(found) => Ok(found),
            PureFirst::Run(plain_error) => {
                effects::run_pure(cx, expr, None).map_err(|e| PureFirst::error(plain_error, e))
            }
        };
    }
    infer_value(cx, expr)
}

/// In a pure context, an expression that performs only through calls whose
/// result is in a bare row (`List.map f xs`, whose result is `{e} (List b)`)
/// is first elaborated as plain calls, by `plain`: the row is settled by
/// unification, the empty row when the callbacks are pure (D1123), and the
/// call is the plain function's (docs/proposals/effect-polymorphism.md,
/// stage 3). If that fails, or leaves a computation (a callback with
/// abilities made the row one, D1124), it's undone and `None` is returned:
/// the caller runs the expression in the empty row as before, which says
/// which ability isn't allowed. If that fails too, the plain way's error is
/// the one reported: it's the error the plain function would give. A plain
/// way that fails because a part of the expression performs an ability
/// (`E-ABILITY`) is that error at once, without running.
fn pure_first(
    cx: &mut Ctx,
    expr: &Expr,
    expected: Option<&Value>,
    plain: impl FnOnce(&mut Ctx) -> Result<(Term, Value)>,
) -> Result<PureFirst> {
    if !effects::performs_only_in_bare_rows(cx, expr, expected)? {
        return Ok(PureFirst::Run(None));
    }
    let snapshot = crate::undo::Snapshot::take(cx);
    let first_new = cx.e.row_constraints.borrow().len();
    // The row comparisons the expression put aside are retried before the
    // row is looked at: a callback whose type was blocked (`Answer ?flag`)
    // may have become a computation with abilities once later arguments were
    // checked, which makes the row effectful (D1124) rather than empty
    // (SW-437).
    let found = plain(cx).and_then(|found| {
        while cx.e.retry_rows_from(first_new)? {}
        Ok(found)
    });
    match found {
        Ok((term, ty)) => {
            let effectful = match effects::comp_parts(cx, &ty)? {
                Some(_) => effects::unknown_bare_value(cx, &ty)?.is_none(),
                None => false,
            };
            if !effectful {
                // A row nothing has settled yet is the empty one: the value
                // is used where it stands, and a proof about it (`rfl` in a
                // `calc` step) needs the plain function now. The type is then
                // the value type: `CompIn Empty T` stays stuck as a value until
                // it's evaluated again.
                let ty = match effects::unknown_bare_value(cx, &ty)? {
                    Some(value) => {
                        effects::settle_empty(cx, &ty)?;
                        value
                    }
                    None => ty,
                };
                return Ok(PureFirst::Done((term, ty)));
            }
            snapshot.restore(cx);
            Ok(PureFirst::Run(None))
        }
        Err(e) if crate::undo::fatal(&e) => Err(e),
        // A part of it that runs performs an ability a pure context can't
        // (found running a nested call, or a callback that turned out to
        // perform, SW-437): running the whole in the empty row runs that
        // part too, so it can only fail the same way. It isn't tried: doing
        // so at every level of nested calls re-elaborated everything below
        // each one (SW-439), and the error names the call that performs.
        Err(e) if e.code == "E-ABILITY" => {
            snapshot.restore(cx);
            Err(e)
        }
        Err(e) => {
            snapshot.restore(cx);
            Ok(PureFirst::Run(Some(e)))
        }
    }
}

/// What [`pure_first`] found.
enum PureFirst {
    /// Elaborated as plain calls, with its type.
    Done((Term, Value)),
    /// To be run in the empty row; the plain way's error, if it failed.
    Run(Option<Diagnostic>),
}

impl PureFirst {
    /// The error to report when running the expression failed too: the
    /// plain way's, unless running it found an ability a pure context
    /// can't perform, which is what the plain way's mismatch came from.
    fn error(plain_error: Option<Diagnostic>, run_error: Diagnostic) -> Diagnostic {
        match plain_error {
            Some(plain) if run_error.code != "E-ABILITY" => plain,
            _ => run_error,
        }
    }
}

/// [`infer_inner`] once it's known that `expr` isn't run as a whole.
pub(crate) fn infer_value(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    if let Some(logic) = crate::logic::classify(cx, expr) {
        return crate::logic::infer(cx, logic);
    }
    match expr {
        Expr::Unit(_) => {
            let unit = builtin_data(cx, Builtin::UnitType)?;
            Ok((
                Term::Ctor(unit, 0, Vec::new()),
                Value::Data(unit, Vec::new()),
            ))
        }
        Expr::Tuple(a, b, _) => infer_tuple(cx, a, b),
        Expr::Match { .. } => crate::matching::infer_match(cx, expr),
        Expr::Reify { .. } => crate::reify::infer_reify(cx, expr),
        Expr::Calc { .. } => crate::calc::infer_calc(cx, expr),
        Expr::Rewrite { .. } => crate::rewrite::infer_rewrite(cx, expr),
        Expr::Omega { .. } => Err(crate::omega::no_goal(cx, expr)),
        Expr::Cases { .. } => Err(crate::cases::no_goal(cx, expr)),
        Expr::Ring { .. } => Err(crate::ring::no_goal(cx, expr)),
        Expr::LocalDefs { defs, body, .. } => crate::local::around(cx, defs, |cx| infer(cx, body)),
        Expr::Effect(row, ty) => {
            let (term, sort) = effects::effect_type(cx, row, ty)?;
            Ok((term, Value::Sort(sort)))
        }
        Expr::Let {
            name,
            ty,
            value,
            body,
            ..
        } => effects::pure_let(cx, name, ty.as_deref(), value, body, None),
        Expr::Seq(..) | Expr::Handle { .. } => {
            unreachable!("these may perform operations, so they're handled above")
        }
        Expr::Var(_) | Expr::App(..) => {
            if let Some((call, args)) = finished_call(cx, expr) {
                let head = infer(cx, call)?;
                return apply_args(cx, head, &args);
            }
            let (head, args) = spine(expr);
            infer_app(cx, head, &args)
        }
        Expr::Bracketed(call, _) => infer(cx, call),
        Expr::Interpolated(text, _) => {
            let (term, ty) = infer_value(cx, text)?;
            cx.e.note_expr(cx, text.span(), &ty);
            Ok((term, ty))
        }
        Expr::Pipe(value, f) => crate::pipe::infer_pipe(cx, value, f),
        Expr::NamedArg(_, _, _, Bracket::Square) => Err(cx.error(
            "E-PARSE",
            "a named implicit argument must follow a function",
            "write `f [x := …]`",
        )),
        Expr::NamedArg(_, _, _, Bracket::Round) => Err(cx.error(
            "E-PARSE",
            "a named argument must follow a function",
            "write `f (x := …)`",
        )),
        // `-k` with nothing expected is an `Int`.
        Expr::Neg(..) => crate::numbers::group(cx, expr, None),
        Expr::Num(n, _) => Ok((
            Term::Nat(Rc::new(n.clone())),
            Value::Data(nat(cx)?, Vec::new()),
        )),
        Expr::Float(text, _) => crate::numbers::infer_decimal(cx, text),
        Expr::Char(c, _) => {
            let char_data = builtin_data(cx, Builtin::Char)?;
            Ok((char_term(cx, *c)?, Value::Data(char_data, Vec::new())))
        }
        // `"ab"` is `MkText ['a', 'b']`: its characters are one compact list
        // when the prelude's `List` and `Char` are registered for it
        // (`stitchwort_core::chars`), and otherwise cons cells.
        Expr::Str(s, _) => {
            let (text, mk_text) = builtin_ctor(cx, Builtin::MkText)?;
            let (list, nil) = builtin_ctor(cx, Builtin::Nil)?;
            let (_, cons) = builtin_ctor(cx, Builtin::Cons)?;
            let chars = match cx.g().builtins.compact_literals() {
                Some(text_rep) => {
                    let buffer: std::rc::Rc<[char]> = s.chars().collect();
                    compact::term(text_rep, &Chars::whole(buffer))
                }
                None => {
                    let mut chars = Term::Ctor(list, nil, Vec::new());
                    for c in s.chars().rev() {
                        chars = Term::ctor(list, cons, vec![char_term(cx, c)?, chars]);
                    }
                    chars
                }
            };
            Ok((
                Term::ctor(text, mk_text, vec![chars]),
                Value::Data(text, Vec::new()),
            ))
        }
        Expr::Include(path, span) => {
            let text = cx.e.read_include(path, *span)?;
            infer(cx, &Expr::Str(text, *span))
        }
        Expr::Binary(BinOp::Append, a, b) => append(cx, a, b),
        // `Type MAX_LEVEL` is the top universe: nothing for it to live in
        // (SW-902).
        Expr::Type(i, span) => match Sort::Type(*i).succ() {
            Some(above) => Ok((Term::Sort(Sort::Type(*i)), Value::Sort(above))),
            None => Err(Diagnostic::error("E-UNIVERSE", format!("`Type {i}` has no type"))
                .with_label(
                    *span,
                    format!("`Type {MAX_LEVEL}` is the largest universe, and no universe holds it"),
                )
                .with_note(format!(
                    "`Type n` can be used as a term for `n` up to {}: every term needs a type, and `Type n : Type n` would make the logic inconsistent",
                    MAX_LEVEL - 1
                ))),
        },
        Expr::Prop(_) => Ok((Term::Sort(Sort::Prop), Value::Sort(Sort::Type(0)))),
        Expr::Hole(_) => {
            let ty = cx.fresh_meta();
            let ty = cx.eval(&ty)?;
            Ok((cx.fresh_meta(), ty))
        }
        // A goal where nothing says its type: that's unknown too, and
        // printed as such if nothing works it out.
        Expr::Goal(_) => {
            let ty = cx.fresh_meta();
            let ty = cx.eval(&ty)?;
            Ok((crate::goals::hole(cx, &ty), ty))
        }
        Expr::Lam(..) if expr.section_name().is_some() => {
            Err(crate::dot::section_unknown(cx, expr))
        }
        Expr::Lam(names, ..) => {
            let names: Vec<Name> = names.iter().map(|name| name.text.as_str().into()).collect();
            infer_lambda(cx, expr, &names)
        }
        // `(x: A) => body`, `[a: Type] => body`, `[auto h: P] => body`:
        // the parameter's type is written, so the function's type follows
        // from the body's, with the parameter's mode (§4.3 of
        // docs/proposals/lambda-syntax.md).
        Expr::TypedLam(name, mode, ann, body, _) => {
            let icit = mode_icit(*mode);
            let (dom, _) = check_type(cx, ann)?;
            let dom = cx.eval(&dom)?;
            let (row, row_value) = inferred_row(cx)?;
            let mark = cx.mark();
            cx.bind(&name.text, dom.clone());
            // A body that may perform abilities is checked against a
            // computation whose row it works out.
            let inferred = effects::may_perform(cx, body).and_then(|performs| {
                if performs {
                    let result = cx.fresh_meta();
                    let cod = cx.eval(&inferred_comp(cx, &row_value, result)?)?;
                    let term = check(cx, body, &cod)?;
                    Ok((term, cx.quote_folded(&cod)?, true))
                } else {
                    let (term, ty) = infer(cx, body)?;
                    let (term, ty) = insert(cx, term, ty)?;
                    Ok((term, cx.quote_folded(&ty)?, false))
                }
            });
            cx.reset(mark);
            let (body, cod, performs) = inferred?;
            if performs {
                settle_inferred_row(cx, &row, &row_value)?;
            }
            let x: Name = name.text.as_str().into();
            let lam = Term::Lam(x.clone(), icit, Rc::new(body));
            let cod = Closure {
                env: cx.env.as_slice().into(),
                body: Rc::new(cod),
            };
            let pi = Value::Pi(x, icit, Rc::new(dom), cod);
            // Annotated for the kernel, which doesn't infer a lambda's type.
            // For an implicit or auto lambda, this shape (an annotation
            // straight around the lambda) is what tells [`insert`] not to
            // apply it to unknowns.
            let ann = Term::Ann(Rc::new(lam), Rc::new(cx.quote_folded(&pi)?));
            Ok((ann, pi))
        }
        Expr::Pi {
            names,
            implicit,
            auto,
            dom,
            cod,
            ..
        } => {
            let icit = match (implicit, auto) {
                (_, true) => Icit::Auto,
                (true, false) => Icit::Implicit,
                (false, false) => Icit::Explicit,
            };
            let (dom, s1) = check_type(cx, dom)?;
            let mark = cx.mark();
            for (k, name) in names.iter().enumerate() {
                let shifted = Rc::new(dom.shift(cx.g(), k, 0)?);
                let ty = cx.eval(&shifted)?;
                cx.bind(&name.text, ty);
                // The type as written, so dot notation on this variable
                // starts from an alias (`bank: Bank`), as for a parameter.
                cx.set_written(crate::dot::Written::Here(shifted));
            }
            let result = check_type(cx, cod);
            cx.reset(mark);
            let (mut term, s2) = result?;
            for (k, name) in names.iter().enumerate().rev() {
                term = Term::Pi(
                    name.text.as_str().into(),
                    icit,
                    Rc::new(dom.shift(cx.g(), k, 0)?),
                    Rc::new(term),
                );
            }
            Ok((term, Value::Sort(Sort::pi(s1, s2))))
        }
        Expr::Arrow(a, b) => {
            let (a, s1) = check_type(cx, a)?;
            let mark = cx.mark();
            let a_value = cx.eval(&a)?;
            cx.bind_hidden("_".into(), a_value);
            let result = check_type(cx, b);
            cx.reset(mark);
            let (b, s2) = result?;
            Ok((
                Term::Pi("_".into(), Icit::Explicit, Rc::new(a), Rc::new(b)),
                Value::Sort(Sort::pi(s1, s2)),
            ))
        }
        // `x in c`: a proposition, by the type of `c`.
        Expr::Binary(BinOp::In(op), a, b) => crate::membership::infer_member(cx, *op, a, b),
        // Arithmetic and comparisons: typed a group at a time.
        Expr::Binary(..) => crate::numbers::group(cx, expr, None),
        Expr::If {
            binder,
            cond,
            then,
            otherwise,
            ..
        } => {
            let ty = cx.fresh_meta();
            let ty = cx.eval(&ty)?;
            let term = check_if(cx, binder.as_ref(), cond, then, otherwise, &ty)?;
            Ok((term, ty))
        }
        Expr::Ann(e, ty, _) => {
            let (ty, _) = check_type(cx, ty)?;
            let ty_value = cx.eval(&ty)?;
            let e = check(cx, e, &ty_value)?;
            Ok((Term::Ann(Rc::new(e), Rc::new(ty)), ty_value))
        }
        Expr::Record {
            base: None, fields, ..
        } => records::infer_literal(cx, fields),
        Expr::Record {
            base: Some(base),
            fields,
            ..
        } => records::infer_update(cx, base, fields),
        Expr::CtorFields { ctor, fields, span } => {
            match records::ctor_fields(cx, ctor, fields, *span, None)? {
                records::Construction::Positional(positional) => infer_inner(cx, &positional),
                records::Construction::Defaults(d, c) => {
                    crate::defaults::ctor_with_defaults(cx, d, c, fields, None)
                }
            }
        }
        Expr::Field(e, field) => crate::dot::infer_call(cx, e, field, &[]),
        Expr::List(..) => {
            let list = builtin_data(cx, Builtin::List)?;
            let elem = cx.fresh_meta();
            let ty = Value::Data(list, vec![cx.eval(&elem)?]);
            let term = check(cx, expr, &ty)?;
            Ok((annotate(cx, term, &ty)?, ty))
        }
    }
}

/// Infers a function on its own, ready to be applied (a name, without
/// inserting its implicit arguments, or filling its parameters' defaults:
/// the caller applies it to the call's arguments).
pub(crate) fn infer_head(cx: &mut Ctx, head: &Expr) -> Result<(Term, Value)> {
    infer_app_with(cx, head, &[], false)
}

/// Infers an application `head args`.
pub(crate) fn infer_app(cx: &mut Ctx, head: &Expr, args: &[Arg]) -> Result<(Term, Value)> {
    infer_app_with(cx, head, args, true)
}

/// `head` applied to `args`, where `head` is a definition or a local
/// definition: with `fill`, a defaulted parameter `args` don't name gets its
/// default (docs/proposals/signature-defaults.md §6.1). Its name is written
/// at `at`.
fn apply_named_head(
    cx: &mut Ctx,
    head: (Term, Value),
    args: &[Arg],
    fill: bool,
    at: Span,
) -> Result<(Term, Value)> {
    match crate::defaults::of_head(cx, &head.0) {
        Some(defaults) if fill => {
            crate::defaults::note_left_out(cx, at, &head, args);
            crate::defaults::apply(cx, head, defaults, args)
        }
        _ => apply_args(cx, head, args),
    }
}

fn infer_app_with(cx: &mut Ctx, head: &Expr, args: &[Arg], fill: bool) -> Result<(Term, Value)> {
    let g = cx.g();
    if let Expr::Field(recv, field) = head {
        return crate::dot::infer_call(cx, recv, field, args);
    }
    let Expr::Var(name) = head else {
        let head = infer(cx, head)?;
        return apply_args(cx, head, args);
    };
    if let Some(head) = cx.local(&name.text)? {
        cx.note_local_use(name, &head.1);
        return apply_named_head(cx, head, args, fill, name.span);
    }
    if let Some(level) = cx.lookup(&name.text) {
        let head = (Term::Var(cx.level() - 1 - level), cx.types[level].clone());
        cx.e.note_local(cx, name, &head.1);
        return apply_args(cx, head, args);
    }
    if let Some(d) = crate::opaque::no_unfold_equation(cx.e, name) {
        return Err(d);
    }
    if let Some(fields) = as_fields(cx, name) {
        return infer_app_with(cx, &fields, args, fill);
    }
    if let Some(form) = crate::quot::head_form(cx, &name.text) {
        return crate::quot::elaborate(cx, form, args, None);
    }
    match name.text.as_str() {
        "rfl" => {
            return Err(cx.error(
                "E-CANNOT-INFER",
                "can't work out what `rfl` proves here",
                "add a type annotation: `(rfl: a = b)`",
            ));
        }
        "J" => {
            let [
                Arg::Explicit(motive),
                Arg::Explicit(base),
                Arg::Explicit(proof),
            ] = args[..]
            else {
                return Err(cx.error(
                    "E-ARITY",
                    "`J` takes 3 arguments: a motive, a base case and a proof",
                    "here",
                ));
            };
            return infer_j(cx, motive, base, proof);
        }
        _ => {}
    }
    cx.e.note_name(name);
    match cx.e.named(&name.text) {
        None => Err(cx.e.not_found(name)),
        Some((Global::Def(id), _)) => {
            let head = (Term::Def(*id), crate::kernel::def_ty(g, *id)?);
            apply_named_head(cx, head, args, fill, name.span)
        }
        // The parameters, then the indices: one telescope; `auto` parameters
        // are found (docs/proposals/interfaces.md §7.5).
        Some((Global::Data(d), _)) => crate::data_auto::data_app(cx, *d, args),
        Some((Global::Unchecked(item), _)) => Err(cx.e.unchecked(name, *item)),
        Some((Global::Failed, _)) => Err(crate::module::failed_name(name)),
        Some((Global::Pending(file, _), _)) => Err(cx.e.unloaded(name, *file)),
        Some((Global::Ability(_), _)) => Err(cx.error(
            "E-ABILITY",
            format!("`{}` is an ability, not a type or a value", name.text),
            "abilities go in a function type's row: `-> {State s} …`",
        )),
        Some((Global::Op(a, i), _)) if args.is_empty() => {
            let (term, ty) = effects::op_value(cx, *a, *i)?;
            let ty_term = cx.quote_folded(&ty)?;
            Ok((Term::Ann(Rc::new(term), Rc::new(ty_term)), ty))
        }
        Some((Global::Op(a, _), _)) => {
            let ability = cx.e.abilities[*a].name.clone();
            Err(cx
                .error(
                    "E-ABILITY",
                    format!(
                        "`{}` is an operation of `{ability}`, which isn't allowed here",
                        name.text
                    ),
                    "this function's type has no abilities",
                )
                .with_note(format!(
                    "add `{ability}` to the function's type: `-> {{{ability} …}} …`"
                )))
        }
        Some((Global::Ctor(d, c), _)) => {
            let explicit = ctor_args(args);
            let missing = ctor_missing(cx, *d, *c, &explicit)?;
            if !missing.is_empty() {
                // A partially applied constructor is a function; unification
                // works out its type. Its parameters keep the fields' names,
                // so they can be given by name (§4.3).
                let expected = fresh_function_type(cx, &missing)?;
                let expected = cx.eval(&expected)?;
                let (term, ty) = ctor_app(cx, *d, *c, &explicit, Some(&expected))?;
                let ann = Term::Ann(Rc::new(term), Rc::new(cx.quote_folded(&ty)?));
                return Ok((ann, ty));
            }
            let (term, ty) = ctor_app(cx, *d, *c, &explicit, None)?;
            Ok((annotate(cx, term, &ty)?, ty))
        }
    }
}

/// `(x1: ?a1) -> … -> (xn: ?an) -> ?b`, with each type a fresh
/// metavariable, for parameters named `names`.
fn fresh_function_type(cx: &mut Ctx, names: &[Name]) -> Result<Term> {
    Ok(fresh_function_type_in(cx, names, None)?.term)
}

/// A function type of unknowns, and whether its result is a computation.
struct FreshFunctionType {
    term: Term,
    result_performs: bool,
}

/// [`fresh_function_type`], for a lambda with body `body` if given: if the
/// body may perform abilities (with the parameters in scope), the result
/// is `CompIn row ?b`.
fn fresh_function_type_in(
    cx: &mut Ctx,
    names: &[Name],
    body: Option<(&Expr, &Value)>,
) -> Result<FreshFunctionType> {
    let Some((name, rest)) = names.split_first() else {
        let result = cx.fresh_meta();
        return Ok(match body {
            Some((body, row)) if effects::may_perform(cx, body)? => FreshFunctionType {
                term: inferred_comp(cx, row, result)?,
                result_performs: true,
            },
            _ => FreshFunctionType {
                term: result,
                result_performs: false,
            },
        });
    };
    let dom = cx.fresh_meta();
    let mark = cx.mark();
    let dom_value = cx.eval(&dom)?;
    // Noted now, not only once the lambda is checked: a case split in its
    // body unpins it from the matched variable ([`unpin_parameter_types`]).
    if let Value::Neutral(Head::Meta(m), _) = force(cx.g(), dom_value.clone())? {
        cx.e.parameter_metas
            .borrow_mut()
            .insert(m, name.to_string());
    }
    cx.bind_hidden(name.clone(), dom_value);
    let cod = fresh_function_type_in(cx, rest, body);
    cx.reset(mark);
    let cod = cod?;
    Ok(FreshFunctionType {
        term: Term::Pi(
            name.clone(),
            Icit::Explicit,
            Rc::new(dom),
            Rc::new(cod.term),
        ),
        result_performs: cod.result_performs,
    })
}

/// A row unknown for the result of a lambda whose body may perform
/// abilities, made outside its parameters, as a row doesn't depend on
/// their values.
fn inferred_row(cx: &Ctx) -> Result<(Term, Value)> {
    let row = cx.fresh_meta();
    let value = cx.eval(&row)?;
    Ok((row, value))
}

/// `CompIn row result`.
fn inferred_comp(cx: &Ctx, row: &Value, result: Term) -> Result<Term> {
    let comp_in = builtin_def(cx, Builtin::CompIn)?;
    Ok(Term::app(
        Term::app(Term::Def(comp_in), cx.quote(row)?),
        result,
    ))
}

/// After a lambda's body was checked against a result in `row`: the row
/// is closed at the abilities the body performs, and noted, so that a row
/// still unknown is the empty one if nothing else settles it.
fn settle_inferred_row(cx: &Ctx, row: &Term, value: &Value) -> Result<()> {
    effects::close_inferred_row(cx, value)?;
    let row_type = Value::Data(builtin_data(cx, Builtin::Row)?, Vec::new());
    crate::rows::note_row_meta(cx, &row_type, row);
    Ok(())
}

/// A lambda with no expected type: checked against a function type whose
/// parameter and result types are unknowns, for its body, its patterns
/// and its later uses to work out. A body that may perform abilities
/// works out the row of its result too.
fn infer_lambda(cx: &mut Ctx, lambda: &Expr, names: &[Name]) -> Result<(Term, Value)> {
    let (row, row_value) = inferred_row(cx)?;
    let body = match lambda {
        Expr::Lam(_, body, _) => Some((&**body, &row_value)),
        _ => None,
    };
    let fresh = fresh_function_type_in(cx, names, body)?;
    let ty = cx.eval(&fresh.term)?;
    let term = check(cx, lambda, &ty)?;
    if fresh.result_performs {
        settle_inferred_row(cx, &row, &row_value)?;
    }
    note_parameter_metas(cx, &ty)?;
    // Annotated for the kernel, which doesn't infer a lambda's type.
    let ann = Term::Ann(Rc::new(term), Rc::new(cx.quote_folded(&ty)?));
    Ok((ann, ty))
}

/// Records each parameter type of `ty` still unknown after checking the
/// lambda, so that if nothing works it out, the error names the parameter.
fn note_parameter_metas(cx: &mut Ctx, ty: &Value) -> Result<()> {
    let g = cx.g();
    let mut level = cx.level();
    let mut rest = force(g, ty.clone())?;
    while let Value::Pi(name, _, dom, cod) = rest {
        if let Value::Neutral(Head::Meta(m), _) = force(g, (*dom).clone())? {
            cx.e.parameter_metas
                .borrow_mut()
                .insert(m, name.to_string());
        }
        rest = force(g, cod.apply(g, Value::var(level))?)?;
        level += 1;
    }
    Ok(())
}

/// Before a case split on variable `level`: the type of each variable in
/// scope that is still the unknown made up for an unannotated lambda's
/// parameter (`x => …`, nothing written) can't depend on `level`, so the
/// split's substitution leaves it as it is (SW-873). Otherwise, in
/// `x => match k with | 0 => g x | …`, `x` would have type `?t k` and, in
/// each arm, `?t 0`, which no type solves when `g x` asks for a `Nat`. A
/// type written by the user, or one already worked out, is never touched:
/// only an unknown in `parameter_metas`, as the parameter's whole type, is,
/// so dependent matching on a written type works as before. The unknown
/// standing for the pruned one is noted in its place, for a later split
/// and for the message if nothing works it out.
pub(crate) fn unpin_parameter_types(cx: &Ctx, level: usize) -> Result<()> {
    let g = cx.g();
    for ty in &cx.types {
        let Value::Neutral(Head::Meta(m), _) = force(g, ty.clone())? else {
            continue;
        };
        let Some(name) = cx.e.parameter_metas.borrow().get(&m).cloned() else {
            continue;
        };
        crate::unify::prune_variable(g, ty, level)?;
        if let Value::Neutral(Head::Meta(m2), _) = force(g, ty.clone())?
            && m2 != m
        {
            cx.e.parameter_metas.borrow_mut().insert(m2, name);
        }
    }
    Ok(())
}

fn ctor_args<'a>(args: &[Arg<'a>]) -> Vec<CtorArg<'a>> {
    args.iter()
        .map(|a| match a {
            Arg::Explicit(e) => CtorArg::Pos(e),
            Arg::Named(n, e) => CtorArg::Named(n, e),
            Arg::NamedExplicit(n, e) => CtorArg::NamedExplicit(n, e),
            Arg::Piped(_) => unreachable!("`|>` applies a constructor as a function"),
            Arg::Default(_) => unreachable!("a constructor's fields aren't filled by default"),
        })
        .collect()
}

/// The fields of constructor `c` of `d` as a signature, for named
/// arguments.
fn ctor_signature(cx: &Ctx, d: DataId, c: usize) -> crate::named::Signature {
    let ctor = &cx.g().data(d).ctors[c];
    crate::named::declared(ctor.fields.iter().enumerate().map(|(i, (name, _))| {
        let implicit = ctor.implicit.get(i).copied().unwrap_or(false);
        let icit = if implicit {
            Icit::Implicit
        } else {
            Icit::Explicit
        };
        (name.clone(), icit)
    }))
}

/// What `args` give each field of constructor `c` of `d` (§4.2 rule 1,
/// D1096), or an error if they don't fit its fields.
fn ctor_fill<'a>(
    cx: &Ctx,
    d: DataId,
    c: usize,
    args: &[CtorArg<'a>],
) -> Result<Vec<Option<&'a Expr>>> {
    let ctor = &cx.g().data(d).ctors[c];
    let as_args: Vec<Arg<'a>> = (args.iter())
        .map(|a| match a {
            CtorArg::Pos(e) => Arg::Explicit(e),
            CtorArg::Named(n, e) => Arg::Named(n, e),
            CtorArg::NamedExplicit(n, e) => Arg::NamedExplicit(n, e),
        })
        .collect();
    let sig = ctor_signature(cx, d, c);
    let (assigned, overflow) = crate::named::assign(cx, &sig, &as_args).map_err(|e| {
        // The constructor's own wording for a field it doesn't have.
        if e.code == "E-UNKNOWN-NAME" {
            let mut e = e;
            e.message = format!("`{}` has no such field", ctor.name);
            e
        } else {
            e
        }
    })?;
    if !overflow.is_empty() {
        let wanted = sig
            .params
            .iter()
            .filter(|p| p.icit == Icit::Explicit)
            .count();
        let given = (args.iter())
            .filter(|a| !matches!(a, CtorArg::Named(..)))
            .count();
        let mut error = cx.error(
            "E-NOT-A-FUNCTION",
            format!("`{}` takes {wanted} argument(s)", ctor.name),
            format!("it's given {given}"),
        );
        if let Some(note) = args.iter().find_map(|a| match a {
            CtorArg::Pos(e) => negative_argument_note(e),
            _ => None,
        }) {
            error = error.with_note(note);
        }
        return Err(match cx.e.hiding_note(&ctor.name) {
            Some(note) => error.with_note(note),
            None => error,
        });
    }
    Ok(assigned
        .into_iter()
        .map(|a| match a {
            Some(Arg::Explicit(e) | Arg::Named(_, e)) => Some(e),
            _ => None,
        })
        .collect())
}

/// The explicit fields of constructor `c` of `d` that `args` leave out: the
/// parameters of the function the application is.
fn ctor_missing(cx: &Ctx, d: DataId, c: usize, args: &[CtorArg]) -> Result<Vec<Name>> {
    let given = ctor_fill(cx, d, c, args)?;
    let ctor = &cx.g().data(d).ctors[c];
    Ok((ctor.fields.iter().enumerate())
        .filter(|(i, _)| !ctor.implicit.get(*i).copied().unwrap_or(false) && given[*i].is_none())
        .map(|(_, (name, _))| name.clone())
        .collect())
}

/// Applies `head` to `args`, inserting implicit arguments where needed.
pub(crate) fn apply_args(cx: &mut Ctx, head: (Term, Value), args: &[Arg]) -> Result<(Term, Value)> {
    apply_args_with(cx, head, args, &mut Supply::new())
}

/// Implicit arguments made in advance, used in order before any new ones:
/// those [`written_result`] made, so the application is elaborated with the
/// metavariables its expected type has already been compared with.
pub(crate) type Supply = std::collections::VecDeque<Term>;

/// [`apply_args`], taking implicit arguments from `supply` first.
///
/// An argument that is a lambda (or a method section) whose parameter type
/// isn't known yet when it's reached is checked after the later arguments,
/// which may fix that type: `List.map (p => p.name) people`. Only the
/// checking order changes; the term's arguments stay in place. A section is
/// always postponed then, unless a later parameter's type depends on it; a
/// plain lambda, or a section with such a dependent, only if checking it in
/// place fails, so what already worked is elaborated as before. A dependent
/// parameter's type holds a placeholder for the lambda until it's checked,
/// which the argument given may solve, as in `memMapElim (e => e.fst) y xs
/// listed` with `listed: y ∈ xs.map (e => e.fst)`. If the application fails
/// anyway, the error is the one checking it in place gave.
pub(crate) fn apply_args_with(
    cx: &mut Ctx,
    head: (Term, Value),
    args: &[Arg],
    supply: &mut Supply,
) -> Result<(Term, Value)> {
    // Named arguments: in their parameters' places (`named.rs`).
    let ordered;
    let args = if crate::named::any(args) {
        let sig = crate::named::signature(cx, &head.1)?;
        // Names behind a type that computes once the arguments are given:
        // `(pick 1) (count := 2)` for `pick 1 (count := 2)`.
        if let Some((first, rest)) = crate::named::split(cx, &sig, args)? {
            let head = apply_args_with(cx, head, &first, supply)?;
            return apply_args_with(cx, head, &rest, supply);
        }
        let slots = crate::named::plan(cx, &sig, args, None)?;
        match crate::named::positional(&slots) {
            Some(positional) => {
                ordered = positional;
                &ordered[..]
            }
            None => return crate::named::apply_slots(cx, head, &slots),
        }
    } else {
        args
    };
    let mut relevant = false;
    for arg in args {
        if let Arg::Explicit(value) = arg
            && (defers_literal(cx, value)? || numbers_in_list(value))
        {
            relevant = true;
        }
    }
    let run = |cx: &mut Ctx, head: (Term, Value), supply: &mut Supply| {
        let mut first_error = None;
        match apply_args_postponing(cx, head, args, supply, &mut first_error) {
            Err(e) if !crate::undo::fatal(&e) => Err(first_error.unwrap_or(e)),
            result => result,
        }
    };
    if !relevant {
        return run(cx, head, supply);
    }
    // A constructor or list with number literals among the arguments: as
    // written first, and only if that fails with it checked last
    // (`defers_literal`, `numbers_in_list`).
    let saved = supply.clone();
    let (result, left) = retrying(cx, |cx| {
        let mut left = saved.clone();
        run(cx, head.clone(), &mut left).map(|result| (result, left))
    })?;
    *supply = left;
    Ok(result)
}

/// Runs `f`; if it fails, once more with a constructor of a generic type
/// that has number literals in it checked after its siblings
/// ([`defers_literal`]), so what already elaborated is elaborated as before.
/// If that fails too, its error is the one given.
pub(crate) fn retrying<T>(cx: &mut Ctx, f: impl Fn(&mut Ctx) -> Result<T>) -> Result<T> {
    if cx.e.late_literals.get() > 0 {
        return f(cx);
    }
    let first_try = crate::undo::Snapshot::take(cx);
    let result = f(cx);
    if !matches!(&result, Err(e) if !crate::undo::fatal(e)) {
        return result;
    }
    first_try.restore(cx);
    let second_try = crate::undo::Snapshot::take(cx);
    cx.e.late_literals.set(1);
    let again = f(cx);
    cx.e.late_literals.set(0);
    match again {
        Err(e) if crate::undo::fatal(&e) => Err(e),
        // Its error blames the literal that doesn't fit the type its
        // siblings gave, where the first one blames the siblings for not
        // being the type the literal defaulted to.
        Err(e) => {
            second_try.restore(cx);
            Err(e)
        }
        ok => ok,
    }
}

/// [`apply_args_with`], keeping the error of the first lambda postponed
/// after failing in place.
fn apply_args_postponing(
    cx: &mut Ctx,
    head: (Term, Value),
    args: &[Arg],
    supply: &mut Supply,
    first_error: &mut Option<Diagnostic>,
) -> Result<(Term, Value)> {
    let (mut term, mut ty) = head;
    let mut postponed = Vec::new();
    // Lambdas to check after the application's type is compared with the
    // type expected of it, if `infer_expecting` says what that is.
    let expecting = match &*cx.e.app_expected.borrow() {
        Some((key, expected))
            if args.iter().any(
                |a| matches!(a, Arg::Explicit(e) if std::ptr::from_ref(*e) as usize == *key),
            ) =>
        {
            Some(expected.clone())
        }
        _ => None,
    };
    let mut after_expected = Vec::new();
    // The argument just passed, when it was a name given as a function.
    let mut function_name: Option<&AstName> = None;
    for (i, arg) in args.iter().enumerate() {
        let previous_function_name = function_name.take();
        match arg {
            Arg::Explicit(value @ Expr::Lam(..)) => {
                (term, ty) = insert_with(cx, term, ty, supply)?;
                let (dom, cod) = function_parts(cx, &ty)?;
                let later = args[i + 1..]
                    .iter()
                    .any(|a| matches!(a, Arg::Explicit(_) | Arg::Piped(_)));
                // Later parameters whose types mention it see the
                // placeholder, which their arguments may solve.
                let dependents = !only_lambdas_depend_on_it(&cod.body, &args[i + 1..]);
                let parameters = match value {
                    Expr::Lam(names, ..) => names.len(),
                    _ => 1,
                };
                let postponable = later && unknown_domain(cx, &dom, parameters)?;
                // Where the application's expected type is known, a lambda
                // whose type has unknowns that fails in place is checked
                // again once the application's type has been compared with
                // it, if no later parameter's type mentions it.
                let late_able = !postponable
                    && expecting.is_some()
                    && only_lambdas_depend_on_it(&cod.body, &[])
                    && crate::interfaces::unsolved_in(cx, &dom)?.is_some();
                let mut late = false;
                let checked = if late_able {
                    let snapshot = crate::undo::Snapshot::take(cx);
                    match check_arg(cx, &term, value, &dom) {
                        Ok(value) => Some(value),
                        Err(e) if crate::undo::fatal(&e) => return Err(e),
                        Err(e) => {
                            snapshot.restore(cx);
                            first_error.get_or_insert(e);
                            late = true;
                            None
                        }
                    }
                } else if !postponable {
                    Some(check_arg(cx, &term, value, &dom)?)
                } else if value.section_name().is_some() && !dependents {
                    None
                } else {
                    let snapshot = crate::undo::Snapshot::take(cx);
                    match check_arg(cx, &term, value, &dom) {
                        Ok(value) => Some(value),
                        Err(e) if crate::undo::fatal(&e) => return Err(e),
                        Err(e) => {
                            snapshot.restore(cx);
                            first_error.get_or_insert(e);
                            None
                        }
                    }
                };
                if let Some(value) = checked {
                    ty = cod.apply_lazy(cx.g(), || eval(cx.g(), &cx.env, &value))?;
                    term = Term::app(term, value);
                    continue;
                }
                // `List.map .position ds`: what `.position` takes is
                // known once `ds` is, so the lambda is checked last.
                let meta = cx.fresh_meta();
                let placeholder = cx.eval(&meta)?;
                ty = cod.apply(cx.g(), placeholder.clone())?;
                let id = match meta.spine().0 {
                    Term::Meta(m) => *m,
                    _ => unreachable!("a fresh metavariable is headed by one"),
                };
                term = Term::app(term, meta);
                if late {
                    after_expected.push((*value, dom, placeholder, id));
                } else {
                    postponed.push((*value, dom, placeholder, id));
                }
            }
            Arg::NamedExplicit(..) => {
                unreachable!("`apply_args_with` puts named arguments in their places")
            }
            Arg::Named(name, value) => {
                (term, ty) = insert_until(cx, term, ty, name, supply)?;
                let Value::Pi(_, icit, dom, cod) = force(cx.g(), ty.clone())? else {
                    unreachable!("insert_until stops at the named implicit parameter");
                };
                let value = check(cx, value, &dom)?;
                ty = cod.apply_lazy(cx.g(), || eval(cx.g(), &cx.env, &value))?;
                term = Term::app_icit(term, value, icit);
            }
            Arg::Piped(piped) => {
                (term, ty) = insert_with(cx, term, ty, supply)?;
                let (dom, cod) = function_parts(cx, &ty)?;
                if !cx.unify(&piped.ty, &dom)? {
                    return Err(piped_mismatch(cx, piped, &dom));
                }
                ty = cod.apply_lazy(cx.g(), || eval(cx.g(), &cx.env, &piped.term))?;
                term = Term::app(term, piped.term.clone());
            }
            Arg::Default(default) => {
                (term, ty) = insert_with(cx, term, ty, supply)?;
                let (_, cod) = function_parts(cx, &ty)?;
                let value = crate::defaults::helper_call(cx, *default, &term)?;
                ty = cod.apply_lazy(cx.g(), || eval(cx.g(), &cx.env, &value))?;
                term = Term::app(term, value);
            }
            Arg::Explicit(value) => {
                (term, ty) = insert_with(cx, term, ty, supply)?;
                let (dom, cod) = function_parts(cx, &ty).map_err(|e| {
                    not_a_function_hint(cx, &term, previous_function_name, value, e)
                })?;
                // `pair (Point 1 "p" 10) m`, where `m: Mark Int Nat`: the
                // constructor's number would be defaulted to a `Nat` before
                // `m` said what the parameter is, so it's checked last, as a
                // lambda whose parameter type isn't known is. So is a list
                // of numbers whose element type isn't known: in
                // `List.map [1, 2] (x => x): List Int` the list comes first
                // (D303), and only the lambda ties its elements to `Int`.
                let later = args[i + 1..]
                    .iter()
                    .any(|a| matches!(a, Arg::Explicit(_) | Arg::Piped(_)));
                if later
                    && cx.e.late_literals.get() > 0
                    && only_lambdas_depend_on_it(&cod.body, &args[i + 1..])
                    && ((matches!(
                        force(cx.g(), dom.clone())?,
                        Value::Neutral(Head::Meta(_), _)
                    ) && defers_literal(cx, value)?)
                        || (numbers_in_list(value)
                            && crate::interfaces::unsolved_in(cx, &dom)?.is_some()))
                {
                    let meta = cx.fresh_meta();
                    let placeholder = cx.eval(&meta)?;
                    ty = cod.apply(cx.g(), placeholder.clone())?;
                    let id = match meta.spine().0 {
                        Term::Meta(m) => *m,
                        _ => unreachable!("a fresh metavariable is headed by one"),
                    };
                    term = Term::app(term, meta);
                    postponed.push((*value, dom, placeholder, id));
                    continue;
                }
                let next_is_unit = matches!(args.get(i + 1), Some(Arg::Explicit(Expr::Unit(_))));
                // An argument that fails in place while its type has
                // unknowns is checked again once the application's type has
                // been compared with the type expected of it, as a lambda is
                // above: a proof found from its goal, as in
                // `Eq.cong Some (omega)` against `Some a = Some b`, or a
                // proof about a `_` that only the expected type fixes, as in
                // `walk _ rest (snocStep moved)` against
                // `P (walk outcome (Cons x rest))`. Whether the type has
                // unknowns is only asked after a failure: it reads the whole
                // type back, which can be large.
                let snapshot = (expecting.is_some() && only_lambdas_depend_on_it(&cod.body, &[]))
                    .then(|| crate::undo::Snapshot::take(cx));
                let value = match check_arg(cx, &term, value, &dom) {
                    Ok(value) => value,
                    Err(e) if crate::undo::fatal(&e) => return Err(e),
                    Err(e) => {
                        let Some(snapshot) = snapshot else {
                            return Err(unit_call_hint(cx, &term, value, &dom, next_is_unit, e));
                        };
                        snapshot.restore(cx);
                        if crate::interfaces::unsolved_in(cx, &dom)?.is_none() {
                            return Err(unit_call_hint(cx, &term, value, &dom, next_is_unit, e));
                        }
                        first_error.get_or_insert(e);
                        let meta = cx.fresh_meta();
                        let placeholder = cx.eval(&meta)?;
                        ty = cod.apply(cx.g(), placeholder.clone())?;
                        let id = match meta.spine().0 {
                            Term::Meta(m) => *m,
                            _ => unreachable!("a fresh metavariable is headed by one"),
                        };
                        term = Term::app(term, meta);
                        after_expected.push((*value, dom, placeholder, id));
                        continue;
                    }
                };
                if let Arg::Explicit(Expr::Var(name)) = arg
                    && matches!(
                        force(cx.g(), dom.clone())?,
                        Value::Pi(_, Icit::Explicit, ..)
                    )
                {
                    function_name = Some(name);
                }
                ty = cod.apply_lazy(cx.g(), || eval(cx.g(), &cx.env, &value))?;
                term = Term::app(term, value);
            }
        }
    }
    for (value, dom, placeholder, id) in postponed {
        let checked = match check(cx, value, &dom) {
            Ok(checked) => checked,
            // The retry sees the types the later arguments gave, so its
            // error is the real one. The in-place try's is kept only when
            // both are can't-infers: then the first names the unknown.
            Err(e) if !crate::undo::fatal(&e) => {
                if e.code != "E-CANNOT-INFER"
                    || first_error
                        .as_ref()
                        .is_none_or(|f| f.code != "E-CANNOT-INFER")
                {
                    *first_error = None;
                }
                return Err(e);
            }
            Err(e) => return Err(e),
        };
        let evaluated = cx.eval(&checked)?;
        if !cx.unify(&evaluated, &placeholder)? {
            return Err(cx.mismatch(&placeholder, &evaluated));
        }
        // The types see the placeholder's solution, a value; the term gets
        // the lambda as it was checked. Reading the value back would write
        // out what its calls unfold to (`r.id == target` on `Text`, with
        // `r`'s type unknown until now, as `Text.decEqFrom … (List.decEq …)`
        // instead of the call `Text.decEq`, which extraction runs natively).
        term = fill_placeholder(&term, id, &checked).unwrap_or(term);
    }
    if let (false, Some(expected)) = (after_expected.is_empty(), &expecting) {
        // The type as `fallback` will compare it: with no implicit
        // parameters left to insert (they'd be made again there).
        let implicit_next = matches!(
            force(cx.g(), ty.clone())?,
            Value::Pi(_, Icit::Implicit | Icit::Auto, ..)
        );
        // Unknowns that only the arguments of a call can fix, as the
        // functions in `List.sumBy xs ?f` with its `Add` dictionary still
        // unknown, are solved from them if the plain comparison fails.
        if implicit_next
            || !(crate::undo::unify(cx, &ty, expected)?
                || crate::undo::unify_solving_arguments(cx, &ty, expected)?)
        {
            return Err(first_error.take().expect("set when the lambda was put off"));
        }
        // With the expected type compared, a lambda that still fails is
        // blamed against the goal as it now stands, not the in-place one.
        *first_error = None;
        for (value, dom, placeholder, id) in after_expected {
            let checked = check_arg(cx, &term, value, &dom)?;
            let evaluated = cx.eval(&checked)?;
            if !cx.unify(&evaluated, &placeholder)? {
                return Err(cx.mismatch(&placeholder, &evaluated));
            }
            term = fill_placeholder(&term, id, &checked).unwrap_or(term);
        }
    }
    let own = own_dictionaries(&term);
    Ok((term, found_dictionaries(cx, &own, ty)?))
}

/// The items of a list literal checked against `elem`, in order, or when
/// retrying (`retrying`) and the element type isn't known, those with a
/// constructor with number literals last (`defers_literal`).
fn check_items(cx: &mut Ctx, items: &[Expr], elem: &Value) -> Result<Vec<Term>> {
    let mut order: Vec<usize> = (0..items.len()).collect();
    if cx.e.late_literals.get() > 0
        && matches!(
            force(cx.g(), elem.clone())?,
            Value::Neutral(Head::Meta(_), _)
        )
    {
        let mut late = Vec::new();
        order.clear();
        for (i, item) in items.iter().enumerate() {
            if defers_literal(cx, item)? {
                late.push(i);
            } else {
                order.push(i);
            }
        }
        order.extend(late);
    }
    let mut checked: Vec<Option<Term>> = vec![None; items.len()];
    for i in order {
        checked[i] = Some(check(cx, &items[i], elem)?);
    }
    Ok(checked.into_iter().flatten().collect())
}

/// Whether the `else` branch of an `if` whose type isn't known yet
/// (`unknown`) is checked first: the `then` branch is a constructor with a
/// number in it and the `else` isn't (`defers_literal`).
fn else_first(cx: &Ctx, then: &Expr, otherwise: &Expr, unknown: bool) -> Result<bool> {
    Ok(unknown
        && cx.e.late_literals.get() > 0
        && defers_literal(cx, then)?
        && !defers_literal(cx, otherwise)?)
}

/// Whether `expr` is a number literal or a list of numbers: what it is
/// depends on where it's used.
pub(crate) fn literal_value(expr: &Expr) -> bool {
    crate::numbers::any_literal(expr) || numbers_in_list(expr)
}

/// Whether `expr` is a list literal with a number literal in it: checked
/// against a list type whose element type isn't known yet, the number would
/// settle it as `Nat` before the arguments after it could say otherwise.
fn numbers_in_list(expr: &Expr) -> bool {
    matches!(expr, Expr::List(..)) && crate::numbers::has_number(expr)
}

/// Whether `expr` is a constructor of a parameterised type applied to
/// arguments with a number literal in them: checked against a type not yet
/// known, the number would settle a parameter as `Nat` before the other
/// operands of the application, list, `if` or comparison it's in could say
/// otherwise, so it's checked after them.
pub(crate) fn defers_literal(cx: &Ctx, expr: &Expr) -> Result<bool> {
    if !matches!(expr, Expr::App(..)) || !crate::numbers::has_number(expr) {
        return Ok(false);
    }
    Ok(match ctor_head(cx, expr)? {
        Some((d, ..)) => !cx.g().data(d).params.is_empty(),
        None => false,
    })
}

/// `term`, an application, with its argument that is the metavariable `id`
/// (applied to the variables in scope) replaced by `with`; `None` if it has
/// no such argument.
fn fill_placeholder(term: &Term, id: usize, with: &Term) -> Option<Term> {
    match term {
        Term::Loc(span, t) => fill_placeholder(t, id, with).map(|t| Term::Loc(*span, Rc::new(t))),
        Term::App(f, a, icit) => {
            if matches!(a.strip_loc().spine().0, Term::Meta(m) if *m == id) {
                return Some(Term::App(f.clone(), Rc::new(with.clone()), *icit));
            }
            fill_placeholder(f, id, with).map(|f| Term::App(Rc::new(f), a.clone(), *icit))
        }
        _ => None,
    }
}

/// The unknowns an application `term` has as `auto` arguments: its own
/// dictionaries (and proofs), not those of the applications in its
/// arguments.
pub(crate) fn own_dictionaries(mut term: &Term) -> Vec<usize> {
    let mut out = Vec::new();
    loop {
        match term {
            Term::Loc(_, t) => term = t,
            Term::App(f, a, icit) => {
                if *icit == Icit::Auto
                    && let Term::Meta(m) = a.strip_loc().spine().0
                {
                    out.push(*m);
                }
                term = f;
            }
            _ => return out,
        }
    }
}

/// After an application with the dictionary obligations `own`, of type `ty`:
/// one whose type its arguments have fixed (`List.sumBy f xs` once
/// `f` is checked) is found now, so the result type computes (its `+` isn't
/// stuck on the dictionary) wherever it's compared next, and `ty` is
/// computed again if it is an equation stuck on one. What's found depends only on the
/// type, so finding it earlier can't change it, unless unification could
/// still solve it (an argument of a type in the result, `Tree k [ord :=
/// ?d]`): those are left (docs/proposals/interfaces.md, "As built (stage
/// 5)").
pub(crate) fn found_dictionaries(cx: &mut Ctx, own: &[usize], ty: Value) -> Result<Value> {
    if own.is_empty() || cx.e.interfaces.is_empty() {
        return Ok(ty);
    }
    Ok(crate::interfaces::find_ready_dictionaries(cx, &ty, Some(own))?.unwrap_or(ty))
}

/// Checks an explicit argument of `head` against its parameter type `dom`.
fn check_arg(cx: &mut Ctx, head: &Term, value: &Expr, dom: &Value) -> Result<Term> {
    match check(cx, value, dom) {
        Err(e) if e.code == "E-PARTIAL-ESCAPE" => {
            Err(partial_callback(cx, head, value, dom).unwrap_or(e))
        }
        Err(e) if e.code == "E-TYPE-MISMATCH" => {
            let e = local_signature(cx, head, e);
            Err(total_callback_note(cx, head, value, dom, e))
        }
        Err(e) if e.code == "E-PARTIAL" => {
            let e = total_rows_note(cx, head, e);
            Err(total_lambda_note(cx, head, value, dom, e))
        }
        result => result,
    }
}

/// `play start ()` is `(play start) ()`: when the argument that doesn't fit is
/// a name of a function from `()` and a `()` follows it, the call was meant to be
/// the argument (`play (start ())`).
fn unit_call_hint(
    cx: &Ctx,
    head: &Term,
    value: &Expr,
    dom: &Value,
    next_is_unit: bool,
    e: Diagnostic,
) -> Diagnostic {
    let (Expr::Var(arg), true, "E-TYPE-MISMATCH") = (value, next_is_unit, e.code) else {
        return e;
    };
    if matches!(force(cx.g(), dom.clone()), Ok(Value::Pi(..))) {
        return e;
    }
    match called_name(cx, head) {
        Some(function) => e.with_note(unit_call_note(&function, &arg.text)),
        None => e,
    }
}

/// `apply start ()`, where `apply` takes a function and `start` is one: the
/// call to `apply` isn't a function, so the `()` was meant for `start`
/// (`apply (start ())`).
fn not_a_function_hint(
    cx: &Ctx,
    head: &Term,
    previous_function_name: Option<&AstName>,
    value: &Expr,
    e: Diagnostic,
) -> Diagnostic {
    if let Some(note) = negative_argument_note(value) {
        return if e.code == "E-NOT-A-FUNCTION" {
            e.with_note(note)
        } else {
            e
        };
    }
    let (Some(arg), Expr::Unit(_), "E-NOT-A-FUNCTION") = (previous_function_name, value, e.code)
    else {
        return e;
    };
    match called_name(cx, head) {
        Some(function) => e.with_note(unit_call_note(&function, &arg.text)),
        None => e,
    }
}

/// The note for an unbracketed negative argument, `n -1`, where the function
/// it's given to isn't one (D1467). The elaborator has no source text, so it
/// names the argument, not the head.
pub(crate) fn negative_argument_note(arg: &Expr) -> Option<String> {
    let Expr::Neg(inner, _, NegForm::Argument) = arg else {
        return None;
    };
    fn text(e: &Expr) -> Option<String> {
        match e {
            Expr::Num(n, _) => Some(n.to_string()),
            Expr::Float(t, _) => Some(t.clone()),
            Expr::Var(n) => Some(n.text.clone()),
            Expr::Field(e, n) => Some(format!("{}.{}", text(e)?, n.text)),
            _ => None,
        }
    }
    let shown = match text(inner) {
        Some(t) => format!("`-{t}`"),
        None => "this `-`".to_string(),
    };
    Some(format!(
        "{shown} here is a negative argument (a space before the `-`, none after it); to \
         subtract, put a space after the `-` as well"
    ))
}

/// The name of the definition or local variable an application calls.
fn called_name(cx: &Ctx, head: &Term) -> Option<String> {
    match head.spine().0.strip_loc() {
        Term::Def(id) => Some(cx.g().def(*id).name.to_string()),
        Term::Var(ix) => Some(cx.names[cx.level() - 1 - ix].to_string()),
        _ => None,
    }
}

/// The note suggesting `function (arg ())` for `function arg ()`.
pub(crate) fn unit_call_note(function: &str, arg: &str) -> String {
    format!(
        "did you mean `{function} ({arg} ())`? Without brackets, `{function} {arg} ()` passes `{arg}` itself to `{function}` and then applies the result to `()`"
    )
}

/// When the function given a partial argument was checked with its
/// row variables total, because its body needs them total (D1215,
/// docs/proposals/partial-stage-3.md §2.2): why it can't take a partial
/// callback, where its signature alone suggests it could.
fn total_rows_note(cx: &Ctx, head: &Term, e: Diagnostic) -> Diagnostic {
    let Term::Def(id) = head.spine().0.strip_loc() else {
        return e;
    };
    let Some(at) = cx.e.total_rows.borrow().get(id).copied() else {
        return e;
    };
    let name = cx.g().def(*id).name.to_string();
    e.with_label(
        at,
        format!("`{name}`'s body needs its row to be total here"),
    )
    .with_note(format!(
        "`{name}` takes only total callbacks: its body puts a callback where only total code \
         can go (a field of a data type, say), so its row variable stands for total rows only"
    ))
}

/// When the function with a wrong argument is a local definition, its whole
/// signature: its leading parameters are the variables it uses, in the order
/// they are written (D228), which nobody could guess from the call.
fn local_signature(cx: &Ctx, head: &Term, e: Diagnostic) -> Diagnostic {
    if let Term::Def(id) = head.spine().0 {
        let def = cx.g().def(*id);
        if cx.e.helper_keys.contains(&def.name.to_string()) {
            // The telescope with its parameters' names, as a signature.
            let g = cx.g();
            let mut names: Vec<Name> = Vec::new();
            let mut shown = Vec::new();
            let mut ty = def.ty.strip_loc();
            while let Term::Pi(x, icit, dom, cod) = ty {
                let dom = pretty::term_for_message_in(g, cx.e, &names, dom);
                shown.push(match (&**x, icit) {
                    ("" | "_", Icit::Explicit) => dom,
                    (x, Icit::Explicit) => format!("({x}: {dom})"),
                    (x, _) => format!("[{x}: {dom}]"),
                });
                names.push(x.clone());
                ty = cod.strip_loc();
            }
            shown.push(pretty::term_for_message_in(g, cx.e, &names, ty));
            return e.with_note(format!(
                "`{}` is a local definition with the signature `{}`; its leading parameters \
                 are the variables it uses, in the order they are written (the header's \
                 parameters, then the arm's pattern variables from left to right)",
                def.name,
                shown.join(" -> ")
            ));
        }
    }
    e
}

/// Whether the function type `dom` ends in a result that must finish: not a
/// computation at all, or one in a total row with no divergence index (a
/// bare `{e}` has one, and may be partial).
fn expects_total_result(cx: &mut Ctx, dom: &Value) -> bool {
    let g = cx.g();
    let mark = cx.mark();
    let result = (|| -> Result<bool> {
        let mut ty = force(g, dom.clone())?;
        if !matches!(ty, Value::Pi(..)) {
            return Ok(false);
        }
        while let Value::Pi(x, _, d, c) = ty {
            let v = Value::var(cx.level());
            cx.bind_hidden(x, (*d).clone());
            ty = force(g, c.apply(g, v)?)?;
        }
        Ok(match crate::effects::comp_parts(cx, &ty)? {
            Some((row, _)) => !row.partial && row.div.is_none(),
            None => true,
        })
    })();
    cx.reset(mark);
    result.unwrap_or(false)
}

/// Whether the function type `dom` ends in a `Delay` over signatures that
/// aren't a row of abilities (`Effect.pfix`'s `Delay (Plus (Rec req) op) …`):
/// the callback builds that computation as a value, so it must finish.
fn builds_delay_value(cx: &mut Ctx, dom: &Value) -> bool {
    let g = cx.g();
    let Some(delay) = g.builtins.primitive_id(Primitive::Delay) else {
        return false;
    };
    let mark = cx.mark();
    let result = (|| -> Result<bool> {
        let mut ty = force(g, dom.clone())?;
        if !matches!(ty, Value::Pi(..)) {
            return Ok(false);
        }
        while let Value::Pi(x, _, d, c) = ty {
            let v = Value::var(cx.level());
            cx.bind_hidden(x, (*d).clone());
            ty = force(g, c.apply(g, v)?)?;
        }
        Ok(
            matches!(&ty, Value::Neutral(Head::Def(d), _) if *d == delay)
                && crate::effects::comp_parts(cx, &ty)?.is_none(),
        )
    })();
    cx.reset(mark);
    result.unwrap_or(false)
}

/// Whether `ty` is a function type whose result is a partial computation.
fn gives_partial_result(cx: &mut Ctx, ty: &Value) -> bool {
    let g = cx.g();
    let mark = cx.mark();
    let result = (|| -> Result<bool> {
        let mut ty = force(g, ty.clone())?;
        if !matches!(ty, Value::Pi(..)) {
            return Ok(false);
        }
        while let Value::Pi(x, _, d, c) = ty {
            let v = Value::var(cx.level());
            cx.bind_hidden(x, (*d).clone());
            ty = force(g, c.apply(g, v)?)?;
        }
        Ok(matches!(
            crate::effects::comp_parts(cx, &ty)?,
            Some((row, _)) if row.partial
        ))
    })();
    cx.reset(mark);
    result.unwrap_or(false)
}

/// The helper a callback is passed to, as the user wrote it, and whether it
/// is in std.
fn helper_name(cx: &Ctx, head: &Term) -> Option<(String, bool)> {
    match head.spine().0 {
        Term::Def(id) => {
            let def = cx.g().def(*id);
            Some((def.name.to_string(), def.path.starts_with("Std.")))
        }
        _ => None,
    }
}

/// Why `helper`, a std function, refuses a partial callback, from its
/// callback's type `param` (shown): with no row there, or a fixed one, the
/// callback must finish. The std functions whose callbacks may be partial
/// say so with a row variable (`a → {e} Bool`), and those take one.
fn std_callback_note(helper: &str, param: &str) -> String {
    let why = if param.contains('}') {
        "whose row is fixed"
    } else {
        "which has no `{e}`"
    };
    format!(
        "`{helper}` doesn't take partial callbacks: its callback has the type `{param}`, \
         {why}, so it must finish"
    )
}

/// A partial function given where the parameter's callback type must finish
/// (`List.sortBy xs partialComparison`): a plain type mismatch, so say why.
fn total_callback_note(
    cx: &mut Ctx,
    head: &Term,
    arg: &Expr,
    dom: &Value,
    e: Diagnostic,
) -> Diagnostic {
    let Expr::Var(name) = arg else {
        return e;
    };
    let Some((helper, in_std)) = helper_name(cx, head) else {
        return e;
    };
    if !expects_total_result(cx, dom) {
        return e;
    }
    let mark = cx.mark();
    let found = infer(cx, arg).map(|(_, ty)| ty);
    let partial = match &found {
        Ok(ty) => gives_partial_result(cx, ty),
        Err(_) => false,
    };
    cx.reset(mark);
    if !partial {
        return e;
    }
    let param = cx.show(dom);
    let note = if in_std {
        format!(
            "{}, and `{}` is partial",
            std_callback_note(&helper, &param),
            name.text
        )
    } else {
        format!(
            "`{helper}`'s parameter has the type `{param}`, which must finish, and `{}` is \
             partial",
            name.text
        )
    };
    e.with_note(note)
}

/// A callback written as a lambda, given where the callback type must
/// finish, and whose body is partial: the enclosing function's type isn't
/// the one to change.
fn total_lambda_note(
    cx: &mut Ctx,
    head: &Term,
    arg: &Expr,
    dom: &Value,
    mut e: Diagnostic,
) -> Diagnostic {
    if !matches!(arg, Expr::Lam(..) | Expr::TypedLam(..)) {
        return e;
    }
    let Some((helper, in_std)) = helper_name(cx, head) else {
        return e;
    };
    if !expects_total_result(cx, dom) {
        return e;
    }
    if builds_delay_value(cx, dom) {
        e.notes.clear();
        return e.with_note(format!(
            "`{helper}`'s callback builds a partial computation and returns it as a value: \
             building it must finish, so the callback can't run anything that might not"
        ));
    }
    let param = cx.show(dom);
    if param.contains('?') {
        return e;
    }
    e.notes.clear();
    e.with_note(if in_std {
        std_callback_note(&helper, &param)
    } else {
        format!(
            "`{helper}`'s parameter has the type `{param}`, which must finish, so its callback \
             can't run anything partial"
        )
    })
}

/// Whether `ty` is a function type whose parameter's type isn't known yet:
/// a lambda checked against it couldn't use its parameter.
/// Whether the parameters after a postponed lambda, `rest` (the type of the
/// application so far), have types that don't mention it, except where the
/// argument given is a lambda too (which is then postponed with it, as in
/// `List.sortBySorted (a b => …) (a b => …) xs`). The result type may mention
/// it: it holds the placeholder, which the lambda then solves.
fn only_lambdas_depend_on_it(rest: &Term, args: &[Arg]) -> bool {
    let mut explicit = args
        .iter()
        .filter(|a| matches!(a, Arg::Explicit(_) | Arg::Piped(_) | Arg::Default(_)));
    let mut ty = rest;
    let mut under = 0;
    while let Term::Pi(_, icit, dom, cod) = ty.strip_loc() {
        let arg = (*icit == Icit::Explicit).then(|| explicit.next()).flatten();
        if dom.mentions(under) && !matches!(arg, Some(Arg::Explicit(Expr::Lam(..)))) {
            return false;
        }
        ty = cod;
        under += 1;
    }
    true
}

fn unknown_domain(cx: &Ctx, ty: &Value, parameters: usize) -> Result<bool> {
    let g = cx.g();
    let mut ty = force(g, ty.clone())?;
    if matches!(ty, Value::Neutral(Head::Meta(_), _)) {
        return Ok(true);
    }
    // Any of the first `parameters` parameters, not only the first: in
    // `(n acc => …)` against `Nat -> b -> c` with `b` still unknown, `n`'s
    // type is known and `acc`'s is not (SW-822).
    for i in 0..parameters {
        let Value::Pi(_, _, dom, cod) = ty else {
            return Ok(false);
        };
        if matches!(force(g, (*dom).clone())?, Value::Neutral(Head::Meta(_), _)) {
            return Ok(true);
        }
        ty = force(g, cod.apply(g, Value::var(cx.level() + i))?)?;
    }
    Ok(false)
}

/// The domain and codomain of `ty`, a function type with an explicit
/// parameter (made one, if it's unknown).
pub(crate) fn function_parts(cx: &mut Ctx, ty: &Value) -> Result<(Value, Closure)> {
    match force(cx.g(), ty.clone())? {
        Value::Pi(_, Icit::Explicit, dom, cod) => Ok(((*dom).clone(), cod)),
        Value::Neutral(Head::Meta(_), _) => {
            // Unknown type: it must be a function type.
            let dom = cx.fresh_meta();
            let dom = cx.eval(&dom)?;
            let mark = cx.mark();
            cx.bind_hidden("x".into(), dom.clone());
            let cod = cx.fresh_meta();
            cx.reset(mark);
            let cod = Closure {
                env: cx.env.as_slice().into(),
                body: Rc::new(cod),
            };
            let pi = Value::Pi(
                "x".into(),
                Icit::Explicit,
                Rc::new(dom.clone()),
                cod.clone(),
            );
            if !cx.unify(ty, &pi)? {
                return Err(cx.mismatch(&pi, ty));
            }
            Ok((dom, cod))
        }
        other => Err(cx.error(
            "E-NOT-A-FUNCTION",
            "this isn't a function",
            format!(
                "it's applied to an argument, but its type is `{}`",
                cx.show(&other)
            ),
        )),
    }
}

/// `x |> f` or `x.f`, where `x`'s type isn't what `f` takes first.
pub(crate) fn piped_mismatch(cx: &Ctx, piped: &Piped, dom: &Value) -> Diagnostic {
    let (message, how, before) = if piped.dot {
        (
            "the value before `.` doesn't fit the function",
            "dot notation",
            "`.`",
        )
    } else {
        (
            "the value piped in doesn't fit the function",
            "`|>`",
            "`|>`",
        )
    };
    Diagnostic::error("E-TYPE-MISMATCH", message).with_label(
        piped.span,
        format!(
            "{how} passes the value as the first argument, which takes `{}`, but the value \
             before {before} has type `{}`",
            cx.show(dom),
            cx.show(&piped.ty)
        ),
    )
}

/// A recursive call of the partial group being described, passed as `arg`
/// to `head`, whose parameter of type `dom` is a function with a fixed row:
/// nothing in `head` can answer its requests (docs/proposals/partial.md
/// §7.3.4).
fn partial_callback(cx: &Ctx, head: &Term, arg: &Expr, dom: &Value) -> Option<Diagnostic> {
    if !matches!(force(cx.g(), dom.clone()), Ok(Value::Pi(..))) {
        return None;
    }
    let (helper, in_std) = match head.spine().0 {
        Term::Def(id) => {
            let def = cx.g().def(*id);
            (def.name.to_string(), def.path.starts_with("Std."))
        }
        Term::Var(ix) => (cx.names[cx.level() - 1 - ix].to_string(), false),
        _ => return None,
    };
    let members = cx.e.recursion.as_ref()?.names.clone();
    let shown = |n: &String| format!("`{n}`");
    let what = match arg {
        Expr::Var(name) if !name.text.starts_with('%') => format!("`{}`", name.text),
        _ => "this".to_string(),
    };
    let param = cx.show(dom);
    // A row that is already open (`| e`), or whose type isn't solved yet
    // (`?N`), is not one a signature edit can fix: the row variable stands
    // for total rows only.
    let open = in_std || param.contains('?') || param.contains('|');
    let mut diagnostic = Diagnostic::error(
        "E-PARTIAL-CALLBACK",
        format!("{what} can't be passed to `{helper}` here"),
    )
    .with_label(
        arg.span(),
        format!(
            "{what} calls {}, so as a value it makes requests that only {}'s own \
             definition can answer",
            members.iter().map(shown).collect::<Vec<_>>().join(", "),
            shown(&members[0]),
        ),
    );
    if in_std {
        diagnostic = diagnostic.with_note(std_callback_note(&helper, &param));
    } else if open {
        diagnostic = diagnostic.with_note(format!(
            "`{helper}`'s parameter has the type `{param}`, whose row variable stands only for \
             total rows here: `{helper}`'s body needs it total, or it's an argument of a data \
             type, so changing `{helper}`'s signature won't help"
        ));
    } else if !param.contains('}') {
        diagnostic = diagnostic.with_note(format!(
            "`{helper}`'s parameter has the type `{param}`, which must finish: give it a \
             `{{Partial | e}}` result and add `| e` to `{helper}`'s own row too"
        ));
    } else {
        // The parameter's type with a row variable added to its last row.
        let suggested = match param.rfind('}') {
            Some(i) => format!("{} | e{}", &param[..i], &param[i..]),
            None => param.clone(),
        };
        diagnostic = diagnostic
            .with_note(format!(
                "`{helper}`'s parameter has the type `{param}`, whose row is fixed"
            ))
            .with_note(format!(
                "make `{helper}` polymorphic in the rest of the row: give the parameter the type \
                 `{suggested}`, and add `| e` to `{helper}`'s own row too"
            ));
    }
    Some(diagnostic)
}

/// Applies `term` to a fresh metavariable for each leading implicit or auto
/// parameter. An auto argument is also recorded as an obligation, to be proved
/// once the declaration has been elaborated (see `auto.rs`).
///
/// A lambda written with an implicit or auto parameter, `[a: Type] => …`,
/// is left as it is: it was written to take that parameter, so it isn't
/// applied to an unknown in its place (as in Agda; the elaboration-zoo's
/// `insert`). An application still applies it ([`insert_with`]).
pub fn insert(cx: &mut Ctx, term: Term, ty: Value) -> Result<(Term, Value)> {
    if binder_lambda(&term) {
        return Ok((term, ty));
    }
    insert_with(cx, term, ty, &mut Supply::new())
}

/// Whether `term` is what [`infer`] makes of a lambda with an implicit or
/// auto parameter: the lambda straight inside its annotation. Elsewhere a
/// lambda in an annotation comes from [`check`], which wraps it in a
/// location first.
fn binder_lambda(term: &Term) -> bool {
    matches!(
        term.strip_loc(),
        Term::Ann(lam, _) if matches!(&**lam, Term::Lam(_, icit, _) if icit.is_implicit())
    )
}

/// The kind of function a lambda parameter's mode makes.
pub(crate) fn mode_icit(mode: Mode) -> Icit {
    match mode {
        Mode::Explicit => Icit::Explicit,
        Mode::Implicit => Icit::Implicit,
        Mode::Auto => Icit::Auto,
    }
}

/// [`insert`], taking implicit arguments from `supply` first.
fn insert_with(
    cx: &mut Ctx,
    mut term: Term,
    mut ty: Value,
    supply: &mut Supply,
) -> Result<(Term, Value)> {
    while let Value::Pi(_, icit, dom, cod) = force(cx.g(), ty.clone())?
        && icit.is_implicit()
    {
        let meta = supplied_arg(cx, icit, &dom, supply);
        let value = cx.eval(&meta)?;
        term = Term::app_icit(term, meta, icit);
        ty = cod.apply(cx.g(), value)?;
    }
    Ok((term, ty))
}

pub(crate) fn implicit_arg(cx: &mut Ctx, icit: Icit, ty: &Value) -> Term {
    let meta = cx.fresh_meta();
    crate::rows::note_row_meta(cx, ty, &meta);
    if icit == Icit::Auto {
        let tree = match meta.spine().0 {
            Term::Meta(m) => *m,
            _ => unreachable!("a fresh metavariable"),
        };
        if let Some(ignorable) = ignorable_arguments(cx, ty) {
            cx.g().set_meta_ignorable(tree, ignorable);
        }
        cx.e.obligations.borrow_mut().push(crate::auto::Obligation {
            env: cx.env.clone(),
            types: cx.types.clone(),
            names: cx.names.clone(),
            goal: ty.clone(),
            meta: meta.clone(),
            span: cx.span,
            tree,
        });
    }
    meta
}

/// For an `auto` argument's unknown proof of `goal`, made by
/// [`Ctx::fresh_meta`]: for each variable it's applied to, whether neither
/// `goal` nor the type of any other variable in scope mentions it (see
/// `Meta::ignorable`). `None` if a type can't be read back.
///
/// Usually a type mentions only earlier variables, but not always: a case
/// split refines the types of earlier variables in terms of the pattern's
/// (in `Int.div`'s `| OfNat m, OfNat (Succ n) => …`, `ok: divisor != OfNat
/// 0` becomes `ok: OfNat (Succ n) != OfNat 0`, which mentions the later
/// `n`). So every type is read back with all `level` variables in scope,
/// and a mention by any of them counts (SW-416).
fn ignorable_arguments(cx: &Ctx, goal: &Value) -> Option<std::rc::Rc<[bool]>> {
    let level = cx.level();
    let mut mentioned = vec![false; level];
    let mut mark = |value: &Value| -> Option<()> {
        let term = quote(cx.g(), level, value).ok()?;
        for (t, binders) in term.subterms() {
            if let Term::Var(i) | Term::Case(i, ..) | Term::NumCase(i, ..) = t
                && *i >= binders
                && *i - binders < level
            {
                mentioned[level - 1 - (*i - binders)] = true;
            }
        }
        Some(())
    };
    mark(goal)?;
    // A variable's own type can't mention it, so marking every type marks
    // each variable only by the others.
    for ty in &cx.types {
        mark(ty)?;
    }
    let ignorable: Vec<bool> = mentioned.iter().map(|m| !m).collect();
    // One entry per argument: the variables `fresh_meta` applies it to.
    Some(
        cx.env
            .iter()
            .enumerate()
            .filter(
                |(l, v)| matches!(v, Value::Neutral(Head::Var(x, _), s) if x == l && s.is_empty()),
            )
            .map(|(l, _)| ignorable[l])
            .collect(),
    )
}

/// An implicit argument from `supply`, or a new one. ([`written_result`] records
/// its auto arguments as obligations itself, as `pipe.rs` does with
/// [`implicit_arg`].)
fn supplied_arg(cx: &mut Ctx, icit: Icit, ty: &Value, supply: &mut Supply) -> Term {
    match supply.pop_front() {
        Some(arg) => arg,
        None => implicit_arg(cx, icit, ty),
    }
}

/// Inserts implicit arguments up to the implicit parameter called `name`.
fn insert_until(
    cx: &mut Ctx,
    mut term: Term,
    mut ty: Value,
    name: &AstName,
    supply: &mut Supply,
) -> Result<(Term, Value)> {
    loop {
        match force(cx.g(), ty.clone())? {
            Value::Pi(x, icit, _, _) if icit.is_implicit() && *x == *name.text => {
                return Ok((term, ty));
            }
            Value::Pi(_, icit, dom, cod) if icit.is_implicit() => {
                let meta = supplied_arg(cx, icit, &dom, supply);
                let value = cx.eval(&meta)?;
                term = Term::app_icit(term, meta, icit);
                ty = cod.apply(cx.g(), value)?;
            }
            _ => {
                return Err(Diagnostic::error(
                    "E-UNKNOWN-NAME",
                    format!("no implicit parameter named `{}` here", name.text),
                )
                .with_label(name.span, "not an implicit parameter of this function"));
            }
        }
    }
}

/// A typed lambda's parameter `name: ann`, checked against a function type
/// of the same kind, `dom` to `cod`: the written type must be `dom`.
fn typed_lambda(
    cx: &mut Ctx,
    name: &AstName,
    icit: Icit,
    ann: &Expr,
    body: &Expr,
    dom: &Value,
    cod: &Closure,
) -> Result<Term> {
    let g = cx.g();
    let (written, _) = check_type(cx, ann)?;
    let written = cx.eval(&written)?;
    if !cx.unify(&written, dom)? {
        let (expected, found) = (cx.show(dom), cx.show(&written));
        return with_span(cx, ann.span(), |cx| {
            Err(cx.error(
                "E-TYPE-MISMATCH",
                "type mismatch",
                format!(
                    "this parameter is annotated `{found}`, but the function is \
                     expected to take `{expected}`"
                ),
            ))
        });
    }
    let mark = cx.mark();
    let var = Value::var(cx.level());
    cx.bind(&name.text, dom.clone());
    let cod = cod.apply(g, var)?;
    let result = check(cx, body, &cod);
    cx.reset(mark);
    Ok(Term::Lam(name.text.as_str().into(), icit, Rc::new(result?)))
}

/// `[a: Type] => body` or `[auto h: P] => body` (`lambda`, with its mode),
/// checked against `expected`: it consumes a function type of its own kind,
/// binding the parameter by name. It never has an implicit parameter
/// introduced in front of it: the first parameter of the expected type must
/// be the one it writes (§4.3 of docs/proposals/lambda-syntax.md, D91).
fn check_binder_lambda(
    cx: &mut Ctx,
    expr: &Expr,
    lambda: (&AstName, Mode, &Expr, &Expr),
    expected: &Value,
) -> Result<Term> {
    let (name, mode, ann, body) = lambda;
    let icit = mode_icit(mode);
    match expected {
        Value::Pi(_, found, dom, cod) if *found == icit => {
            typed_lambda(cx, name, icit, ann, body, dom, cod)
        }
        // Not known yet: the lambda's own type settles it.
        Value::Neutral(Head::Meta(_), _) => fallback(cx, expr, expected),
        _ => {
            let takes = match mode {
                Mode::Auto => "an `auto` parameter",
                _ => "an implicit parameter",
            };
            let instead = match expected {
                Value::Pi(_, Icit::Explicit, ..) => "takes an explicit one",
                Value::Pi(_, Icit::Implicit, ..) => "takes an implicit one",
                Value::Pi(_, Icit::Auto, ..) => "takes an `auto` one",
                _ => "isn't a function type",
            };
            let shown = cx.show(expected);
            let error = cx.error(
                "E-TYPE-MISMATCH",
                "type mismatch",
                format!(
                    "this lambda takes {takes} first, but the expected type `{shown}` {instead}"
                ),
            );
            Err(match expected {
                Value::Pi(..) => error.with_note(
                    "a lambda takes its expected type's parameters in order: `[a: …]` takes \
                     `[a: …] -> …`, `[auto h: …]` takes `[auto h: …] -> …`, and `x` or \
                     `(x: …)` takes `(x: …) -> …` (with implicit ones in front of it \
                     introduced for you)",
                ),
                _ => error,
            })
        }
    }
}

pub fn check(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    cx.g().budget.nesting(PASS)?;
    let span = expr.span();
    with_span(cx, span, |cx| {
        let term = check_inner(cx, expr, expected)
            .map_err(|e| crate::numbers::explain_default(cx, e, &[expected]))?;
        cx.e.note_expr(cx, span, expected);
        Ok(Term::Loc(span, Rc::new(term)))
    })
}

fn check_inner(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    if let Expr::Interpolated(text, _) = expr {
        let term = check_inner(cx, text, expected)?;
        cx.e.note_expr(cx, text.span(), expected);
        return Ok(term);
    }
    let g = cx.g();
    let named = expected;
    let expected = force(g, expected.clone())?;
    if cx.e.divergence_case_body() {
        let (term, found) = infer_unrun(cx, expr)?;
        let (term, found) = insert(cx, term, found)?;
        return compare(cx, term, &found, &expected);
    }
    // A computation in a row of abilities: computation mode.
    if !matches!(expr, Expr::Hole(_) | Expr::Goal(_))
        && let Some((row, t)) = effects::comp_parts(cx, &expected)?
    {
        // While its results are unknown (`Comp NoOp ?r Nat`), a computation
        // of its own (`c : Comp NoOp r Nat`) is passed as it is, and decides
        // them; anything else is a computation in the row, whose results
        // are then the row's (SW-851).
        if effects::results_unsettled(cx, &expected)?
            && matches!(
                expr,
                Expr::Var(_) | Expr::App(..) | Expr::Field(..) | Expr::Pipe(..)
            )
            && let Some(term) = crate::undo::attempt(cx, |cx| {
                let (term, found) = infer_unrun(cx, expr)?;
                let (term, found) = insert(cx, term, found)?;
                if effects::is_comp_type(cx, &found)? && cx.unify(&found, &expected)? {
                    Ok(term)
                } else {
                    Err(cx.error("E-TYPE-MISMATCH", "not passed as it is", "here"))
                }
            })?
        {
            return Ok(term);
        }
        if effects::settle_results(cx, &expected)? {
            return effects::comp_check_written(cx, expr, &row, &t);
        }
    }
    if effects::may_perform_at(cx, expr, Some(&expected))? {
        // A computation where a computation whose row isn't known yet is
        // expected (`Effect.bind c k`'s `c`): passed as it is, not run
        // (stage 0 of docs/proposals/effect-polymorphism.md).
        if matches!(
            expr,
            Expr::Var(_) | Expr::App(..) | Expr::Field(..) | Expr::Pipe(..)
        ) && effects::is_comp_type(cx, &expected)?
        {
            let (term, found) = infer_unrun(cx, expr)?;
            let (term, found) = insert(cx, term, found)?;
            return compare(cx, term, &found, &expected);
        }
        let plain = |cx: &mut Ctx| Ok((check_value(cx, expr, &expected)?, expected.clone()));
        return match pure_first(cx, expr, Some(&expected), plain)? {
            PureFirst::Done((term, _)) => Ok(term),
            PureFirst::Run(plain_error) => effects::run_pure(cx, expr, Some(&expected))
                .map(|(term, _)| term)
                .map_err(|e| PureFirst::error(plain_error, e)),
        };
    }
    name_unknown_type(cx, expr, named)?;
    check_value(cx, expr, &expected).or_else(|e| {
        // A `Comp` whose results aren't its row's is a data type, not a
        // computation in the row (SW-851): say why a value didn't fit.
        if e.code != "E-TYPE-MISMATCH" {
            return Err(e);
        }
        let notes = effects::foreign_results_notes(cx, &expected)?;
        Err(notes.into_iter().fold(e, |e, n| e.with_note(n)))
    })
}

/// A variable whose type isn't known yet, checked against a type that names
/// a definition (`free` against `FreeSpace` in `FreeSpace.moveFile free
/// file`, `free` a lambda's parameter): its type is solved with the name
/// before [`check_inner`] forces the expected type to what it unfolds to
/// (`Map Nat (Set Nat)`), so a later `free.moveFile` still looks in
/// `FreeSpace` (SW-846; place 3 of docs/proposals/alias-functions.md). Only
/// for an unknown type: the solution is the same type either way, with its
/// name kept.
fn name_unknown_type(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<()> {
    let Expr::Var(name) = expr else {
        return Ok(());
    };
    if cx.local(&name.text)?.is_some() {
        return Ok(());
    }
    let Some(level) = cx.lookup(&name.text) else {
        return Ok(());
    };
    let g = cx.g();
    let found = cx.types[level].clone();
    if !matches!(
        stitchwort_core::value::force_solved(g, found.clone())?,
        Value::Neutral(Head::Meta(_), _)
    ) {
        return Ok(());
    }
    let named = stitchwort_core::value::force_solved(g, expected.clone())?;
    if matches!(named, Value::Call(..)) {
        // Only a better name for the same type: if it doesn't unify, the
        // ordinary check below reports the mismatch.
        crate::undo::attempt(cx, |cx| crate::undo::unify(cx, &found, &named))?;
    }
    Ok(())
}

/// [`check_inner`] once it's known that `expr` isn't run as a whole, against
/// a forced `expected` that isn't a computation.
fn check_value(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let g = cx.g();
    let expected = expected.clone();
    if let Some(logic) = crate::logic::classify(cx, expr) {
        return crate::logic::check_against(cx, logic, &expected);
    }
    match (expr, &expected) {
        (Expr::Unit(_), Value::Sort(_)) => {
            let unit = builtin_data(cx, Builtin::UnitType)?;
            let found = Value::Sort(Sort::Type(0));
            if cx.unify(&found, &expected)? {
                Ok(Term::Data(unit, Vec::new()))
            } else {
                Err(cx.mismatch(&expected, &found))
            }
        }
        // `()` where a proof of the proposition `Unit` is wanted is its one
        // proof, `Trivial`.
        (Expr::Unit(_), Value::Data(d, _)) if g.registry.is_data(Builtin::Unit, *d) => {
            let (unit, trivial) = builtin_ctor(cx, Builtin::Trivial)?;
            Ok(Term::Ctor(unit, trivial, Vec::new()))
        }
        (Expr::Hole(_), _) => {
            let hole = cx.fresh_meta();
            if let Some(log) = cx.e.hole_log.borrow_mut().as_mut() {
                log.push((hole.clone(), cx.level(), expected.clone()));
            }
            if crate::patlet::proposition(cx, &expected)?
                && let Term::Meta(m) = hole.spine().0
            {
                cx.e.proof_holes.borrow_mut().insert(*m);
            }
            Ok(hole)
        }
        (Expr::Goal(_), _) => Ok(crate::goals::hole(cx, &expected)),
        (Expr::LocalDefs { defs, body, .. }, _) => {
            crate::local::around(cx, defs, |cx| check(cx, body, &expected))
        }
        (
            Expr::Let {
                name,
                ty,
                value,
                body,
                ..
            },
            _,
        ) => Ok(effects::pure_let(cx, name, ty.as_deref(), value, body, Some(&expected))?.0),
        // `(A, B)` where a type is expected is `Pair A B`, and `(a, b)` where
        // a pair is expected is `MkPair a b`.
        (Expr::Tuple(a, b, _), Value::Sort(_)) => {
            let (term, ty) = type_tuple(cx, a, b)?;
            if cx.unify(&ty, &expected)? {
                Ok(term)
            } else {
                Err(cx.mismatch(&expected, &ty))
            }
        }
        (Expr::Tuple(a, b, _), Value::Data(d, params))
            if *d == builtin_data(cx, Builtin::Pair)? =>
        {
            let (pair, mk) = builtin_ctor(cx, Builtin::MkPair)?;
            let a = check(cx, a, &params[0])?;
            let b = check(cx, b, &params[1])?;
            Ok(Term::ctor(pair, mk, vec![a, b]))
        }
        // `[a: Type] => body` and `[auto h: P] => body` take the parameter
        // of the function type they're checked against, rather than having
        // it introduced for them (§4.3 of docs/proposals/lambda-syntax.md).
        (Expr::TypedLam(name, mode, ann, body, _), _) if *mode != Mode::Explicit => {
            check_binder_lambda(cx, expr, (name, *mode, ann, body), &expected)
        }
        // Implicit parameters are introduced automatically.
        (_, Value::Pi(x, icit, dom, cod)) if icit.is_implicit() => {
            let mark = cx.mark();
            let var = Value::var(cx.level());
            cx.bind_hidden(x.clone(), (**dom).clone());
            let result = check(cx, expr, &cod.apply(g, var)?);
            cx.reset(mark);
            Ok(Term::Lam(x.clone(), *icit, Rc::new(result?)))
        }
        // A literal takes its type from what's expected (a `Nat` or an
        // `Int`), and so does arithmetic.
        (Expr::Num(..) | Expr::Neg(..), _) if crate::numbers::literal(expr).is_some() => {
            let (k, negative) = crate::numbers::literal(expr).expect("just checked");
            crate::numbers::check_literal(cx, k, negative, &expected)
        }
        (Expr::Float(..) | Expr::Neg(..), _) if crate::numbers::decimal(expr).is_some() => {
            let (text, negative) = crate::numbers::decimal(expr).expect("just checked");
            crate::numbers::check_decimal(cx, text, negative, &expected)
        }
        (Expr::Binary(BinOp::In(op), a, b), _) => {
            crate::membership::check_member(cx, *op, a, b, &expected)
        }
        (Expr::Binary(op, ..), _) if crate::numbers::is_arith(*op) => {
            Ok(crate::numbers::group(cx, expr, Some(&expected))?.0)
        }
        (Expr::Neg(..), _) => Ok(crate::numbers::group(cx, expr, Some(&expected))?.0),
        (Expr::Match { .. }, _) => crate::matching::check_match(cx, expr, &expected),
        (Expr::Reify { .. }, _) => crate::reify::check_reify(cx, expr, &expected),
        (Expr::Calc { .. }, _) => crate::calc::check_calc(cx, expr, &expected),
        (Expr::Rewrite { .. }, _) => crate::rewrite::check_rewrite(cx, expr, &expected),
        (Expr::Omega { .. }, _) => crate::omega::check_omega(cx, expr, &expected),
        (Expr::Cases { .. }, _) => crate::cases::check_cases(cx, expr, &expected),
        (Expr::Ring { .. }, _) => crate::ring::check_ring(cx, expr, &expected),
        (
            Expr::If {
                binder,
                cond,
                then,
                otherwise,
                ..
            },
            _,
        ) => check_if(cx, binder.as_ref(), cond, then, otherwise, &expected),
        (Expr::Lam(names, body, span), Value::Pi(_, Icit::Explicit, dom, cod)) => {
            if expr.section_name().is_some()
                && let Some(term) = crate::dot::section_partial(cx, expr, dom, &expected)?
            {
                return Ok(term);
            }
            let shadowed = lambda_shadow(cx, names, *span)?;
            let (first, rest) = names.split_first().expect("lambdas have parameters");
            let mark = cx.mark();
            let var = Value::var(cx.level());
            cx.bind(&first.text, (**dom).clone());
            let cod = cod.apply(g, var)?;
            let result = if rest.is_empty() {
                check(cx, body, &cod)
            } else {
                check(cx, &Expr::Lam(rest.to_vec(), body.clone(), *span), &cod)
            };
            cx.reset(mark);
            let result = result.map_err(|d| shadow_note(d, shadowed.as_ref()));
            Ok(Term::Lam(
                first.text.as_str().into(),
                Icit::Explicit,
                Rc::new(result?),
            ))
        }
        (
            Expr::TypedLam(name, Mode::Explicit, ann, body, _),
            Value::Pi(_, Icit::Explicit, dom, cod),
        ) => typed_lambda(cx, name, Icit::Explicit, ann, body, dom, cod),
        (Expr::Lam(names, _, span), _) => {
            let shadowed = lambda_shadow(cx, names, *span)?;
            let error = cx.error(
                "E-TYPE-MISMATCH",
                "type mismatch",
                format!(
                    "this is a function, but the expected type is `{}`",
                    cx.show(&expected)
                ),
            );
            let error = if names.len() == 1 && names[0].text == SECTION {
                // A section inside the body of another section.
                error.with_note(
                    "a section's argument is used once, at the start of the expression: to \
                     use it twice, write the lambda, as in `x => x.f || x.g`",
                )
            } else {
                error
            };
            Err(shadow_note(error, shadowed.as_ref()))
        }
        (Expr::Var(name), Value::Eq(_, a, b))
            if name.text == "rfl" && cx.lookup("rfl").is_none() =>
        {
            if crate::undo::unify(cx, a, b)?
                || crate::lift::await_helpers(cx, a, b, crate::lift::Failure::Refl)?
            {
                Ok(Term::Refl)
            } else {
                // The message shows the sides as the failed comparison left
                // them.
                cx.unify(a, b)?;
                Err(refl_error(cx, a, b))
            }
        }
        (Expr::Var(name), _) if name.text == "rfl" && cx.lookup("rfl").is_none() => Err(cx.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!(
                "`rfl` proves an equation, but the expected type is `{}`",
                cx.show(&expected)
            ),
        )),
        (Expr::List(items, _), Value::Data(d, params)) => {
            let (list, nil) = builtin_ctor(cx, Builtin::Nil)?;
            let (_, cons) = builtin_ctor(cx, Builtin::Cons)?;
            if *d != list {
                return fallback(cx, expr, &expected);
            }
            let elem = params[0].clone();
            // An element type not known yet is settled by the first item
            // that can: if `[Point 1 "p" 10, m]` fails as written, it's
            // checked as `[m, Point …]` (the terms stay in place), so the
            // `1` isn't defaulted to a `Nat` first.
            let unknown = matches!(
                force(cx.g(), elem.clone())?,
                Value::Neutral(Head::Meta(_), _)
            );
            let mut relevant = false;
            if unknown {
                for item in items {
                    relevant |= defers_literal(cx, item)?;
                }
            }
            let terms = if relevant {
                retrying(cx, |cx| check_items(cx, items, &elem))?
            } else {
                check_items(cx, items, &elem)?
            };
            // A long literal would be a `Cons` chain as deep as it is long,
            // and every pass over terms recurses on that depth (the checker,
            // zonking, lowering, code generation, …): so it's cut into chunks
            // joined by a balanced tree of `append`s, which is as deep as a
            // chunk plus the logarithm of their number (SW-62).
            // Chunking is a fallback: evaluating the `append`s costs about
            // 200 steps an element, so a literal that fits the stack as one
            // chain stays one (SW-332: `rfl` on a 20,000-element literal got
            // six times dearer).
            let chunk = if terms.len() <= cx.e.limits.stack / LITERAL_BYTES {
                usize::MAX
            } else {
                LITERAL_CHUNK
            };
            let mut chunks: Vec<Term> = terms
                .chunks(chunk)
                .map(|chunk| {
                    let mut term = Term::Ctor(list, nil, Vec::new());
                    for item in chunk.iter().rev() {
                        term = Term::ctor(list, cons, vec![item.clone(), term]);
                    }
                    term
                })
                .collect();
            if chunks.len() > 1 {
                let append = Term::app_icit(
                    Term::Def(builtin_def(cx, Builtin::Append)?),
                    cx.quote_folded(&elem)?,
                    Icit::Implicit,
                );
                while chunks.len() > 1 {
                    let mut joined = Vec::with_capacity(chunks.len().div_ceil(2));
                    let mut pairs = chunks.into_iter();
                    while let Some(a) = pairs.next() {
                        joined.push(match pairs.next() {
                            Some(b) => Term::app(Term::app(append.clone(), a), b),
                            None => a,
                        });
                    }
                    chunks = joined;
                }
            }
            Ok(chunks
                .pop()
                .unwrap_or_else(|| Term::Ctor(list, nil, Vec::new())))
        }
        (Expr::Var(_) | Expr::App(..), Value::Data(..) | Value::Pi(_, Icit::Explicit, _, _)) => {
            match ctor_head(cx, expr)? {
                // A constructor where an effectful function is expected
                // (`List.map Succ xs`) is a pure function, made to fit the
                // row by `compare` (SW-393).
                Some((d, _, _))
                    if Some(d) != cx.g().registry.data(Builtin::Comp)
                        && returns_computation(cx, &expected)? =>
                {
                    fallback(cx, expr, &expected)
                }
                Some((d, c, args)) => {
                    let (term, ty) = ctor_app(cx, d, c, &args, Some(&expected))?;
                    if cx.unify(&ty, &expected)? {
                        Ok(term)
                    } else {
                        Err(cx.mismatch(&expected, &ty))
                    }
                }
                None => fallback(cx, expr, &expected),
            }
        }
        (Expr::Record { base, fields, .. }, _) => {
            records::check_record(cx, base.as_deref(), fields, &expected)
        }
        (Expr::CtorFields { ctor, fields, span }, _) => {
            match records::ctor_fields(cx, ctor, fields, *span, Some(&expected))? {
                records::Construction::Positional(positional) => {
                    check_inner(cx, &positional, &expected)
                }
                records::Construction::Defaults(d, c) => {
                    Ok(crate::defaults::ctor_with_defaults(cx, d, c, fields, Some(&expected))?.0)
                }
            }
        }
        // A quotient form, with the expected type to find its implicit
        // arguments from.
        (Expr::Var(_) | Expr::App(..), _) if crate::quot::applied(cx, expr).is_some() => {
            let (form, args) = crate::quot::applied(cx, expr).expect("just checked");
            let (term, ty) = crate::quot::elaborate(cx, form, &args, Some(&expected))?;
            compare(cx, term, &ty, &expected)
        }
        _ => fallback(cx, expr, &expected),
    }
}

/// `'a'` is `MkChar 97 rfl`: the kernel checks that 97 is a scalar value by
/// computing `isScalar 97`.
fn char_term(cx: &Ctx, c: char) -> Result<Term> {
    let (char_data, mk_char) = builtin_ctor(cx, Builtin::MkChar)?;
    let code = Term::Nat(Rc::new(u32::from(c).into()));
    Ok(Term::ctor(char_data, mk_char, vec![code, Term::Refl]))
}

/// `a ++ b`: `textAppend` for texts, `append` for lists, chosen by the type of
/// whichever side can be inferred.
/// A record literal in `a` takes its type from `b` if `b` can say it
/// (`records::last_resort`).
fn append(cx: &mut Ctx, a: &Expr, b: &Expr) -> Result<(Term, Value)> {
    crate::records::last_resort(cx, |cx| append_tried(cx, a, b))
}

fn append_tried(cx: &mut Ctx, a: &Expr, b: &Expr) -> Result<(Term, Value)> {
    let first = crate::records::held(cx, |cx| infer(cx, a).and_then(|(t, ty)| insert(cx, t, ty)));
    let (a, b, ty) = match first {
        Ok((a, ty)) => (a, check(cx, b, &ty)?, ty),
        Err(e) if e.code == "E-CANNOT-INFER" => {
            let (b, ty) = infer(cx, b)?;
            let (b, ty) = insert(cx, b, ty)?;
            (check(cx, a, &ty)?, b, ty)
        }
        Err(e) => return Err(e),
    };
    let text = builtin_data(cx, Builtin::Text)?;
    let list = builtin_data(cx, Builtin::List)?;
    let head = match force(cx.g(), ty.clone())? {
        Value::Data(d, _) if d == text => Term::Def(builtin_def(cx, Builtin::TextAppend)?),
        Value::Data(d, params) if d == list => {
            let elem = cx.quote_folded(&params[0])?;
            Term::app_icit(
                Term::Def(builtin_def(cx, Builtin::Append)?),
                elem,
                Icit::Implicit,
            )
        }
        other => {
            let other = cx.show(&other);
            return Err(cx.error(
                "E-TYPE-MISMATCH",
                "`++` joins two texts or two lists",
                format!("this is {} `{}`", crate::article(&other), other),
            ));
        }
    };
    Ok((Term::app(Term::app(head, a), b), ty))
}

/// `if c then a else b` is `ifThenElse c (_ => a) (_ => b)`, and
/// `if h : P then a else b` is `elimDec (decision for P) (h => a) (h => b)`.
/// The branches are functions so only the chosen one is evaluated.
///
/// `if c` with no binder where `c` isn't a `Bool` but a proposition is
/// `if _ : c` (as in Lean): `if x < y`. The `Bool` reading is tried first,
/// exactly as before, so a `Bool` condition elaborates as it always has;
/// only if it fails is everything it did undone and `c` tried as a
/// proposition. If that fails too, the `Bool` reading's error is reported,
/// unless `c` is a proposition with no decision procedure.
pub(crate) fn check_if(
    cx: &mut Ctx,
    binder: Option<&AstName>,
    cond: &Expr,
    then: &Expr,
    otherwise: &Expr,
    expected: &Value,
) -> Result<Term> {
    let unknown = matches!(
        force(cx.g(), expected.clone())?,
        Value::Neutral(Head::Meta(_), _)
    );
    // `ifThenElse` and `elimDec` return a `Type`, so an `if` whose branches
    // prove a proposition would fail with a universe mismatch that says
    // nothing useful: say what's going on.
    if crate::omega::is_prop(cx, expected)? == Some(true) {
        return Err(cx.error(
            "E-UNIVERSE",
            "`if` can't choose between proofs yet",
            "this `if` has proofs as its branches; use `match b with | True => … | False => …`",
        ));
    }
    if unknown && defers_literal(cx, then)? {
        return retrying(cx, |cx| {
            check_if_in(cx, binder, cond, then, otherwise, expected)
        });
    }
    check_if_in(cx, binder, cond, then, otherwise, expected)
}

fn check_if_in(
    cx: &mut Ctx,
    binder: Option<&AstName>,
    cond: &Expr,
    then: &Expr,
    otherwise: &Expr,
    expected: &Value,
) -> Result<Term> {
    let result_ty = cx.quote_folded(expected)?;
    let branch = |cx: &mut Ctx, name: &str, ty: Value, body: &Expr| -> Result<Term> {
        let mark = cx.mark();
        cx.bind(name, ty);
        let result = check(cx, body, expected);
        cx.reset(mark);
        Ok(Term::Lam(name.into(), Icit::Explicit, Rc::new(result?)))
    };
    match binder {
        None => {
            let unit_data = builtin_data(cx, Builtin::Unit)?;
            let cond = match crate::logic::condition(cx, cond, "if")? {
                crate::logic::Condition::Bool(cond) => cond,
                crate::logic::Condition::Decided { prop, decision } => {
                    let as_bool = decision.clone();
                    let decision = decision.term(cx)?;
                    let decided = decided_if(
                        cx,
                        "_",
                        prop.clone(),
                        decision,
                        result_ty.clone(),
                        &branch,
                        then,
                        otherwise,
                    )?;
                    return unused_proof_if(cx, decided, as_bool, prop, result_ty);
                }
            };
            let unit = Value::Data(unit_data, Vec::new());
            let unknown = matches!(
                force(cx.g(), expected.clone())?,
                Value::Neutral(Head::Meta(_), _)
            );
            let (then, otherwise) = if else_first(cx, then, otherwise, unknown)? {
                let otherwise = branch(cx, "_", unit.clone(), otherwise)?;
                (branch(cx, "_", unit, then)?, otherwise)
            } else {
                let then = branch(cx, "_", unit.clone(), then)?;
                (then, branch(cx, "_", unit, otherwise)?)
            };
            let ite = builtin_def(cx, Builtin::IfThenElse)?;
            let head = Term::app_icit(Term::Def(ite), result_ty, Icit::Implicit);
            Ok(Term::app(Term::app(Term::app(head, cond), then), otherwise))
        }
        Some(h) => {
            let (prop, sort) = check_type(cx, cond).map_err(|e| {
                if e.code == "E-NOT-A-TYPE" {
                    e.with_note("`if h: P` needs a proposition `P`; for a `Bool`, write `if c then … else …`")
                } else if is_true_test(cond) {
                    e.with_note(format!(
                        "in `if {}: …` the guard is already a proposition: write `if {}: a < b then` \
                         for `a < b`, without `= True`",
                        h.text, h.text
                    ))
                } else {
                    e
                }
            })?;
            if sort != Sort::Prop {
                return Err(cx.error(
                    "E-TYPE-MISMATCH",
                    "`if h: …` needs a proposition",
                    "this is a type of data; use `if c then … else …` for a `Bool`",
                ));
            }
            let decision = crate::bind::decide(cx, &prop)?.term(cx)?;
            decided_if(
                cx, &h.text, prop, decision, result_ty, &branch, then, otherwise,
            )
        }
    }
}

/// Whether `cond` is `… = True`, an `if h:` guard written as a `Bool` test.
fn is_true_test(cond: &Expr) -> bool {
    match cond {
        Expr::Binary(BinOp::Eq, _, rhs) => matches!(&**rhs, Expr::Var(x) if x.text == "True"),
        Expr::Bracketed(inner, _) => is_true_test(inner),
        _ => false,
    }
}

/// `if c then a else b` on a decided proposition `c` whose branches don't
/// use the proof: `ifThenElse` on the decision's `Bool`, the term a `Bool`
/// is expected (`filter (x => x < k)`) gives, so lemmas stated with a
/// `Bool` test match. `decided` (the `elimDec` form) where a branch uses
/// the proof (an `auto` argument found from it) or may yet.
fn unused_proof_if(
    cx: &mut Ctx,
    decided: Term,
    decision: crate::bind::Decision,
    prop: Term,
    result_ty: Term,
) -> Result<Term> {
    let Term::App(rest, otherwise, _) = &decided else {
        return Ok(decided);
    };
    let Term::App(_, then, _) = &**rest else {
        return Ok(decided);
    };
    let level = cx.level();
    let zonked = |cx: &Ctx, branch: &Term| -> Result<Term> {
        crate::unify::zonk_in(cx.g(), level, branch, &|_| true, &[]).map_err(|e| match e {
            crate::unify::ZonkError::Resource(e) => Diagnostic::from(e),
            crate::unify::ZonkError::Unsolved(_) => {
                unreachable!("every unsolved metavariable is kept")
            }
        })
    };
    let uses_proof = |branch: &Term| match branch.strip_loc() {
        Term::Lam(_, _, body) => body.mentions(0),
        _ => true,
    };
    let mut branches = [zonked(cx, then)?, zonked(cx, otherwise)?];
    // An unsolved metavariable is applied to the proof, as to every
    // variable in scope. Instances whose type is known are found now, so
    // that one that doesn't use the proof doesn't count as using it.
    if branches.iter().any(uses_proof) {
        let unsolved: Vec<usize> = (branches.iter())
            .flat_map(|b| b.subterms().map(|(t, _)| t))
            .filter_map(|t| match t {
                Term::Meta(m) => Some(*m),
                _ => None,
            })
            .collect();
        if unsolved.is_empty() || !cx.e.solve_ready_instances_keeping(&[], Some(&unsolved))? {
            return Ok(decided);
        }
        branches = [zonked(cx, then)?, zonked(cx, otherwise)?];
        if branches.iter().any(uses_proof) {
            return Ok(decided);
        }
    }
    let cond = decision.into_bool(cx, prop)?;
    let ite = builtin_def(cx, Builtin::IfThenElse)?;
    let head = Term::app_icit(Term::Def(ite), result_ty, Icit::Implicit);
    Ok(Term::app(
        Term::app(Term::app(head, cond), (**then).clone()),
        (**otherwise).clone(),
    ))
}

/// `elimDec decision (name => then) (name => otherwise)`, where `decision`
/// decides `prop`: `name` is a proof of `prop` in `then` and of `Not prop`
/// in `otherwise`.
#[allow(clippy::too_many_arguments)]
fn decided_if(
    cx: &mut Ctx,
    name: &str,
    prop: Term,
    decision: Term,
    result_ty: Term,
    branch: &dyn Fn(&mut Ctx, &str, Value, &Expr) -> Result<Term>,
    then: &Expr,
    otherwise: &Expr,
) -> Result<Term> {
    // The branches' assumptions need the proposition's value (that's what
    // a proof in them is about); `Not prop` reuses it rather than
    // computing it again.
    let prop_value = cx.eval(&prop)?;
    let not = builtin_def(cx, Builtin::Not)?;
    let not_prop =
        stitchwort_core::value::apply(cx.g(), cx.eval(&Term::Def(not))?, prop_value.clone())?;
    let (then, otherwise) = if else_first(
        cx,
        then,
        otherwise,
        matches!(result_ty.strip_loc().spine().0, Term::Meta(_)),
    )? {
        let otherwise = branch(cx, name, not_prop, otherwise)?;
        (branch(cx, name, prop_value, then)?, otherwise)
    } else {
        let then = branch(cx, name, prop_value, then)?;
        (then, branch(cx, name, not_prop, otherwise)?)
    };
    let elim = builtin_def(cx, Builtin::ElimDec)?;
    let head = Term::app_icit(
        Term::app_icit(Term::Def(elim), prop, Icit::Implicit),
        result_ty,
        Icit::Implicit,
    );
    Ok(Term::app(
        Term::app(Term::app(head, decision), then),
        otherwise,
    ))
}

/// Checks `expr` by inferring its type and comparing. An application whose
/// result type is known before its arguments are checked is compared with
/// `expected` first, so the arguments are checked knowing more
/// (docs/proposals/syntax-conveniences.md §7).
/// Whether `ty` is a function type whose result, after all its explicit
/// arguments, is a computation (`a -> {e} b`, `a -> b -> {Fail} c`). Not
/// when that is a `CompIn ?e b` whose row is still unknown: the row rule
/// settles it once the constructor's type is compared with it, so the
/// constructor is checked against `b` as any other (`xs.map (Cons { … })`).
fn returns_computation(cx: &mut Ctx, ty: &Value) -> Result<bool> {
    let g = cx.g();
    let mark = cx.mark();
    let mut ty = force(g, ty.clone())?;
    let mut any = false;
    let result = (|| -> Result<bool> {
        while let Value::Pi(x, Icit::Explicit, dom, cod) = ty {
            let v = Value::var(cx.level());
            cx.bind_hidden(x, (*dom).clone());
            ty = force(g, cod.apply(g, v)?)?;
            any = true;
        }
        Ok(any
            && effects::comp_parts(cx, &ty)?.is_some()
            && effects::unknown_bare_value(cx, &ty)?.is_none())
    })();
    cx.reset(mark);
    result
}

fn fallback(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    // `[1, 2] |> List.map (x => x)` is the call `List.map [1, 2] (x => x)`
    // (D304), and checked as one, so a literal on the left takes its type
    // from the expected type and the other arguments as it would there.
    if let Expr::Pipe(value, f) = expr
        && literal_value(value)
        && !matches!(&**f, Expr::Lam(..) | Expr::TypedLam(..))
    {
        let call = crate::pipe::as_call((**value).clone(), f);
        return fallback(cx, &call, expected);
    }
    if cx.e.no_propagation.get() == 0
        && let Some(found) = propagate(cx, expr, expected)?
    {
        return found;
    }
    let (term, found) = infer_expecting(cx, expr, expected)?;
    let (term, found) = insert(cx, term, found)?;
    if let Some(term) = decide_to_bool(cx, expr, &term, &found, expected)? {
        return Ok(term);
    }
    match compare(cx, term, &found, expected) {
        Err(e) if e.code == "E-TYPE-MISMATCH" && matches!(expr, Expr::App(..)) => {
            let e = awaiting_note(cx, e, expr, &found, expected);
            Err(extra_negative_argument_note(cx, e, expr, &found, expected))
        }
        result => result,
    }
}

/// An application whose last argument is an unbracketed negative argument
/// (`k x -1`), checked against a function type, where the application itself
/// isn't a function: the `-1` was meant as a subtraction, or the function has
/// one parameter fewer than the call supposes (D1467). The error is a
/// mismatch at the result, not `E-NOT-A-FUNCTION`, so it gets the same note.
fn extra_negative_argument_note(
    cx: &Ctx,
    e: Diagnostic,
    expr: &Expr,
    found: &Value,
    expected: &Value,
) -> Diagnostic {
    let g = cx.g();
    let is_function =
        |v: &Value| matches!(force(g, v.clone()), Ok(Value::Pi(_, Icit::Explicit, ..)));
    if !is_function(expected) || is_function(found) {
        return e;
    }
    let Some(Arg::Explicit(last) | Arg::NamedExplicit(_, last)) = spine(expr).1.last().copied()
    else {
        return e;
    };
    match negative_argument_note(last) {
        Some(note) => e.with_note(note),
        None => e,
    }
}

/// [`infer`]s the application `expr`, which is checked against `expected`
/// afterwards: a lambda argument that fails where its type has unknowns is
/// checked again after the application's type is compared with `expected`
/// (`apply_args_postponing`). Its result type may depend on the arguments, so it
/// couldn't be compared first (`propagate`): `List.mapCong _ _ xs (x => …)`
/// against `List.map f xs = List.map g xs`.
fn infer_expecting(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<(Term, Value)> {
    let key = match spine(expr).1.last() {
        Some(Arg::Explicit(last) | Arg::NamedExplicit(_, last)) => {
            std::ptr::from_ref(*last) as usize
        }
        _ => return infer(cx, expr),
    };
    if matches!(
        force(cx.g(), expected.clone())?,
        Value::Neutral(Head::Meta(_), _)
    ) {
        return infer(cx, expr);
    }
    let outer = cx.e.app_expected.replace(Some((key, expected.clone())));
    let result = infer(cx, expr);
    *cx.e.app_expected.borrow_mut() = outer;
    result
}

/// A call that is still a function where something else is expected (a
/// partial application, or a call with parameters left out): the note
/// names what it's waiting for (docs/proposals/named-arguments.md §6.3).
fn awaiting_note(
    cx: &Ctx,
    e: Diagnostic,
    expr: &Expr,
    found: &Value,
    expected: &Value,
) -> Diagnostic {
    let g = cx.g();
    let is_function =
        |v: &Value| matches!(force(g, v.clone()), Ok(Value::Pi(_, Icit::Explicit, ..)));
    if !is_function(found)
        || is_function(expected)
        || matches!(
            force(g, expected.clone()),
            Ok(Value::Neutral(Head::Meta(_), _))
        )
    {
        return e;
    }
    let Ok(sig) = crate::named::signature(cx, found) else {
        return e;
    };
    let explicit: Vec<&crate::named::Param> = (sig.params.iter())
        .filter(|p| p.icit == Icit::Explicit)
        .collect();
    let named: Vec<String> = (explicit.iter())
        .filter(|p| !p.name.is_empty() && &*p.name != "_" && !p.name.starts_with('%'))
        .map(|p| format!("`{}`", p.name))
        .collect();
    let waiting = if named.len() == explicit.len() && !named.is_empty() {
        crate::named::list(named)
    } else if explicit.len() == 1 {
        "one more argument".to_string()
    } else {
        format!("{} more arguments", explicit.len())
    };
    let filled = crate::defaults::filled_by_call(cx, expr);
    let filled = if filled.is_empty() {
        String::new()
    } else {
        format!("; {}", filled.join("; "))
    };
    e.with_note(format!(
        "this expression is a function still waiting for {waiting}{filled}"
    ))
}

/// Where a `Bool` is expected, a proposition with a decision procedure is
/// decided, as Lean's `decide` coercion does: `term : Prop` becomes
/// `Decidable.toBool {term} decision`, so `List.filter (n => n <= k) xs`
/// works. `None` (nothing done) unless `expected` is the library's `Bool`
/// and `found` is `Prop`, so other comparisons don't pay for it. A
/// condition (`if c`, `&&` …) whose `Bool` reading is being tried isn't
/// decided here: its proposition reading decides it (`logic::condition`).
fn decide_to_bool(
    cx: &mut Ctx,
    expr: &Expr,
    term: &Term,
    found: &Value,
    expected: &Value,
) -> Result<Option<Term>> {
    if cx.e.condition.get() == std::ptr::from_ref(expr) as usize
        || !matches!(force(cx.g(), found.clone())?, Value::Sort(Sort::Prop))
    {
        return Ok(None);
    }
    if !matches!(force(cx.g(), expected.clone())?,
        Value::Data(d, _) if cx.g().registry.is_data(Builtin::Bool, d))
    {
        return Ok(None);
    }
    let decision = match crate::bind::decide(cx, term) {
        Ok(decision) => decision,
        Err(mut e) if e.code == "E-AUTO-NONE" && !e.notes.is_empty() => {
            e.labels.clear();
            e.notes[0] = "a `Bool` is expected here, and a proposition is turned into one only \
                          if it has a decision procedure: an `instance` returning `Decidable …`"
                .into();
            // A variable the compiler made (holding what an operation run
            // first returned) has no name to show.
            if let Term::Var(ix) = term.strip_loc()
                && let Some(level) = cx.names.len().checked_sub(ix + 1)
                && cx.names[level].starts_with('%')
            {
                e.message = "no way to decide this proposition".into();
            }
            return Err(e.with_label(expr.span(), "this is a proposition, and nothing decides it"));
        }
        Err(e) => return Err(e),
    };
    Ok(Some(decision.into_bool(cx, term.clone())?))
}

/// `term`, of type `found`, where `expected` is expected.
pub(crate) fn compare(cx: &mut Ctx, term: Term, found: &Value, expected: &Value) -> Result<Term> {
    if crate::undo::unify(cx, found, expected)? {
        return Ok(term);
    }
    // A dictionary still to be found may be what's in the way (`List.sort xs`
    // against its value for `Nat`): find those whose type is known by now,
    // and compare again (docs/proposals/interfaces.md, "As built (stage 3)").
    // (Read back and computed again: a projection stuck on the dictionary's
    // metavariable takes its step now.)
    // (Or found already, by the application that made it: then a side may
    // still be stuck on it.)
    let ready = cx.e.solve_ready_instances()?;
    if ready
        || (!cx.e.interfaces.is_empty()
            && (crate::interfaces::stuck_on_found(cx, found)?
                || crate::interfaces::stuck_on_found(cx, expected)?))
    {
        let found = crate::interfaces::refresh(cx, found)?;
        let expected = crate::interfaces::refresh(cx, expected)?;
        if crate::undo::unify(cx, &found, &expected)? {
            return Ok(term);
        }
    }
    // A dictionary whose type only this comparison fixes (`List.sumByZero xs`
    // against `List.sumBy xs (x => 0) = 0`: only the expected type says the
    // sum is of `Nat`s). Two calls of one definition are compared by their
    // arguments only if that solves nothing, so the dictionary is compared
    // inside its unfolding (`Add.zero ?add` against `0`), fails, and the
    // types it learnt are undone with the rest. Kept here, they make the
    // dictionary ready to find; all of it is undone unless the comparison
    // then succeeds.
    if !cx.e.interfaces.is_empty()
        && crate::undo::transaction(cx, |cx| {
            cx.unify(found, expected)?;
            if !cx.e.solve_ready_instances()? {
                return Ok(None);
            }
            let found = crate::interfaces::refresh(cx, found)?;
            let expected = crate::interfaces::refresh(cx, expected)?;
            Ok(cx.unify(&found, &expected)?.then_some(()))
        })?
        .is_some()
    {
        return Ok(term);
    }
    // An effectful function whose row lists the same abilities in a
    // different order, or a total one where a partial one is expected.
    if let Some(term) =
        crate::undo::transaction(cx, |cx| effects::coerce(cx, &term, found, expected))?
    {
        return Ok(term);
    }
    // A computation type over a row unknown, against a type that may yet
    // compute to a `Comp`: decided later (docs/proposals/effect-polymorphism.md
    // §5.C.1, step 5).
    if crate::rows::postpone(cx, found, expected)? {
        return Ok(term);
    }
    // A `match` not lifted yet, against the same `match` elsewhere (a
    // finished helper's call): compared again once it is lifted.
    if crate::lift::await_helpers(cx, found, expected, crate::lift::Failure::Mismatch)? {
        return Ok(term);
    }
    // The message shows the types as the failed comparison left them, as it
    // always has: repeat it, keeping what it solved before failing.
    cx.unify(found, expected)?;
    if let Some(d) = effects::partial_mismatch(cx, found, expected)? {
        Err(d)
    } else {
        Err(crate::numbers::explain_default(
            cx,
            cx.mismatch(expected, found),
            &[found],
        ))
    }
}

/// Checks the application `expr` against `expected`, comparing its result
/// type with `expected` first (§7.2); `None` if that doesn't apply: `expr`
/// isn't an application of a variable or a definition, or its result type
/// depends on the arguments written or isn't known, or doesn't match
/// `expected` (and then nothing has changed). If it applies but the
/// application then fails, everything is undone and the application is
/// elaborated again the old way, with no propagation inside, and that way's
/// result is the answer: so a program rejected before keeps its message
/// (§7.4).
/// `args`, applied to a function of type `ty`, in their parameters' places
/// (`named::plan`), if they match and leave no parameter out: for the
/// speculative walks that elaborate a call as its positional form would be.
pub(crate) fn ordered_args<'a>(
    cx: &Ctx,
    ty: &Value,
    args: &[Arg<'a>],
) -> Result<Option<Vec<Arg<'a>>>> {
    let sig = crate::named::signature(cx, ty)?;
    if crate::named::split(cx, &sig, args)?.is_some() {
        return Ok(None);
    }
    Ok(match crate::named::plan(cx, &sig, args, None) {
        Ok(slots) => crate::named::positional(&slots),
        Err(_) => None,
    })
}

fn propagate(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Option<Result<Term>>> {
    if matches!(
        force(cx.g(), expected.clone())?,
        Value::Neutral(Head::Meta(_), _)
    ) {
        return Ok(None);
    }
    let (head, mut args) = spine(expr);
    if args.is_empty() && !matches!(head, Expr::Field(..)) {
        return Ok(None);
    }
    let dotted;
    let (head, args) = if let Expr::Field(recv, field) = head {
        // `recv.f a` is `T.f … recv …` (SW-129).
        let Some((head, full)) = crate::dot::prefix_form(cx, recv, field, &args)? else {
            return Ok(None);
        };
        dotted = full;
        (head, &dotted)
    } else {
        let Some(head) = known_head(cx, head) else {
            return Ok(None);
        };
        // A call that fills defaults is elaborated the ordinary way.
        if crate::defaults::of_head(cx, &head.0).is_some() {
            return Ok(None);
        }
        // Named arguments in their places; a call with a parameter left
        // out (a function) or arguments that don't match is elaborated
        // the ordinary way.
        if crate::named::any(&args) {
            let Some(ordered) = ordered_args(cx, &head.1, &args)? else {
                return Ok(None);
            };
            args = ordered;
        }
        (head, &args)
    };
    let snapshot = crate::undo::Snapshot::take(cx);
    let Some((written, mut supply)) = written_result(cx, &head.1, args)? else {
        snapshot.restore(cx);
        return Ok(None);
    };
    // A result in a bare row not known yet (`List.map`'s `{e} (List b)`):
    // its value type is compared, and the row is left to the arguments, so a
    // callback with abilities makes it effectful (D1124) before the
    // comparison at the end settles it.
    let written = effects::unknown_bare_value(cx, &written)?.unwrap_or(written);
    if !cx.unify(&written, expected)? {
        snapshot.restore(cx);
        return Ok(None);
    }
    // As `infer` and then `insert` would, for the application.
    let span = expr.span();
    let result = (|| -> Result<Term> {
        cx.g().budget.nesting(PASS)?;
        let (term, found) = apply_args_with(cx, head, args, &mut supply)?;
        let term = Term::Loc(span, Rc::new(term));
        let (term, found) = insert_with(cx, term, found, &mut supply)?;
        if !supply.is_empty() {
            // The types as elaborated didn't line up with the walk's.
            return Err(Diagnostic::error(
                "E-PROPAGATE",
                "unused implicit arguments",
            ));
        }
        compare(cx, term, &found, expected)
    })();
    match result {
        Ok(term) => Ok(Some(Ok(term))),
        Err(e) if crate::undo::fatal(&e) => Err(e),
        Err(propagated) => {
            snapshot.restore(cx);
            let off = &cx.e.no_propagation;
            off.set(off.get() + 1);
            let old = (|| {
                let (term, found) = infer(cx, expr)?;
                let (term, found) = insert(cx, term, found)?;
                compare(cx, term, &found, expected)
            })();
            let off = &cx.e.no_propagation;
            off.set(off.get() - 1);
            // Both fail inside the same lambda argument: the first knew what
            // the lambda must prove, where the second only had unknowns.
            match old {
                Err(old)
                    if !crate::undo::fatal(&old) && in_same_lambda(args, &propagated, &old) =>
                {
                    Ok(Some(Err(propagated)))
                }
                old => Ok(Some(old)),
            }
        }
    }
}

/// Whether the errors `first` and `second` both point inside the same
/// lambda among `args`.
fn in_same_lambda(args: &[Arg], first: &Diagnostic, second: &Diagnostic) -> bool {
    let (Some(first), Some(second)) = (first.labels.first(), second.labels.first()) else {
        return false;
    };
    let inside = |outer: Span, inner: Span| {
        outer.file == inner.file && outer.start <= inner.start && inner.end <= outer.end
    };
    args.iter().any(|arg| match arg {
        Arg::Explicit(lambda @ (Expr::Lam(..) | Expr::TypedLam(..))) => {
            inside(lambda.span(), first.span) && inside(lambda.span(), second.span)
        }
        _ => false,
    })
}

/// [`propagate`] for an effectful call (`effects::comp_app`): `head`, a
/// function of type `ty`, applied to `args` (already free of operations,
/// and in parameter order), whose result is a computation expected to
/// return an `expected`. That value type is compared with `expected` before
/// the arguments are checked, as a pure call's whole result type is, so
/// `Abort.orElse 0 (() => …)` at `Int` checks the `0` as an `Int` (SW-223). The row isn't compared: the
/// caller fits it to its own by lifting. `None` if that doesn't apply (no
/// arguments, an unknown `expected`, a result type that depends on the
/// arguments or isn't a computation, or a value type that doesn't match), or
/// if the application then fails: everything is undone, and the caller
/// applies the arguments as before, so a rejected program keeps its message.
pub(crate) fn propagate_comp(
    cx: &mut Ctx,
    head: &(Term, Value),
    args: &[Arg],
    expected: &Value,
) -> Result<Option<(Term, Value)>> {
    if args.is_empty()
        || cx.e.no_propagation.get() != 0
        || matches!(
            force(cx.g(), expected.clone())?,
            Value::Neutral(Head::Meta(_), _)
        )
    {
        return Ok(None);
    }
    let snapshot = crate::undo::Snapshot::take(cx);
    let Some((written, mut supply)) = written_result(cx, &head.1, args)? else {
        snapshot.restore(cx);
        return Ok(None);
    };
    let Some((_, value)) = effects::comp_parts(cx, &written)? else {
        snapshot.restore(cx);
        return Ok(None);
    };
    if !cx.unify(&value, expected)? {
        snapshot.restore(cx);
        return Ok(None);
    }
    let result = (|| -> Result<(Term, Value)> {
        let (term, found) = apply_args_with(cx, head.clone(), args, &mut supply)?;
        let (term, found) = insert_with(cx, term, found, &mut supply)?;
        if !supply.is_empty() {
            // The types as elaborated didn't line up with the walk's.
            return Err(Diagnostic::error(
                "E-PROPAGATE",
                "unused implicit arguments",
            ));
        }
        Ok((term, found))
    })();
    match result {
        Ok(found) => Ok(Some(found)),
        Err(e) if crate::undo::fatal(&e) => Err(e),
        Err(_) => {
            snapshot.restore(cx);
            Ok(None)
        }
    }
}

/// `W-LAMBDA-SHADOW` (docs/proposals/lambda-syntax.md §7.2): a lambda with two
/// or more parameters whose first is a plain name that, in the scope around
/// the lambda, is a function: `map x => …` where `map (x => …)` was probably
/// meant. Returns the lambda's first two parameters then, and records the
/// warning (once per lambda). Called for the lambda as written, not for the
/// rest of its parameters that checking peels off one at a time.
fn lambda_shadow(cx: &Ctx, names: &[AstName], span: Span) -> Result<Option<(AstName, AstName)>> {
    let [first, second, ..] = names else {
        return Ok(None);
    };
    // A pattern parameter is named `%arg…`, and `_` hides nothing; the first
    // parameter is the lambda's first token, unless a typed parameter came
    // before it.
    if first.text.starts_with('%') || first.text == "_" || first.span.start != span.start {
        return Ok(None);
    }
    if !names_a_function(cx, &first.text)? {
        return Ok(None);
    }
    let mut seen = cx.e.lambda_warnings.borrow_mut();
    if !seen
        .iter()
        .any(|w| w.labels.first().is_some_and(|l| l.span == first.span))
    {
        seen.push(
            Diagnostic::warning(
                "W-LAMBDA-SHADOW",
                format!(
                    "this lambda's first parameter `{}` hides the function `{}`",
                    first.text,
                    hidden_function_name(cx, &first.text)
                ),
            )
            .with_label(first.span, format!("`{}` is a parameter here", first.text))
            .with_note(shadow_advice(first, second)),
        );
    }
    Ok(Some((first.clone(), second.clone())))
}

/// The function `name` names, in full where it's declared outside the
/// module (`Parse.span` for `span`), so a name brought in unqualified says
/// where it's from.
fn hidden_function_name(cx: &Ctx, name: &str) -> String {
    if cx.local(name).ok().flatten().is_some() || cx.lookup(name).is_some() {
        return name.to_string();
    }
    match cx.e.resolve(name) {
        scope::Resolved::Found { key, rest, .. }
            if rest.is_empty() && key.strip_prefix(cx.e.namespace_root.as_str()) != Some(name) =>
        {
            scope::display(key).to_string()
        }
        _ => name.to_string(),
    }
}

fn shadow_advice(first: &AstName, second: &AstName) -> String {
    format!(
        "if you meant to pass a lambda to `{0}`, put it in brackets: `{0} ({1} => …)`; \
         otherwise rename the parameter",
        first.text, second.text
    )
}

/// `d`, with `W-LAMBDA-SHADOW`'s advice added if it was reported inside or at
/// a lambda that shadows a function.
fn shadow_note(d: Diagnostic, shadowed: Option<&(AstName, AstName)>) -> Diagnostic {
    match shadowed {
        Some((first, second)) => {
            let advice = shadow_advice(first, second);
            if d.notes.contains(&advice) {
                d
            } else {
                d.with_note(advice)
            }
        }
        None => d,
    }
}

/// Whether `name`, as seen from where the lambda starts, is a function: a
/// local variable or local definition whose type is one, a definition or
/// ability operation, or a definition of this module not checked yet that is
/// declared with a function type.
fn names_a_function(cx: &Ctx, name: &str) -> Result<bool> {
    let g = cx.g();
    let is_pi = |ty: &Value| -> Result<bool> { Ok(matches!(force(g, ty.clone())?, Value::Pi(..))) };
    if let Some((_, ty)) = cx.local(name)? {
        return is_pi(&ty);
    }
    if let Some(level) = cx.lookup(name) {
        return is_pi(&cx.types[level]);
    }
    match cx.e.named(name) {
        Some((Global::Def(id), _)) => is_pi(&g.def(*id).ty_value),
        Some((Global::Op(..), _)) => Ok(true),
        Some((Global::Unchecked(item), _)) => Ok(cx.e.item_is_function(*item)),
        // A library name whose file isn't loaded: the index knows its type's shape.
        Some((Global::Pending(file, _), _)) => Ok(cx.e.pending_is_function(name, *file)),
        _ => Ok(false),
    }
}

/// The function at the head of an application, if it's a variable or a
/// definition, as `infer_app` finds it (without inserting implicit
/// arguments).
pub(crate) fn known_head(cx: &Ctx, head: &Expr) -> Option<(Term, Value)> {
    let Expr::Var(name) = head else {
        return None;
    };
    if let Ok(Some(local)) = cx.local(&name.text) {
        cx.note_local_use(name, &local.1);
        return Some(local);
    }
    if let Some(level) = cx.lookup(&name.text) {
        cx.e.note_local(cx, name, &cx.types[level]);
        return Some((Term::Var(cx.level() - 1 - level), cx.types[level].clone()));
    }
    if as_fields(cx, name).is_some()
        || matches!(name.text.as_str(), "rfl" | "J")
        || crate::quot::head_form(cx, &name.text).is_some()
    {
        return None;
    }
    match cx.e.named(&name.text) {
        Some((Global::Def(id), _)) => {
            // Propagation elaborates the application from this head without
            // going through `infer_app`, which would note the name.
            cx.e.note_name(name);
            Some((Term::Def(*id), crate::kernel::def_ty(cx.g(), *id).ok()?))
        }
        _ => None,
    }
}

/// The type of the application of a function of type `ty` to `args`, before
/// they're checked (§7.2): implicit parameters get metavariables, as
/// `apply_args` and then `insert` would give them, returned in order;
/// parameters given by `args` get fresh variables. `None` if the type
/// mentions those variables (it depends on the arguments' values), or isn't
/// known, or an auto parameter is met after an argument (its proposition
/// could mention it) or in the result.
fn written_result(cx: &mut Ctx, ty: &Value, args: &[Arg]) -> Result<Option<(Value, Supply)>> {
    let g = cx.g();
    let base = cx.level();
    let mut ty = ty.clone();
    let mut supply = Supply::new();
    let mut written = 0;
    for arg in args {
        let stop = |x: &Name, icit: Icit| match arg {
            Arg::Named(name, _) => icit.is_implicit() && **x == *name.text,
            Arg::NamedExplicit(..) => icit == Icit::Explicit,
            Arg::Explicit(_) | Arg::Piped(_) | Arg::Default(_) => icit == Icit::Explicit,
        };
        let Some(Value::Pi(_, icit, _, cod)) = implicits(cx, &mut ty, &mut supply, written, stop)?
        else {
            return Ok(None);
        };
        if icit == Icit::Auto {
            return Ok(None);
        }
        ty = cod.apply(g, Value::var(base + written))?;
        written += 1;
    }
    if implicits(cx, &mut ty, &mut supply, written, |_, _| false)?.is_none() {
        return Ok(None);
    }
    // What's left: an auto parameter anywhere in it rules propagation out.
    let mut rest = ty.clone();
    let mut level = base + written;
    loop {
        match force(g, rest)? {
            Value::Pi(_, Icit::Auto, _, _) => return Ok(None),
            Value::Pi(_, _, _, cod) => {
                rest = cod.apply(g, Value::var(level))?;
                level += 1;
            }
            _ => break,
        }
    }
    // Calls stay folded: reading back their unfoldings can be costly, and a
    // call mentions every variable its unfolding does.
    let term = stitchwort_core::value::quote_folded(g, base + written, &ty)?;
    if (0..written).any(|i| term.mentions(i)) {
        return Ok(None);
    }
    Ok(Some((ty, supply)))
}

/// Gives the implicit parameters at the front of `ty` metavariables, added
/// to `supply`, until `stop` says to stop at one: that parameter's function
/// type (or `ty`, forced, if it isn't a function type). An auto parameter
/// met before any argument is written (`Set.fromList [auto ord: Ord k] xs`)
/// gets a metavariable too, recorded as an obligation as `insert` would, so
/// the result type reaches the arguments first (its proposition can't
/// mention an argument). `None` at an auto parameter after `written`
/// arguments.
fn implicits(
    cx: &mut Ctx,
    ty: &mut Value,
    supply: &mut Supply,
    written: usize,
    stop: impl Fn(&Name, Icit) -> bool,
) -> Result<Option<Value>> {
    let g = cx.g();
    loop {
        let forced = force(g, ty.clone())?;
        match &forced {
            Value::Pi(x, icit, _, _) if stop(x, *icit) => return Ok(Some(forced)),
            Value::Pi(_, Icit::Auto, _, _) if written > 0 => return Ok(None),
            Value::Pi(_, icit @ (Icit::Implicit | Icit::Auto), dom, cod) => {
                let meta = implicit_arg(cx, *icit, dom);
                let value = cx.eval(&meta)?;
                supply.push_back(meta);
                *ty = cod.apply(g, value)?;
            }
            _ => return Ok(Some(forced)),
        }
    }
}

/// The prelude's data type `b`, which syntax stands for (the built-in
/// registry, docs/proposals/namespaces.md §4.7): by identity, never by what
/// its name means here.
pub fn builtin_data(cx: &Ctx, b: Builtin) -> Result<DataId> {
    cx.g()
        .registry
        .data(b)
        .ok_or_else(|| missing_builtin(cx, b))
}

/// The prelude's constructor `b`: its data type and index.
pub fn builtin_ctor(cx: &Ctx, b: Builtin) -> Result<(DataId, usize)> {
    cx.g()
        .registry
        .ctor(b)
        .ok_or_else(|| missing_builtin(cx, b))
}

/// The prelude's definition `b`.
pub fn builtin_def(cx: &Ctx, b: Builtin) -> Result<stitchwort_core::DefId> {
    cx.g().registry.def(b).ok_or_else(|| missing_builtin(cx, b))
}

/// Only while the prelude loads, before `b`'s declaration is admitted: user
/// code isn't elaborated until every built-in is bound.
fn missing_builtin(cx: &Ctx, b: Builtin) -> Diagnostic {
    cx.error(
        "E-UNKNOWN-NAME",
        format!("this needs the prelude's `{}`", b.name()),
        "here",
    )
}

/// A qualified name that's really field access: its first component is a
/// local variable (`P.name`), or it names a declaration followed by
/// components that don't (`Origin.x`).
fn as_fields(cx: &Ctx, name: &AstName) -> Option<Expr> {
    let (first, _) = name.text.split_once('.')?;
    let parts: Vec<&str> = name.text.split('.').collect();
    let taken = if cx.lookup(first).is_some() {
        1
    } else {
        match cx.e.resolve(&name.text) {
            // A type has no fields: `List.chunksOf` is a function of
            // `List`'s, and if there's none, that's the error
            // (`Elaborator::no_member`).
            crate::scope::Resolved::Found { global, .. } if cx.e.is_type_former(global) => {
                return None;
            }
            crate::scope::Resolved::Found { rest, .. } if !rest.is_empty() => {
                parts.len() - rest.len()
            }
            _ => return None,
        }
    };
    let mut expr = Expr::Var(AstName {
        text: parts[..taken].join("."),
        span: name.span,
    });
    for field in &parts[taken..] {
        expr = Expr::Field(
            Box::new(expr),
            AstName {
                text: field.to_string(),
                span: name.span,
            },
        );
    }
    Some(expr)
}

/// If `expr` is a constructor applied to explicit arguments: the constructor
/// and the arguments.
fn ctor_head<'a>(cx: &Ctx, expr: &'a Expr) -> Result<Option<(DataId, usize, Vec<CtorArg<'a>>)>> {
    let mut args = Vec::new();
    let mut head = expr;
    while let Expr::App(f, a) = head {
        args.push(a.as_ref());
        head = f;
    }
    args.reverse();
    let Expr::Var(name) = head else {
        return Ok(None);
    };
    if cx.lookup(&name.text).is_some() || as_fields(cx, name).is_some() {
        return Ok(None);
    }
    cx.e.note_name(name);
    match cx.e.named(&name.text) {
        Some((Global::Ctor(d, c), _)) => {
            let args = (args.into_iter())
                .map(|a| match a {
                    Expr::NamedArg(n, e, _, Bracket::Square) => CtorArg::Named(n, e),
                    Expr::NamedArg(n, e, _, Bracket::Round) => CtorArg::NamedExplicit(n, e),
                    e => CtorArg::Pos(e),
                })
                .collect();
            Ok(Some((*d, *c, args)))
        }
        _ => Ok(None),
    }
}

/// An argument of a constructor: positional, for an explicit field,
/// `[n := e]`, for an implicit one (docs/proposals/indexed-families.md §7.2),
/// or `(n := e)`, for an explicit one by name (D1096).
#[derive(Clone, Copy)]
pub(crate) enum CtorArg<'a> {
    Pos(&'a Expr),
    Named(&'a AstName, &'a Expr),
    NamedExplicit(&'a AstName, &'a Expr),
}

/// Elaborates constructor `c` of `d` applied to `args`. The data type's
/// parameters come from `expected` if given, or are left to unification;
/// implicit fields not given by name are left to unification too.
/// A partially applied constructor is a function, which needs `expected`.
fn ctor_app(
    cx: &mut Ctx,
    d: DataId,
    c: usize,
    args: &[CtorArg],
    expected: Option<&Value>,
) -> Result<(Term, Value)> {
    let g = cx.g();
    let data = g.data(d);
    let ctor = &data.ctors[c];
    let k = ctor.fields.len();
    let implicit: Vec<bool> = (0..k)
        .map(|i| ctor.implicit.get(i).copied().unwrap_or(false))
        .collect();
    // What each field is given, by position or by name (`named.rs`).
    let given = ctor_fill(cx, d, c, args)?;
    let missing: Vec<usize> = (0..k)
        .filter(|&i| !implicit[i] && given[i].is_none())
        .collect();

    // Partial application: `x … => C args x …`, checked against a function
    // type, with a parameter for each explicit field not given (§4.2 rule 3).
    let mut missing_types = Vec::new();
    let mut missing_level: Vec<Option<usize>> = vec![None; k];
    let mark = cx.mark();
    // The parameters, if `expected` doesn't fix them, are metavariables made
    // out here, before the parameters of the lambda are bound: a meta made
    // under them would take them into its spine, and would leak them when it
    // solves one of the outer metas of `expected` (`Eq.cong (Call o) p`).
    let fallback_params: Vec<Value> = if missing.is_empty() {
        Vec::new()
    } else {
        data.params
            .iter()
            .map(|_| {
                let meta = cx.fresh_meta();
                cx.eval(&meta)
            })
            .collect::<Result<_>>()?
    };
    let mut target = expected.cloned();
    for &i in &missing {
        match target.as_ref().map(|t| force(g, t.clone())).transpose()? {
            Some(Value::Pi(_, Icit::Explicit, dom, cod)) => {
                let var = Value::var(cx.level());
                let name: Name = ctor.fields[i].0.clone();
                missing_level[i] = Some(cx.level());
                cx.bind_hidden(name.clone(), (*dom).clone());
                missing_types.push(name);
                target = Some(cod.apply(g, var)?);
            }
            _ => {
                cx.reset(mark);
                return Err(cx.error(
                    "E-CANNOT-INFER",
                    format!("`{}` is missing {} argument(s)", ctor.name, missing.len()),
                    "add the missing arguments, or a type annotation",
                ));
            }
        }
    }

    let np = data.params.len();
    // A callback of an effect-polymorphic function whose row isn't known yet
    // (`xs.map (Cons { … })`, a `CompIn ?e (List Hit)` result): the
    // parameters are the value type's. The comparison below settles the row.
    let value_target = match &target {
        Some(t) => effects::unknown_bare_value(cx, t)?.or_else(|| Some(t.clone())),
        None => None,
    };
    let params = match value_target.map(|t| force(g, t)).transpose()? {
        Some(Value::Data(d2, args)) if d2 == d && args.len() >= np => args[..np].to_vec(),
        _ if !missing.is_empty() => fallback_params,
        _ => data
            .params
            .iter()
            .map(|_| {
                let meta = cx.fresh_meta();
                cx.eval(&meta)
            })
            .collect::<Result<_>>()?,
    };
    // A missing field's type is known from `expected` (`List Hit` in
    // `xs.map (Cons { … })`): unify it first, so the parameters it fixes are
    // known when the given arguments are checked, whatever the field order.
    // Only for a type that doesn't depend on earlier fields.
    for (i, (_, field_ty)) in ctor.fields.iter().enumerate() {
        let Some(level) = missing_level[i] else {
            continue;
        };
        if (0..i).any(|j| field_ty.mentions(i - 1 - j)) {
            continue;
        }
        let mut early = params.clone();
        early.extend((0..i).map(|_| unused()));
        let ty = eval(g, &early, field_ty)?;
        let found = cx.types[level].clone();
        // A mismatch is reported by the pass below.
        cx.unify(&found, &ty)?;
    }
    let mut env = params.clone();
    let mut terms = Vec::new();
    for (i, (_, field_ty)) in ctor.fields.iter().enumerate() {
        let ty = eval(g, &env, field_ty)?;
        let term = if let Some(level) = missing_level[i] {
            let found = cx.types[level].clone();
            if !cx.unify(&found, &ty)? {
                cx.reset(mark);
                return Err(cx.mismatch(&ty, &found));
            }
            Term::Var(cx.level() - 1 - level)
        } else {
            match given[i] {
                Some(e) => check(cx, e, &ty)?,
                None => implicit_arg(cx, Icit::Implicit, &ty),
            }
        };
        let needed = kernel::later_types_mention(&ctor.fields, i)
            || ctor.result.iter().any(|r| r.mentions(k - 1 - i));
        env.push(if needed { cx.eval(&term)? } else { unused() });
        terms.push(term);
    }
    let indices = (ctor.result.iter())
        .map(|r| eval(g, &env, r))
        .collect::<std::result::Result<Vec<_>, _>>()?;
    let result_ty = Value::Data(d, params.into_iter().chain(indices).collect());
    if let Some(target) = &target
        && !cx.unify(&result_ty, target)?
    {
        let error = cx.mismatch(target, &result_ty);
        cx.reset(mark);
        return Err(error);
    }
    cx.reset(mark);
    let mut term = Term::ctor(d, c, terms);
    if missing_types.is_empty() {
        return Ok((term, result_ty));
    }
    for name in missing_types.into_iter().rev() {
        term = Term::Lam(name, Icit::Explicit, Rc::new(term));
    }
    Ok((term, expected.expect("checked above").clone()))
}

/// Wraps an inferred constructor in a type annotation, so the kernel (which
/// can only check constructors of parameterised types) can infer it too.
fn annotate(cx: &Ctx, term: Term, ty: &Value) -> Result<Term> {
    Ok(match force(cx.g(), ty.clone())? {
        Value::Data(d, _) if !cx.g().data(d).params.is_empty() => {
            Term::Ann(Rc::new(term), Rc::new(cx.quote_folded(ty)?))
        }
        _ => term,
    })
}

/// `term`, inferred from `expr`, without the annotation [`annotate`] put on
/// a constructor: for a receiver or piped value passed as an explicit
/// argument, where the parameter's type is known, so it elaborates as the
/// same argument checked in prefix form does. An annotation written in the
/// source stays.
pub(crate) fn without_inferred_annotation(expr: &Expr, term: Term) -> Term {
    if matches!(expr, Expr::Ann(..)) {
        return term;
    }
    let span = match &term {
        Term::Loc(span, _) => Some(*span),
        _ => None,
    };
    match term.strip_loc() {
        Term::Ann(inner, _) if matches!(inner.strip_loc(), Term::Ctor(..)) => match span {
            Some(span) => Term::Loc(span, inner.clone()),
            None => (**inner).clone(),
        },
        _ => term,
    }
}

/// `Pair A B` for `(A, B)`: each component must be a type in `Type`, as
/// `Pair`'s parameters are (a proposition can't be a component).
fn type_tuple(cx: &mut Ctx, a: &Expr, b: &Expr) -> Result<(Term, Value)> {
    let pair = builtin_data(cx, Builtin::Pair)?;
    let mut parts = Vec::new();
    for part in [a, b] {
        let (term, sort) = check_type(cx, part)?;
        if sort != Sort::Type(0) {
            return Err(cx.mismatch(&Value::Sort(Sort::Type(0)), &Value::Sort(sort)));
        }
        parts.push(Rc::new(term));
    }
    Ok((Term::Data(pair, parts), Value::Sort(Sort::Type(0))))
}

/// `(a, b)` with no expected type: a type tuple if the first component's
/// type is a universe, otherwise a value tuple.
fn infer_tuple(cx: &mut Ctx, a: &Expr, b: &Expr) -> Result<(Term, Value)> {
    let (ta, tya) = infer(cx, a)?;
    if let Value::Sort(_) = force(cx.g(), tya.clone())? {
        return type_tuple(cx, a, b);
    }
    let (tb, tyb) = infer(cx, b)?;
    let (pair, mk) = builtin_ctor(cx, Builtin::MkPair)?;
    Ok((
        Term::ctor(pair, mk, vec![ta, tb]),
        Value::Data(pair, vec![tya, tyb]),
    ))
}

pub fn check_type(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Sort)> {
    let span = expr.span();
    if let Expr::Unit(_) = expr {
        return Ok((
            Term::Data(builtin_data(cx, Builtin::UnitType)?, Vec::new()),
            Sort::Type(0),
        ));
    }
    // A tuple where a type is wanted is a type tuple, whatever its components
    // look like (a function's domain, for one).
    if let Expr::Tuple(a, b, _) = expr {
        let (term, _) = type_tuple(cx, a, b)?;
        return Ok((term, Sort::Type(0)));
    }
    // `p && q`, `p || q` and `not p` where a type is wanted are propositions.
    if let Some(logic) = crate::logic::classify(cx, expr) {
        let span = expr.span();
        let term = with_span(cx, span, |cx| crate::logic::as_prop(cx, logic))?;
        return Ok((Term::Loc(span, Rc::new(term)), Sort::Prop));
    }
    let (term, ty) = infer(cx, expr)?;
    // Trailing implicit and `auto` parameters, as in a synonym's
    // `type Set (k: Type) [auto ord: Ord k] = …`: `Set Nat` finds `ord`
    // (docs/proposals/interfaces.md §7.5).
    let (term, ty) = match force(cx.g(), ty.clone())? {
        Value::Pi(_, icit, _, _) if icit.is_implicit() => insert(cx, term, ty)?,
        _ => (term, ty),
    };
    match force(cx.g(), ty)? {
        Value::Sort(s) => Ok((term, s)),
        ty @ Value::Neutral(Head::Meta(_), _) => {
            // An unknown type of types defaults to `Type`.
            if cx.unify(&ty, &Value::Sort(Sort::Type(0)))? {
                Ok((term, Sort::Type(0)))
            } else {
                Err(not_a_type(cx, span, &ty))
            }
        }
        other => Err(not_a_type(cx, span, &other)),
    }
}

fn not_a_type(cx: &Ctx, span: Span, ty: &Value) -> Diagnostic {
    Diagnostic::error("E-NOT-A-TYPE", "expected a type").with_label(
        span,
        format!("this has type `{}`, so it isn't a type", cx.show(ty)),
    )
}

fn infer_j(cx: &mut Ctx, motive: &Expr, base: &Expr, proof: &Expr) -> Result<(Term, Value)> {
    let g = cx.g();
    let (proof, proof_ty) = infer(cx, proof)?;
    let (proof, proof_ty) = insert(cx, proof, proof_ty)?;
    let Value::Eq(ty, x, y) = force(g, proof_ty.clone())? else {
        return Err(cx.error(
            "E-TYPE-MISMATCH",
            "`J` needs a proof of an equation",
            format!("its last argument has type `{}`", cx.show(&proof_ty)),
        ));
    };
    let Expr::Lam(names, body, _) = motive else {
        return Err(motive_error(cx));
    };
    let [y_name, p_name] = &names[..] else {
        return Err(motive_error(cx));
    };
    let mark = cx.mark();
    let level = cx.level();
    cx.bind(&y_name.text, (*ty).clone());
    cx.bind(
        &p_name.text,
        Value::Eq(ty.clone(), x.clone(), Rc::new(Value::var(level))),
    );
    let result = check_type(cx, body);
    cx.reset(mark);
    let (body, _) = result?;
    let motive = Term::Lam(
        y_name.text.as_str().into(),
        Icit::Explicit,
        Rc::new(Term::Lam(
            p_name.text.as_str().into(),
            Icit::Explicit,
            Rc::new(body),
        )),
    );
    let motive_value = cx.eval(&motive)?;
    let base_ty = apply(
        g,
        apply(g, motive_value.clone(), (*x).clone())?,
        Value::Refl,
    )?;
    let base = check(cx, base, &base_ty)?;
    let proof_value = cx.eval(&proof)?;
    let result = apply(g, apply(g, motive_value, (*y).clone())?, proof_value)?;
    Ok((
        Term::J(Rc::new(motive), Rc::new(base), Rc::new(proof)),
        result,
    ))
}

fn motive_error(cx: &Ctx) -> Diagnostic {
    cx.error(
        "E-CANNOT-INFER",
        "the first argument of `J` must be a function of two arguments",
        "write it as `y p => …`",
    )
}

/// `Nat`, which numbers need.
pub(crate) fn nat(cx: &Ctx) -> Result<DataId> {
    cx.e.globals
        .builtins
        .nat
        .ok_or_else(|| cx.error("E-UNKNOWN-NAME", "numbers need the prelude's `Nat`", "here"))
}

/// Arguments as written, for [`apply_args`].
pub(crate) fn args_of(exprs: &[Expr]) -> Vec<Arg<'_>> {
    exprs.iter().map(arg_of).collect()
}

/// The two sides of the goal's `=` as they were written, if the type being
/// checked is the definition's declared type (or what remains of it after
/// its parameters) and its sides evaluate to `a` and `b`.
fn written_sides(cx: &Ctx, a: &Value, b: &Value) -> Option<(String, String)> {
    let (level, goal) = cx.goal.as_ref()?;
    if *level != cx.level() {
        return None;
    }
    let Term::Eq(_, ga, gb) = goal.strip_loc() else {
        return None;
    };
    let same = |t: &Term, v: &Value| -> Option<bool> {
        let value = cx.eval(t).ok()?;
        cx.unify(&value, v).ok()
    };
    if !same(ga, a)? || !same(gb, b)? {
        return None;
    }
    let show = |t: &Term| pretty::term_for_message_in(cx.g(), cx.e, &cx.names, t);
    Some((show(ga), show(gb)))
}

/// The `E-REFL` error for sides `a` and `b` that aren't equal (kept out of
/// `check`, whose stack frame is on every recursion).
#[inline(never)]
pub(crate) fn refl_error(cx: &Ctx, a: &Value, b: &Value) -> Diagnostic {
    let (shown_a, shown_b) = (cx.show(a), cx.show(b));
    // What the sides compute to: their normal forms, calls unfolded.
    let (normal_a, normal_b) = if cx.g().glue.get() {
        (cx.show_unfolded(a), cx.show_unfolded(b))
    } else {
        (shown_a.clone(), shown_b.clone())
    };
    let computed = |sa: &str, sb: &str| match (sa != normal_a, sb != normal_b) {
        (true, true) => Some(format!(
            "computing both sides gives `{normal_a}` and `{normal_b}`"
        )),
        (true, false) => Some(format!("computing the left side gives `{normal_a}`")),
        (false, true) => Some(format!("computing the right side gives `{normal_b}`")),
        (false, false) => None,
    };
    let written = written_sides(cx, a, b);
    let (side_a, side_b) = written.unwrap_or_else(|| (shown_a.clone(), shown_b.clone()));
    let label = format!("`{side_a}` and `{side_b}` aren't equal");
    let computed = computed(&side_a, &side_b);
    // Both sides print the same, and differ only in what the compiler fills
    // in (`Int.modNat x 3 [ok := p]` with two different proofs `p`).
    let (label, hidden) = if shown_a == shown_b || side_a == side_b {
        let (ha, hb) = (cx.show_hidden(a), cx.show_hidden(b));
        if ha != hb && cx.differ_only_in_hidden(a, b) {
            (format!("`{ha}` and `{hb}` aren't equal"), true)
        } else {
            (label, false)
        }
    } else {
        (label, false)
    };
    let alike = !hidden && (shown_a == shown_b || normal_a == normal_b || side_a == side_b);
    // Whether a printed pair may hide where the sides differ: the same text,
    // or parts shown as `…`.
    let unclear = |x: &str, y: &str| x == y || x.contains('…') || y.contains('…');
    let difference = !hidden
        && (unclear(&side_a, &side_b) || computed.is_some() && unclear(&normal_a, &normal_b));
    let mut error = cx.error("E-REFL", "`rfl` can't prove this", label);
    if hidden {
        error = error.with_note(
            "the two sides differ only in arguments the compiler fills in, shown here in \
             `[brackets]` (an implicit argument, or a proof such as `d != 0`; proofs of the \
             same statement aren't interchangeable)",
        );
    } else if let Some(computed) = computed {
        error = error.with_note(computed);
    }
    if difference && let Some(note) = cx.first_difference_note(a, b) {
        error = error.with_note(note);
    }
    // Both sides still print the same, as written or computed.
    if alike {
        error = cx.with_alike_updates_note(error, &[a, b]);
    }
    let error =
        error.with_note("`rfl` proves `a = b` only when both sides compute to the same value");
    let error = cx.with_unused_equation_notes(error, &[a, b]);
    cx.with_opaque_notes(error, &[a, b])
}

#[cfg(test)]
mod tests {
    use stitchwort_syntax::SourceMap;

    use super::*;

    fn span() -> Span {
        let mut sources = SourceMap::new();
        Span::point(sources.add("test", ""), 0)
    }

    /// A case split can refine an earlier variable's type to mention a
    /// later one, as `Int.div`'s `ok: divisor != OfNat 0` mentions `n` in
    /// its `OfNat (Succ n)` case. That later variable isn't ignorable, and
    /// reading the earlier type back mustn't assume it mentions only earlier
    /// variables (SW-416: an overflow in debug builds, and in release a
    /// mention silently lost).
    #[test]
    fn a_later_variable_mentioned_by_an_earlier_refined_type_is_not_ignorable() {
        let e = Elaborator::new();
        let type0 = || Value::Sort(Sort::Type(0));
        let eq = |a: Value, b: Value| {
            Value::Eq(Rc::new(Value::Sort(Sort::Type(1))), Rc::new(a), Rc::new(b))
        };
        // `a: Type0`, `ok: n = n`, `n: Type0`, proving `Type0 = Type0`.
        let cx = Ctx::from_parts(
            &e,
            (0..3).map(Value::var).collect(),
            vec![type0(), eq(Value::var(2), Value::var(2)), type0()],
            vec!["a".into(), "ok".into(), "n".into()],
            span(),
        );
        let ignorable = ignorable_arguments(&cx, &eq(type0(), type0())).expect("types read back");
        assert_eq!(&*ignorable, &[true, true, false]);
    }

    /// Elaborates `text`, a closed expression, with no library: the shown
    /// type, or the error's message and labels.
    fn elaborate(text: &str) -> std::result::Result<String, String> {
        let mut sources = SourceMap::new();
        let file = sources.add("test", text);
        let expr = stitchwort_syntax::parse_expression(file, text).expect("parses");
        let mut e = Elaborator::new();
        match e.infer_expr(&expr) {
            Ok((_, ty)) => Ok(e.show(&ty)),
            Err(d) => Err(format!(
                "{} {}",
                d.message,
                d.labels
                    .iter()
                    .map(|l| l.message.as_str())
                    .collect::<Vec<_>>()
                    .join(" ")
            )),
        }
    }

    /// docs/proposals/lambda-syntax.md §4.3 (D91): inferring a lambda with
    /// an implicit or auto parameter builds a function type of that kind.
    #[test]
    fn a_binder_lambda_infers_a_function_type_of_its_mode() {
        assert_eq!(
            elaborate("[a: Type] (x: a) => x").as_deref(),
            Ok("[a: Type] → a → a")
        );
        assert_eq!(
            elaborate("[a: Type] [auto h: a] (x: a) => h").as_deref(),
            Ok("[a: Type] → [auto h: a] → a → a")
        );
        // Not applied to an unknown in an annotation, either.
        assert_eq!(
            elaborate("([a: Type] (x: a) => x: [b: Type] -> b -> b)").as_deref(),
            Ok("[b: Type] → b → b")
        );
    }

    /// Checking consumes a function type of the lambda's mode, and only
    /// that: a mismatch says which kind each side has.
    #[test]
    fn a_binder_lambda_consumes_only_its_own_kind_of_parameter() {
        let mismatch = |text: &str, says: &str| {
            let message = elaborate(text).expect_err(text);
            assert!(message.contains(says), "{text}: {message}");
        };
        mismatch(
            "([a: Type] (x: a) => x: Type -> Type)",
            "takes an implicit parameter first, but the expected type `Type → Type` takes an \
             explicit one",
        );
        mismatch(
            "([a: Type] (x: a) => x: [auto h: Type] -> Type)",
            "takes an `auto` one",
        );
        mismatch(
            "([auto h: Type] => h: [a: Type] -> Type)",
            "this lambda takes an `auto` parameter first",
        );
        mismatch("([a: Type] => a: Type)", "isn't a function type");
        // The written type must agree with the expected one.
        mismatch(
            "([a: Type 1] => a: [a: Type] -> Type)",
            "this parameter is annotated `Type 1`",
        );
        // A plain lambda still has the implicit parameter introduced.
        assert_eq!(
            elaborate("(x => x: [a: Type] → a → a)").as_deref(),
            Ok("[a: Type] → a → a")
        );
    }
}
