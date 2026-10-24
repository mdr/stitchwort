//! Inferring rows: row comparisons put aside until more is known, and
//! defaulting row unknowns to the empty row (design C of
//! docs/proposals/effect-polymorphism.md, §5.C.1, D1123).
//!
//! The unifier decides `CompIn ?e B ≟ T` at once when `T` settles it
//! (`unify::row_rule`). When `T` is blocked (a definition stuck on an unknown
//! or a variable, which may yet compute to a `Comp`), `compare` accepts the
//! term and keeps the comparison here. Kept comparisons are retried in the
//! end-of-declaration rounds, with the auto arguments and instances
//! (`auto.rs`), after re-evaluating both sides. When the rounds stop making
//! progress, each row unknown that was made for a row-polymorphic function's
//! implicit row parameter and is still unsolved is set to the empty row, and
//! the comparisons are retried once more. `CompIn Empty B` is `B`, so
//! defaulting never makes a term ill typed; a comparison still failing then is
//! reported as a mismatch. Nothing unchecked reaches the kernel, which
//! re-checks the final term anyway.

use stitchwort_core::budget::ResourceError;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, eval, force, quote};
use stitchwort_core::{Globals, Name, Term, Value};
use stitchwort_syntax::Span;

use crate::Elaborator;
use crate::check::{Ctx, Result};
use crate::unify::{RowConstraint, unify_postponing};

/// A row unknown made for an implicit row parameter, with the context it was
/// made in.
#[derive(Clone)]
pub struct RowMeta {
    env: Vec<Value>,
    types: Vec<Value>,
    names: Vec<Name>,
    meta: Term,
    span: Span,
}

/// A row comparison put aside, with the context it was made in.
#[derive(Clone)]
pub struct Postponed {
    env: Vec<Value>,
    types: Vec<Value>,
    names: Vec<Name>,
    span: Span,
    constraint: RowConstraint,
}

impl Postponed {
    /// The context the comparison was made in, with the variables it was
    /// made under (inside function types) in scope, unnamed, so that its
    /// sides can be shown.
    fn context<'e>(&self, e: &'e Elaborator) -> Ctx<'e> {
        let mut cx = Ctx::from_parts(
            e,
            self.env.clone(),
            self.types.clone(),
            self.names.clone(),
            self.span,
        );
        while cx.level() < self.constraint.level {
            cx.bind_hidden("x".into(), Value::Sort(stitchwort_core::Sort::Type(0)));
        }
        cx
    }
}

/// Records `meta`, made for an implicit parameter of type `ty`, if `ty` is
/// `Effect.Effects`.
pub(crate) fn note_row_meta(cx: &Ctx, ty: &Value, meta: &Term) {
    let Ok(Value::Data(d, _)) = force(cx.g(), ty.clone()) else {
        return;
    };
    if !cx.g().registry.is_data(Builtin::Row, d) {
        return;
    }
    cx.e.row_metas.borrow_mut().push(RowMeta {
        env: cx.env.clone(),
        types: cx.types.clone(),
        names: cx.names.clone(),
        meta: meta.clone(),
        span: cx.span,
    });
}

/// Why a row couldn't be built.
#[derive(Debug)]
pub(crate) enum RowFault {
    /// The prelude hasn't declared `Effects` yet.
    Missing,
    /// Computing the operation type took too long.
    Resource(ResourceError),
    /// The operations are `NoOp`: a row with no abilities, which must be
    /// `Empty`.
    NoAbilities,
}

/// The empty row, `Empty`. With [`ops_row`], the only place the elaborator
/// makes a value of type `Effects`, so the canonical-form invariant (a row
/// with no abilities is `Empty`, never `Ops NoOp NoRes`;
/// docs/proposals/effect-polymorphism.md §5.C.2) is checked in one place.
/// Rows are made by `effects::row_value` (the rows of `{A | e}` types),
/// `unify::row_rule` (a row unknown solved from a `Comp`) and
/// `default_rows` (an unsolved row unknown set to the empty row).
pub(crate) fn empty_row(g: &Globals) -> Option<Value> {
    let (data, ctor) = g.registry.ctor(Builtin::RowEmpty)?;
    Some(Value::Ctor(data, ctor, Vec::new().into()))
}

/// `Ops op res`, the row of a computation with at least one ability. `op`
/// is checked not to be `NoOp` (once computed): a debug assertion, and in
/// release builds a [`RowFault::NoAbilities`] the caller reports. The check
/// stays in release because a non-canonical row is silently wrong, not a
/// crash: `CompIn (Ops NoOp NoRes) a` is a tree where `CompIn Empty a` is
/// `a`, so the same pure function would compile two ways. It costs one
/// `force` of a term the caller just built.
pub(crate) fn ops_row(g: &Globals, op: Value, res: Value) -> std::result::Result<Value, RowFault> {
    let (Some((data, ctor)), Some(no_op)) = (
        g.registry.ctor(Builtin::RowOps),
        g.registry.data(Builtin::NoOp),
    ) else {
        return Err(RowFault::Missing);
    };
    let forced = force(g, op.clone()).map_err(RowFault::Resource)?;
    let none = matches!(forced, Value::Data(d, _) if d == no_op);
    debug_assert!(!none, "a row with no abilities must be `Empty`, not `Ops NoOp NoRes`");
    if none {
        return Err(RowFault::NoAbilities);
    }
    Ok(Value::Ctor(data, ctor, vec![op, res].into()))
}

/// [`empty_row`], for the elaborator: an error if the prelude lacks it.
pub(crate) fn empty_row_in(cx: &Ctx) -> Result<Value> {
    match empty_row(cx.g()) {
        Some(value) => Ok(value),
        None => Err(missing(cx, Builtin::RowEmpty)),
    }
}

/// [`ops_row`], for the elaborator: a violation is an `E-INTERNAL` error.
pub(crate) fn ops_row_in(cx: &Ctx, op: Value, res: Value) -> Result<Value> {
    ops_row(cx.g(), op, res).map_err(|fault| match fault {
        RowFault::Missing => missing(cx, Builtin::RowOps),
        RowFault::Resource(e) => e.into(),
        RowFault::NoAbilities => cx
            .error(
                "E-INTERNAL",
                "internal error: the elaborator made `Ops NoOp NoRes`, a row with no abilities",
                "here",
            )
            .with_note("a row with no abilities is `Empty`: a bug in the compiler"),
    })
}

fn missing(cx: &Ctx, b: Builtin) -> stitchwort_syntax::Diagnostic {
    match crate::check::builtin_ctor(cx, b) {
        Err(d) => d,
        Ok(_) => cx.error("E-INTERNAL", "internal error: no row constructor", "here"),
    }
}

/// After `found` failed to unify with `expected`: whether they unify once
/// the row comparisons that can't be decided yet are put aside. If so, those
/// are kept, to be retried later, and what unifying solved stays solved;
/// otherwise nothing changes.
pub(crate) fn postpone(cx: &mut Ctx, found: &Value, expected: &Value) -> Result<bool> {
    let snapshot = crate::undo::Snapshot::take(cx);
    match unify_postponing(cx.g(), cx.level(), found, expected)? {
        Some(put_aside) if !put_aside.is_empty() => {
            let mut kept = cx.e.row_constraints.borrow_mut();
            for constraint in put_aside {
                kept.push(Postponed {
                    env: cx.env.clone(),
                    types: cx.types.clone(),
                    names: cx.names.clone(),
                    span: cx.span,
                    constraint,
                });
            }
            Ok(true)
        }
        _ => {
            snapshot.restore(cx);
            Ok(false)
        }
    }
}

/// `value` read back and computed again, with `level` variables in scope: a
/// definition stuck on an unknown solved since takes its step.
fn refresh_at(cx: &Ctx, level: usize, value: &Value) -> Result<Value> {
    let env: Vec<Value> = (0..level).map(Value::var).collect();
    Ok(eval(cx.g(), &env, &quote(cx.g(), level, value)?)?)
}

impl Elaborator {
    /// Retries the row comparisons put aside. Whether any was settled. One
    /// that can't hold any more is an error.
    pub(crate) fn retry_rows(&self) -> Result<bool> {
        let kept = std::mem::take(&mut *self.row_constraints.borrow_mut());
        let mut progress = false;
        let mut still = Vec::new();
        for item in kept {
            let cx = item.context(self);
            let RowConstraint { level, a, b } = &item.constraint;
            let (a, b) = (refresh_at(&cx, *level, a)?, refresh_at(&cx, *level, b)?);
            match unify_postponing(cx.g(), *level, &a, &b)? {
                Some(again) if again.is_empty() => progress = true,
                Some(again) => {
                    for constraint in again {
                        still.push(Postponed {
                            constraint,
                            ..item.clone()
                        });
                    }
                }
                None => {
                    self.row_constraints.borrow_mut().extend(still);
                    return Err(cx.mismatch(&b, &a));
                }
            }
        }
        self.row_constraints.borrow_mut().extend(still);
        Ok(progress)
    }

    /// At the end of a declaration, after the rounds: retries the row
    /// comparisons put aside until nothing changes, then defaults the
    /// remaining row unknowns to the empty row and retries once more, with
    /// the auto arguments and instances. A comparison still put aside then
    /// is reported.
    pub(crate) fn settle_rows(&self) -> Result<()> {
        while self.retry_rows()? {}
        let defaulted = self.default_rows()?;
        if !defaulted.is_empty() {
            let after = self.solve_obligations().and_then(|()| {
                while self.retry_rows()? {}
                Ok(())
            });
            after.map_err(|d| explain_defaulted(d, &defaulted))?;
        }
        let first = self.row_constraints.borrow().first().cloned();
        if let Some(item) = first {
            let cx = item.context(self);
            let RowConstraint { a, b, .. } = &item.constraint;
            let d = cx
                .mismatch(b, a)
                .with_note("a row variable's row couldn't be worked out here");
            return Err(explain_defaulted(d, &defaulted));
        }
        self.row_metas.borrow_mut().clear();
        Ok(())
    }

    /// Sets each row unknown made for an implicit row parameter, and still
    /// unsolved, to the empty row. Where each one that was set was made (the
    /// calls whose row became empty).
    fn default_rows(&self) -> Result<Vec<Span>> {
        let metas = std::mem::take(&mut *self.row_metas.borrow_mut());
        let mut defaulted = Vec::new();
        for item in metas {
            let cx = Ctx::from_parts(self, item.env, item.types, item.names, item.span);
            let value = cx.eval(&item.meta)?;
            if !matches!(
                force(cx.g(), value.clone())?,
                Value::Neutral(Head::Meta(_), _)
            ) {
                continue;
            }
            let empty = empty_row_in(&cx)?;
            if cx.unify(&value, &empty)? {
                defaulted.push(item.span);
            }
        }
        Ok(defaulted)
    }
}

/// Adds to `d`, an error found after the row unknowns at `defaulted` were set
/// to the empty row, where that happened and why (as
/// `numbers::explain_default` does for a literal made `Nat`).
fn explain_defaulted(
    d: stitchwort_syntax::Diagnostic,
    defaulted: &[Span],
) -> stitchwort_syntax::Diagnostic {
    let Some(first) = defaulted.first() else {
        return d;
    };
    d.with_label(*first, "the row of this call was set to the empty row")
        .with_note(
            "nothing said which abilities this call may perform, so its row defaulted to the \
             empty row (pure); give the callback's type, or annotate the result, if it was meant \
             to perform something",
        )
}

/// `unify::row_rule`, one test per row of its table, against the unifier
/// directly (docs/proposals/effect-polymorphism.md §5.C.1).
#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use stitchwort_core::partial::Primitive;
    use stitchwort_core::value::{Elim, Head};
    use stitchwort_core::{Globals, Icit, Sort};
    use stitchwort_syntax::SourceMap;

    use super::*;
    use crate::unify::unify;

    /// Runs `test` with the core loaded, on a thread with room for it.
    fn with_core(test: impl FnOnce(&Elaborator) + Send + 'static) {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(move || {
                let mut sources = SourceMap::new();
                let file = sources.add("<prelude>", crate::PRELUDE);
                let module =
                    stitchwort_syntax::parse_module(file, crate::PRELUDE).expect("the core parses");
                let mut e = Elaborator::new();
                e.loading_prelude = true;
                let diagnostics = e.elaborate_module(&module);
                assert!(
                    diagnostics
                        .iter()
                        .all(|d| d.severity != stitchwort_syntax::Severity::Error),
                    "the core checks"
                );
                e.finish_core().expect("a complete core");
                test(&e);
            })
            .expect("a thread")
            .join()
            .expect("the test passes");
    }

    fn span() -> Span {
        let mut sources = SourceMap::new();
        Span::point(sources.add("test", ""), 0)
    }

    fn data(g: &Globals, builtin: Builtin, args: Vec<Value>) -> Value {
        Value::Data(g.registry.data(builtin).expect("a built-in"), args)
    }

    fn applied(head: Head, args: Vec<Value>) -> Value {
        Value::Neutral(
            head,
            args.into_iter()
                .map(|a| Elim::App(a, Icit::Explicit))
                .collect(),
        )
    }

    fn nat(g: &Globals) -> Value {
        data(g, Builtin::Nat, Vec::new())
    }

    /// A fresh row unknown `?e`, and `CompIn ?e result`.
    fn comp_in(g: &Globals, result: Value) -> (usize, Value) {
        let meta = g.new_meta(span());
        let comp_in = g.registry.def(Builtin::CompIn).expect("CompIn");
        let row = applied(Head::Meta(meta), Vec::new());
        (meta, applied(Head::Def(comp_in), vec![row, result]))
    }

    /// Whether `?meta` was solved with the row constructor `which`.
    fn solved_with(g: &Globals, meta: usize, which: Builtin) -> bool {
        let (d, c) = g.registry.ctor(which).expect("a constructor");
        matches!(
            g.meta_solution(meta).map(|v| force(g, v)),
            Some(Ok(Value::Ctor(d2, c2, _))) if d2 == d && c2 == c
        )
    }

    #[test]
    fn a_data_type_makes_the_row_empty_and_the_results_are_compared() {
        with_core(|e| {
            let g = &e.globals;
            let (meta, left) = comp_in(g, nat(g));
            assert!(unify(g, 0, &left, &nat(g)).unwrap());
            assert!(solved_with(g, meta, Builtin::RowEmpty));
            let (_, left) = comp_in(g, nat(g));
            let boolean = data(g, Builtin::Bool, Vec::new());
            assert!(!unify(g, 0, &left, &boolean).unwrap());
        });
    }

    #[test]
    fn a_function_type_a_sort_and_a_variable_make_the_row_empty() {
        with_core(|e| {
            let g = &e.globals;
            let nat_id = g.registry.data(Builtin::Nat).expect("Nat");
            let nat_term = Rc::new(Term::Data(nat_id, Vec::new()));
            let function = eval(
                g,
                &[],
                &Term::Pi("x".into(), Icit::Explicit, nat_term.clone(), nat_term),
            )
            .unwrap();
            for (level, other) in [
                (0, function),
                (0, Value::Sort(Sort::Type(0))),
                (1, Value::var(0)),
            ] {
                let (meta, left) = comp_in(g, other.clone());
                assert!(unify(g, level, &left, &other).unwrap());
                assert!(solved_with(g, meta, Builtin::RowEmpty));
            }
        });
    }

    #[test]
    fn a_comp_over_abilities_gives_its_row() {
        with_core(|e| {
            let g = &e.globals;
            let no_op = data(g, Builtin::NoOp, Vec::new());
            let ops = data(g, Builtin::Plus, vec![nat(g), no_op]);
            // Closed, so that it can be part of `?e`'s solution.
            let res = eval(
                g,
                &[],
                &Term::Lam(
                    "o".into(),
                    Icit::Explicit,
                    Rc::new(Term::Sort(Sort::Type(0))),
                ),
            )
            .unwrap();
            let comp = data(g, Builtin::Comp, vec![ops, res, nat(g)]);
            let (meta, left) = comp_in(g, nat(g));
            assert!(unify(g, 0, &left, &comp).unwrap());
            assert!(solved_with(g, meta, Builtin::RowOps));
        });
    }

    #[test]
    fn a_comp_over_no_abilities_is_data() {
        with_core(|e| {
            let g = &e.globals;
            let no_op = data(g, Builtin::NoOp, Vec::new());
            let comp = data(g, Builtin::Comp, vec![no_op, Value::var(0), nat(g)]);
            // `?e := Empty`, so the result is compared with the whole `Comp`.
            let (meta, left) = comp_in(g, comp.clone());
            assert!(unify(g, 1, &left, &comp).unwrap());
            assert!(solved_with(g, meta, Builtin::RowEmpty));
        });
    }

    #[test]
    fn a_partial_computation_never_fits_a_row_variable() {
        with_core(|e| {
            let g = &e.globals;
            let delay = g.builtins.primitive_id(Primitive::Delay).expect("Delay");
            let partial = applied(Head::Def(delay), vec![nat(g)]);
            let (meta, left) = comp_in(g, nat(g));
            assert!(!unify(g, 0, &left, &partial).unwrap());
            assert!(unify_postponing(g, 0, &left, &partial).unwrap().is_none());
            assert!(g.meta_solution(meta).is_none());
        });
    }

    #[test]
    fn a_type_stuck_on_an_unknown_is_put_aside() {
        with_core(|e| {
            let g = &e.globals;
            // `rowOp ?f`: a definition stuck on an unknown.
            let row_op = g.registry.def(Builtin::RowOp).expect("rowOp");
            let unknown = applied(Head::Meta(g.new_meta(span())), Vec::new());
            let stuck = applied(Head::Def(row_op), vec![unknown]);
            let (meta, left) = comp_in(g, nat(g));
            assert!(!unify(g, 0, &left, &stuck).unwrap());
            let put_aside = unify_postponing(g, 0, &left, &stuck).unwrap();
            assert_eq!(put_aside.map(|p| p.len()), Some(1));
            assert!(g.meta_solution(meta).is_none());
        });
    }

    /// The canonical-form invariant: a row with no abilities is `Empty`
    /// (docs/proposals/effect-polymorphism.md §5.C.2), so `ops_row` refuses
    /// `NoOp`.
    #[test]
    fn ops_row_refuses_no_abilities_and_accepts_an_ability() {
        with_core(|e| {
            let g = &e.globals;
            let no_op = data(g, Builtin::NoOp, Vec::new());
            let res = Value::Sort(Sort::Type(0));
            // `Plus Nat NoOp`: one ability.
            let plus = data(g, Builtin::Plus, vec![nat(g), no_op.clone()]);
            assert!(matches!(ops_row(g, plus, res.clone()), Ok(Value::Ctor(..))));
            // `NoOp`: a debug build asserts, a release build reports it.
            let no_abilities = std::panic::AssertUnwindSafe(|| ops_row(g, no_op, res));
            if cfg!(debug_assertions) {
                assert!(std::panic::catch_unwind(no_abilities).is_err());
            } else {
                assert!(matches!(no_abilities(), Err(RowFault::NoAbilities)));
            }
            assert!(matches!(empty_row(g), Some(Value::Ctor(..))));
        });
    }
}
