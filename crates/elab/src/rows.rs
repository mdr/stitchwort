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

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, eval, force, quote};
use stitchwort_core::{Name, Term, Value};
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
/// `Effect.Row`.
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
        if self.default_rows()? {
            self.solve_obligations()?;
            while self.retry_rows()? {}
        }
        let first = self.row_constraints.borrow().first().cloned();
        if let Some(item) = first {
            let cx = item.context(self);
            let RowConstraint { a, b, .. } = &item.constraint;
            return Err(cx
                .mismatch(b, a)
                .with_note("a row variable's row couldn't be worked out here"));
        }
        self.row_metas.borrow_mut().clear();
        Ok(())
    }

    /// Sets each row unknown made for an implicit row parameter, and still
    /// unsolved, to the empty row. Whether any was.
    fn default_rows(&self) -> Result<bool> {
        let metas = std::mem::take(&mut *self.row_metas.borrow_mut());
        let mut any = false;
        for item in metas {
            let cx = Ctx::from_parts(self, item.env, item.types, item.names, item.span);
            let value = cx.eval(&item.meta)?;
            if !matches!(
                force(cx.g(), value.clone())?,
                Value::Neutral(Head::Meta(_), _)
            ) {
                continue;
            }
            let (d, c) = crate::check::builtin_ctor(&cx, Builtin::RowEmpty)?;
            let empty = Value::Ctor(d, c, Vec::new().into());
            if cx.unify(&value, &empty)? {
                any = true;
            }
        }
        Ok(any)
    }
}
