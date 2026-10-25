//! The kernel's checking API, as the elaborator uses it. Everything is
//! re-exported unchanged except the declare and define calls, which are
//! timed for `STITCHWORT_TIMINGS` (`timings.rs`). The kernel crate itself
//! has no timing code. A definition refused only because it uses
//! unfinished declarations (an open goal, `?`) is reported as unfinished,
//! not as an error (`goals.rs`); the kernel's verdict is unchanged.

use stitchwort_core::check as k;
use stitchwort_core::globals::HashKey;
use stitchwort_core::{DataId, DefId, Globals, Name, Sort, Term};
use stitchwort_syntax::{Diagnostic, Span};

pub use k::*;

use crate::timings::kernel_call;

type Result<T> = std::result::Result<T, Diagnostic>;

/// A kernel call, timed, with gluing off (`Globals::glue`): the kernel
/// checks as it always has (D483, docs/proposals/folded-calls.md).
fn unglued<T>(g: &mut Globals, f: impl FnOnce(&mut Globals) -> T) -> T {
    let was = g.glue.replace(false);
    let out = kernel_call(|| f(g));
    g.glue.set(was);
    out
}

/// `f` with gluing off: for the kernel's inference, which `rewrite` and
/// matching use on the elaborator's terms.
pub fn without_glue<T>(g: &Globals, f: impl FnOnce() -> T) -> T {
    let was = g.glue.replace(false);
    let out = f();
    g.glue.set(was);
    out
}

pub fn define_def(g: &mut Globals, id: DefId, body: &Term) -> Result<()> {
    unglued(g, |g| k::define_def(g, id, body))
        .map_err(|d| crate::goals::unfinished_dependency(g, [body], &[HashKey::Def(id)], d))
}

pub fn define_group(g: &mut Globals, members: &[(DefId, Term)]) -> Result<()> {
    unglued(g, |g| k::define_group(g, members)).map_err(|d| {
        let own: Vec<HashKey> = members.iter().map(|(id, _)| HashKey::Def(*id)).collect();
        crate::goals::unfinished_dependency(g, members.iter().map(|(_, t)| t), &own, d)
    })
}

pub fn declare_def(
    g: &mut Globals,
    name: &Name,
    ty: &Term,
    theorem: bool,
    export: bool,
    span: Span,
) -> Result<DefId> {
    unglued(g, |g| k::declare_def(g, name, ty, theorem, export, span))
        .map_err(|d| crate::goals::unfinished_dependency(g, [ty], &[], d))
}

pub fn retype_def(g: &mut Globals, id: DefId, ty: &Term) -> Result<()> {
    unglued(g, |g| k::retype_def(g, id, ty))
        .map_err(|d| crate::goals::unfinished_dependency(g, [ty], &[], d))
}

#[allow(dead_code)]
pub fn declare_data(
    g: &mut Globals,
    name: Name,
    params: Vec<(Name, Term)>,
    sort: Sort,
    span: Span,
) -> Result<DataId> {
    unglued(g, |g| k::declare_data(g, name, params, sort, span))
}

pub fn declare_data_group(
    g: &mut Globals,
    params: Vec<(Name, Term)>,
    sort: Sort,
    members: Vec<(Name, Span)>,
) -> Result<Vec<DataId>> {
    unglued(g, |g| k::declare_data_group(g, params, sort, members))
}

#[allow(dead_code)]
pub fn declare_data_group_as(
    g: &mut Globals,
    params: Vec<(Name, Term)>,
    sort: Sort,
    members: Vec<(Name, Span, bool)>,
) -> Result<Vec<DataId>> {
    unglued(g, |g| k::declare_data_group_as(g, params, sort, members))
}

pub fn declare_indexed_data_group(
    g: &mut Globals,
    params: Vec<(Name, Term)>,
    sort: Sort,
    members: Vec<DataDecl>,
) -> Result<Vec<DataId>> {
    unglued(g, |g| {
        k::declare_indexed_data_group(g, params, sort, members)
    })
}

#[allow(dead_code)]
pub fn define_ctors(g: &mut Globals, d: DataId, ctors: Vec<CtorDecl>) -> Result<()> {
    unglued(g, |g| k::define_ctors(g, d, ctors))
}

pub fn define_data_group(g: &mut Globals, members: Vec<(DataId, Vec<CtorDecl>)>) -> Result<()> {
    unglued(g, |g| k::define_data_group(g, members))
}

/// [`substitute`] for the elaborator's case splits: each value is read back
/// with its calls folded (`value::quote_folded`), so a refined context keeps
/// what was written (`isWall p = False`, not the dungeon map `isWall`
/// computes from) while staying convertible with the kernel's normal form.
/// Without gluing there are no calls and this is [`substitute`].
pub fn substitute_folded(
    g: &Globals,
    level: usize,
    x: usize,
    value: &stitchwort_core::Value,
    values: &[stitchwort_core::Value],
) -> stitchwort_core::budget::Result<Vec<stitchwort_core::Value>> {
    use stitchwort_core::value::{eval, quote_folded};
    let mut env: Vec<stitchwort_core::Value> =
        (0..level).map(stitchwort_core::Value::var).collect();
    env[x] = value.clone();
    values
        .iter()
        .map(|v| eval(g, &env, &quote_folded(g, level, v)?))
        .collect()
}
