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

/// A kernel call, timed, entered with gluing off (`Globals::glue`): the
/// kernel decides for itself where it glues (only checking a definition's
/// body, to compare two calls of the same definition by their arguments
/// first; D483, docs/proposals/folded-calls.md §7 stage 4).
fn unglued<T>(g: &mut Globals, f: impl FnOnce(&mut Globals) -> Result<T>) -> Result<T> {
    let was = g.glue.replace(false);
    let out = kernel_call(|| f(g));
    g.glue.set(was);
    if let Err(d) = &out
        && RECORDING.get()
    {
        REJECTIONS.with(|r| r.borrow_mut().push((d.code, d.message.clone())));
    }
    out
}

thread_local! {
    /// Whether [`REJECTIONS`] records, on this thread. Off unless a test
    /// turns it on, so a long-running session (the language server) doesn't
    /// keep every refusal.
    static RECORDING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The code and message of every error the kernel returned to a declare
    /// or define call on this thread while recording, since
    /// [`take_rejections`] was last called. For the elaborator fuzzer
    /// (`crates/driver/tests/fuzz_elab.rs`): the kernel's refusal of a term
    /// the elaborator built looks like any other diagnostic, so a test that
    /// wants to tell the two apart has to see what the kernel said before the
    /// elaborator reworded or dropped it.
    static REJECTIONS: std::cell::RefCell<Vec<(&'static str, String)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Starts or stops recording the kernel's rejections on this thread: see
/// `REJECTIONS`.
pub fn record_rejections(on: bool) {
    RECORDING.set(on);
}

/// Returns (and clears) the kernel's rejections on this thread: see
/// `REJECTIONS`.
pub fn take_rejections() -> Vec<(&'static str, String)> {
    REJECTIONS.with(|r| std::mem::take(&mut *r.borrow_mut()))
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
    define_group(g, &[(id, body.clone())])
}

/// Defines a group, with every partial occurrence of a member first applied
/// to all its parameters (`saturate.rs`).
pub fn define_group(g: &mut Globals, members: &[(DefId, Term)]) -> Result<()> {
    let (members, expanded) = crate::saturate::saturate(g, members)?;
    unglued(g, |g| k::define_group(g, &members)).map_err(|d| {
        let own: Vec<HashKey> = members.iter().map(|(id, _)| HashKey::Def(*id)).collect();
        let d = crate::goals::unfinished_dependency(g, members.iter().map(|(_, t)| t), &own, d);
        crate::saturate::explain(d, &expanded)
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

pub fn declare_data_group(
    g: &mut Globals,
    params: Vec<(Name, Term)>,
    sort: Sort,
    members: Vec<(Name, Span)>,
) -> Result<Vec<DataId>> {
    unglued(g, |g| k::declare_data_group(g, params, sort, members))
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

pub fn define_data_group(g: &mut Globals, members: Vec<(DataId, Vec<CtorDecl>)>) -> Result<()> {
    unglued(g, |g| k::define_data_group(g, members))
}

/// The kernel's substitution for the elaborator's case splits, in a context
/// whose environment is `env` (`check::substitute_in`): each value is read
/// back with its calls folded (`value::quote_folded`), so a refined context
/// keeps what was written (`isWall p = False`, not the dungeon map `isWall`
/// computes from) while staying convertible with the kernel's normal form,
/// and a variable known apart from some numbers stays so.
pub fn substitute_folded(
    g: &Globals,
    env: &[stitchwort_core::Value],
    x: usize,
    value: &stitchwort_core::Value,
    values: &[stitchwort_core::Value],
) -> stitchwort_core::budget::Result<Vec<stitchwort_core::Value>> {
    k::substitute_in(g, env, x, value, values)
}

/// Definition `id`'s type as a value under the current transparency set
/// (`check::def_type`): its stored type when nothing is unfolded, as almost
/// everywhere; else evaluated again, so a type that names an opaque
/// definition being unfolded computes (docs/proposals/opaque-definitions.md
/// §6.4: a body sees `start: Code` as `start: Nat` when it unfolds `Code`).
///
/// The stored type has every definition unfolded. While gluing, a type that
/// names a definition is evaluated again, so the definitions written in it
/// stay as calls: in `codes: List Code`, a parameter or a constant, `Code`
/// is kept, and dot notation finds `Code`'s namespace on anything inferred
/// from `codes`. A type that names none is the same either way, and isn't
/// evaluated again.
pub fn def_ty(g: &Globals, id: DefId) -> stitchwort_core::budget::Result<stitchwort_core::Value> {
    let def = g.def(id);
    if g.glue.get() && def.ty.subterms().any(|(t, _)| matches!(t, Term::Def(_))) {
        stitchwort_core::value::eval(g, &[], &def.ty)
    } else {
        k::def_type(g, def)
    }
}
