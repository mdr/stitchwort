//! The kernel's checking API, as the elaborator uses it. Everything is
//! re-exported unchanged except the declare and define calls, which are
//! timed for `STITCHWORT_TIMINGS` (`timings.rs`). The kernel crate itself
//! has no timing code. A definition refused only because it uses
//! unfinished declarations (an open goal, `?`) is reported as unfinished,
//! not as an error (`goals.rs`); the kernel's verdict is unchanged.

use stitchwort_core::Ev;
use stitchwort_core::check as k;
use stitchwort_core::globals::HashKey;
use stitchwort_core::{DataId, DefId, Kernel, Name, Sort, Term, pretty};
use stitchwort_syntax::{Diagnostic, Span};

pub use k::*;

use crate::state::{ScopedCell, Tables, Unit};
use crate::timings::kernel_call;

type Result<T> = std::result::Result<T, Diagnostic>;

/// A kernel refusal, recorded for the fuzzer: what it said, and where.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rejection {
    /// Its stable diagnostic code.
    pub code: &'static str,
    /// Its message, before the elaborator rewords or drops it.
    pub message: String,
    /// The source location it blamed.
    pub location: RejectionLocation,
}

/// Where a [`Rejection`] happened.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RejectionLocation {
    /// The source span of the kernel diagnostic's primary label.
    Span(Span),
    /// The declaration being checked, when the kernel gave no span. A
    /// diagnostic matches it when its span lies inside it.
    Declaration(Span),
}

/// A kernel call, timed, with its refusal recorded for the fuzzer. The
/// kernel takes its own modes (gluing off but for a body, D483; no
/// transparency it doesn't set; erasure off) whatever the elaborator's are
/// (`machine::in_kernel_modes`, D2294).
///
/// `declaration` is the span of the declaration being checked, used when the
/// kernel's refusal names no source location.
fn timed<T>(
    g: &mut Kernel,
    declaration: Span,
    f: impl FnOnce(&mut Kernel) -> Result<T>,
) -> Result<T> {
    let out = kernel_call(|| f(g));
    if let Err(d) = &out
        && (RECORDING.get() || debug_wanted())
    {
        let location = match d.labels.first().map(|label| label.span) {
            Some(span) if span != Span::NOWHERE => RejectionLocation::Span(span),
            _ => RejectionLocation::Declaration(declaration),
        };
        let rejection = Rejection {
            code: d.code,
            message: d.message.clone(),
            location,
        };
        if debug_wanted() {
            print_rejection(g, declaration, &rejection);
        }
        if RECORDING.get() {
            REJECTIONS.with(|r| r.borrow_mut().push(rejection));
        }
    }
    out
}

/// Whether `STITCHWORT_KERNEL_DEBUG` is on. Read once.
fn debug_wanted() -> bool {
    static WANTED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *WANTED.get_or_init(|| stitchwort_core::env_flag::env_flag("STITCHWORT_KERNEL_DEBUG"))
}

/// Under `STITCHWORT_KERNEL_DEBUG`, prints a kernel refusal to stderr as it
/// happens, before the elaborator rewords or drops it: the declaration's
/// name (when the kernel already holds it; a refused `declare` has none),
/// the code, the message and the span (file id and byte range).
fn print_rejection(g: &Kernel, declaration: Span, rejection: &Rejection) {
    let name = g
        .env
        .defs()
        .iter()
        .rev()
        .find(|def| def.span() == declaration)
        .map_or_else(
            || "(not yet declared)".to_string(),
            |def| def.path().to_string(),
        );
    let (kind, span) = match rejection.location {
        RejectionLocation::Span(span) => ("span", span),
        RejectionLocation::Declaration(span) => ("declaration span", span),
    };
    eprintln!(
        "kernel refused {name}: {}: {} ({kind} file {:?} {}..{})",
        rejection.code, rejection.message, span.file, span.start, span.end
    );
}

thread_local! {
    /// Whether [`REJECTIONS`] records, on this thread. Off unless a test
    /// turns it on, so a long-running session (the language server) doesn't
    /// keep every refusal.
    static RECORDING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The code, message and location of every error the kernel returned to
    /// a declare or define call on this thread while recording, since
    /// [`take_rejections`] was last called. For the elaborator fuzzer
    /// (`crates/driver/tests/fuzz_elab.rs`): the kernel's refusal of a term
    /// the elaborator built looks like any other diagnostic, so a test that
    /// wants to tell the two apart has to see what the kernel said before the
    /// elaborator reworded or dropped it.
    static REJECTIONS: std::cell::RefCell<Vec<Rejection>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

thread_local! {
    /// The names already dumped under `STITCHWORT_DUMP_KERNEL` on this
    /// thread: a declaration checked twice (a retry, a live update) is
    /// printed once.
    static DUMPED: std::cell::RefCell<stitchwort_core::collections::HashSet<String>> =
        std::cell::RefCell::new(stitchwort_core::collections::HashSet::default());
}

/// The declaration `STITCHWORT_DUMP_KERNEL` names, if it is set. Read once.
fn dump_wanted() -> Option<&'static str> {
    static WANTED: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    WANTED
        .get_or_init(|| std::env::var("STITCHWORT_DUMP_KERNEL").ok())
        .as_deref()
}

/// With `STITCHWORT_DUMP_KERNEL` set to a declaration's full name, prints
/// the type and value the kernel is given for it, after zonking and
/// saturation: exactly the terms it checks.
fn dump_kernel_declaration(g: &Kernel, members: &[(DefId, Term)]) {
    let Some(wanted) = dump_wanted() else {
        return;
    };
    for (id, body) in members {
        let def = g.def(*id);
        let name = def.path().to_string();
        if name != wanted {
            continue;
        }
        let fresh = DUMPED.with(|dumped| dumped.borrow_mut().insert(name.clone()));
        if !fresh {
            continue;
        }
        let ev = g.ev();
        eprintln!("kernel dump: {name}");
        eprintln!("  type: {}", pretty::term(&ev, &[], def.ty()));
        eprintln!("  value: {}", pretty::term(&ev, &[], body));
    }
}

/// Starts or stops recording the kernel's rejections on this thread: see
/// `REJECTIONS`.
pub fn record_rejections(on: bool) {
    RECORDING.set(on);
}

/// Returns (and clears) the kernel's rejections on this thread: see
/// `REJECTIONS`.
pub fn take_rejections() -> Vec<Rejection> {
    REJECTIONS.with(|r| std::mem::take(&mut *r.borrow_mut()))
}

/// `f` with gluing off: for the kernel's inference, which `rewrite` and
/// matching use on the elaborator's terms.
pub fn without_glue<T>(g: &Ev, f: impl FnOnce() -> T) -> T {
    let _off = ScopedCell::set(&g.machine.glue, false);
    f()
}

pub fn define_def(g: &mut Kernel, tables: &Tables, id: DefId, body: &Term) -> Result<()> {
    define_group(g, tables, &[(id, body.clone())])
}

/// Defines a group, with every partial occurrence of a member first applied
/// to all its parameters (`saturate.rs`).
pub fn define_group(g: &mut Kernel, tables: &Tables, members: &[(DefId, Term)]) -> Result<()> {
    let (members, expanded) = crate::saturate::saturate(&g.ev(), members)?;
    dump_kernel_declaration(g, &members);
    let declaration = members
        .first()
        .map_or(Span::NOWHERE, |(id, _)| g.def(*id).span());
    timed(g, declaration, |g| k::define_group(g, &members)).map_err(|d| {
        let own: Vec<HashKey> = members.iter().map(|(id, _)| HashKey::Def(*id)).collect();
        // A member's type was declared without its failed references being
        // refused: the kernel finds them here, with the body's.
        let ev = g.ev();
        let types = members.iter().map(|(id, _)| ev.def(*id).ty());
        let d = crate::goals::unfinished_dependency(
            &ev,
            tables,
            members.iter().map(|(_, t)| t).chain(types),
            &own,
            d,
        );
        crate::saturate::explain(d, &expanded)
    })
}

/// Defines `members` as the groups their checked bodies make: each set of
/// definitions that really call each other (by `DefId`, a strongly connected
/// component of their references), every group after the ones it uses.
/// Stops at the first refusal, leaving the members after it pending.
///
/// A group the module's dependency analysis made can be bigger than that:
/// a dot call such as `tree.size` is linked there to every `size` the
/// receiver's type might have, before types are known. Members joined only
/// by such a guess don't call each other, so no call between them is on a
/// cycle; checked together, though, a bare occurrence of one in another
/// (`boxes.map Box.size`) is refused as an unsaturated recursive call
/// (SW-3738). Split, each group's termination is decided from the same
/// cycles, so this only accepts more.
pub fn define_reference_groups(
    g: &mut Kernel,
    tables: &Tables,
    members: &[(DefId, Term)],
) -> Result<()> {
    let ev = g.ev();
    let edges: Vec<Vec<usize>> = members
        .iter()
        .map(|(id, body)| {
            let ty = ev.def(*id).ty();
            let mut out: Vec<usize> = [body, ty]
                .into_iter()
                .flat_map(Term::subterms)
                .filter_map(|(t, _)| match t {
                    Term::Def(d) => members.iter().position(|(m, _)| m == d),
                    _ => None,
                })
                .collect();
            out.sort_unstable();
            out.dedup();
            out
        })
        .collect();
    // Tarjan's algorithm finishes a component only after every component
    // it reaches, so each comes after the ones it uses.
    for mut component in crate::module::tarjan(&edges) {
        component.sort_unstable();
        let group: Vec<(DefId, Term)> = component.iter().map(|&i| members[i].clone()).collect();
        define_group(g, tables, &group)?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn declare_def(
    g: &mut Kernel,
    tables: &Tables,
    unit: &Unit,
    name: &Name,
    ty: &Term,
    theorem: bool,
    export: bool,
    span: Span,
) -> Result<DefId> {
    let path = unit.path(name);
    timed(g, span, |g| {
        k::declare_def(g, name, &path, ty, theorem, export, span)
    })
    .map_err(|d| crate::goals::unfinished_dependency(&g.ev(), tables, [ty], &[], d))
}

pub fn retype_def(g: &mut Kernel, tables: &Tables, id: DefId, ty: &Term) -> Result<()> {
    let declaration = g.def(id).span();
    timed(g, declaration, |g| k::retype_def(g, id, ty))
        .map_err(|d| crate::goals::unfinished_dependency(&g.ev(), tables, [ty], &[], d))
}

pub fn declare_data_group(
    g: &mut Kernel,
    params: Vec<(Name, Term)>,
    sort: Sort,
    members: Vec<(Name, Name, Span)>,
) -> Result<Vec<DataId>> {
    let declaration = members.first().map_or(Span::NOWHERE, |(_, _, span)| *span);
    timed(g, declaration, |g| {
        k::declare_data_group(g, params, sort, members)
    })
}

pub fn declare_indexed_data_group(
    g: &mut Kernel,
    params: Vec<(Name, Term)>,
    sort: Sort,
    members: Vec<DataDecl>,
) -> Result<Vec<DataId>> {
    let declaration = members.first().map_or(Span::NOWHERE, |member| member.span);
    timed(g, declaration, |g| {
        k::declare_indexed_data_group(g, params, sort, members)
    })
}

pub fn define_data_group(g: &mut Kernel, members: Vec<(DataId, Vec<CtorDecl>)>) -> Result<()> {
    let declaration = members
        .first()
        .map_or(Span::NOWHERE, |(id, _)| g.data(*id).span());
    timed(g, declaration, |g| k::define_data_group(g, members))
}

// The check cache's trusted admission (`check::admit_trusted_*`, D1660),
// timed as kernel calls too. Only `cache::admit_replayed` calls these.

pub fn admit_trusted_def(
    g: &mut Kernel,
    name: &Name,
    path: &Name,
    ty: &Term,
    theorem: bool,
    span: Span,
) -> Result<DefId> {
    timed(g, span, |g| {
        k::admit_trusted_def(g, name, path, ty, theorem, span)
    })
}

/// Its one caller is the replay of an entry read without proofs
/// (`cache::Elaborator::admit_stated`).
pub fn admit_trusted_stated(
    g: &mut Kernel,
    name: &Name,
    path: &Name,
    ty: &Term,
    span: Span,
) -> Result<DefId> {
    timed(g, span, |g| {
        k::admit_trusted_stated(g, name, path, ty, span)
    })
}

/// Its one caller is the replay of an interface entry
/// (`cache::Elaborator::admit_stated`).
pub fn admit_trusted_unproved(
    g: &mut Kernel,
    name: &Name,
    path: &Name,
    ty: &Term,
    span: Span,
) -> Result<DefId> {
    timed(g, span, |g| {
        k::admit_trusted_unproved(g, name, path, ty, span)
    })
}

/// Its one caller is the interface pass (`Elaborator::group_checked`).
pub fn leave_stated(g: &mut Kernel, id: DefId) -> Result<()> {
    let declaration = g.def(id).span();
    timed(g, declaration, |g| k::leave_stated(g, id))
}

pub fn admit_trusted_group(g: &mut Kernel, members: &[(DefId, Term)]) -> Result<()> {
    let declaration = members
        .first()
        .map_or(Span::NOWHERE, |(id, _)| g.def(*id).span());
    timed(g, declaration, |g| k::admit_trusted_group(g, members))
}

pub fn admit_trusted_run_body(g: &mut Kernel, id: DefId, body: &Term) -> Result<()> {
    let declaration = g.def(id).span();
    timed(g, declaration, |g| k::admit_trusted_run_body(g, id, body))
}

pub fn admit_trusted_data_decls(
    g: &mut Kernel,
    params: Vec<(Name, Term)>,
    sort: Sort,
    members: Vec<DataDecl>,
) -> Result<Vec<DataId>> {
    let declaration = members.first().map_or(Span::NOWHERE, |member| member.span);
    timed(g, declaration, |g| {
        k::admit_trusted_data_decls(g, params, sort, members)
    })
}

pub fn admit_trusted_data_group(
    g: &mut Kernel,
    members: Vec<(DataId, Vec<stitchwort_core::globals::Ctor>)>,
    recompute_sorts: bool,
) -> Result<()> {
    let declaration = members
        .first()
        .map_or(Span::NOWHERE, |(id, _)| g.data(*id).span());
    timed(g, declaration, |g| {
        k::admit_trusted_data_group(g, members, recompute_sorts)
    })
}

// The check cache's re-check (check-cache-across-updates.md §4.4, stage
// 2): an entry's terms through the checking calls, timed as kernel calls.
// The terms are the ones the kernel gave back when they were first checked,
// already saturated (`define_group` above), so they go to the kernel as
// they are.

// Marks are cleared first: the kernel derives them again, so a mark an
// older kernel stored and this one derives differently is a quiet miss of
// nothing, not `E-MALFORMED` on a term that checks.

pub fn recheck_def(
    g: &mut Kernel,
    name: &Name,
    path: &Name,
    ty: &Term,
    theorem: bool,
    span: Span,
) -> Result<DefId> {
    timed(g, span, |g| {
        let ty = unmarked(g, ty)?;
        k::declare_def(g, name, path, &ty, theorem, false, span)
    })
}

pub fn recheck_group(g: &mut Kernel, members: &[(DefId, Term)]) -> Result<()> {
    let declaration = members
        .first()
        .map_or(Span::NOWHERE, |(id, _)| g.def(*id).span());
    timed(g, declaration, |g| {
        let members = members
            .iter()
            .map(|(id, body)| Ok((*id, unmarked(g, body)?)))
            .collect::<Result<Vec<_>>>()?;
        k::define_group(g, &members)
    })
}

pub fn recheck_run_body(g: &mut Kernel, id: DefId, body: &Term) -> Result<()> {
    let declaration = g.def(id).span();
    timed(g, declaration, |g| {
        let body = unmarked(g, body)?;
        k::set_run_body(g, id, &body)
    })
}

fn unmarked(g: &Kernel, term: &Term) -> Result<Term> {
    Ok(term.without_marks(&g.ev())?)
}

/// The kernel's substitution for the elaborator's case splits, in a context
/// whose environment is `env` (`check::substitute_in`): each value is read
/// back with its calls folded (`value::quote_folded`), so a refined context
/// keeps what was written (`isWall p = False`, not the dungeon map `isWall`
/// computes from) while staying convertible with the kernel's normal form,
/// and a variable known apart from some numbers stays so.
pub fn substitute_folded(
    g: &Ev,
    env: &[stitchwort_core::Value],
    x: usize,
    value: &stitchwort_core::Value,
    values: &[stitchwort_core::Value],
) -> stitchwort_core::budget::Result<Vec<stitchwort_core::Value>> {
    k::substitute_in(g, env, x, value, values)
}

/// Each of `values`, with `level` variables in scope, with the solved
/// metavariables in it replaced by their solutions (`check::reread`).
pub fn reread(
    g: &Ev,
    level: usize,
    values: &[stitchwort_core::Value],
) -> stitchwort_core::budget::Result<Vec<stitchwort_core::Value>> {
    k::reread(g, level, values)
}

/// Each of `values` read back folded and evaluated again in `env`
/// (`check::reread_in`).
pub fn reread_in(
    g: &Ev,
    env: &[stitchwort_core::Value],
    values: &[stitchwort_core::Value],
) -> stitchwort_core::budget::Result<Vec<stitchwort_core::Value>> {
    k::reread_in(g, env, values)
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
pub fn def_ty(g: &Ev, id: DefId) -> stitchwort_core::budget::Result<stitchwort_core::Value> {
    let def = g.def(id);
    if g.machine.glue.get() && def.ty().subterms().any(|(t, _)| matches!(t, Term::Def(_))) {
        stitchwort_core::value::eval(g, &[], def.ty())
    } else {
        k::def_type(g, def)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::Ordering;

    use stitchwort_core::budget::{Limits, Saved};
    use stitchwort_core::globals::KernelMark;
    use stitchwort_core::{Sort, Term, Value};
    use stitchwort_syntax::{SourceMap, Span};

    use crate::Elaborator;

    /// SW-1995: a skipped equation or induction rewinds the environment
    /// partway through a declaration's check, which must leave the
    /// operation's budget as it was; clearing it (as `Kernel::rewind` does)
    /// left the rest of the declaration with no limits.
    #[test]
    fn rewinding_globals_partway_through_an_operation_keeps_its_budget() {
        let mut e = Elaborator::new();
        let (saved, floor) = start_operation(&mut e);
        let mark = declare_one(&mut e);
        note_cancellation(&e);
        e.rewind_globals(&mark);
        assert_eq!(e.kernel.mark().defs(), mark.defs(), "the def is gone");
        assert_operation_kept(&e, floor);
        e.kernel.machine.budget.restore(saved);
    }

    /// `Kernel::forget_since` leaves the running operation alone, and
    /// `Kernel::rewind` ends it: the difference admitting a replayed check
    /// cache entry depends on (it uses the first, partway through a
    /// namespace's check).
    #[test]
    fn forget_since_keeps_the_operation_and_rewind_ends_it() {
        let mut e = Elaborator::new();
        let (saved, floor) = start_operation(&mut e);
        let mark = declare_one(&mut e);
        note_cancellation(&e);
        e.kernel.forget_since(&mark);
        assert_eq!(e.kernel.mark().defs(), mark.defs(), "the def is gone");
        assert_operation_kept(&e, floor);

        e.kernel.rewind(&mark);
        let budget = &e.kernel.machine.budget;
        assert_eq!(budget.size_limit(), u64::MAX, "the limits are cleared");
        assert_eq!(budget.stack_floor(), 0, "the stack floor is cleared");
        assert!(!budget.cancelled(), "the noted cancellation is cleared");
        assert!(
            budget.cancel_flag().unwrap().load(Ordering::Relaxed),
            "the shared flag is its owner's to clear"
        );
        e.kernel.machine.budget.restore(saved);
    }

    fn limits() -> Limits {
        Limits {
            size: 12_345,
            ..Limits::for_stack(1 << 20)
        }
    }

    /// Starts an operation with a size limit, and returns what ends it and
    /// its stack floor.
    fn start_operation(e: &mut Elaborator) -> (Saved, usize) {
        let budget = &e.kernel.machine.budget;
        let saved = budget.start(limits());
        let floor = budget.stack_floor();
        assert_ne!(floor, 0, "the operation has a stack floor");
        (saved, floor)
    }

    /// Sets the cancellation flag, and has the operation see it: any
    /// operation started now notes it.
    fn note_cancellation(e: &Elaborator) {
        let budget = &e.kernel.machine.budget;
        budget.set_cancel_flag(Default::default());
        budget.watch_cancel(true);
        budget.cancel_flag().unwrap().store(true, Ordering::Relaxed);
        let inner = budget.start(limits());
        budget.restore(inner);
        assert!(budget.cancelled());
    }

    fn declare_one(e: &mut Elaborator) -> KernelMark {
        let span = Span::point(SourceMap::new().add("t", ""), 0);
        let mark = e.kernel.mark();
        stitchwort_core::check::declare_def(
            &mut e.kernel,
            &"t".into(),
            &"t".into(),
            &Term::Sort(Sort::Type(1)),
            false,
            false,
            span,
        )
        .unwrap();
        mark
    }

    fn assert_operation_kept(e: &Elaborator, floor: usize) {
        let budget = &e.kernel.machine.budget;
        assert_eq!(budget.size_limit(), 12_345, "the size limit survives");
        assert_eq!(budget.stack_floor(), floor, "the stack floor survives");
        assert!(budget.cancelled(), "the noted cancellation survives");
    }

    /// Admission sees no metavariable solutions (D2291, globals-split.md
    /// G5): a term mentioning a metavariable the elaborator has solved is
    /// refused, as an unsolved one is, in a type and in a body.
    #[test]
    fn admission_refuses_a_solved_metavariable() {
        let mut e = Elaborator::new();
        let _operation = e.kernel.machine.budget.start(Limits::default());
        let span = Span::point(SourceMap::new().add("t", ""), 0);
        let m = e.attempt.store.new_meta(span);
        e.attempt.store.solve_meta(m, Value::Sort(Sort::Type(0)));
        assert!(
            e.ev().meta_solution(m).is_some(),
            "solved for the elaborator"
        );
        assert!(
            e.kernel.ev().meta_solution(m).is_none(),
            "not for the kernel"
        );

        let in_type = stitchwort_core::check::declare_def(
            &mut e.kernel,
            &"t".into(),
            &"t".into(),
            &Term::Meta(m),
            false,
            false,
            span,
        );
        assert_eq!(in_type.err().map(|d| d.code), Some("E-MALFORMED"));

        let x = stitchwort_core::check::declare_def(
            &mut e.kernel,
            &"x".into(),
            &"x".into(),
            &Term::Sort(Sort::Type(1)),
            false,
            false,
            span,
        )
        .expect("declared");
        let in_body = stitchwort_core::check::define_def(&mut e.kernel, x, &Term::Meta(m));
        assert_eq!(in_body.err().map(|d| d.code), Some("E-MALFORMED"));
    }
}
