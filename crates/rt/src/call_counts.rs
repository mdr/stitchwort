//! Counts of native code's calls into the runtime, for profiling
//! (docs/reviews/SW-2296-native-profiles.md): how often each helper
//! (`sw_ctor`, `sw_prim` and the rest) is called, and `sw_prim`'s and
//! `sw_prim_owned`'s calls split by operation. A sampling profiler shows
//! where the time goes, but not how many calls it is spread over, nor which
//! operation a generic helper ran. Beyond the helpers, the report splits
//! `sw_apply_prepare` by the kind of function value applied, counts the
//! apply-cache misses `sw_apply_cached` serves (per call site and by
//! whether the cache was cold), and counts the effect runtime's pushes,
//! pops and routes, the routes by handler clause and operation
//! (docs/proposals/parse-runtime.md, stage 0). Cache hits are not counted:
//! they are decided inline in compiled code, which has no hook.
//!
//! With the cargo feature `call-counts`, every counted helper adds one to a
//! relaxed atomic, and a native run prints the counts to standard error at
//! its end when the environment variable `STITCHWORT_CALL_COUNTS` is set.
//! Without the feature, every hook is an empty `#[inline(always)]`
//! function. The feature is for a runtime library built apart, which a
//! profiling build links in place of the usual one (`STITCHWORT_RUNTIME`;
//! `dev/profile-native` does both), so no shipped or test build has it.

use crate::ir::PrimOp;

/// The helpers counted. `Prim` and `PrimOwned` are counted by [`hit_op`].
#[derive(Clone, Copy)]
#[cfg_attr(not(feature = "call-counts"), allow(dead_code))]
pub(crate) enum Helper {
    Ctor,
    CtorReuse,
    DropWords,
    FreeEmptied,
    Unpack,
    DropReuse,
    Prim,
    PrimOwned,
    Test,
    NatPred,
    NumSwitch,
    ApplyCached,
    ApplyPrepare,
    Closure,
    Pap,
    Unary,
    Bind,
    EffStep,
}

#[cfg(feature = "call-counts")]
const HELPERS: usize = Helper::EffStep as usize + 1;

#[cfg(feature = "call-counts")]
const HELPER_NAMES: [&str; HELPERS] = [
    "sw_ctor",
    "sw_ctor_reuse",
    "sw_drop_words",
    "sw_free_emptied",
    "sw_unpack",
    "sw_drop_reuse",
    "sw_prim",
    "sw_prim_owned",
    "sw_test",
    "sw_nat_pred",
    "sw_num_switch",
    "sw_apply_cached",
    "sw_apply_prepare",
    "sw_closure",
    "sw_pap",
    "sw_unary",
    "sw_bind",
    "sw_eff_step",
];

/// The kind of function value `sw_apply_prepare` was given (each head it
/// enters: `bind (Done x) k` goes round again with `k`).
#[derive(Clone, Copy)]
#[cfg_attr(not(feature = "call-counts"), allow(dead_code))]
pub(crate) enum ApplyKind {
    /// A partial application given exactly its remaining arguments, built
    /// in the plan with no vectors (the fast path).
    PapFast,
    /// Any other partial application (too few or too many arguments, or a
    /// head that isn't compiled code).
    PapSlow,
    GlobalFunction,
    GlobalNative,
    /// `bind` as a value.
    EffectBind,
    /// A fold, `translate`, `runPure` or state-passing handler as a value.
    EffectOther,
    Closure,
    DoneK,
    StateK,
    JumpK,
    DelayK,
    LazyResume,
    EagerResume,
    StateRun,
    Other,
}

#[cfg(feature = "call-counts")]
const APPLY_KINDS: usize = ApplyKind::Other as usize + 1;

#[cfg(feature = "call-counts")]
const APPLY_KIND_NAMES: [&str; APPLY_KINDS] = [
    "partial application, fast path",
    "partial application, slow path",
    "global function (not a fast-path pap)",
    "global native",
    "effect native: bind",
    "effect native: fold/translate/runPure/state handler",
    "closure",
    "DoneK",
    "StateK",
    "JumpK",
    "DelayK",
    "lazy resumption",
    "eager resumption",
    "StateRun",
    "other",
];

/// Events of the effect runtime that native code's steps pass through.
#[derive(Clone, Copy)]
#[cfg_attr(not(feature = "call-counts"), allow(dead_code))]
pub(crate) enum Event {
    /// A `Bind` node's continuation pushed on the pending list.
    Push,
    /// A `Done` met a continuation, which is popped.
    Pop,
    /// A `Done` ended the computation.
    Finish,
    /// An operation routed to a fold, `translate` or state-passing handler
    /// (a call of its clause).
    Route,
    /// An operation reaching `Handler::Step`.
    RouteStep,
    /// `sw_resume_begin`: an eager resumption or state function entered.
    ResumeBegin,
    /// `sw_state_step`.
    StateStep,
    /// A miss in an apply cache that `sw_apply_cached` served with code.
    CacheMissResolved,
    /// A miss that sent the apply to `sw_apply_prepare`.
    CacheMissUnresolved,
    /// A miss in a cache that had never held a target.
    CacheCold,
}

#[cfg(feature = "call-counts")]
const EVENTS: usize = Event::CacheCold as usize + 1;

#[cfg(feature = "call-counts")]
const EVENT_NAMES: [&str; EVENTS] = [
    "bind node pushed (continuation pushed)",
    "continuation popped (Done met a pending one)",
    "computation finished (Done, none pending)",
    "operation routed to a handler clause (fold/state/translate)",
    "operation reached Handler::Step",
    "sw_resume_begin",
    "sw_state_step",
    "apply-cache miss served with code (global/closure)",
    "apply-cache miss sent to sw_apply_prepare",
    "apply-cache miss in a cold cache",
];

/// Whether this build counts.
pub const ENABLED: bool = cfg!(feature = "call-counts");

#[cfg(feature = "call-counts")]
mod enabled {
    use std::collections::BTreeMap;
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::{APPLY_KINDS, EVENTS, HELPERS};

    pub(super) static HELPER_COUNTS: [AtomicU64; HELPERS] = [const { AtomicU64::new(0) }; HELPERS];
    /// Per operation, by its number in the program's table of operations
    /// (`Numbering::op`), plain and owned; numbers past the end share the
    /// last slot.
    pub(super) const OPS: usize = 4096;
    pub(super) static OP_COUNTS: [[AtomicU64; OPS]; 2] =
        [const { [const { AtomicU64::new(0) }; OPS] }; 2];
    /// Each operation's name, made at its first call.
    pub(super) static OP_NAMES: Mutex<BTreeMap<(usize, usize), String>> =
        Mutex::new(BTreeMap::new());

    pub(super) static APPLY_COUNTS: [AtomicU64; APPLY_KINDS] =
        [const { AtomicU64::new(0) }; APPLY_KINDS];
    pub(super) static EVENT_COUNTS: [AtomicU64; EVENTS] = [const { AtomicU64::new(0) }; EVENTS];
    /// Apply-cache misses per cache (call site), by its address.
    pub(super) static SITE_MISSES: Mutex<BTreeMap<usize, u64>> = Mutex::new(BTreeMap::new());
    /// Routes per (handler clause, operation): the clause is described
    /// (`global NAME` or `lambda N`), the operation as its constructor tag
    /// inside the `L`/`R` injections it had been wrapped in.
    pub(super) static ROUTES: Mutex<BTreeMap<(String, String), u64>> = Mutex::new(BTreeMap::new());

    pub(super) fn add(i: usize) {
        HELPER_COUNTS[i].fetch_add(1, Ordering::Relaxed);
    }

    pub(super) fn load(i: usize) -> u64 {
        HELPER_COUNTS[i].load(Ordering::Relaxed)
    }
}

/// One call of `helper`.
#[inline(always)]
pub(crate) fn hit(helper: Helper) {
    #[cfg(feature = "call-counts")]
    enabled::add(helper as usize);
    #[cfg(not(feature = "call-counts"))]
    let _ = helper;
}

/// One `sw_apply_prepare` entering a function value of `kind`.
#[inline(always)]
pub(crate) fn hit_apply(kind: ApplyKind) {
    #[cfg(feature = "call-counts")]
    enabled::APPLY_COUNTS[kind as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    #[cfg(not(feature = "call-counts"))]
    let _ = kind;
}

/// One `event` of the effect runtime or apply caches.
#[inline(always)]
pub(crate) fn hit_event(event: Event) {
    #[cfg(feature = "call-counts")]
    enabled::EVENT_COUNTS[event as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    #[cfg(not(feature = "call-counts"))]
    let _ = event;
}

/// A miss in the apply cache at address `site`.
#[inline(always)]
pub(crate) fn hit_site_miss(site: usize) {
    #[cfg(feature = "call-counts")]
    {
        *enabled::SITE_MISSES
            .lock()
            .unwrap()
            .entry(site)
            .or_insert(0) += 1;
    }
    #[cfg(not(feature = "call-counts"))]
    let _ = site;
}

/// An operation routed to a handler: `clause` and `op` describe the
/// handler's clause and the operation, made only with the feature.
#[inline(always)]
pub(crate) fn hit_route(clause: impl FnOnce() -> String, op: impl FnOnce() -> String) {
    #[cfg(feature = "call-counts")]
    {
        *enabled::ROUTES
            .lock()
            .unwrap()
            .entry((clause(), op()))
            .or_insert(0) += 1;
    }
    #[cfg(not(feature = "call-counts"))]
    let _ = (clause, op);
}

/// One call of `sw_prim` (`owned`: `sw_prim_owned`) running `op`, number
/// `number` in the program's table of operations.
#[inline(always)]
pub(crate) fn hit_op(number: u32, op: PrimOp, owned: bool) {
    #[cfg(feature = "call-counts")]
    {
        use std::sync::atomic::Ordering;
        enabled::add(if owned {
            Helper::PrimOwned
        } else {
            Helper::Prim
        } as usize);
        let at = (number as usize).min(enabled::OPS - 1);
        if enabled::OP_COUNTS[owned as usize][at].fetch_add(1, Ordering::Relaxed) == 0 {
            enabled::OP_NAMES
                .lock()
                .unwrap()
                .entry((owned as usize, at))
                .or_insert_with(|| format!("{}{op:?}", if owned { "owned " } else { "" }));
        }
    }
    #[cfg(not(feature = "call-counts"))]
    let _ = (number, op, owned);
}

/// The counts so far, as lines: each helper called, then each operation,
/// most calls first.
pub fn report() -> Vec<String> {
    #[cfg(feature = "call-counts")]
    {
        let mut lines = vec!["runtime calls from native code:".to_string()];
        let mut helpers: Vec<(u64, &str)> = (0..HELPERS)
            .map(|i| (enabled::load(i), HELPER_NAMES[i]))
            .filter(|(n, _)| *n > 0)
            .collect();
        helpers.sort_by_key(|h| std::cmp::Reverse(h.0));
        for (n, name) in helpers {
            lines.push(format!("  {n:>14}  {name}"));
        }
        lines.push("sw_prim and sw_prim_owned by operation:".to_string());
        let names = enabled::OP_NAMES.lock().unwrap();
        let mut ops: Vec<(u64, &String)> = names
            .iter()
            .map(|(&(owned, at), name)| {
                let n = enabled::OP_COUNTS[owned][at].load(std::sync::atomic::Ordering::Relaxed);
                (n, name)
            })
            .collect();
        ops.sort_by_key(|o| std::cmp::Reverse(o.0));
        for (n, name) in ops {
            lines.push(format!("  {n:>14}  {name}"));
        }
        use std::sync::atomic::Ordering::Relaxed;
        let total: u64 = enabled::APPLY_COUNTS.iter().map(|c| c.load(Relaxed)).sum();
        lines.push(format!(
            "sw_apply_prepare by kind of function value entered ({total} in all; a bind continuing counts twice):"
        ));
        let mut kinds: Vec<(u64, &str)> = (0..APPLY_KINDS)
            .map(|i| (enabled::APPLY_COUNTS[i].load(Relaxed), APPLY_KIND_NAMES[i]))
            .filter(|(n, _)| *n > 0)
            .collect();
        kinds.sort_by_key(|k| std::cmp::Reverse(k.0));
        for (n, name) in kinds {
            lines.push(format!("  {n:>14}  {name}"));
        }
        lines.push("effect runtime and apply-cache events:".to_string());
        for (count, name) in enabled::EVENT_COUNTS.iter().zip(EVENT_NAMES) {
            let n = count.load(Relaxed);
            if n > 0 {
                lines.push(format!("  {n:>14}  {name}"));
            }
        }
        let sites = enabled::SITE_MISSES.lock().unwrap();
        let mut by_site: Vec<(u64, usize)> = sites.iter().map(|(&a, &n)| (n, a)).collect();
        by_site.sort_by_key(|s| std::cmp::Reverse(s.0));
        lines.push(format!(
            "apply-cache misses by call site ({} sites; top 8):",
            by_site.len()
        ));
        for (n, addr) in by_site.into_iter().take(8) {
            lines.push(format!("  {n:>14}  site {addr:#x}"));
        }
        let routes = enabled::ROUTES.lock().unwrap();
        let mut by_route: Vec<(u64, &(String, String))> =
            routes.iter().map(|(k, &n)| (n, k)).collect();
        by_route.sort_by_key(|r| std::cmp::Reverse(r.0));
        lines.push(format!(
            "operations routed, by handler clause and operation ({} pairs; top 40):",
            by_route.len()
        ));
        for (n, (clause, op)) in by_route.into_iter().take(40) {
            lines.push(format!("  {n:>14}  {clause}  {op}"));
        }
        lines
    }
    #[cfg(not(feature = "call-counts"))]
    Vec::new()
}

/// Prints [`report`] to standard error if this build counts and
/// `STITCHWORT_CALL_COUNTS` is set.
pub fn print_if_asked() {
    if ENABLED && std::env::var_os("STITCHWORT_CALL_COUNTS").is_some() {
        for line in report() {
            eprintln!("{line}");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::HoleOp;

    /// With the feature, the report lists each helper and operation with
    /// its count; without it, there is nothing to report. (The counts are
    /// process-wide, so this is the one test that counts.)
    #[test]
    fn the_report_counts_helpers_and_operations() {
        for _ in 0..3 {
            hit(Helper::Ctor);
        }
        hit_op(7, PrimOp::Hole(HoleOp::Fill), false);
        hit_op(7, PrimOp::Hole(HoleOp::Fill), false);
        hit_apply(ApplyKind::DoneK);
        hit_apply(ApplyKind::DoneK);
        hit_event(Event::Push);
        hit_site_miss(0x40);
        hit_route(|| "lambda 3".to_string(), || "tag 5".to_string());
        let report = report();
        if ENABLED {
            assert!(
                report
                    .iter()
                    .any(|l| l.ends_with("  sw_ctor") && l.trim_start().starts_with("3 ")),
                "{report:?}"
            );
            assert!(
                report
                    .iter()
                    .any(|l| l.ends_with("  sw_prim") && l.trim_start().starts_with("2 ")),
                "{report:?}"
            );
            assert!(
                report
                    .iter()
                    .any(|l| l.ends_with("  Hole(Fill)") && l.trim_start().starts_with("2 ")),
                "{report:?}"
            );
            for (count, name) in [
                ("2 ", "  DoneK"),
                ("1 ", "  bind node pushed (continuation pushed)"),
                ("1 ", "  site 0x40"),
                ("1 ", "  lambda 3  tag 5"),
            ] {
                assert!(
                    report
                        .iter()
                        .any(|l| l.ends_with(name) && l.trim_start().starts_with(count)),
                    "{name}: {report:?}"
                );
            }
        } else {
            assert!(report.is_empty());
        }
    }
}
