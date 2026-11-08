//! Counts of native code's calls into the runtime, for profiling
//! (docs/reviews/SW-2296-native-profiles.md): how often each helper
//! (`sw_ctor`, `sw_prim` and the rest) is called, and `sw_prim`'s and
//! `sw_prim_owned`'s calls split by operation. A sampling profiler shows
//! where the time goes, but not how many calls it is spread over, nor which
//! operation a generic helper ran.
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

/// Whether this build counts.
pub const ENABLED: bool = cfg!(feature = "call-counts");

#[cfg(feature = "call-counts")]
mod enabled {
    use std::collections::BTreeMap;
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::HELPERS;

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
        } else {
            assert!(report.is_empty());
        }
    }
}
