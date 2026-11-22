//! `STITCHWORT_ENV_METRICS=1`: how long closure environments are when the
//! evaluator extends one by a value, and how often the environment being
//! extended has no other holder, so that it could have grown in place
//! (docs/proposals/cheaper-values.md, step 0). The timings report
//! (`STITCHWORT_TIMINGS`, `check --timings`) prints them. Counted over the
//! whole process, every thread together; nothing reads them but the report.

use std::fmt::Write;
use std::sync::atomic::{AtomicU8, AtomicU64, Ordering::Relaxed};

/// Lengths below this are counted one by one; longer ones in power-of-two
/// buckets from here up, the last open-ended.
const EXACT: usize = 32;
const BUCKETS: usize = EXACT + 5;

static EXTENDED: [AtomicU64; BUCKETS] = [const { AtomicU64::new(0) }; BUCKETS];
static UNSHARED: [AtomicU64; BUCKETS] = [const { AtomicU64::new(0) }; BUCKETS];

/// 0 before the variable is read, then 1 for off and 2 for on: one relaxed
/// load on the evaluator's path when off.
static STATE: AtomicU8 = AtomicU8::new(0);

/// Whether `STITCHWORT_ENV_METRICS=1`.
#[inline]
pub fn on() -> bool {
    match STATE.load(Relaxed) {
        0 => read_variable(),
        state => state == 2,
    }
}

#[cold]
fn read_variable() -> bool {
    let on = std::env::var("STITCHWORT_ENV_METRICS").is_ok_and(|v| v == "1");
    STATE.store(if on { 2 } else { 1 }, Relaxed);
    on
}

fn bucket(len: usize) -> usize {
    if len < EXACT {
        len
    } else {
        // 32-63 is EXACT, 64-127 the next, and so on.
        let above =
            (usize::BITS - 1 - len.leading_zeros()) as usize - EXACT.trailing_zeros() as usize;
        (EXACT + above).min(BUCKETS - 1)
    }
}

fn label(bucket: usize) -> String {
    if bucket < EXACT {
        bucket.to_string()
    } else if bucket == BUCKETS - 1 {
        format!("{}+", EXACT << (bucket - EXACT))
    } else {
        let low = EXACT << (bucket - EXACT);
        format!("{}-{}", low, 2 * low - 1)
    }
}

/// Counts an extension of an environment of `len` values; `unshared` if
/// nothing else held it.
#[inline(never)]
pub fn record(len: usize, unshared: bool) {
    let b = bucket(len);
    EXTENDED[b].fetch_add(1, Relaxed);
    if unshared {
        UNSHARED[b].fetch_add(1, Relaxed);
    }
}

/// The report's lines, if the counters are on: per length, the extensions,
/// their share of all, the running share, and the share unshared.
pub fn report() -> Option<String> {
    if !on() {
        return None;
    }
    let counts: Vec<(u64, u64)> = (0..BUCKETS)
        .map(|b| (EXTENDED[b].load(Relaxed), UNSHARED[b].load(Relaxed)))
        .collect();
    let total: u64 = counts.iter().map(|c| c.0).sum();
    let unshared: u64 = counts.iter().map(|c| c.1).sum();
    let pct = |n: u64, of: u64| {
        if of == 0 {
            0.0
        } else {
            100.0 * n as f64 / of as f64
        }
    };
    let mut out = String::new();
    let _ = writeln!(
        out,
        "environment extensions: {total}, {unshared} ({:.1}%) of an environment nothing else held; \
         size_of Value {} bytes, Elim {} bytes",
        pct(unshared, total),
        std::mem::size_of::<crate::value::Value>(),
        std::mem::size_of::<crate::value::Elim>(),
    );
    let _ = writeln!(
        out,
        "{:>9}  {:>14}  {:>7}  {:>7}  {:>9}",
        "length", "extensions", "share", "up to", "unshared"
    );
    let mut running = 0;
    for (b, &(n, u)) in counts.iter().enumerate() {
        if n == 0 {
            continue;
        }
        running += n;
        let _ = writeln!(
            out,
            "{:>9}  {:>14}  {:>6.2}%  {:>6.2}%  {:>8.1}%",
            label(b),
            n,
            pct(n, total),
            pct(running, total),
            pct(u, n)
        );
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lengths_fall_in_their_buckets() {
        assert_eq!(bucket(0), 0);
        assert_eq!(bucket(31), 31);
        assert_eq!(label(bucket(32)), "32-63");
        assert_eq!(label(bucket(63)), "32-63");
        assert_eq!(label(bucket(64)), "64-127");
        assert_eq!(label(bucket(511)), "256-511");
        assert_eq!(label(bucket(512)), "512+");
        assert_eq!(label(bucket(usize::MAX)), "512+");
    }
}
