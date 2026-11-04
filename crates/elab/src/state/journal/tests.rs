//! The journal against a model (docs/proposals/elaborator-state.md §4.8.6,
//! item 1): a reference keeps a plain map and, for each open checkpoint, a
//! copy of it. Generated sequences of writes and of the journal's
//! operations, on both, must leave the same map after every step.

use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};

use super::*;

type Table = Logged<u8, u32>;
type J = Journal<usize>;

fn contents(t: &Table) -> BTreeMap<u8, u32> {
    t.iter().map(|(k, v)| (*k, *v)).collect()
}

/// The review's sequence (docs/reviews/elaborator-state-review.md,
/// concern 3): rewinding to one checkpoint twice, then to an older one.
#[test]
fn the_reviewers_sequence() {
    let (mut j, mut t) = (J::default(), Table::default());
    let x = 0;
    t.insert(x, 0);
    let a = j.checkpoint(&mut t);
    t.insert(x, 1);
    let b = j.checkpoint(&mut t);
    t.insert(x, 2);
    j.rewind(&b, &mut t);
    assert_eq!(t.get(&x), Some(&1));
    t.insert(x, 3);
    j.rewind(&b, &mut t);
    assert_eq!(t.get(&x), Some(&1));
    j.rewind(&a, &mut t);
    assert_eq!(t.get(&x), Some(&0));
    // `b` was dropped by the rewind to `a`.
    let stale = catch_unwind(AssertUnwindSafe(|| j.rewind(&b, &mut t)));
    assert!(stale.is_err());
    assert_eq!(t.get(&x), Some(&0));
    j.release(a, &mut t);
    assert!(!j.is_open());
    assert_eq!(t.entries(), 0);
}

/// A set's additions and removals.
#[test]
fn a_set() {
    let (mut j, mut t) = (Journal::<usize>::default(), LoggedSet::<u8>::default());
    assert!(t.add(1));
    let c = j.checkpoint(&mut t);
    assert!(!t.add(1));
    assert!(t.add(2));
    assert!(t.remove(&1));
    assert_eq!(t.entries(), 2, "the addition and the removal logged");
    j.rewind(&c, &mut t);
    assert!(t.contains_key(&1) && !t.contains_key(&2));
    j.release(c, &mut t);
    assert_eq!(t.entries(), 0);
}

/// Writes before any checkpoint aren't logged, and the logs are dropped
/// once nothing is open.
#[test]
fn nothing_is_logged_while_nothing_is_open() {
    let (mut j, mut t) = (J::default(), Table::default());
    t.insert(1, 1);
    assert_eq!(t.entries(), 0);
    let tr = j.begin(&mut t);
    t.insert(1, 2);
    t.insert(2, 2);
    t.insert(1, 3);
    assert_eq!(t.entries(), 2, "one entry per key in a generation");
    j.commit(tr, &mut t);
    assert_eq!(t.entries(), 0);
    t.insert(3, 3);
    assert_eq!(t.entries(), 0);
    let s = j.stats(&t);
    assert_eq!((s.entries, s.transactions, s.held), (2, 1, 0));
}

/// A rewind past an open transaction panics and changes nothing.
#[test]
fn a_rewind_past_a_transaction_panics() {
    let (mut j, mut t) = (J::default(), Table::default());
    let c = j.checkpoint(&mut t);
    t.insert(1, 1);
    let tr = j.begin(&mut t);
    t.insert(1, 2);
    assert!(catch_unwind(AssertUnwindSafe(|| j.rewind(&c, &mut t))).is_err());
    assert_eq!(t.get(&1), Some(&2));
    j.abort(tr, &mut t);
    assert_eq!(t.get(&1), Some(&1));
    j.rewind(&c, &mut t);
    assert!(t.is_empty());
}

/// Segments by unit (§4.8.3): a unit's write-set is what its own segments
/// logged, each key with its value where the first of them logged it,
/// whatever the units nested in it did; after a rewind the log goes on in
/// the unit the checkpoint was taken in.
#[test]
fn a_units_write_set_is_its_own_segments() {
    use super::super::owners::Owners;
    use super::super::table::Ids;
    let ids = Ids { defs: 0, datas: 0 };
    let (mut j, mut t, mut owners) = (J::default(), Table::default(), Owners::default());
    t.insert(9, 0);
    let a = owners.begin(ids);
    j.set_unit(a, &mut t);
    let tr = j.begin(&mut t);
    t.insert(1, 1);
    t.insert(9, 1);
    let outer = owners.enter(ids);
    let b = owners.current();
    j.set_unit(b, &mut t);
    t.insert(2, 2);
    t.insert(9, 2);
    owners.leave(ids, outer);
    j.set_unit(a, &mut t);
    t.insert(3, 3);
    t.insert(2, 4);
    let write_set = |j: &J, t: &Table, unit: UnitId| {
        let parts: Vec<(usize, Option<usize>)> = (j.segments_since(&tr, |u| u == unit))
            .into_iter()
            .map(|(at, end)| (*at, end.copied()))
            .collect();
        let mut keys: Vec<(u8, Option<u32>)> = (t.changed_in(&parts).into_iter())
            .map(|(k, v)| (*k, v.copied()))
            .collect();
        keys.sort();
        keys
    };
    let a_writes = vec![(1, None), (2, Some(2)), (3, None), (9, Some(0))];
    assert_eq!(write_set(&j, &t, a), a_writes);
    assert_eq!(write_set(&j, &t, b), vec![(2, None), (9, Some(1))]);
    // A checkpoint in `a`'s unit, then `b`'s again, rewound.
    let c = j.checkpoint(&mut t);
    j.set_unit(b, &mut t);
    t.insert(6, 6);
    j.rewind(&c, &mut t);
    t.insert(5, 5);
    let mut with_5 = a_writes.clone();
    with_5.push((5, None));
    with_5.sort();
    assert_eq!(write_set(&j, &t, a), with_5);
    assert_eq!(write_set(&j, &t, b), vec![(2, None), (9, Some(1))]);
    j.release(c, &mut t);
    j.commit(tr, &mut t);
    assert_eq!((j.segments(), t.entries()), (0, 0), "dropped with the logs");
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "a transaction dropped without commit or abort")]
fn a_dropped_transaction_fails_a_debug_assertion() {
    let (mut j, mut t) = (J::default(), Table::default());
    let _ = j.begin(&mut t);
}

/// xorshift64*: small and deterministic.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

enum Handle {
    Checkpoint(Checkpoint),
    Transaction(Transaction),
    /// Open, but its handle was consumed by a use that panicked.
    Lost,
}

/// An open checkpoint, in the journal and in the model.
struct Opened {
    handle: Handle,
    /// The model's map when it was opened.
    copy: BTreeMap<u8, u32>,
}

#[derive(Default)]
struct Run {
    steps: usize,
    writes: usize,
    checkpoints: usize,
    transactions: usize,
    rewinds: usize,
    repeated_rewinds: usize,
    releases: usize,
    commits: usize,
    aborts: usize,
    stale_uses: usize,
    refused: usize,
}

/// One generated sequence of up to `len` steps.
fn sequence(rng: &mut Rng, len: usize, run: &mut Run) {
    let (mut j, mut t) = (J::default(), Table::default());
    let mut model: BTreeMap<u8, u32> = BTreeMap::new();
    let mut open: Vec<Opened> = Vec::new();
    // Handles a rewind to an older checkpoint dropped.
    let mut stale: Vec<Checkpoint> = Vec::new();
    let mut last_rewound: Option<usize> = None;
    for _ in 0..rng.below(len) + 1 {
        run.steps += 1;
        let key = rng.below(6) as u8;
        let value = rng.below(4) as u32;
        match rng.below(20) {
            // Insert or overwrite.
            0..=5 => {
                run.writes += 1;
                t.insert(key, value);
                model.insert(key, value);
            }
            6 => {
                run.writes += 1;
                t.insert_absent(key, value);
                model.entry(key).or_insert(value);
            }
            7 => {
                run.writes += 1;
                assert_eq!(t.remove(&key), model.remove(&key).is_some());
            }
            // Removes every row of one value.
            8 => {
                run.writes += 1;
                t.retain(|_, v| *v != value);
                model.retain(|_, v| *v != value);
            }
            9 => {
                run.writes += 1;
                let had = t.update(&key, |v| *v += 1);
                assert_eq!(had, model.get_mut(&key).map(|v| *v += 1).is_some());
            }
            10..=11 => {
                run.checkpoints += 1;
                let c = j.checkpoint(&mut t);
                open.push(Opened {
                    handle: Handle::Checkpoint(c),
                    copy: model.clone(),
                });
            }
            12 => {
                run.transactions += 1;
                let tr = j.begin(&mut t);
                open.push(Opened {
                    handle: Handle::Transaction(tr),
                    copy: model.clone(),
                });
            }
            // Rewind to an open checkpoint; often the one rewound to last.
            13..=15 => {
                let target = match last_rewound {
                    Some(i) if i < open.len() && rng.below(2) == 0 => Some(i),
                    _ if open.is_empty() => None,
                    _ => Some(rng.below(open.len())),
                };
                let Some(i) = target else { continue };
                let Handle::Checkpoint(c) = &open[i].handle else {
                    continue;
                };
                let past_transaction = open[i + 1..]
                    .iter()
                    .any(|o| matches!(o.handle, Handle::Transaction(_)));
                if past_transaction {
                    run.refused += 1;
                    let r = catch_unwind(AssertUnwindSafe(|| j.rewind(c, &mut t)));
                    assert!(r.is_err(), "a rewind past an open transaction");
                } else {
                    run.rewinds += 1;
                    if last_rewound == Some(i) {
                        run.repeated_rewinds += 1;
                    }
                    j.rewind(c, &mut t);
                    model = open[i].copy.clone();
                    for dropped in open.drain(i + 1..) {
                        if let Handle::Checkpoint(c) = dropped.handle {
                            stale.push(c);
                        }
                    }
                    last_rewound = Some(i);
                }
            }
            // End the newest.
            16..=17 => match open.pop() {
                None => {}
                Some(Opened {
                    handle: Handle::Checkpoint(c),
                    ..
                }) => {
                    run.releases += 1;
                    j.release(c, &mut t);
                }
                Some(Opened {
                    handle: Handle::Transaction(tr),
                    copy,
                }) => {
                    check_write_set(&j, &tr, &t, &copy, &model);
                    if rng.below(2) == 0 {
                        run.commits += 1;
                        j.commit(tr, &mut t);
                    } else {
                        run.aborts += 1;
                        j.abort(tr, &mut t);
                        model = copy;
                    }
                }
                Some(
                    o @ Opened {
                        handle: Handle::Lost,
                        ..
                    },
                ) => open.push(o),
            },
            // A handle that is no longer valid, or a release that isn't
            // the newest: refused, and nothing changes.
            _ => {
                if !stale.is_empty() && rng.below(2) == 0 {
                    run.stale_uses += 1;
                    let c = &stale[rng.below(stale.len())];
                    let r = catch_unwind(AssertUnwindSafe(|| j.rewind(c, &mut t)));
                    assert!(r.is_err(), "a stale checkpoint was rewound to");
                } else if open.len() >= 2 {
                    let i = rng.below(open.len() - 1);
                    if let Handle::Checkpoint(_) = open[i].handle {
                        run.refused += 1;
                        let Handle::Checkpoint(c) =
                            std::mem::replace(&mut open[i].handle, Handle::Lost)
                        else {
                            unreachable!()
                        };
                        let r = catch_unwind(AssertUnwindSafe(|| j.release(c, &mut t)));
                        assert!(r.is_err(), "a checkpoint released below another");
                    }
                }
            }
        }
        assert_eq!(contents(&t), model);
        assert_eq!(j.is_open(), !open.is_empty());
        if open.is_empty() {
            assert_eq!(t.entries(), 0, "the logs are dropped once nothing is open");
        }
    }
    // End what is open, newest first.
    while let Some(o) = open.pop() {
        match o.handle {
            Handle::Transaction(tr) => {
                check_write_set(&j, &tr, &t, &o.copy, &model);
                j.abort(tr, &mut t);
                model = o.copy;
            }
            Handle::Checkpoint(c) => j.release(c, &mut t),
            Handle::Lost => {
                // Dropped by an older one's rewind or abort, or left open.
                if let Some(Opened {
                    handle: Handle::Checkpoint(c),
                    ..
                }) = open.last()
                {
                    j.rewind(c, &mut t);
                    model = open.last().unwrap().copy.clone();
                }
            }
        }
        assert_eq!(contents(&t), model);
    }
}

/// A transaction's write-set, read before it ends: every key whose value
/// differs from its value when the transaction began is in it, with that
/// value; a key in it may also be back to that value.
fn check_write_set(
    j: &J,
    tr: &Transaction,
    t: &Table,
    copy: &BTreeMap<u8, u32>,
    model: &BTreeMap<u8, u32>,
) {
    let set = t.changed_since(*j.began_at(tr));
    for (k, old) in &set {
        assert_eq!(*old, copy.get(*k), "the value a key had when it began");
    }
    let changed: BTreeMap<u8, Option<u32>> = set
        .iter()
        .filter(|(k, old)| *old != t.get(k))
        .map(|(k, old)| (**k, old.copied()))
        .collect();
    let expected: BTreeMap<u8, Option<u32>> = (0..6u8)
        .filter(|k| copy.get(k) != model.get(k))
        .map(|k| (k, copy.get(&k).copied()))
        .collect();
    assert_eq!(changed, expected);
}

#[test]
fn logged_against_a_model() {
    let mut rng = Rng(0x5717_c4f0_2026_1103);
    let mut run = Run::default();
    for _ in 0..10_000 {
        sequence(&mut rng, 50, &mut run);
    }
    // The generator reaches every operation, many times.
    for (what, n) in [
        ("writes", run.writes),
        ("checkpoints", run.checkpoints),
        ("transactions", run.transactions),
        ("rewinds", run.rewinds),
        ("repeated rewinds", run.repeated_rewinds),
        ("releases", run.releases),
        ("commits", run.commits),
        ("aborts", run.aborts),
        ("stale uses", run.stale_uses),
        ("refused", run.refused),
    ] {
        assert!(n >= 500, "only {n} {what} in {} steps", run.steps);
    }
    eprintln!(
        "{} steps: {} writes, {} checkpoints, {} transactions, {} rewinds ({} repeated), \
         {} releases, {} commits, {} aborts, {} stale uses, {} refused",
        run.steps,
        run.writes,
        run.checkpoints,
        run.transactions,
        run.rewinds,
        run.repeated_rewinds,
        run.releases,
        run.commits,
        run.aborts,
        run.stale_uses,
        run.refused
    );
}
