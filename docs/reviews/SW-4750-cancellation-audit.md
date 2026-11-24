# SW-4750: can a cancelled or exhausted computation be kept as an answer?

An audit after SW-4744 (a hash that stopped was encoded as "no hash", so a
cancelled `check --jobs` fill or editor check could write an entry with a
wrong interface digest). Opus, 24 Nov 2026.

## How cancellation behaves

`Budget` notes a cancellation once a poll sees the flag (at an operation's
start, and every `POLL` steps on `step`'s slow path) and keeps it until
`Budget::reset`, which only a rewind calls. Once seen, every later
operation and attempt fails, and an attempt that ends after it leaves the
operation exhausted (`Budget::restore`, `Operation::drop`). So:

- a check of `cancelled()` *after* a computation is sound: if it says no,
  nothing the computation did saw a cancellation, and its result is
  complete;
- a flag set after the last poll is simply not seen: the result is a real
  one, and keeping it is fine;
- a site that reads an attempt's `Err` as "no" is harmless for
  cancellation as long as it, or what it feeds, takes another step or
  `nesting` check before its result is kept, and the result is dropped
  with the rewind. The danger is a value kept *without* such a step: a
  memo that survives a rewind, a disk write, a verdict.
- Hashing (`hash.rs`) takes no steps: it fails only at `nesting`, after the
  operation has run out. A memoised hash returns before that check, so
  under cancellation memoised hashes still come out right and fresh ones
  fail (the SW-4744 shape).

The cancellation flag is watched only inside `Session::cancellable_at`
(the editor's checks) and a `--jobs` worker's fill. Tests, trials, hash
listings and printing run unwatched: there only running out (steps, stack,
deadline) can happen.

## Findings

| # | Where | What turns `Err` into a value, or checks before | Reaches | Verdict |
|---|---|---|---|---|
| 1 | `replay_namespace`, `--recheck` / carried entry from another kernel: digest computed again | a cancellation during the digest gives `Err` ("hashing a declaration stopped"), compared as a mismatch | `E-CACHE-DIGEST` error, `digest_mismatches`, `failed_namespaces`, and **this build's entry blanked** (`store.write(unit, key, &[])`) | **bug, fixed**: a cancelled re-check is a late miss. Reachable: `check --jobs --recheck` worker panic (blanks a good exact entry); the editor with carry-over on (blanks its own slot; the error itself is dropped by the rewind). Test `check_cache::a_recheck_cancelled_while_its_digest_is_computed_keeps_the_entry` |
| 2 | `live/trial.rs` `hashes()`, `declhash::session_hashes`: `def_hash(..).ok().flatten()` and the statement/proofless hashes | running out (one operation for all the hashes; not cancellation, unwatched) reads as `None`, "not final" | `Promise::keeps`: `was.hash == now.hash` with both `None` is **kept**, so a declaration whose hashes both ran out is reported unchanged by a trial or `trial-edits` | **bug, not fixed** (fix spreads: a hash that ran out needs its own outcome in `Decl`/`DeclHash` and in what the trial reports). Filed as a finding |
| 3 | `hash.rs` `proof_argument` / group filter → `erase::proof_positions` fallback ("nothing is a proof") on `Err` | the fallback isn't memoised, but the proofless hash built on it is (`caches.proofless`), and for an old declaration it survives a rewind | `Promise::ProofsOnly` comparisons | harmless: a hash with more in it only makes a difference, so the error is a refusal, never an acceptance. Contradicts `proof_positions`' doc ("a proofless hash can't depend on what ran first"). Filed as a finding |
| 4 | `cache_after` (library file) | `ok && !cancelled()` before encoding, `cancelled()` again after (SW-4744) | disk entry | safe |
| 5 | `elaborate_namespace_cached` write | same pair of checks (SW-4744) | disk entry, `namespace_keys` digest | safe |
| 6 | `load_from_cache` → `keep_rechecked` (library) | none needed: called only after `replay` returned `Ok`, and a cancelled kernel call or `hashes_as_recorded` hash is `Err` → `Bad` | restamped entry | safe |
| 7 | namespace replay `Ok` → `keep_rechecked` | as 6, plus the digest check of 1 (now a late miss when cancelled) | restamped entry | safe after fix 1 (before it, a cancelled digest took the mismatch path, never this one) |
| 8 | `decode`: `interface_hash(..).ok().flatten()` / `data_hash` on dependencies | a cancelled fresh hash is `None` → "isn't what the entry was made with" | a miss; the namespace is then elaborated under the cancellation and not written | harmless (only misses) |
| 9 | `replay` (library) refusal counters | already guarded by `cancelled()` | stats | safe |
| 10 | `Session::cancellable_at` (editor's session keep, `LiveProject::step`) | `cancelled()` after `f`, then rewind | the kept session, `names`, `steps` | safe: post-hoc and sticky |
| 11 | `parallel::Worker::job` | "written" judged from stats; a job that wrote nothing is rewound | which entries the fill leaves | safe |
| 12 | `Stats` counters (`late_misses`, `namespace_carried`, …) | not rewound | the editor's carried-over note, `--cache-stats` | harmless: counts of a cancelled check (only wording) |
| 13 | test-result cache (`run_selected`, `Cache::put`) | `OutOfResources` is never stored; tests aren't cancellable | `.stitchwort/tests` | safe |
| 14 | `result_key`: goal `def_hash(..).ok().flatten()` → zeros | running out reads as a zero goal hash | the test-result key | harmless: another key, so a miss (a collision needs the same test and two goal sets whose hashes both ran out) |
| 15 | `run_selected`: `is_partial(..).unwrap_or(false)` | running out reads as "total" | on the machine/native runners, a partial test run as total, outcome possibly cached | harmless in practice: a test's type is `Bool` or `Delay Bool`, whose normal form takes a handful of steps; noted as a finding |
| 16 | `check.rs` `same_unglued` (`aside`), `unify.rs` `value_forms`, zonk unfolding, `counterexample` | each passes on `exhausted()` (cancellation, stack) and reads only the attempt's own running out as "no" | elaboration | by design (D3733) |
| 17 | `closing.rs`, `search.rs`, `omega.rs`, `ring.rs`, `equations` attempts | read their attempt's `Err` as "no"; a cancellation inside leaves the operation exhausted, so the next step fails and the check is rewound | elaboration, dropped | by design: a cancelled check never survives its rewind |
| 18 | memos kept across a rewind for old declarations: `Caches::result_heads`, `performs`; kernel `hashes`, `interfaces`, `erasure_defs`, `proof_positions`, `reliance` | written only on `Ok` of computations that pass `Err` on (`?`); `erasure`/`proof_positions` fallbacks unmemoised; `reliance` is a syntactic walk | later checks in the same session | safe (except the proofless hash, 3) |
| 19 | `plan_namespace` (`check` leaving namespaces out) | compares text hashes and entry stamps only | which namespaces are skipped | safe (no budget) |

## Also found

- SW-4744's test `a_check_cancelled_while_an_entry_is_encoded_writes_nothing`
  checked nothing for namespaces: its fixture wrote `some 1`, an unknown
  name, so the namespace had an error and was never written, cancelled or
  not. Fixed to `Some 1`, with an assertion that the uninterrupted check
  writes it.
- `cancel_while_encoding_entries` now makes the cancellation seen at once
  (it starts an operation, which polls), as a poll landing there would: a
  small digest takes too few steps to poll at all, so the hook didn't
  reach the window it was meant for.
