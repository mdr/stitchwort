# Caching the elaborated core (SW-4623)

**Status:** note, 22 November 2026, Opus paper lane SW-4623. Read from the code at
`388a96702`; nothing built or run. One decision is Matt's (§6, D-question 2: whether the
core's terms may be trusted from a cache, as std's are); the rest is the orchestrator's.

Marks: **[measured]** figures SW-4593 measured (docs/proposals/std-import-cost.md, release
build, Speedwell); **[estimated]** my reckoning from them; **[read]** read from the code.

## 1. In short

**The problem.** Every session elaborates the core, `std/core/`, from source: about 0.1 s and
956,007 steps (81.5 ms elaboration, 22.0 ms kernel admission, 591 declarations)
**[measured]**, with or without a check cache. Once std replays from the cache it is the
largest fixed cost of a small program: a warm `stitchwort check` of a one-line file takes
0.094 s, most of it the core (check-cache.md's table), and a warm Parse example 0.48 s,
of which the core is about a fifth. Every session the test suites make pays it, as does
every playground check and every editor session start.

**Why it isn't cached.** Nobody decided against it; the cache was scoped to library files and
the core was left out for three practical reasons (§2): the cache is attached to a session
only after the core has loaded, the encoder refuses a unit that binds core built-ins or
primitives (which the core is made of), and in October the core's 0.08 s was judged "not a
priority for the CLI" (check-cache.md, SW-185). It is not a trust decision: D1660's trusted
replay was simply never offered the core.

**Recommendation.**

1. **First, in the test harness: one session per sweep thread, rewound after the core**
   (option D, §4). Test-only, small, saves the whole 0.1 s per example in every tier
   including the all tier, and changes nothing the kernel checks: the core is still
   elaborated from source, once per thread. It needs a reset of the per-program counters
   that `rewind` keeps, and a differential test.
2. **Then the core as a cache entry, re-checked by the kernel on every replay** (option A2,
   §4): saves about 60 ms of the 100 ms wherever a cache is used (CLI, editor, playground,
   tests), with no change to what the kernel checks.
3. **Trusting the core's entry without the kernel's checks** (option A1) saves about 20 ms
   more. That changes what the kernel checks in a cached session, so it is Matt's; I
   recommend not yet (§6).

No option changes a content hash.

## 2. Why the core isn't cached today

Read from `crates/driver/src/driver.rs` (`Session::start_in`), `crates/elab/src/cache/mod.rs`
and `crates/elab/src/lib.rs` **[read]**:

1. **Ordering.** `Session::start_in` elaborates the core (`elaborate_module` on the index's
   parsed `files[0]`, then `finish_load`, then `finish_core`) before it returns. Every host
   attaches its cache afterwards: the CLI (`main.rs`, `Session::for_stack` then
   `use_check_cache` or `use_library_check_cache`), the language server (`session_for` then
   `use_check_cache`), the playground (`library_session` then a `BundleStore`), the tests
   (`Session::for_stack` then `use_test_std_cache`). So no store exists when the core loads.
   The only place a cache is set inside `start_in` is the eager test path, also after the
   core.
2. **The encoder refuses what the core does.** `Elaborator::encode` will not write a unit
   that binds a primitive or a core built-in: "a core built-in may also tell the evaluator
   about a native, which replay couldn't take back". A library file's replay can be refused
   halfway and undone (`Kernel::forget_since`); a native registered with the evaluator, or
   `+`'s second-argument rule (`nat_add::register`), can't be. The core binds all of them
   (`bind_builtin_data`, `bind_builtin_def`: `Nat`, `Bool`, `Float`, `Char`, the natives, the
   `NatAddSucc` rule, `List.length`'s run body).
3. **The core doesn't go through the cached path at all.** Library files load through
   `load_library_file` and namespaces through `elaborate_namespace_cached`, where the
   capture-and-encode hooks are; the core is a plain `elaborate_module` with
   `loading_prelude` set, and the cache's entry points return early while
   `unit.loading_prelude` is on. The core also does things no library file does:
   `scope.clear_imports`, `tables.prelude_defs`, the core link names for doc links (a broken
   one fails the load), the statement-style warnings, the chain warnings moved into
   `library_warnings`, `registry::check_complete_core` and `check_library_declares_all`.
4. **Judged small.** check-cache.md's interaction table: "The core itself costs about 0.08 s
   per process ... so it is not a priority for the CLI", leaving in-process sharing to
   SW-185, which was closed in the October board prune without a change.

What is *not* a reason: trust. The core's text is already part of every library and
namespace key (`library_interface` hashes `index.files[0].text`), and check-cache-trust.md's
M1 (D2801) keys on the core text actually elaborated, so a custom-prelude test session gets
keys of its own. Entries refer to core declarations by path and content hash, so a library
entry already relies on the core being exactly what it was when the entry was written.

## 3. What the core's cost is spent on, and who pays it

| who | sessions | core today | note |
|---|---|---|---|
| `stitchwort check`/`test`/`run`, warm | one per process | 0.1 s of 0.094 s (one-line file) to 0.48 s (Parse example) **[measured]** | the user-visible case |
| language server | one per project open, then rewinds | 0.1 s at start | rewinds keep the core already |
| playground | one per check (`new_session`) | 0.1 s natively, more in WebAssembly **[not measured]** | std already comes from a bundle built with the page |
| examples sweeps, driver tests (lane, quick, broad tiers) | one per example or test | 0.1 s each | std replays from the test std cache |
| the same, all tier | one per example | 0.1 s each | std checked from source on purpose |
| CLI tests spawning `--no-cache` | one per spawn | 0.1 s each | `--no-cache` means the full check |
| `examples` benchmark | one per example, 1,993 | 1.9 G of its 16.5 G steps **[estimated, SW-4593]** | counts the library on purpose (SW-4593 option B) |

SW-4593's estimate for the examples sweeps: about 190 s of CPU per all-tier sweep and about
50 s at the quick tier's quarter sample **[estimated]**.

## 4. Options

Replay cost, used below: SW-4593 replayed 42 library files, about 3,700 declarations, in
107 ms **[measured]**, about 29 µs a declaration with everything an entry holds. At that rate
the core's 591 declarations replay in about **17 ms** trusted, and about **40 ms** with the
kernel's 22 ms of checks added back **[estimated]**.

### A. The core as a check cache entry

The core becomes a unit like a library file (`std.core`, with the navigation tag when
recorded), keyed by the format, the modes and limits, the core text actually elaborated
(M1) and the library interface (doc links resolve into it). Replay goes through
`admit_replayed` as a library file's does.

What it takes:

- **Sessions get their store before the core loads.** `Session::start` takes the store (or
  a builder sets it), and the four hosts above pass it at construction instead of after.
  This is most of the diff by line count, all mechanical.
- **Encoding the core's built-ins.** Entries already list library built-ins and replay binds
  them through `bind_builtin_def`/`bind_builtin_data`, comparing the result with the list.
  The core's entry needs the same for primitives and core built-ins (a `FORMAT` bump). The
  undo problem in §2.2 goes away for the core: a refused core replay throws the whole
  `Elaborator` away and elaborates the core from source in a new one, so nothing has to be
  taken back.
- **The core-only steps** of §2.3 either run after replay as now (`finish_core`,
  `check_complete_core`, `check_library_declares_all`, `clear_imports`, `prelude_defs`) or
  are covered by the key (doc links, statement style). The chain warnings are not stored, as
  library files' warnings aren't; `library_warning_report` already requires a session
  without a cache.
- **Replay order.** Replay defines each group as soon as what its terms name is final,
  "never later than the elaborator defined it" (check-cache.md, stage 1 point 1). Inside the
  core that can be *earlier* than a native or rule was registered: a proof that relies on
  `+` computing on its second argument names `Nat.add`, not the `NatAddSucc` lemma whose
  binding turns the rule on. Re-checked out of order, it would be refused. That is a safe
  failure (a miss, then the core from source), but it would make A2 useless, so the core's
  entry must replay in the elaborator's order. A1 doesn't check, so order matters there
  only for the registrations themselves.
- **Tests**: the existing differential test (cache against source, same terms and hashes)
  extended to the core; a refused core entry falls back; a custom-prelude session misses.

Two variants:

**A1. Trusted, as std's entries are (D1660).** Saving about **85 ms** per session where a
cache is used **[estimated]**. Soundness: in a cached session the kernel no longer checks
the core's terms; it checked them when the entry was written. That extends the trusted base
of a cached session (cache files, decoder, key completeness) to the core, whose definitions
the natives are pinned to. Pins are still checked, since replay binds through
`bind_builtin_def`, and `pins::check_bound_def` compares content hashes. `--no-cache` still
elaborates and checks everything. **This changes what the kernel checks in a cached session:
Matt's decision.**

**A2. Re-checked on every replay.** The same entry replayed with the kernel's checking calls
(`submit` with `hit.recheck`, the path `check --recheck` and carried-over entries already
use), and `hashes_as_recorded` comparing every content hash. Saving about **60 ms** per
session **[estimated]**: elaboration is skipped, admission isn't. Soundness: the kernel
checks exactly what it checks today, every core declaration on every session start. What
changes is where its input comes from: the cache entry instead of the elaborator, which is
untrusted either way. A wrong entry can only give a stale meaning (a different, well-typed
core), which the key and the content-hash comparison are there to stop, as for
carried-over entries (check-cache-across-updates.md's question E: "a stale answer, never an
unsound one"). Not a decision for Matt, in my reading; the orchestrator may want to confirm.

Where A saves (A2 figures):

- warm `check` of a one-line file: 0.094 s to about 0.035 s; a warm Parse example 0.48 s to
  about 0.42 s **[estimated]**;
- playground: each check, once the page's bundle carries the core's entry (the bundle
  builder, `library_bundle`, would record it with the library's);
- tests through the test std cache: about 60 ms per session in the lane, quick and broad
  tiers; about 30 s of CPU per quick-tier examples sweep **[estimated]**, more across the
  driver tests (session count not measured);
- not the all tier, `--no-cache` runs or the benchmark, by design.

Cost: medium to large, near the cache's trust boundary; Opus.

### B. Snapshot the whole initial session

Keep one elaborator per process (per thread: the elaborator is `Rc`-based and not `Send`)
just after the core, and give each new session a copy.

- Saving: the whole 0.1 s for every session after the first in a process: tests, the
  playground worker, the language server's extra sessions. Nothing for the CLI, which makes
  one session per process **[estimated]**.
- Soundness: the copy is of a core elaborated and checked from source in this process;
  nothing changes in what the kernel checks. Counters are copied at their just-after-core
  values, so the copy is exactly a fresh session, which answers SW-4593's worry about
  counters.
- Hashes: unchanged.
- Cost: large. Neither `Elaborator` nor `Kernel` is `Clone`, and much of their state is
  shared through `Rc` and `RefCell` (terms, memo tables, the journal), where a shallow copy
  would alias mutable state between sessions. It needs a deep copy that every field must say
  how to do, as `rewind` makes every field say how it rewinds, and a test that catches a
  field copied wrongly. D gets the same saving with machinery that exists.

### C. Build the core into the binary

Elaborate the core at compile time and embed its entry (`include_bytes!`), so even the first
session of a process replays it.

- Saving: as A, plus the first run with an empty cache, and `stitchwort` without a writable
  cache directory **[estimated]**.
- Soundness: A1 or A2, whichever replay it uses. The entry comes from the same source as the
  binary, as the playground's bundle does ("the bundle comes from the build that made the
  WebAssembly reading it", `check_cache.rs`).
- Hashes: unchanged.
- Cost: a build script needs the elaborator. `stitchwort-driver` can't depend on itself,
  so it would be `crates/cli`'s `build.rs` with `stitchwort-driver` as a build dependency:
  core, elab and driver compiled a second time for the build script on every compiler change,
  on every lane's build. A committed generated file instead would churn with every core or
  elaborator change and bloat the repo. Not worth it for native hosts, where A's cache entry
  is written on the first run. **For the playground it is just A**: `web/build.sh` already
  builds a bundle at page-build time, and the core's entry goes in it.

### D. One session per test thread, rewound after the core

The examples sweeps (`crates/cli/tests/running/examples.rs`: `accepted_examples_check` and
the rejected, soundness and extract sweeps) run every example in one process through
`par_map_labelled`, each in a fresh `Session::for_stack`. Instead each thread keeps one
session, set up as now (`untimed`, the test std cache), marks it (`Session::mark`) and
rewinds to the mark before each example. The language server already works this way, and
`crates/driver/tests/projects/rewind.rs` is the differential test that rewinding "gives what
a fresh session gives".

- Saving: the whole 0.1 s per example, minus a rewind (cost proportional to what the example
  changed): about 50 s of CPU per quick-tier sweep and about 190 s per all-tier sweep
  **[estimated, SW-4593's figures]**. Other test binaries that make many sessions in a loop
  could follow.
- Soundness: nothing changes. The core is elaborated and checked from source, once per
  thread, in every tier, so the all tier keeps its from-source guard.
- Hashes: unchanged (`hash_stability` keeps fresh sessions).
- **The risk SW-4593 named: what `rewind` keeps.** `state::Session::mark` lists what is
  "counted, never reused or taken back": `source_epoch`, `standalone_inputs`,
  `instance_waits`, `cache_stats`, `stats` (the queue's and unifier's counters); "checked on
  use": `assumed`, `blocked`, `waiting_names`, `failed_sources`, `broken_tests`,
  `failed_decls`; "recorded for the caller, never taken back": `expansions`, `walks`,
  `facts`. Also kept: `options` (an example that changes one would leak it) and the
  kernel's step counters. Any of these that reaches a rendered diagnostic, a snapshot or an
  outcome would make an example's output depend on which examples ran before it on the
  same thread, which is nondeterministic under `par_map_labelled`. So D needs:
  - a `Session::reset_for_program` (or the harness re-applying its own options) that
    clears the per-program accumulators, each one justified against the list above;
  - a differential test: a fixed sample of accept and reject examples through one reused
    session, in two different orders, against fresh sessions, with identical rendered
    output and warnings;
  - `-- metrics:` headers keep working (`metrics::start_collecting` is global, not
    session state).
- Cost: small to medium; test code plus the reset. Sonnet, with the reset reviewed by Opus.

## 5. Summary

| option | saving per session | where | what the kernel checks | hashes | cost |
|---|---|---|---|---|---|
| A1 core entry, trusted | ~85 ms | cached sessions | **less**: the core's terms trusted from cache (Matt's) | same | medium-large |
| A2 core entry, re-checked | ~60 ms | cached sessions | same | same | medium-large |
| B snapshot copy | ~100 ms | 2nd+ session in a process | same | same | large |
| C built into the binary | as A1/A2 | also first run | as A1/A2 | same | large natively; playground: part of A |
| D thread session + rewind | ~100 ms | test sweeps, all tiers | same | same | small-medium |

All savings **[estimated]** from SW-4593's measurements.

## 6. Recommendation and first step

1. **D first.** First step: a Sonnet lane on `crates/cli/tests/running/examples.rs` alone:
   a thread-local session marked after `untimed`, rewound per example; the reset of the
   per-program counters in `state::Session`; the two-order differential test on a sample of
   about 40 examples. Measure one sweep's CPU before and after (the lane runs the
   differential test; the before-and-after sweep timing is the verifier's or Overmind's).
2. **A2 next**, as an Opus lane: the store passed at session construction in the four hosts,
   the core's entry with its built-ins, replay in the elaborator's order through the
   checking path, the differential test extended to the core. The playground's bundle gains
   the core's entry in the same lane or a follow-up (option C for the web only).
3. **A1 is Matt's** (D-question 2 below), after A2 has been measured: it would take a further
   ~20 ms off each cached session by no longer re-checking the core's terms. I recommend
   against it for now: 20 ms is small next to A2's 60 ms, and the core is where the natives'
   pins and the kernel's built-in reduction rules attach, so it is the last place to widen
   trusted replay without a measured need.
4. **B: no**; D gets the same saving with existing machinery. **C natively: no**; only as
   part of the playground's bundle.

Questions for the orchestrator to put to Matt, when a lane needs them:

- (1) None for D or A2 in my reading: neither changes what the kernel checks. The
  orchestrator may want Matt's nod that A2's "kernel checks the cached core's terms" counts
  as unchanged.
- (2) A1: may a cached session admit the core's declarations through trusted replay, as it
  does std's (D1660)? [rec: not now; revisit with A2's measurements.]
