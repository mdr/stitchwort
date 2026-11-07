# What the check cache trusts (SW-1971)

**Status:** design note, 7 November 2026, for Matt's decisions. Nothing is
built. Questions are D2800 to D2802, plus D2680 from the driver review,
which this note answers. They are at the [end](#7-decisions-for-matt).

It builds on three of today's reviews and doesn't repeat them:
[code-review-elab-rest.md](../reviews/code-review-elab-rest.md) (F1, F10,
F11), [code-review-driver.md](../reviews/code-review-driver.md) (M1, L1,
D2680) and [code-review-core.md](../reviews/code-review-core.md) (F7, F8 on
the trusted path). The background is [check-cache.md](check-cache.md), "As
built (stage 3)". I read the code at `b42f164bf` and ran nothing. A claim
with a file:line is one I read. **[inferred]** marks reasoning I didn't
confirm by reading every caller.

## 1. In short

**What you get.** A check that comes back from the cache is something this
compiler really did check, from these sources, in a session set up like
this one. If an entry doesn't fit, the session ends up exactly where it
would have been without that entry. And a full-tier check would tell us if
the cache ever answered differently from a check from source.

**Why it matters.** Since D1660 a cache hit skips the kernel. Whatever the
cache replays goes into the trusted base without being checked again
(`cache/mod.rs:16-22`). Every review found that this is the one route by
which results reach the kernel unchecked, and each found a different gap at
it. Here is one argument that covers all of them, so a fix to one gap
doesn't leave the others open.

**The argument.** Replaying an entry is safe when three things hold:

1. **The key covers every input** that can change what checking the unit
   gives, and each part of the key is computed from what the session
   actually read, not from a description of what it ought to have read (§2).
   M1 breaks this.
2. **The entry is what a full check admitted.** The encoder and decoder
   round-trip, and the differential tests check this (§4).
3. **A refused replay is undone completely**, by one kernel primitive that
   covers all of the kernel's state (§3). F1 breaks this.

One more check sits beside these, and it never expects to fire: a
**verify mode** that checks a real, long-lived cache against a check from
source (§5). Today nothing does this for the check cache.
`--verify-cache` exists only for `test`, and it compares test results while
still replaying the check cache (`cli/src/main.rs:1403-1415`, `use_cache` at
`1331`).

**Recommendations.**

- Undo with a new `Kernel::forget_since(&mark)`. Not with `Kernel::rewind`
  as F1 suggests, because that resets the running operation's budget (§3.2).
- Key on the hash of the core text that was actually elaborated (§2.2).
- Keep dev and release builds sharing entries, and write down why that is
  safe (§6).
- Add `check --verify-cache` to the full tier. Don't add a sampled kernel
  recheck to the daily tier (§5).

**Tickets.** This note reshapes SW-1925 (its undo changes) and the M1 part
of SW-1919. It also files a finding nobody had seen: equations and
induction already call `Kernel::rewind` partway through a declaration (§3.2).

## 2. What a cache key must cover

### 2.1 The rule

**The problem, plainly.** Suppose a test makes a session with a modified
prelude, say one where `Nat.sub` truncates differently, and gives it a check
cache. Every key it computes is the same as a normal session's, so it
replays the library as checked against the *standard* prelude. Its results
are then those of a prelude it never loaded. Nobody does this today (driver
review, M1), but nothing stops it either.

**The rule.** A key is a hash of every input that can change what checking
the unit gives. Each part is taken **from the value the session consumed,
at the point it consumed it**. `std_dir.rs:18-20` already states this for
the library's text ("caches key on what is actually on disk"). M1 is the one
place that breaks it: `library_interface` (`cache/mod.rs:520-548`) hashes
`index.files[0].text`, which is what the index *says* the core is.
`Session::start` loads something else whenever its prelude differs
(`driver.rs:541-548`).

**What the key covers today**, read from `library_keys` (`mod.rs:239-274`),
`namespace_cache_key` (`565-600`), `modes` (`277-286`) and
`Options::cache_key` (`state/options.rs:93-128`):

| Input | In the key | How sure |
|---|---|---|
| Compiler: version, the source of every crate in the driver's graph, `Cargo.lock`, toolchain, target | `store.compiler()` (`check_cache.rs:59`, `build.rs`) | read |
| Entry format | `FORMAT` (`mod.rs:77`) | read |
| Natives and compact text on or off | `modes` | read |
| Options that change results: limits, glue, `numbers_as_succ`, rewrite and instance budgets, uniform operators | `Options::cache_key`, which destructures `Options`, so a new field has to be placed before it compiles | read |
| What navigation records | `nav_tag`, in the key and in the unit's name | read |
| The core's text | **the index's**, not the loaded one (M1) | read |
| The library's names: path, key, kind, flags | `library_interface` | read |
| A library file's path and text, and the keys of the files it needs | `library_keys` | read |
| A namespace's sources, as the host hashes them, and its dependencies' keys | `namespace_cache_key` | read |
| The library files and includes a namespace used | listed in the entry and compared when it loads (`library_unchanged`, `includes_unchanged`, `mod.rs:461-493`) | read |
| Build profile and cargo features | **not covered** (L1, D2680; see §6) | read |
| Kernel switches other than natives and compact text: `disable_float_natives`, `float_natives_outside_runs`, erasure's | not covered. Float natives fire only in runs or the float gate (`native.rs:183-199`), and `in_kernel_modes` resets erasure for admission (`machine.rs:57-76`) | inferred: they don't change what checking gives |
| Environment variables: `STITCHWORT_GLUE` (in through `Options`), `STITCHWORT_DECIDE_BOTH` (`auto.rs:797`), `STITCHWORT_DEBUG_FORCE_UNGLUED` (`value.rs:2333`) | only the first | inferred: the other two are instrumentation that throws its results away |

Apart from M1 and the profile, I found no input that is missing. The rows
marked inferred rest on each switch's documented promise that it changes no
result. §5's verify mode is what would catch a switch that breaks that
promise.

### 2.2 M1: key on the loaded core

**Design A (recommended): hash the text that was elaborated.** When the
core is elaborated (`Session::start`, `driver.rs:541-551`), the session
records a digest of `prelude`, the text it parsed or reused. It passes the
digest to the elaborator, for example as an argument to `finish_core`.
`library_interface` then hashes that digest instead of
`index.files[0].text`. A custom-prelude session gets keys of its own: it
misses on standard entries and can keep entries of its own. The comment on
`cache_usable` (`mod.rs:212-214`), which says such a session "finds its
entries' dependencies have other hashes: misses", becomes true by
construction, not partly true by luck. The cost is one hash of about 100 KB
of text per session, which is nothing.

**Design B: refuse a cache in a custom-prelude session.** The driver review
offers this as its first choice: a debug assertion plus a no-op in
`use_check_cache` and `use_test_std_cache`. It is just as small, but it
keeps the shape of the bug, a key computed from a description. The next
session type that loads something other than what the index says has to
remember to refuse too. A rules out the whole class, so I recommend A
(D2801). B's refusal can stay as a debug assertion beside A if the
implementer likes, but it isn't needed.

**What it should do, and how we'd know.** A test like the one the driver
review asks for (its L12): a session with a custom prelude and a cache dir
gets only misses against a standard session's entries, then hits on its own
second run.

## 3. What a replay may add, and undoing all of it

### 3.1 What replay touches

**The problem, plainly.** A cached entry for the Float file binds `Float.add`
to definition number *n*. Later in the same entry, the kernel refuses a
group. The cache undoes the entry and checks the file from source. If the
source no longer puts `Float.add` at *n*, whatever definition next gets
number *n* is still computed as the Float native, so a program or an `rfl`
gives a wrong answer (elab review, F1). This is rare. The point is that the
undo has to be exactly the inverse of what replay did, and today nothing
makes it so.

Here is everything an entry's replay changes before it is known to fit,
from `admit_replayed` and `submit` (`mod.rs:2566-2899`):

| State | Written by | Undone today by `forget_declarations_from` (`globals.rs:704-707`) + truncating owners and paths? |
|---|---|---|
| Definitions and data types | `admit_trusted_*` | yes, `env.truncate` |
| Registry entries | `bind_builtin_def`/`_data` → `registry::bind_def`/`bind_data` (`registry.rs:684-716`) | yes, `registry.forget_from` (`env.rs:142`) |
| Natives, primitives, `float_defs` | `register_native`, `float::register_def` | **no** |
| The `nat`, `bool`, `decidable`, `nat_neq`, `nat_add_rule`, `text` and `float` slots | `register_nat` and the rest, `chars::register`, `nat_add::register`, `float::register_data` | **no** |
| Run bodies, flags, unfolding sets | on the definitions themselves | yes, they go with the definition |
| Content hashes, erasure cache | `caches` | yes, `caches.forget_from` |
| Owners, paths | elaborator session | yes (`mod.rs:2591-2592`) |
| `Machine::apart_sets` | evaluation, if admission evaluates a type that makes one | no, and it needn't be: append-only, and nothing outside the removed declarations refers to the new entries [inferred] |
| Side tables, hashes the entry records | `replay_tables`, the hash seeding at `2598-2609` | not needed: both run only after success |
| A namespace's early names, library files it loaded | `replay_namespace` (`mod.rs:859-936`) | not undone, on purpose: the late-miss path keeps them and elaborates in what is left (tested by `a_replay_that_fails_part_way_gives_the_same_result`) |

The gap is the two rows marked **no**: the `Builtins` struct
(`native.rs:123-163`). `Builtins::rewind` (`native.rs:261-283`) already
handles all of it. Only `Kernel::rewind` calls it, and replay doesn't use
that.

### 3.2 Why not `Kernel::rewind`

F1's suggested fix is "`self.kernel.mark()` before `submit` and
`self.kernel.rewind(&mark)` on failure". But `Kernel::rewind` ends with
`machine.reset()` (`globals.rs:752`), and that calls `Budget::reset`
(`budget.rs:505-515`), which clears the current operation's work and step
limit (to `u64::MAX`), its stack floor (to 0), its frame limit, its
`exhausted` state and the `cancelled` flag. That is right for its intended
caller, the language server rewinding between checks ("taken between
declarations (no operation running)", `globals.rs:717-719`). It is wrong in
the middle of a load. A library file can be replayed while a namespace is
being elaborated (`load_needs`, called from `replay_namespace` at
`mod.rs:912`, and from elaboration). If an operation is running there, the
rest of it would run with no step limit and no stack guard, and a deep term
could then abort the process instead of giving `E-RESOURCE`. That breaks
D2543. [inferred: I didn't trace every caller of `load_from_cache` to see
whether an operation is running. The fix below doesn't depend on that.]

**This is already happening elsewhere.** `equations.rs:2460` and
`equations/induct.rs:349` take `self.kernel.mark()` inside a declaration's
check and, on a skipped or refused equation, call `rewind_globals`
(`lib.rs:1121-1128`), which calls `Kernel::rewind`. So after a skipped
equation, the rest of that declaration's operation runs without its limits
or stack floor, until the enclosing `restore` puts the outer operation's
state back [inferred from `Budget::start`/`restore`, `budget.rs:337-363`].
The doc on `Kernel::mark` says the elaborator's `mark` is its only caller,
which is also out of date. I file this as a ticket in §8.

### 3.3 The undo design

**Design A (recommended): one kernel undo primitive.** Split
`Kernel::rewind` into two parts:

- `Kernel::forget_since(&KernelMark)`: `env.rewind(defs, datas, builtins)`
  plus `caches.forget_from`. That is everything recorded about the
  declarations since the mark (definitions, data types, registry, natives,
  primitives, Float, the slots, hashes, erasure), and nothing about the
  running operation.
- `Kernel::rewind(&mark)` = `forget_since(&mark)` + `machine.reset()`, as
  today, for the language server.

Then delete `forget_declarations_from`, so there is one way to undo
declarations and it can't miss a table. `admit_replayed` takes
`let mark = self.kernel.mark()` before `submit` and calls `forget_since` on
failure. `rewind_globals` moves to `forget_since` too (§3.2's finding).
Make `Builtins::mark`/`rewind` destructure `Builtins`, as `Kernel::rewind`
destructures `Kernel` (`globals.rs:739-744`), so a new field has to say how
it is undone before it compiles. Today `rewind` names its fields by hand:
all fourteen are covered now, four of them as settings, but nothing makes
the next one covered.

**Design B: `Kernel::rewind` as F1 proposed.** Rejected for §3.2's reason.

**Design C: the elaborator's `mark`/`rewind`.** This undoes everything,
elaborator tables included. But it asserts that no library file is loading
(`rewind.rs:89-93`), and replaying a library file is a library file loading.
It would also take back the library files a namespace's late miss
deliberately keeps. Rejected.

**Design D: bind built-ins only after the whole entry is admitted.** Then a
refusal would have nothing of `Builtins` to undo. But replay must bind in
the order elaborating does: a later group's type is evaluated on admission
(`push_def`), and that evaluation can depend on an earlier native or on
`nat` being registered [inferred]. D would change what replay computes.
Rejected.

**Design E: a persistent environment**, as in Lean 4, where adding a
declaration makes a new `Environment` value and a failed `addDecl` just
keeps the old one, so undo costs nothing. That is the deepest fix but far
too large for this. I note it as the end state if rollback bugs keep coming.

**Also in this change:**

- **F11, bind only where elaboration binds.** Bind built-ins on replay for
  library entries only, and refuse a namespace entry whose `bound` isn't
  empty, early, before anything is admitted. This takes away the one
  ordinary way a refusal happens.
- **Count refusals.** With a complete key and a correct encoder, the kernel
  never refuses an entry for the current key, so a refusal means a bug, not
  an ordinary miss. Add `Stats::refused` (beside `late_misses`), report it
  under `STITCHWORT_CACHE_DEBUG`, and have the differential tests assert it
  is zero, as they do for `late_misses` (`check_cache.rs:200-204`). The
  module doc (`mod.rs:38-42`) lists a refused entry as an ordinary miss;
  it should say it is never expected.

## 4. Testing the boundary

**The problem, plainly.** No test today reaches the undo at all. A corrupted
entry fails its checksum before `submit` (`a_corrupt_entry_is_a_miss_…`,
`check_cache.rs:501`). `fail_namespace_replays_late` fails *before* the
namespace's declarations are admitted (`mod.rs:919-921`). And even a test
that did refuse an entry and then compared dumps after the file was checked
from source would pass with F1's bug: elaborating the same source binds the
same id again, which overwrites the leftover binding. The bug needs ids to
move, which a test has to arrange on purpose.

**The change.**

1. **A forced refusal at a chosen point.** A hidden test option,
   `fail_replays_after(groups)`, makes `submit` return `refused` after that
   many groups have been admitted and bound, for library and namespace
   entries alike. It sits beside `fail_replays_late` in `Options` and, like
   that field, stays out of the key by the destructuring rule.
2. **Check the state at the undo, not after the recheck.** In test builds
   (the `reference` feature, which every dev build has), the undo path
   compares a kernel-only dump taken at the mark with one taken after
   `forget_since`, and panics if they differ. Refusals are rare, so dumping
   the whole environment twice costs nothing in practice. This tests the
   mechanism directly, with no need to arrange for ids to move.
3. **A full dump (F10).** `canonical_dump` (`dump.rs:304-325`) prints the
   registry and `native(id)`, but not `float_defs`, `primitives`, the Float
   binding, `nat_add_rule` or the slots. Print `Builtins` by destructuring
   it, so a new field fails to compile until it's printed (the pattern in
   `state/`). Item 2 uses this dump.
4. **The scenario test.** Load the library with a cache, forcing a refusal
   in `std/Float/Float.sw` after the group that binds `Float.add`. Check
   that item 2's assertion holds and that the final dump equals a fresh
   run's. (SW-1204 says that file isn't cached today. If it still isn't,
   use the first cached file that binds a native or a primitive.) A second
   case, a namespace entry forced to refuse after its first group, checks
   that the late-miss path still gives the fresh result.
5. **M1's test** (§2.2) and **the zero-refusals assertion** (§3.3) in the
   existing differential tests.

**How we'd know.** With item 2 and today's `forget_declarations_from`, the
scenario test fails on `float_defs`. With `forget_since` it passes. The
differential tests then pin `refused == 0` on every corpus they already
cover.

## 5. Should some tier recheck replayed entries?

**The problem, plainly.** Every test of the check cache starts from an empty
cache folder (check-cache.md, "The gates still run the kernel"). So they
prove that one fresh pass and the replay of its own entries agree. They
never look at a cache with a history, like `aoc/.stitchwort/cache` after a
week of proof lanes. The fingerprint leaves out `std/*.sw` and the AoC
sources (`build.rs`), so most lanes' merges keep the same build and their
entries pile up. A key with a hole, or a bug like F1 that needs one earlier
refusal, shows up only in a cache like that. Note too that "the gates still
run the kernel" is no longer quite true: since SW-1751, tests in every tier
but full load the library through the test std cache, which trusts it
(`driver.rs:582-603`). The entries do come from the same build.

**Design 1: nothing more.** The differential tests stay the guard. They
cost nothing, and history-dependent holes go unseen.

**Design 2: a sampled kernel recheck in the daily tier**, in the style of
Lean's `lean4checker`: replay a sample of entries through the *checking*
admission (`declare_def`/`define_group`) instead of the trusted one. Kernel
time was about a fifth of a full check (19% in check-cache.md §3; 9.2 s of
a warm 9.9 s before stage 3), so a 1-in-4 sample of AoC costs a few seconds.
But it catches only an entry the kernel would *reject*, that is unsound
staleness. A stale entry that is still sound, such as a name resolved the
old way or a missing warning, passes. It also needs a checked replay path,
option A from before stage 3, kept working beside the trusted one. That is
M, and a second path to keep in step.

**Design 3 (recommended): `stitchwort check --verify-cache`.** This is the
check-cache counterpart of `test --verify-cache`, and the "verify mode" that
check-cache-key.md §6 sketches: `read` always misses, every unit is
elaborated and kernel-checked from source, and `write` compares the fresh
entry with the one already stored under the same name. It reports
"differs" (unit and first differing byte offset, and with
`STITCHWORT_CACHE_DEBUG` the first differing dump line), "no entry", or
"same". It writes nothing. Encoding is already byte-for-byte deterministic,
and two tests assert it: `a_corrupt_entry_is_a_miss_and_is_rewritten` checks
the rewritten bytes, and
`a_namespace_writes_the_same_entry_whether_its_library_files_hit_or_miss`.
Only error-free units are written, and counterexample searches, which have
a wall-clock limit, run only for failing theorems, so a written unit never
ran one. A byte comparison is therefore sound.

It catches everything design 2 does, since a matching entry is one the
kernel has just accepted, plus every sound-but-stale difference. It costs a
`--no-cache` check: 35.6 s on `aoc` at 135 namespaces (check-cache.md,
stage 3 measurements; more now), plus the roguelike. Run it in the full
tier, inside `task test:verify-cache` next to the test cache's check, on
the checkout's own long-lived `aoc/` and `games/rogue/` caches, which is
where the history is. It is also the assurance step for a user before
sharing a proof (Lean's `lake check`), so it is a CLI flag, not a hidden
test hook: D2802.

**Not a daily sample.** Adding design 3 to the daily tier would cost a
whole-AoC cold check, about 40 s or more, every day, to catch something
that has never happened yet. Keep it in the full tier and revisit if it
ever finds anything.

**Other systems.** Lean 4 trusts `.olean` imports and offers
`lean4checker` (`lake check`) to replay them through the kernel on request
(check-cache.md §A.4). That is design 2, run by hand. rustc's incremental
cache has a debugging flag, `-Z incremental-verify-ich`, that recomputes
results loaded from the cache and compares their fingerprints. That is
design 3, and it is off by default (from memory, not checked).

## 6. D2680: is sharing between dev and release builds safe?

**The question.** The CLI and editor (release, no `dev` features) and the
AoC tests (dev features) share `aoc/.stitchwort/cache`. Debug and release
test binaries share `target/test-std-cache/{stack}`. The profile and
features aren't in the fingerprint (L1).

**The argument that it's safe.** An entry is a record that some build of
**these exact sources** checked the unit fully and without errors (D284).
A different build may replay it soundly if everything that build would
accept is something the writer would also accept, apart from running out of
resources. The ways profile and features differ:

- **Assertions:** `debug_assertions`, overflow checks, and `validate_inert`
  under `reference` (`check.rs:1782-1785`, uncounted, `budget.rs:369`).
  Each one either panics or does nothing. A panic means no entry is
  written, so a dev build never writes a result that release would refuse,
  or the reverse. What sharing loses is the *tripwire*: a dev build that
  replays a release entry skips the dev-only checks on that unit. That's a
  loss of test coverage, not of soundness.
- **Stack:** debug frames are bigger, and `Limits::stack` counts bytes.
  Replaying a release entry hides a debug-only `E-RESOURCE`, so a debug
  build reports success where it would have run out (L1). That is a
  resource result, not a different accepted theorem.
- **`test-bypass`** writes broken states directly into the kernel, for the
  tests that need them. Those tests use no shared cache folder [inferred
  from check-cache.md, "The gates still run the kernel": each cache test
  has its own temp folder], and an entry is only ever encoded from an
  elaborated unit, never from a bypass write.
- **Overflow wrapping in release** that debug would catch would be a bug in
  the checker itself. Sharing doesn't create it. It only lets a release
  result stand where the debug tripwire would have fired.

So sharing is safe on the condition that **a profile or feature may change
only whether a check runs out or trips an assertion, never what it
accepts**. That is already true of today's code, as far as I read it. It
should be written down in `check_cache.rs` as the invariant that makes
sharing sound, and §5's verify mode, run from a release CLI against a cache
the dev-built tests filled, checks it directly.

**The other design: split the entries.** Add a profile and features tag to
`CheckCache::compiler`. Cargo works this way, with separate `target/debug`
and `target/release` folders and the profile in every fingerprint, as does
Bazel, whose action keys hold every flag. It would keep the tripwires
running on every unit in dev builds, and it would cost the warm sharing
between the editor and the AoC tests. That sharing is the point of one
cache folder per project.

**Recommendation:** keep sharing (D2680 yes), and write the invariant and
its argument into `check_cache.rs`.

## 7. Decisions for Matt

- **D2800: Is §1's three-part argument the contract for replay?** Keys from
  what was consumed, entries equal to a full check, undo to the mark. A
  refusal counts as a bug, asserted to be zero in the differential tests,
  not as an ordinary miss. [rec: yes. It turns three separate review
  findings into one rule each future change can be checked against, and
  makes the next F1 show up as a failing count instead of a silent miss.]
- **D2801: For M1, key on the core text actually elaborated, rather than
  refusing a cache for a custom-prelude session?** [rec: yes. It removes
  the class of bug (a key computed from a description), costs one hash per
  session, and lets such sessions cache too.]
- **D2802: Add `stitchwort check --verify-cache` (a user-visible flag), run
  in the full tier on `aoc/` and `games/rogue/` beside the test cache's
  verify, and no sampled kernel recheck in the daily tier?** [rec: yes. It
  catches every kind of stale entry, not only unsound ones, on the caches
  with real history. It costs a full-tier `--no-cache` check, about a
  minute, and needs no second admission path to maintain.]
- **D2680 (driver review): keep check-cache entries shared between dev and
  release builds?** [rec: yes, with §6's invariant written into
  `check_cache.rs`. Sharing loses only dev-only tripwires and debug-stack
  failures on replayed units, never soundness.]

I decided these myself, as implementation details: undo through a new
`forget_since` rather than `rewind` (§3.3), the test hook's name and shape,
and dumping the kernel in the undo path only in `reference` builds.

## 8. Tickets to file

In order. The first two can run side by side, since they touch different
functions in `cache/mod.rs`.

1. **[Opus] Replay undo through one kernel primitive** (replaces SW-1925's
   plan, and keeps its scope: F1, F10, F11). Add `Kernel::forget_since`,
   make `Kernel::rewind` call it, delete `forget_declarations_from`, and
   destructure `Builtins` in `mark`/`rewind`. In `admit_replayed`: mark,
   then `forget_since` on failure. Bind on replay only for library entries,
   and refuse early a namespace entry with a non-empty `bound`. Add
   `Stats::refused`, the `fail_replays_after` hook, the undo-path dump
   assertion under `reference`, a full `Builtins` dump, the Float scenario
   test and the namespace case, and assert zero refusals in
   `assert_cache_changes_nothing` and `assert_targets_share`. Correct the
   module doc's "one the kernel refuses". Trust boundary and kernel, so
   Opus. 75 min. Tests: `task test:one --` the new tests,
   `check_cache::a_replay_that_fails_part_way_gives_the_same_result`,
   `check_cache::the_whole_library_loads_the_same_from_the_cache`,
   `-E 'package(stitchwort-core) & binary(it) & test(/^trusted::/)'`, and one
   small `rewind::` test that uses `Kernel::rewind`.
2. **[Sonnet] Key on the loaded core** (reshapes SW-1919's M1; SW-1919
   keeps L3 and L4). Record a digest of the elaborated prelude in
   `Session::start` and hand it to the elaborator. `library_interface`
   hashes it. Correct `cache_usable`'s comment. Add D2680's invariant
   comment to `check_cache.rs` (the driver review's lane A already planned
   that comment). Test: a custom-prelude session with a cache gets only
   misses on standard entries, then hits on its own second run. After
   D2801. 45 min. Tests: `task test:one --` the new test and
   `check_cache::an_entry_under_another_key_is_a_miss`.
3. **[Sonnet] Equations and induction rewind mid-operation** (new, from
   §3.2). Change `rewind_globals` (`lib.rs:1121`) to use `forget_since`, so
   a skipped equation no longer resets the declaration's step limit, stack
   floor and cancellation. Correct `Kernel::mark`'s doc about its callers.
   Before the change, confirm the effect with a unit test: after a skipped
   equation inside an operation, the budget's limit is still the
   operation's. After ticket 1. 40 min. Tests: `task test:lane AREA=…` for
   equations, or `task test:one --` the equation-skip tests and the new
   one.
4. **[Sonnet] `stitchwort check --verify-cache`** (new, after D2802). Add a
   `CheckCache` verifying mode (read misses; write compares with the stored
   entry; nothing written) and a `check` flag mirroring `test`'s, with the
   `--json` contract of SW-1952. Add it to `task test:verify-cache` for
   `aoc/` and `games/rogue/`. Update the CLI docs, `docs/testing.md`'s full
   tier list, check-cache.md's "How to get a full check", and the stale
   "The gates still run the kernel" paragraph (the test std cache).
   75 min. Tests: a CLI test on a small project, with one entry tampered
   with after sealing (rewritten with a valid checksum, through a test
   helper), that reports "differs", and an untouched cache that reports all
   "same". Not the full-tier task itself, which needs Matt's go-ahead.

**Related, not absorbed:** core review F8 (D2641, a `TrustedReplay` token so
the bypass shows in every signature) is the type-level half of §1's
argument and stays its own ticket. SW-1204 (the Float file isn't cached)
affects which file ticket 1's scenario test uses.

## 9. What this note doesn't cover

- Tampering by someone who can write to the cache folder is out of scope,
  as in check-cache.md §3.1.
- The test *result* cache's key (test-cache-key.md) and whether the
  fingerprint could be narrower (check-cache-key.md).
- Whether `ty_value`'s evaluation on admission (SW-1200) changes the undo.
  It doesn't seem to, since the values hang off the removed definitions,
  but I didn't check.
- I measured nothing. The costs in §5 come from check-cache.md's stage 3
  measurements, which are a week old and from a smaller AoC project.
