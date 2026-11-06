# Check caches across a compiler change (SW-1753)

**Status:** design note, 6 November 2026, for Matt's decisions (SW-1745).
Nothing is built: the recommendation isn't a narrower key, so the brief's
"build it if it's (a) or (c) and small" doesn't apply. Decisions D2560 and
D2562 are at the [end](#8-decisions-for-matt).

The test *result* cache already has its own narrower key, the evaluation
fingerprint ([test-cache-key.md](test-cache-key.md), SW-1329). This note is
about the *check* caches: the test std cache under `target/test-std-cache`,
and the project check caches (`aoc/.stitchwort/cache/check`) that the AoC
tests and the CLI and editor share. §6 of test-cache-key.md already said that
the evaluation fingerprint can't apply here; this note measures what a
narrower key could still win.

Claims are **[checked]** when I read the code or ran the command (on `main`
at `4b59b15f0`), **[measured]** from git history, and **[estimate]** when
they are my reasoning.

## 1. In short

- **The problem.** Every check-cache entry is filed under `FINGERPRINT`: the
  sources of the driver and every crate it's built with. A compiler change
  makes every entry a miss, so the first std check of a test binary takes
  14.4 s instead of 0.46 s (SW-1716 profile), up to 8 times at once per
  stack size, and AoC's project check starts from source.
- **What a narrower key would win: little.** Of the 348 commits on `main` in
  the last ten days that changed `FINGERPRINT`, **316 (91%) touched `elab`,
  `core`, `syntax`, `dev-features` or the workspace manifests [measured]**:
  the checker itself, where any sound key must go cold. A key over only what
  checking runs would have stayed warm for at most 23 of them (7%), and
  realistically 10 to 15 (3 to 4%), since several of those commits touched
  driver files that run during a check (§3). Changes to `lsp`, `cli`, `web`,
  `native`, `fmt`, tests and docs *already* keep the caches warm: they aren't
  in the driver's crate graph, so `FINGERPRINT` doesn't cover them
  [checked].
- **The change I recommend instead.** Pay the unavoidable cold check once
  per build, not once per process: SW-1741 (fill the test std cache in a
  nextest setup script before the tests start). That turns up to 8 × 14 s of
  CPU and 14 s of latency into one 14 s fill per stack size per run. For AoC,
  SW-1732 and SW-1733 already moved the daily tests towards one warm-up
  shared by the days.
- **Also not worth it:** sharing the test std cache across this machine's
  checkouts (e). The main checkout's merged build equalled a lane's in 11%
  of merges (§5).
- **Not now:** a narrower check fingerprint (option c below). It's sound if
  its file list is right, but the list is partly hand-kept (the driver's
  files that run during a check), its win is 3 to 4% of the
  invalidations, and a mistake in it is a stale *trusted* entry (D1660: no
  kernel re-check on replay). Revisit only if SW-1741 is in and the cold
  fill still shows up in the profiles.
- **Never:** a hand-bumped "checker semantics version" (b). A forgotten bump
  is exactly a stale cache hiding a failure, and 91% of compiler commits
  would need one anyway.

## 2. What a cached check depends on [checked]

A check-cache entry is the elaborator's output for one unit (a library file
or a project namespace): its definitions, content hashes, flags, side tables,
diagnostics and, with `+nav`, navigation. The elaborator encodes and replays
it (`crates/elab/src/cache`); `crates/driver/src/check_cache.rs` only stores
it. Since D1660 a replayed entry is trusted: the kernel doesn't re-check it.
The unit's key already covers its text, its includes, its dependencies' keys
and the modes and limits (check-cache.md §4.2), so the only question is which
*Rust* decides the output for a fixed input.

| Code | Can change a cached check? | Why |
|---|---|---|
| `syntax`, `elab`, `core` (kernel, evaluator, natives, hashing, compact text) | **Yes** | They are the checker; `core` also decides the content hashes the entry records. |
| `dev-features` and the manifests | **Yes** | They pick `core`'s and `syntax`'s features (`stack-check`, `test-bypass`, `reference`). `FINGERPRINT` doesn't hash `dev-features` today: it is a dev-dependency, and `source_crates` follows `[dependencies]` only. The evaluation fingerprint names it explicitly; the check cache's key should too (a finding, not part of this design). |
| `rt` | **Yes, through one door** | `Session::start` gives the elaborator `counterexample::run_fast` (`driver.rs:438`), which lowers to and runs on `rt`'s machine; a counterexample found while checking is a diagnostic. |
| The driver: `driver.rs` (`Session::start`: the prelude, limits, `library_tests`, core link names, the library install), `counterexample.rs`, `check_cache.rs` (entry names), `project.rs` and `live.rs` (namespace sources, rechecks, the editor's sessions) | **Yes** | They run inside, or set up, the check that writes the entry. |
| The driver's other files: `test_run.rs`, `run.rs`, `render.rs`, `audit.rs`, `doc*`, `search*`, `at.rs`, `nav.rs`, `completion.rs`, `marks.rs`, `rewind.rs`, `axioms.rs`, `float_gate.rs` | No [estimate] | They read a checked session; nothing they compute is in an entry. |
| `js` | No | Its export checks (`driver.rs:680`) run after a load and aren't in the entry; they are recomputed each time. |
| `host` | No | Thread stacks; the stack size is in the key via the limits. |
| `lsp`, `cli`, `web`, `native`, `fmt`, `bench`, `standalone`, tests, docs | No, and already outside `FINGERPRINT` | Not in the driver's crate graph. |

The toolchain and target stay in any key (float literals and primitives come
from Rust's standard library: float.md §3.3), as do `Cargo.lock` and the
compiler version.

## 3. Measurements [measured]

For every first-parent commit on `main` in the ten days to `4b59b15f0` (2,416
commits, most of them board and merge bookkeeping), I took the files it
changed among those `FINGERPRINT` hashes (`crates/{driver,syntax,core,elab,
js,rt,host,dev-features}/{Cargo.toml,build.rs,src/**/*.rs}`, `Cargo.toml`,
`Cargo.lock`) and sorted the 348 commits with any:

| What the commit touched | Commits | A narrower key would |
|---|---|---|
| `elab`, `core`, `syntax`, `dev-features` or a manifest | 316 (91%) | go cold too: these are the checker |
| `rt`, but none of the above | 9 (3%) | stay warm only if `rt` is left out, which isn't sound (§2) |
| Only the driver, `js` or `host` | 23 (7%) | stay warm if none of the files is one that runs during a check |

Of the 23, the files were mostly `live.rs` (5), `driver.rs` (6), `at.rs`
(4), `project.rs` (4) and `search_at.rs` (3). `driver.rs`, `project.rs` and
`live.rs` are on the "yes" side of §2's table, so a key that hashes them
would still have gone cold for about half of the 23. **The realistic win is
about 10 to 15 of 348 invalidations, 3 to 4%.**

Merges, which bear on sharing the cache across checkouts rather than on
the key, are in §5.

## 4. The options

**(a) A fingerprint over the dependency graph of the checking crates plus
std.** The graph of `elab` and `rt` is `elab`, `core`, `syntax`, `rt`. The
driver can't be taken as a crate (it holds both `Session::start` and the
test runner), so (a) becomes (c). *Guarantee:* as strong as the list of
crates; the crates are read from manifests, like `source_crates` today.
Std needs nothing: its text is in each unit's key already.

**(b) A hand-bumped checker semantics version.** *Guarantee:* none beyond
people remembering. 91% of compiler commits would need a bump, so it would
be bumped nearly always, and a forgotten one is a stale trusted entry.
Rejected.

**(c) A fingerprint of the checker's sources.** `source_crates("crates/elab")
∪ source_crates("crates/rt")`, `dev-features`, the driver files in §2's
"yes" row, the manifests, `Cargo.lock`, the toolchain and the target. Built
like `evaluation_fingerprint` (a `NOT_CHECKING` list for the crates left
out, and a test against `cargo metadata` so a new dependency is covered by
default). *Guarantee:* sound if every Rust function that runs while a unit is
checked is in a hashed file. That holds for the crates by construction, but
not for the driver's files: a new call from `Session::start` into, say,
`doc.rs` would make `doc.rs` matter without anything noticing. The guard in
§6 would catch that within a day, not at once. *Win:* 3 to 4% (§3).

**(d) Keep the key, fill the cache once per run (SW-1741).** *Guarantee:*
unchanged: the key is the whole driver graph, as today. *Win:* the cold
check still happens after every compiler change, but once per stack size
per run, before the tests, instead of in each binary that wants std at
once. That is the "many times over" in SW-1745: with 8 test threads, up to
8 × 14 s of CPU and 14 s of the first test's latency (SW-1716, fix 7).

**(e) Share the test std cache across this machine's checkouts.** The key
is content-based (paths relative to the root, file contents), so a lane's
worktree and the main checkout compute the same `FINGERPRINT` for the same
sources. Today each checkout keeps its own `target/test-std-cache`, so the
post-merge verifier fills it again even when a lane has just filled it for
identical sources. A machine-wide folder (`~/.cache/stitchwort/test-std-cache`,
say) would let it reuse the lane's. *Guarantee:* unchanged (same key), plus
the salt check, which a shared folder keeps (one header). *Caveats:* the
grace sweep must then keep other builds' entries long enough for parallel
lanes (minutes is too short; the size is a few hundred KB per build per
stack); and the Nix-sandboxed gate can't see it, which is fine. *Win:* about 11% of
post-merge fills (§5).

**(f) Re-check stale entries instead of trusting them.** Replay an entry of
another build with the kernel re-checking it (check-cache.md option A).
*Guarantee:* no false theorem, but not "no hidden failure": an elaborator
change that now rejects a std definition, or now gives another diagnostic,
would still be hidden by the old entry. Fails the non-negotiable. Rejected.

## 5. Merges and a shared cache

Of the 663 merges on `main` in the same ten days, 539 changed the inputs of
`FINGERPRINT` (counted by the git trees of the driver graph's crates, whole,
so test-only changes count too: an overcount). In **58 of them (11%) the
merged inputs equal one merged lane tip's [measured]**: only then would a
cache the lane filled be warm for the main checkout. Usually a batch holds
two or more lanes that touch the checker, or `main` moved under the lane,
so the merge is a build nobody has checked yet. Sharing (e) is worth about
as little as narrowing (c).

## 6. The non-negotiable, and a guard

A stale entry must never make a test pass that would fail from source.

- **Today's key** guarantees it by covering every crate the driver is built
  with: anything that can run during a check is hashed. (d) and (e) keep
  that key, so they keep the guarantee as it is.
- **(c)** guarantees it only if its file list is right. Its guard would be a
  check that compares a fresh check with the cache under the *narrow* key:
  a "verify" mode for `CheckCache` in which `read` always misses and `write`
  compares the fresh entry with the one already on disk under the same name,
  failing on a difference. Run once a day on the std library (14 s) with a
  test std cache written by an earlier build. It assumes entries are
  byte-for-byte deterministic for a fixed input; counterexample searches have
  a wall-clock timeout (`elab/src/counterexample/mod.rs`), so where they run
  the comparison would have to be of the replayed state, not the bytes
  [estimate].
- **`verify-cache`** (`task test:verify-cache`, full tier) is no guard for
  the check cache: it runs `stitchwort test --verify-cache`, which compares
  *test results* with the test cache. The check cache's guard today is the
  differential `check_cache` tests (`crates/driver/tests/check_cache.rs`,
  sampled in daily and merge, whole in full), which compare a cached and an
  uncached check *by the same build*. They catch a hole in a unit's key,
  not in the compiler part of it.

## 7. Users

The CLI and the editor use the same `FINGERPRINT` (`CheckCache::at`). A
user on a release gets a new version number with every upgrade, and the
version is in the key (`COMPILER`), so a narrower fingerprint would only
help someone running the compiler from a checkout, like Matt in VS Code,
and only for the 3 to 4% of changes in §3. Changing it would be a
user-visible cache behaviour, so it isn't mine to build: D2561.

## 8. Decisions for Matt

- **D2560: build SW-1741 (fill the test std cache once per run) as the fix
  for SW-1745, and close SW-1745's "narrower key" half? [rec: yes]** The
  measured win of a narrower key is 3 to 4% of invalidations, for a
  partly hand-kept list whose mistakes are trusted stale entries.
- **D2561: keep one key (`FINGERPRINT`) for the CLI, editor and test check
  caches, rather than giving users a narrower one? [rec: yes]** Releases
  change the version anyway; a narrower key would only help checkout
  builds, by little.
- **D2562: share the test std cache across this machine's checkouts (§4e),
  as a follow-up lane? [rec: no]** It would have been warm after 58 of 539
  merges (11%, §5), and it adds a shared folder with its own sweep rules.
