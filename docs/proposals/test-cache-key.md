# A finer test-cache key (SW-1328)

**Status:** design note, 5 November 2026, for Matt's decisions (D2375: "an
Opus note on what's safe"). Nothing is built. Decisions P1–P5 are at the
[end](#10-decisions-for-matt).

Claims about Stitchwort are **[checked]** when I read the code or ran the
command named (on `main` at `8f149e5e3`; line numbers are at that commit),
**[measured]** when they come from the cache files on disk (§5), and
**[estimate]** when they are my reasoning. Claims about Unison are
**[unverified]**: from memory, not checked against its sources.

## 1. In short

- **The problem.** `stitchwort test` keeps each result under
  `<compiler version>-<fingerprint>-<modes>-<test hash>`. The fingerprint
  covers the source of every crate the driver is built with and the text of
  the whole standard library. So any compiler rebuild, and any std edit,
  throws the whole cache away. Overnight on 4–5 November, `aoc/` had nine
  full test runs after the first; **none of their 12,272 results came from an
  earlier build's cache [measured]**, although **82% of those tests had a
  hash an earlier build had already run, with the same result [measured]**.
- **The change.** Two steps, both automatic:
  1. Take the std text out of the key. A test's hash already covers every
     std definition it uses (§3). This alone would have reused 18% overnight.
  2. Replace the fingerprint of the whole compiler with an **evaluation
     fingerprint**: only the Rust that decides what a test computes once its
     term is fixed. That is the `core` crate (evaluators, natives, the
     kernel's checks that set unhashed flags, the hash function), the `rt`
     crate (the machine `stitchwort test` uses by default), the driver's
     test-running code, `Cargo.lock` and the Rust toolchain. Not the parser,
     the elaborator, diagnostics, printing, the language server, the
     formatter, the audit or JS extraction: they can only change a result by
     changing the test's term, which changes its hash. Together with step 1
     this would have reused **50% overnight [measured]**.
- **What it should do.** Elaborator, std and AoC changes, which are most of
  the merges, keep the cache. A change to the evaluator still starts afresh.
  A daily run with the cache off compares its results with the cache and
  fails loudly on any disagreement, so a hole in the key shows up within a
  day rather than as a silent stale pass.
- **Not recommended now:** a hand-bumped "evaluation contract" version (like
  `FLOAT_CONTRACT`). It would have reused 71–82% overnight, but it moves the
  safety from the build to people remembering, and its guard test would make
  every `core` or `rt` edit update a pinned digest (§4, option d). Worth
  revisiting with a few weeks of data from the daily comparison.

## 2. What the key is today [checked]

- `Cache::key` (`crates/driver/src/driver.rs:1074`) is
  `stitchwort-<CARGO_PKG_VERSION>-<build_fingerprint()>-<modes>-<test hash>`.
- `FINGERPRINT` is made by `crates/driver/build.rs` with
  `fingerprint::source_crates(root, "crates/driver")`: the driver and every
  workspace crate it depends on, read from the manifests. Today that is
  `driver`, `syntax`, `core`, `elab`, `js`, `rt`, `host`, `dev-features`,
  `fmt` and `partial-model`: each one's `Cargo.toml`, `build.rs` and
  `src/**/*.rs`. It adds `Cargo.lock` and the toolchain (`rustc -vV`,
  `TARGET`), because float literals and primitives come from Rust's standard
  library (docs/proposals/float.md §3.3).
- `build_fingerprint()` (`driver.rs:985`) hashes `FINGERPRINT` with the
  prelude's text and every library file's path and text. It was added with
  std-from-disk (SW-145, commit `300550fc6`): once std could be read at run
  time, the Rust fingerprint no longer covered it. The commit gives no
  hole it closes; it extended the "invalidate more than needed" stance of
  docs/proposals/compact-text.md ("Hashing and caches").
- `modes` is `n<natives>c<compact text>`, plus `m` for the machine runner
  (`driver.rs:1021`, `:1321`). `stitchwort test` uses the machine unless
  `--reference` is given (`crates/cli/src/main.rs:1529`), so AoC results are
  `n1c1m`.
- Results that ran out of resources aren't cached (`driver.rs:1155`), so
  limits aren't in the key.
- The check cache uses the same `build_fingerprint()` as the compiler part of
  its keys (`crates/driver/src/check_cache.rs:62`, `:72`).

## 3. What a test's result depends on

A test is a closed term of type `Bool` (or a partial computation of one).
Its content hash (`crates/core/src/hash.rs`) covers its type and body after
elaboration, and each declaration it refers to by that declaration's hash,
so transitively everything it can reach. The question is what *else* the
result depends on. I went through Matt's list and the code.

| Input | In the test's hash? | Notes |
|---|---|---|
| The test's term, with implicit arguments | yes | Elaborated term, so a different elaboration is a different hash [checked] |
| Every std or project definition it uses, transitively | yes | References are hashed as hashes; groups as units [checked, `hash.rs:1-44`] |
| Std definitions it doesn't use | no, and they can't matter | Nothing at run time looks a definition up by name [estimate, from the rows below] |
| Number literals | yes | `Term::Nat` hashes `Nat`'s data hash with the value (`hash.rs:544`) [checked] |
| Compact text | yes | `Term::Chars` hashes `List`'s and `Char`'s data hashes and the code points; `Char`'s fields cover `isScalar` (`hash.rs:558`) [checked] |
| Float primitives | yes | A primitive hashes as its name, its type and `FLOAT_CONTRACT` (`hash.rs:144`) [checked]. What the primitive computes is Rust, and the toolchain's |
| Natives (number, text, float, rt) | the definition is | A native replaces a definition the test reaches, so that definition's hash is covered. Natives are bound by registry identity and, for the kernel's natives, `+`'s rules, text and floats, by pinned hash (`PINS` in `crates/core/src/pins.rs`; `LIST_HASH`/`CHAR_HASH`). A native must compute what its definition computes (DESIGN.md §13), so whether one fires changes only speed, unless the native is wrong. A wrong native is a Rust bug, in `core` or `rt` [checked: `native.rs`, `nat_add.rs:55`, `chars.rs:155`, `pins.rs`, `driver/tests/pinned_hashes.rs`] |
| `+`'s extra rules (R3, R4) | the definition is | Rust in `nat_add.rs`, on only when `Nat.add` has the pinned hash [checked] |
| Registry built-ins (`List.Mem`, `Decidable.andThen`, …) | as used | The elaborator puts them in terms; the runner reaches them only through terms [checked: `registry.rs` header; estimate for every entry] |
| `fold` flag | no | Changes how goals print; "the fold is off while a program runs" (docs/core.md) [checked] |
| `@[js.*]` attributes | no | JS only, never seen by the evaluators (docs/core.md, D598) [checked] |
| Whether the test is partial | yes | A partial test has type `Effect.Delay …`, so a different hash (docs/core.md; the runner asks at `driver.rs:1368`) [checked] |
| Case-tree compilation | yes | Done by the elaborator; the result is the term [checked: pattern-guards.md §3] |
| Quotient erasure flags | **no** | Set by the kernel's checker (`check.rs:833`), read when running; not hashed (docs/core.md "Running") [checked] |
| Inert marks (proof irrelevance) | **no** | Computed by `check.rs:1731` through `inert.rs`, stored beside the definition. They change conversion, which skips inert arguments. A test's `Bool` is computed by evaluation, not decided by conversion, so marks shouldn't change it, but they live in `core` [checked where; estimate for the effect] |
| Erasure (what isn't computed) | no | `core/src/erase.rs` and `rt/src/erasure.rs`: Rust [checked] |
| The evaluator's semantics | no | `core`: `value.rs`, `reference.rs`, `step.rs`, `native.rs`, `nat_add.rs`, `chars.rs`, `float.rs`, `partial.rs`, `budget.rs`; and all of `rt` for the machine runner [checked] |
| The hash function and term representation | — | `hash.rs`, `term.rs`, `globals.rs`. A change that drops a component could make two different tests share a hash: these must be in the key [estimate] |
| How a value becomes an outcome | no | `run_selected` (`driver.rs:1317`) and `run_partial` (`driver/src/run.rs:548`): constructor 1 of `Bool` is a pass [checked] |
| Modes (natives, compact text, runner) | in the key | `n1c1m` [checked] |
| Limits | not needed | Out of resources isn't cached. A cached pass under looser limits is still a true pass [checked] |
| External crates (`num-bigint`, …), toolchain | no | `Cargo.lock`, `rustc -vV`, target [checked] |

**Answer to Matt's first point: yes.** Std edits are already accounted for
by the test's hash. I found no path by which a std change alters a test's
result without changing that test's hash [estimate, from the table]. The std
text in the key is redundant for the test cache.

**Answer to the second point.** Grouped by what they can do to a result
whose term is fixed:

- **Can change it** (keep in the key): `crates/core` (the evaluators, the
  natives and their pins, the checker's unhashed flags, the hash function),
  `crates/rt` (lowering, optimisation, the machine, its natives),
  `crates/dev-features` (feature flags compiled into both), the driver's
  test-running code, `Cargo.lock`, the toolchain and target.
- **Can't change it, except by changing the term and so the hash** (drop):
  `crates/syntax` (parser, lexer; `core` uses it only for diagnostics and
  spans [estimate]), `crates/elab` (all elaboration, `auto`, `omega`,
  equations, derived code, the prelude's loading), the rest of
  `crates/driver` (rendering, navigation, the language server's support,
  `audit` and the counterexample search, `doc`), `crates/js`, `crates/fmt`,
  `crates/host` (the IO host: a test performs nothing), `crates/partial-model`.

Within `core`, `pretty.rs`, `termination.rs`, `sct.rs` and `js_repr.rs` can't
change a result either. Leaving them out would have saved 1.6 points
overnight (§5) and adds a list to keep right, so I'd keep `core` whole.

## 4. The options

"Stale pass" means: the cache says a test passed (or failed), a fresh run
with this compiler would say otherwise, and nothing reports it.

| | Key's compiler part | What could go stale | How a mistake is caught | Cost to build | Cost to keep | Reuse overnight [measured] |
|---|---|---|---|---|---|---|
| **a** today | All driver-graph Rust, lock, toolchain, std text | Nothing known | — | — | — | **0%** |
| **b** drop std text | All driver-graph Rust, lock, toolchain | Nothing, if §3 is right | The daily comparison (§8) | Delete five lines of `build_fingerprint` for the test cache | None | **18%** |
| **c** evaluation fingerprint | `core`, `rt`, `dev-features`, the test runner's file, lock, toolchain (automatic, by build script) | A file outside the list that changes results: a new crate `core` or `rt` starts to depend on, or test-running code that moves out of its file | A test that the list covers `core`'s and `rt`'s dependency graph (as `the_fingerprint_covers_the_crate_graph` does today); the daily comparison | About an hour: a second fingerprint in `build.rs`, move `run_selected`/`run_partial` into one module, the graph test | Low: the list changes only when the crates do | **49%** (crate level), 50% (without `pretty`/`termination`/`sct`/`js_repr`) |
| **d** hand-bumped contract | `EVAL_CONTRACT: u32` in `core`, plus lock and toolchain; a test pins a digest of the (c) files and fails when they change, saying "bump the contract if this can change a result, then update the pin" | A change that alters results with the pin updated but the contract not bumped: a judgement call made wrong | The daily comparison only. Review sees the pin change but can't easily tell a semantic change from a refactor | About an hour, as (c) | **High:** every `core` or `rt` edit (79 commits in the last week [checked: `git log --since=2026-10-29 -- crates/core/src crates/rt/src`]) updates the pin line; lanes touching `core` in parallel conflict on it | **71%** if SW-93 had bumped, **82%** if not |
| **e1** = b + c | as c | as c | as c | as c | as c | **50%** |
| **e2** = b + d | as d | as d | as d | as d | as d | **71–82%** |

Notes on each:

- **(b)** is safe on the argument of §3 and nearly free. Alone it buys
  little, because the Rust graph changes on most merges: of the nine full
  runs, only two followed a build whose Rust was unchanged.
- **(c)** keeps the property the build fingerprint was made for (compact-text
  note: "the same weakness as the version number, which is already the known
  failure mode"): no one has to remember anything. It errs on the side of
  rerunning: two of its three overnight misses came from changes that can't
  alter a result (§5).
- **(d)** wins more but puts a person in the loop for every evaluator edit.
  `FLOAT_CONTRACT` works because the float primitives' meaning changes
  rarely and deliberately; `value.rs` and `rt` change daily. And the guard
  test that makes (d) safe is the part that costs: a pinned digest over
  files that many lanes touch.
- A middle form of (d), pinning only the files that *define* semantics
  (`value.rs`, `reference.rs`, `native.rs`, …) and fingerprinting the rest
  automatically, has the costs of both and saves little [estimate].

## 5. Measurements

**Method [measured].** `aoc/.stitchwort/cache/tests/` in the main checkout
keeps other builds' results for a day, and each file name carries the
build's fingerprint, the test and its hash. On 5 November at 07:56 it held
13,917 results from 15 builds, nine of them full runs (1,341–1,368 tests).
For each build I took the `main` commit current when its first result was
written, computed what each option's key would have been at that commit
(a digest of `git ls-tree` over the option's files), and counted the build's
tests whose hash an earlier build with the same key had already run. The
script is not committed; it is about 60 lines of Python over the file names
and `git`.

| Build (first write) | `main` at | Tests | a | b | c | d (no bump) |
|---|---|---:|---:|---:|---:|---:|
| 4 Nov 21:31 | `7d6ac8f03` | 1,341 | — | — | — | — |
| 22:50 | `8132188b3` | 1,358 | 0 | 5 | 1,300 | 1,300 |
| 23:46 | `f14eff602` | 1,358 | 0 | 0 | 1,118 | 1,118 |
| 23:57 | `be68fbf1f` | 1,364 | 0 | 1,114 | 1,114 | 1,114 |
| 5 Nov 00:27 | `8e46dca0b` | 1,366 | 0 | 1,110 | 1,110 | 1,110 |
| 00:59 | `906cadc00` (SW-93) | 1,363 | 0 | 0 | 0 | 1,338 |
| 01:58 | `d7a2516e6` | 1,363 | 0 | 0 | 1,333 | 1,333 |
| 02:55 | `0b73f0875` (SW-1305, SW-93 follow-ups) | 1,364 | 0 | 0 | 0 | 1,343 |
| 03:27 | `22e48b737` (SW-1310) | 1,368 | 0 | 0 | 0 | 1,141 |
| 07:03 | `9bfa4b6b5` (SW-1324) | 1,368 | 0 | 0 | 222 | 222 |
| **Total of nine runs** | | **12,272** | **0** | **2,229 (18%)** | **6,197 (50%)** | **10,019 (82%)** |

Column (c) is the file-level variant; crate level gives 6,004 (49%). Column
(d) assumes no bump; had SW-93 bumped the contract, the 00:59 run would have
reused nothing and the total would be 8,681 (71%). Six smaller runs (17–112
tests, single namespaces) are left out of the totals.

**No reused hash had a different outcome** in any later build: 10,019 reuses,
0 disagreements [measured]. Every result was a pass, so this shows the
hashes were stable, not that a failing test would have been caught.

**Why (c) missed three runs** [checked, `git diff` between the builds' commits]:

- 00:59, SW-93 (proof irrelevance, stage 1): `value.rs`, `reference.rs`,
  `globals.rs`, new `inert.rs`. A real change to evaluation and conversion;
  rerunning is right.
- 02:55, SW-1305 and SW-93's follow-ups: three new registry entries for the
  elaborator (`registry.rs`), a test-build-only `Budget::uncounted`
  (`budget.rs`, behind `cfg(feature = "reference")`), and the reference
  evaluator's validator. None can change a result.
- 03:27, SW-1310: `float.rs`'s pinned `NATIVE_HASHES` updated because a std
  edit moved three `Float` definitions' hashes; and `Cargo.lock` gained
  `serde_json` for a test (SW-1281). Neither can change a result (the tests
  that use those floats have new hashes anyway).

**Why every option missed most of the 07:03 run.** SW-1324 changed how list
literals elaborate in computations, so 1,146 of 1,368 AoC tests got new
hashes: different terms, equal in meaning. No key on the compiler can save
those; see §7.

**Longer run [estimate].** Over the last week, 79 commits touched
`crates/core/src` or `crates/rt/src`, out of about 2,000 on `main`,
board commits included. Most merges are std, elaborator and AoC work, so
the overnight 50% under (c) is a fair guide; on nights with fewer `core`
merges it would be higher.

## 6. The check cache

The check cache (docs/proposals/check-cache.md) keys each unit by its own
text and its dependencies' keys, chained (§4.2 items 3 and 6 there), and
also by `build_fingerprint()` [checked: `check_cache.rs:62`]. So:

- **Dropping the std text applies there too.** A unit's key already covers
  the text of every library file it loads, through the chain; the std text
  in the global part only makes one std edit re-elaborate every unit instead
  of the edited file and what depends on it [estimate: I read §4.2, not the
  key code]. Check-cache entries are trusted without the kernel (D1660), so
  this needs its differential test to cover a std edit before it lands.
- **The evaluation fingerprint doesn't apply.** A check-cache entry *is* the
  elaborator's output, so it depends on `syntax` and `elab` as much as on
  `core`. Only (b) is available there.

## 7. What a definition's content is: Stitchwort and Unison

**Unison** [unverified] hashes a definition's syntax tree after name
resolution: names are replaced by the hashes of what they refer to, local
names by positions, and the tree is otherwise what was written. Types are
inferred and stored beside it. Data types are structural unless declared
`unique` (and `unique` became the default for `type`), and test results
(`test>` watches) are cached by hash in the codebase.

**Stitchwort** [checked, docs/core.md and `hash.rs`] hashes the **elaborated
kernel term**: what the elaborator produced, implicit arguments, inserted
instances, compiled case trees, generated proofs and all. Names and
locations aren't hashed; data types are nominal (their name, constructors'
and fields' names are hashed); a mutual group is hashed as a unit.

Consequences for caching:

- **The good side.** The hash is of exactly what the evaluator runs. So a
  result keyed by it depends only on the evaluator, never on the elaborator
  that produced it; that is what makes option (c) possible. Under Unison's
  scheme, the compiler from source tree to runnable code would also be part
  of the result's inputs.
- **The cost.** Any elaborator change that produces a *different but equal*
  term moves hashes and reruns the tests, though their results can't change.
  SW-1324 did this to 84% of AoC's tests overnight [measured]. So does a
  change to how instances are found, how `auto` builds a proof inside a
  definition, or the order of implicit arguments. Unison's scheme would
  not see most of those, because they don't change the written tree.
- **Proofs inside definitions.** A definition whose body contains a proof
  (a `decreasing_by`, an `auto` argument) changes hash when the proof does,
  though running it erases the proof. The test cache could key on the
  hash of the *erased* term instead, which would survive proof-search
  changes. That is a larger design (erasure would have to be stable and
  hashable on its own) and not proposed here; I mention it as the next
  step if elaborator churn turns out to dominate the misses [estimate].
- **Nominal data types.** Renaming a constructor or field reruns every test
  that uses the type. That matches what the JS and records depend on, so
  it's the right trade.

## 8. Catching a mistake

Every option except (a) can be wrong in a way the key doesn't show. The
defence is the same for all of them: **a scheduled run with the cache off
that compares results with the cache.** Concretely: `stitchwort test
--verify-cache` runs every test fresh and, for each one, reads what the
cache holds under the current key; any disagreement fails with the test's
name, its hash and both outcomes. Run it in the daily tier on `aoc/` and
`games/rogue/` [estimate: the first full AoC run overnight wrote its 1,341
results within two minutes, by the files' timestamps].

A disagreement means the key missed an input (or a result was flaky), never
a false theorem: a test result isn't a proof the kernel relies on. I couldn't
confirm that any tier today runs all of AoC's `test`s with the cache off:
`aoc_answers.rs` runs the days' answers with `--no-cache` [checked], not
their tests [estimate]. So this run is worth having whatever the key.

## 9. Recommendation and plan

**Recommendation: e1 (= b + c), with the daily comparison.** It would have
taken overnight reuse from 0% to 50%, it can't be broken by someone
forgetting a bump, and what it still reruns needlessly is small (two of its
three misses overnight, from small `core` edits). If the daily comparison stays clean for a few weeks and
`core` churn still costs a lot, revisit (d).

The lane, about a Sonnet hour and a half [estimate]:

1. `crates/driver/build.rs`: a second fingerprint, `STITCHWORT_EVAL_FINGERPRINT`,
   over `crates/core`, `crates/rt`, `crates/dev-features` (manifest, build
   script, Rust sources), the driver's test-runner module, `Cargo.lock`,
   `rustc -vV` and the target.
2. Move `run_selected`, `lower_tests`, `modes` and `run_partial` into one
   driver module (say `crates/driver/src/test_run.rs`), so the fingerprint can
   name one file. `failure` (which explains a failure) can stay out: it
   doesn't decide the outcome.
3. `Cache::key` and `Cache::build` use the evaluation fingerprint, without
   the std text. The check cache keeps `build_fingerprint()` until P3 is
   decided.
4. A test, like `the_fingerprint_covers_the_crate_graph`, that every
   non-dev workspace dependency of `core` and `rt` is either covered or on a
   short list of crates that can't change a result (today: `syntax`), so a
   new dependency fails loudly.
5. `stitchwort test --verify-cache` and a daily-tier step running it on
   `aoc/` and `games/rogue/` (P4).
6. docs/core.md "Tests and content hashes" and the `build.rs` header: what
   the test key covers and why.

## 10. Decisions for Matt

- **P1: take the std text out of the test cache's key?** [rec: yes] §3
  found no way a std edit can change a test's result without changing its
  hash.
- **P2: which compiler part for the test key: (b) the whole Rust graph, (c)
  an automatic evaluation fingerprint (`core`, `rt`, `dev-features`, the test
  runner), or (d) a hand-bumped contract with a pinned-digest guard?**
  [rec: (c); 50% reuse overnight against 18% for (b); (d)'s 71–82% isn't
  worth a pin every `core` edit must update]
- **P3: take the std text out of the check cache's fingerprint too?** [rec:
  yes, as a separate lane after P1's, gated on the check cache's
  differential test covering a std edit, since its entries are trusted]
- **P4: add `stitchwort test --verify-cache` to the daily tier, on `aoc/` and
  `games/rogue/`?** [rec: yes; it is the safety net for P1 and P2, and today
  nothing runs AoC's tests with the cache off]
- **P5: start the implementation lane (§9) on Sonnet?** [rec: yes, after
  P1, P2 and P4; expected 90 min]
