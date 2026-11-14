# SW-2962: why single tests take over an hour in the full tier

The full tier at 58c3bcac7 on Overmind (12 Nov 2026) ran 2,059 of 2,591
tests in 14,160 s, with eleven single tests between 725 s and 6,081 s. This
note says, for each, what it iterates over, what an item costs, and what
would bound it. Every number says whether it was **measured** (and where)
or **estimated**.

Three fixes are in this branch. The rest are numbered follow-ups and three
D questions at the end.

## First: about half of each figure is the machine

Overmind is a 4-core, 8-thread i7-6700HQ with 15 GiB, about 2x slower per
core than Speedwell (whole AoC check without a cache: 134 s against 65 s,
measured in SW-2144's calibration). The full tier there runs 4 tests at once
(`TIER_THREADS`), and two of them can be corpus sweeps with pools of 5
threads (`corpus-sweeps`, `STITCHWORT_TEST_THREADS=5`). That is up to 14
busy threads on 4 cores.

The bench tests show how big this effect is, because they are serial by
nature (allocations are counted per process):

| Test | Expected alone on Speedwell | Overmind full tier | Ratio |
|---|---|---|---|
| `repeat` `counts_repeat_within_a_process` (the `examples` benchmark twice) | about 190 s (the test's own comment) | 2,328 s | about 12x |
| `baseline` `counts_have_not_regressed` (every benchmark once) | 145 to 166 s daily without `examples`, plus one `examples` run: about 250 s (estimated) | 2,211 s | about 9x |

So the hour-long figures are each test's own cost multiplied by roughly 5
to 12 for the machine and the oversubscription. Both parts matter: the tier
has to finish on Overmind, and each test's own cost is still far over a
minute on Speedwell. The Speedwell-alone figures below are what each test
costs by itself.

## The tests

### 1. `rewind` `rewinding_changes_nothing_for_the_examples`: 6,081 s

**What it checks.** For every example (1,582 files in `accept`, `extract`,
`reject` and `soundness`, 76 projects, 44 `goals`: 1,702 items), a check in
a fresh session, then check-rewind-check-rewind-check in one session, then a
cancelled check and a check after it. Each result is compared with the fresh
one through a canonical dump of 3 to 18 MB. Projects also re-check each
namespace.

**Cost model.** About 5 checks an item: 1,702 × 5 = about 8,500 checks.
The full tier makes each check dearer in two ways. It checks the library
from source in every session, where the other tiers replay it from the test
std cache. It also runs the counterexample search in every session, where
the other tiers run it only for the examples about it.

Measured on Speedwell (load 25 to 30), 11 items (every 200th file and every
10th project), one thread, fresh + check-rewind-check + cancel + cleared:

| Session setup | Time for the 11 items |
|---|---|
| full tier (library from source, search on) | 36.0 s |
| full tier, search off | 26.4 s |
| lane tier (library replayed, search only where named) | 11.8 s |

So the full tier's setup costs about 3x per item. Most of that is items
that load 15 to 25 library files: `ranges.sw` took 9.6 s in the full setup
against 2.7 s in the lane setup. Items that load almost none of the library
cost about the same either way, 0.5 to 1 s. The heavy tail also matters:
the daily sample (every 8th file, lane setup) takes 85 s on a pool of 5,
about 1.6 s an item.

Estimated for Speedwell alone: 1,702 items × 1.6 s × 3 / 5 threads = about
1,600 s, which Overmind multiplies about 4x.

**Fixes.** Not done here, because each needs a decision:

- Library from source and the search in every session: D3538.
- What a full corpus costs at any setup: about 1,700 items × 1.6 s / 5 =
  about 540 s on Speedwell. That is over Matt's "a minute or so" whatever is
  done per item. D3539.

### 2. `machine::aoc_agrees` (rt): 5,953 s. **Changed**

**What it checks.** That the machine agrees with the reference evaluator on
the AoC project:
- every AoC test (but the real-input tests) on both;
- each of the 17 answered days' `main` on the machine against the known
  answers;
- each answered day's `main` on its real input and its example input, on
  both.

**Cost model.** One session checked the whole project (65 s on Speedwell,
measured in SW-2144), then everything above ran on one thread. Most of the
time is the reference evaluator.

Measured on Speedwell, one day at a time:
- 2024 day 1: check 3.3 s; its tests, lowering and the machine about 0.1 s
  each; real input 0.03 s on the machine and 0.8 s on the reference
  evaluator.
- 2021 day 5: check 17.3 s; tests 0.4 to 0.6 s; real input 8.7 s on the
  machine and **over 120 s** on the reference evaluator (stopped at the
  time limit).
- All of 2024's tests on the reference evaluator: over 110 s (stopped
  there).

The days vary by over 100x, and the heavy ones are the reference
evaluator's real-input runs.

**The change.** The project is taken a part at a time: `Aoc.Common`, and
each day with the namespaces under it (73 parts). Each part runs in a
session of its own on `par_map`, which runs the part's own tests and its
day's `main`. `differential::aoc_parts` lists the parts from the folders and
fails on a file that is in no part. `AOC_PARTS=Year2024.Day01,Common` keeps
only the named parts.

Every test and every `main` comparison is still made. What is lost is
lowering every definition of the whole project into one program: each part
is lowered together with what it uses instead.

**Measured.** `STITCHWORT_TIER=full AOC_PARTS=Year2024.Day01,Year2025.Day01,Common`:
3 parts, 112 tests, 9.4 s.

**Projected** (estimated): the same reference-evaluator work, plus about 73
part checks of 3 to 17 s each (about 600 s of CPU), on 5 threads instead of
one. That is about 4x faster on Speedwell. On Overmind, which is already
oversubscribed, perhaps 2 to 3x: about 2,000 to 3,000 s. The test can never
be faster than its slowest part, a heavy day's real-input run on the
reference evaluator (minutes). D3540 is about that run.

### 3. `lower::every_aoc_main_lowers` (rt): 5,606 s. **Changed**

**What it checks.** Every definition of the AoC project lowers to the IR and
is well formed. Every AoC test (but the real-input tests) gives the same
outcome on the IR interpreter as on the reference evaluator. Every `main`
lowers.

**Cost model.** The same shape as `aoc_agrees`, with no real-input runs:
one whole-project session, then every test on the reference evaluator and
on the IR interpreter, on one thread. Most of the time is the reference
evaluator again (over 110 s for 2024 alone, measured above).

**The change.** As for `aoc_agrees`: one part at a time, side by side, each
part's own tests and its `main`s. **Measured:** the same 3 parts, 112
tests, 6.5 s. **Projected:** about 4x faster on Speedwell, 2 to 3x on
Overmind (estimated).

Both tests still run the whole project's tests on the reference evaluator,
each in its own process: follow-up 1.

### 4. `check_cache` `the_cache_changes_nothing_for_the_examples`: 3,573 s

**What it checks.** For every example (1,658: files and projects, but not
`goals`), three runs: fresh, cold through a new cache (which writes it), and
warm (which loads from it). The three dumps must be equal, with the cache
statistics as expected.

**Cost model.** 3 runs an item. The library is checked from source in the
fresh and cold runs in every tier; this test never uses the test std cache.

Measured on Speedwell, the same 11 items: 14 s. Items that load 17 to 23
library files cost 1 to 2.4 s per from-source run; the warm run costs
0.1 to 0.25 s. The daily tier (every 8th) takes 89 s, so the full corpus is
about 8 × 89 = **about 710 s on Speedwell** (estimated), which Overmind
multiplies by 5.

Most of the cost is the same library files elaborated from source, again
and again: twice per item, 1,658 times. What the test adds beyond the two
whole-library tests is each example elaborated against replayed library
entries, which is where a forgotten side table would show.

**Fixes.** None done. Follow-up 2, and D3539 for the corpus as a whole.

### 5. `check_cache` `aocs_namespaces_load_on_their_own_from_the_whole_projects_cache`: 2,558 s

**What it checks.** The whole AoC project's check fills a cache. Then, for
each namespace written (about 300: each day's namespace, `Tests`, `Spec` and
`Proofs`, and `Common`'s), the namespace alone is checked fresh, then loaded
alone from the cache, and the two dumps must be equal.

**Cost model.** Each fresh run checks the namespace and everything it uses
from source, with the library. A day's namespaces mostly share one chain
(`Proofs` uses `Spec` uses the day uses `Common`), so the chain is checked
again for each of them. The cost grows with the sum of the dependency
closures, not with the number of namespaces.

Estimated: about 300 × 3 to 17 s (a day's subtree check, measured above) =
about 2,400 s of CPU, or about 500 s on 5 threads on Speedwell.

**Fixes.** Follow-up 3.

### 6. `bench` `repeat` `counts_repeat_within_a_process`: 2,328 s, and `baseline` `counts_have_not_regressed`: 2,211 s

**What they check.** `repeat`: a benchmark's counts are the same on its
second run in a process as on its first, so no one-time work hides in a
count. `baseline`: every benchmark's counts are within the baseline's
thresholds.

**Cost model.** The `examples` benchmark checks the whole example corpus
serially. Allocations are counted per process, so it can't use a pool.
`repeat` runs it twice (about 190 s on Speedwell, from its own comment) and
`baseline` once, on top of the other benchmarks. On Overmind, beside the
sweeps, the two tests take 2,328 s and 2,211 s: the machine factor above.

**Fixes.** Follow-up 4.

### 7. `rewind` `emptying_the_caches_changes_nothing_for_the_examples`: 2,287 s

**What it checks.** For the same 1,702 examples as test 1, a fresh check,
then a check with every cache emptied before every declaration, which must
give the same outcome.

**Cost model.** 2 checks an item, with the same full-tier setup as test 1:
library from source and the search in every session. The cleared check
costs about the same as the fresh one (measured, the 11 items above). The
fresh check is the same one test 1 makes for the same item, in the same
setup.

**Fixes.** D3538 applies here too. Follow-up 5 would share the fresh check
with test 1.

### 8. `fmt_hashes` `formatting_changes_no_declaration_hash`: 2,213 s. **Changed**

**What it checks.** The formatter's hash oracle: every tracked `.sw` file
(and every project) in its scope is loaded as written and as formatted, and
every declaration's hash must be the same.

**Cost model.** 2 loads an item. In the full tier this includes the whole
AoC project, checked twice on one thread.

But the repository is kept formatted. **Measured** (`stitchwort fmt
--check`, 12 Nov 2026): formatting changes 2 of the 819 standalone files in
scope and no project at all, AoC included. So nearly all of the test's time
went on loading the same text twice. That compares nothing that can differ:
two fresh sessions on the same text, and the determinism of hashes is what
the `hash_stability` snapshots guard.

**The change.** A file that formatting leaves as it is, or a project none
of whose files it changes, is not loaded. Formatting the whole corpus is
cheap, so every tier now formats all of it, with no sample, and loads
everything formatting changes. The AoC project, if formatting ever changes
one of its files, is still loaded in the full tier only.

**Measured:** daily tier 54 s → **9.9 s** (Speedwell, load about 20).
**Projected:** the full tier the same, since it does the same work now:
2,213 s → about 10 to 40 s on Overmind.

**What's lost:** nothing that was being checked. Follow-up 6 is about the
oracle itself: with a formatted corpus it has almost nothing to compare.

### 9. `rewind` `rewinding_changes_nothing_for_the_aoc_project`: 1,109 s

**What it checks.** The whole AoC project, in 3 sessions side by side:
check-rewind-check, each namespace re-checked, and cancel-then-check. A
fourth session measures what a mark and a rewind cost. Each is a
whole-project check (65 s alone on Speedwell, measured in SW-2144),
several of them done twice.

The cost is about 7 whole AoC checks on 4 threads. That is about right for
what it checks, and the 1,109 s is mostly the machine. Follow-up 7.

### 10. `search_bench` `proof_uses_find_their_lemma_among_the_first_ten`: 725 s

**What it checks.** Over 5,000 queries, one for each place in the library
where a proof uses a lemma, run serially in one session. Recall@10 must be
at least 50%. It is a benchmark rather than a correctness test. Follow-up 8.

## Follow-ups

1. **One reference run for the two rt AoC sweeps.** `aoc_agrees` and
   `every_aoc_main_lowers` each run every AoC test on the reference
   evaluator, and the outcomes are the same. Either fold them into one
   test that compares both the machine and the IR interpreter against one
   reference run per part, or keep the reference outcomes in a file in the
   test's target folder. That saves about half their combined
   reference-evaluator time (estimated). Sonnet, about 45 min.
2. **`check_cache` examples: shard or share.** (a) Split the sweep into a
   fixed number of tests by stride, for example `_part_0` to `_part_7`
   with items `i % 8 == k`, so that nextest spreads them and no single test
   is the tier's long pole. This keeps all the coverage. (b) Look at whether
   the fresh run can share the library: give the fresh and cold sessions
   one pre-elaborated copy of the library files the example uses, which
   would need a session snapshot API. That is design work: Opus.
3. **`aocs_namespaces_load_on_their_own`: one fresh chain per day.** Check
   fresh, in one session, a day's namespaces in dependency order, taking a
   mark after each, and compare each namespace's cached-alone load with the
   dump at its mark, if a dump at a mark can be made to equal a fresh
   alone-check. That would make the cost linear in the namespaces. Needs a
   look at whether the dumps are order-independent first: Opus, 1 h to
   investigate. Failing that, D3539's answer applies.
4. **Bench: one fewer whole-corpus run.** In the full tier, `baseline` could
   run `examples` twice (`run(b, 2, false)`) and fail on a variation, as
   `repeat` does. `repeat` would then run its four fast benchmarks in every
   tier. That saves one serial whole-corpus run: about 95 s on Speedwell,
   about 1,100 s on Overmind (estimated). The catch: in `baseline`,
   `examples` runs after the other benchmarks in the same process, so
   one-time work they also do is already done. The fast benchmarks still
   catch that kind of work in `repeat`. Sonnet, 30 min, with a check that
   it is the same check.
5. **Share the fresh check between the two `rewind` example sweeps.**
   `emptying_the_caches` recomputes test 1's fresh outcome. Folding the
   cleared-caches check into test 1's per-item loop saves one check of
   seven an item (about 14%). The cost is that the two failures share a
   test name. Small: Sonnet, 20 min.
6. **The formatter's oracle needs unformatted input.** With the corpus
   formatted, `fmt_hashes` compares 2 files. Its scope leaves out
   `examples/reject` and `soundness`, where formatting changes 71 files,
   because those don't load. A stronger oracle would de-format each file
   first (re-indent, re-wrap, add and remove optional brackets) and check
   that formatting it back gives the same hashes. Design question for the
   formatter's owner: Opus, paper.
7. **Overmind's full tier: pools sized to the machine.** On an 8-thread
   machine, `STITCHWORT_TEST_THREADS=5` with two sweeps and 4 tests puts 14
   threads on 4 cores. `TIER_THREADS` already lowers the test count under
   24 GiB; it could also set the pools to 2 or 3 there. That won't lower
   the CPU total, but it would cut the thrashing, and memory with it.
   Measure on one Overmind full-tier run. Orchestrator's call, small.
8. **`search_bench` proof uses: a pool or a sample.** The 5,000 queries are
   independent once the candidates are built. Either run them on `par_map`
   with a session per worker (the library load, about 5 s each), or score a
   fixed sample of 1,000 in full. The latter changes what the benchmark's
   recall figure means. Sonnet, 30 min.

## Decisions for Matt

The numbers continue from the highest in use when this was written
(D3537). The orchestrator renumbers them if they have been taken since.

**D3538: in the full tier, should the `rewind` example sweeps check the
library from source and run the counterexample search in every session,
or only on the daily sample's items? [rec: only on the daily sample's
items]**

- **The problem.** For about 1,700 examples, each of several sessions
  re-elaborates the same library files and runs the search. That makes each
  item about 3x dearer: 36 s against 12 s on 11 items, measured.
- **The change.** In the full tier, every 8th item (the daily sample) keeps
  the library from source and the search. The rest replay the library from
  the test std cache, with no search, as the other tiers do.
- **What it should do.** Test 1 goes from about 1,600 s to about 650 s on
  Speedwell, and from about 6,000 s to about 2,500 s on Overmind. Test 7
  roughly halves. All estimated.
- **What's lost.** Rewinding over library elaboration and over a search is
  still checked, on about 220 items instead of 1,700. The library is the same
  files each time; only which of them load differs.

**D3539: what should a full-tier corpus sweep be in the end state:
the whole corpus in each run, split into several tests, or a rotating
sample with a fresh seed each run, like the fuzzers? [rec: split, then a
rotating sample if the tier still doesn't fit]**

- **The problem.** Matt wants nothing anywhere near an hour, and ideally
  nothing over about a minute even in the full tier. At about 1.6 s an
  item, a 1,700-example sweep on 5 threads is at least about 540 s on
  Speedwell, whatever is done per item. There are about a dozen such sweeps.
- **The change.** Two options:
  - (a) Split each big sweep into a fixed number of tests by stride, run as
    separate tests in the full tier only: `the_cache_changes_nothing_for_the_examples_part_3`
    of 8. The daily and merge tiers keep one test on their sample.
  - (b) A rotating sample: the full tier covers a different eighth each run
    (the offset from the date, printed so that a failure can be rerun), so
    every item is covered over 8 runs.
- **What it should do.**
  - (a) keeps all the coverage. Each test is about 1/8 of today's, about
    70 to 200 s on Speedwell (estimated). The tier finishes sooner because
    there is no single long pole at the end, but the CPU total doesn't
    change.
  - (b) also cuts the full tier's sweep time to about 1/8. A regression in
    one item is found within 8 runs rather than in the next run.

**D3540: should `aoc_agrees` stop running each answered day's `main` on
its real input on the reference evaluator? [rec: yes]**

- **The problem.** On real inputs the reference evaluator takes minutes on
  the heavy days: 2021 day 5 took over 120 s, against 8.7 s on the machine
  (measured). It is now the floor of `aoc_agrees`'s time.
- **The change.** Compare the machine's output on the real input only with
  the known answers, which the test already does. Keep both evaluators on
  the example input.
- **What it should do.** `aoc_agrees` drops by its slowest days' reference
  runs: its time becomes about the same as `every_aoc_main_lowers`'s
  (estimated).
- **What's lost.** Nothing then runs the reference evaluator at real-input
  scale. It is the oracle, so its being right on small inputs is what the
  tests rely on.

## Tests run for this note and the fixes

All on Speedwell, one at a time, `nice -n 15`, at load 12 to 30:

- Temporary probes (`#[ignore]`d tests, not committed):
  - `rewind::sw2962_probe` at `full`, `full` with the search off, and
    `lane` (36.0, 26.4 and 11.8 s);
  - `check_cache::sw2962_probe` (14 s);
  - `lower::sw2962_probe` on 2024 day 1, 2021 day 5 and all of 2024
    (the last two stopped by their time limits, at 150 s and 170 s).
- `fmt_hashes::formatting_changes_no_declaration_hash`, daily: passed,
  9.9 s.
- `lower::every_aoc_main_lowers` and `machine::aoc_agrees`, with
  `STITCHWORT_TIER=full AOC_PARTS=Year2024.Day01,Year2025.Day01,Common`:
  passed, 6.5 s and 9.4 s.
- `cargo clippy --release -p stitchwort-rt -p stitchwort-native --tests`:
  clean. The native copy of `differential.rs` builds.
