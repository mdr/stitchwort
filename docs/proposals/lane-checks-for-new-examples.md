# Lane checks for new examples and for cost (SW-4578)

Status: proposal for Matt. Nothing here is a rule yet; `docs/workflow.md` and
`CLAUDE.md` stay as they are until he decides. The numbers marked
"estimated" were not measured (this was a paper lane, with no builds or
tests); the others come from the logs, the baseline and the code.

## The problem

The all tier was paused from 12 to 22 Nov (D3712 ran it again on 22 Nov).
In those ten days two things slipped through that only the all tier looks at:

- **A new extraction example went four days without the checks that compare
  it against the reference evaluator.** SW-3936 added
  `examples/extract/opaque-nickname-precondition.sw` on 18 Nov (`26cd1c836`).
  Nothing in a lane or in the quick tier ran it through
  `extract::run_lines_agree_with_the_reference_evaluator` or
  `extract::random_inputs_agree_with_the_reference_evaluator`: those take
  `examples().sampled(2)`, which is every example in the all tier, every
  second in broad, and every eighth in quick and lane (`tier_sample`, 4 times
  the broad stride). So whether a new file is in the sample depends on its
  place in the sorted list. The all-tier run on 22 Nov was the first to run
  it, and the random-inputs and run-lines tests failed (SW-4564's second
  cause: the test's reference path hid opaque bodies). That was a bug in the
  test harness, not in the shipped code, but it shows the same hole: the
  example's own coverage was unproved for four days.
- **A deliberate cost went unrecorded.** SW-3930 (`526f98b64`, D3680) kept
  declared types glued and checks a `Refl` body unglued. It made
  `check-number-table` and `check-number-wide` 12.5% heavier in steps and
  part of `check-text-literal` 15% heavier in allocations; its merge note
  said 1.06x on `byComputing` only. The benchmark's counts have a 10% alarm
  (`bench/baseline.toml`, `baseline` test), but that test runs only in the
  all tier, so the change showed on 22 Nov together with the std growth from
  SW-4218 and 14 days of other work, and SW-4569 had to bisect it
  (`docs/performance/log.md`, 22 Nov).

The cheap `generated_code_is_stable` test (every extraction example's JS and
`.d.ts` snapshot) does run every example in the quick tier, so the snapshot
side was covered. The missing parts are the differential comparison and the
benchmark counts.

## What exists now

**Running one example through extraction and the differential checks.**

- The extraction differential tests are in `crates/cli/tests/extraction/extract.rs`
  (binary `extraction`, package `stitchwort-cli`):
  `extract::run_lines_agree_with_the_reference_evaluator` (the `-- run:` and
  `-- rejects:` lines, JS in node against the reference) and
  `extract::random_inputs_agree_with_the_reference_evaluator` (100 random
  inputs per export, from a fixed seed). They take the tier's sample, and
  there is **no way to name one example**: `EXAMPLES` and `task test:example
  NAME=` only reach the accepted, rejected, soundness and goal sweeps, and
  `STITCHWORT_TIER=all` runs all 59 files.
- The evaluator differential,
  `differential::the_evaluators_agree_on_the_prelude_and_every_example`
  (binary `proofs`, package `stitchwort-driver`), compares the machine and the
  reference evaluator on every `examples/accept` and `examples/extract` file
  (unless it says `-- differential: skip`). It already has
  `STITCHWORT_DIFFERENTIAL_ONLY=<part of the name>`, chosen from every example
  rather than the tier's sample (SW-4374, `docs/testing.md`, "Slicing the
  differential sweep"). Command:

  ```
  STITCHWORT_DIFFERENTIAL_ONLY=opaque-nickname STITCHWORT_TEST_THREADS=2 NEXTEST_TEST_THREADS=2 \
    nice -n 15 task test:one -- -E 'binary(proofs) & test(=differential::the_evaluators_agree_on_the_prelude_and_every_example)'
  ```

  It always compares the whole prelude first (more than 200 definitions and 100
  conversions, asserted), so the cost is mostly that fixed part.
- `task test:affected` can already pick tests from the files a diff touches
  (`dev/test-affected.toml`, rules by path, with shell commands allowed). It
  has no rule for `examples/extract/**` today.

**Running a few benchmark cases.** `stitchwort-bench` (`crates/bench`) takes
name fragments as arguments, `--no-time` for the deterministic counts from one
run each, and `--parts FILE` for per-example counts. `task bench -- ...` or
`cargo run --release -p stitchwort-bench -- check-number --no-time` runs only
the benchmarks whose names contain `check-number` (six: `-pattern`, `-table`,
`-huge`, `-wide`, `-dependent`, `-columns`) and compares each with
`bench/baseline.toml`; a filtered run compares only what it ran. The counts
(steps, visits, allocations, peak bytes) are the same on every run, so one run
is a fair signal; a rise over 10% fails. The `examples` sweep, 1,993 files and
most of the 80 s of `--no-time`, is only run if its name matches (the filter
`examples` would; `check-` and `run-` don't). Times in the baseline for the
cases a kernel or checker lane would choose, one run each:

| Cases | Baseline time (recorded) |
|---|---|
| `check-number-*` (six) | 1.5 + 9.4 + 1.5 + 73 + 10.7 + 76 = about 170 ms |
| `check-closed-*` (eight, about 1.3 M steps each) | about 1.0 s |
| `check-list-rfl`, `check-list-sym-rfl`, `check-list-byComputing`, `check-long-sum`, `check-nested-apps` | about 1.2 s |
| `check-text-literal` | 1.5 ms |

So the benchmark work itself is about 1 to 3 s for a useful handful; what
dominates is a release build of the bench crate (kache hit: seconds, estimated;
a cold change to `crates/core` or `crates/elab`: a few minutes, estimated, and
the lane has to build its release test binaries anyway if it is running tests
at all) and loading std once per process (a few seconds, estimated).
(Several benchmarks are `run-machine-*`: they check the machine, not the
checker, and are not what SW-3930 touched.)

**Overmind's rolling check.** Its script is not in the repo: `docs/workflow.md`
("Overmind, the soak laptop") describes it, `dev/soak/run` is named there but
isn't in the tree, and the job lives in Overmind's own session. I could not
read what it runs beyond that description: the quick tier plus whole-AoC and
roguelike `check --no-cache` per newly pushed commit, about an hour behind.
The quick tier already samples every 8th extraction example and every 16th of
the evaluator differential, and doesn't run the bench tests at all (they are
all-tier).

## Three options

### 1. A lane that adds an example runs that one example by name

**The change.** The brief for a lane that adds or changes a file under
`examples/` (any kind) says to run, by name, the checks that compare that file
with another implementation:

- for `examples/extract/NAME.sw`: the evaluator differential with
  `STITCHWORT_DIFFERENTIAL_ONLY=NAME` (works today), and the two extraction
  differential tests restricted to NAME (needs a small harness change below);
- for `examples/accept/NAME.sw`: the evaluator differential with
  `STITCHWORT_DIFFERENTIAL_ONLY=NAME`.

The harness change: `examples()` in `extract.rs` gets a
`STITCHWORT_EXTRACT_ONLY=<part of file name>` filter, like the differential's,
that picks from all examples instead of the sample (and the all-tier `sliced`
guard idea in the differential test applies: any slice variable set means
"not the full sweep"). It is about a dozen lines and a test that the filter
selects the named example and that an unknown name fails rather than running
nothing. A `test:affected` rule for `examples/extract/**` and
`examples/accept/**` could then choose the named run from the changed file
name, so a lane doesn't need the brief to say it.

**What it catches.** A new example that doesn't agree with the reference
evaluator, in JS or in the machine; a new example whose `-- run:` lines are
missing or wrong; a harness blind spot like SW-4564's (it would have failed in
the lane on the day SW-3936 added the file). It would not have caught SW-4564's other cause (the unifier's
last-arguments rule, four search tests), which has nothing to do with an
example.

**Cost per lane.** Only for lanes that add an example, perhaps one lane in
four. Estimated, not measured: the extraction run-lines test took 93 s and the
random-inputs test 68 s over all 59 examples in the all tier (SW-4564's
reruns, which included checking each example), so one example is about 1 to 3
s each plus the first node start and std load, 5 to 10 s in all; the evaluator
differential's fixed prelude comparison, estimated 15 to 40 s (the whole sweep
is "10 minutes" per `docs/testing.md`; the prelude is a small part). Say
**30 to 60 s** per example-adding lane, two commands, one at a time.

**Fit with "minimal lane tests".** It is the rule's own shape: a test selected
by name, for the file the lane added, under two minutes, no suite or sweep. It
adds one named test and one filter variable, not a broader run. It needs Matt's
OK only because it adds a standing step to every example-adding brief.

### 2. A kernel or checker lane runs bench --no-time on a few cases

**The change.** A lane that changes the kernel, the unifier, `rfl`/`byComputing`
checking, or conversion (the lanes that already run
`examples::soundness` for kernel changes) runs, once before it reports:

```
nice -n 15 cargo run --release -p stitchwort-bench -- --no-time check-number check-text-literal check-closed-print check-list-byComputing
```

(four name fragments, 17 cases: the six `check-number-*`, `check-text-literal`, the eight `check-closed-*` and `check-list-byComputing`, about 2 s of work in all). It reads
the printed comparison against `bench/baseline.toml` and puts any case over
+5% in steps or visits in its report with the reason ("deliberate, because
..."). If the cost is deliberate it says so in its commit, and the orchestrator
writes the performance-log entry (D3444) at merge, not after an all tier
notices it.

Nothing is gated, only reported: the all tier's `baseline` test stays the
gate (10% alarm). The lane's note is the missing piece: SW-3930's cost was
real and accepted, but nobody was told on the day.

**What it catches.** A change in steps, visits, allocations or peak bytes on
the checker's hot paths, on the day it merges: SW-3930's +12.5% on
`check-number-table` and `-wide` would have shown in a four-line table. It does
not catch growth that comes from std growing (the `check-closed-*` +11.6%, from
92 lemmas moving into std): that moves with other work and can't be assigned to
one lane.

**Cost per lane.** Only kernel/checker lanes, perhaps one in eight. About 1 to
3 s of benchmark work (the baseline times above) plus the release build of the
bench crate. If the lane already built the release CLI with kache, the bench
crate adds its own compile: estimated 20 s to 3 minutes, depending on cache. So
**under a minute warm, a few minutes cold.** One command; no suite. A lane
should skip the build step by not running it at all when it hasn't built
release at all, rather than building for this alone: its note then says "not
run", and the orchestrator's verifier or the all tier covers it.

**Fit with "minimal lane tests".** Cheap and named, but it is a build of a
second binary (`stitchwort-bench`); the rule forbids "the benchmark" and a
workspace build. This is the filtered form (named cases, `--no-time`, not the
whole benchmark and not the `examples` sweep), so it should be called out as an
exception the brief states by name, as the rule allows ("a brief may allow more
only with Matt's agreement"). That is the decision to make.

### 3. The alternative: Overmind's rolling check runs these

**The change.** No lane step. Overmind's per-commit job adds, beside the quick
tier, (a) the named differential for every `examples/extract` and
`examples/accept` file added or changed since its last check (git diff names),
and (b) `stitchwort-bench -- --no-time` on the filtered handful above, with
its comparison against the baseline, reported as a table with the commit it
first moved. It would also be a reasonable place for the whole bench `--no-time`
(80 s) per push, which is more than a lane should do.

**What it catches.** The same two things, an hour or so after the push instead
of before the merge: the problem in this proposal was the all tier not running
for ten days, and this puts a copy of the two cheapest all-tier signals into
the check that does run. It also catches a combination of lanes (two
individually small increases that together cross 10%), which neither lane sees.

**Cost per lane.** Zero for lanes. For Overmind: the filtered bench is about
the build (a few minutes, estimated, on a laptop twice as slow as Speedwell
for checking, per the 7 Nov soak report) plus a few seconds of work; the
differential per new file 1 to 2 minutes, estimated. Within its "under 60 min
a cycle" budget.

**Fit with "minimal lane tests".** Fully: lanes run nothing more. It costs
the orchestrator's attention when a failure is reported and lets the failure
reach `main` first, which D3546 already accepts. The weakness is the one in
this ticket: it only helps while Overmind's loop is running. It was "paused"
for the all tier, not for the rolling check, but I can't see the script from
here, and a check an hour behind finds the problem after the lane's context is
gone, so the fix is a new lane. Also, Overmind's script isn't in the repo, so
the change there is not reviewable or versioned with the checks themselves.

## Recommendation

- **Do 1 for the differential**, because the harness hole is real and cheap to
  close, and a lane has the context to fix a disagreement while it is fresh.
  Include the `STITCHWORT_EXTRACT_ONLY` filter and a `test:affected` rule so it
  is automatic and the brief needn't remember. [rec: yes]
- **Do 3 for the benchmark**, not 2: a lane's benchmark step costs a second
  binary's build and asks agents to judge a +5% number; Overmind can run the
  same filtered command on every push and name the commit, and the orchestrator
  records accepted costs at merge from that report. Revisit 2 for a lane that
  is itself about performance, which already profiles. [rec: yes]
- Put Overmind's scripts under `dev/overmind/` in the repo so these two additions
  are reviewable, and add "what it runs" next to the tier table in
  `docs/testing.md`. That's the second thing I couldn't check. [rec: yes]

What I did not do: no code, no tests, no change to `docs/workflow.md`,
`CLAUDE.md`, `dev/test-affected.toml` or the Taskfile; the harness filter, the
rule and Overmind's script would each be a ticket once Matt decides.
