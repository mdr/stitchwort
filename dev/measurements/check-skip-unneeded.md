# Loading only the namespaces `check` needs (SW-1193, D2300)

The implementation (D2301) is described under "As built" at the end; the
rest is the investigation that led to it.

Measured on 4 Nov 2026, release build, `aoc/` of this worktree, warm check
cache. The machine was shared and busy (load average 30-80 during the runs,
about 65 on average; 10 cores), so **CPU time (user+sys) is the number to
trust; wall time is inflated and noisy** (a base run of the same edit took
3.5 s to 17.6 s wall at about the same 3.5 s of CPU). Scripts and raw output:
`dev/check-skip-unneeded/`.

## Summary

**The problem.** After editing one file in aoc, `stitchwort check` takes
3.3-3.7 s of CPU (4-8 s wall) when only 1-4 of the 207 namespaces need
checking. The other 203-206 have a cache entry that says they passed, but
`check` still replays each entry into memory (declares every definition to
the kernel, fills the tables), and that replay is 80% of the run (about 2.8 s
of 3.4 s CPU). Nothing in a plain `check` looks at those declarations.

**The proposed change.** In `Session::load_analysis`, when the caller only
wants diagnostics (plain `check`, without `--index` or `--counterexamples`),
work out each namespace's cache key from the sources alone (the keys are
chained: a namespace's key hashes its closure's keys, so no replay is needed
to compute them). A namespace whose entry is present and valid is a hit; the
namespaces to load are the misses and everything they import, directly or
not. The other hits are not replayed: they count as checked, and their stored
warnings are reported from the entry. Estimated size: 250-400 lines in
`crates/elab/src/cache` and `crates/driver/src/project.rs`, one cache format
bump, plus tests. Every other command keeps today's path.

**What it saves.** Measured with a prototype (a few lines, env-var switched,
which skips the unneeded replays but does not yet report the stored warnings
or check exports):

| edit (3 runs each, median) | namespaces re-checked | loaded | today CPU | prototype CPU | today wall | prototype wall |
|---|---:|---:|---:|---:|---:|---:|
| a `Tests` namespace | 1 | 4 | 3.30 s | **0.56 s** | 5.7 s | 0.7 s |
| a `Proofs` namespace | 1 | 5 | 3.48 s | **0.64 s** | 7.8 s | 1.2 s |
| a day's code namespace | 4 | 6 | 3.53 s | **0.69 s** | 8.6 s | 2.1 s |
| `Aoc.Common` | 59 | 59 | 21.95 s | **18.47 s** | 55 s | 31 s |

So 5-6x less CPU for the three edits users make most (a saving of about
2.8 s each), and 3.5 s of 22 s (16%) when the edit forces 59 namespaces to be
re-checked. Real implementation will cost a little more than the prototype
(reading warnings out of the entries, the export check): estimated 0.05-0.15 s.
Measured: all the table figures. Estimated: the cost of the real
implementation; anything about commands other than `check`.

## 1. What `check` uses a loaded cached namespace for

`check` (crates/cli/src/main.rs `check`) calls `Session::load_project` ->
`load_analysis` (crates/driver/src/project.rs), which walks the namespaces in
canonical order and, for each, `check_project_namespace` ->
`Elaborator::elaborate_namespace` -> `elaborate_namespace_cached`
(crates/elab/src/cache/mod.rs). On a hit that calls `replay_namespace`:
walk the syntax for navigation, declare the names, load the library files it
needs, then `decode` the entry and `admit_replayed` its definitions and data
types to the kernel and `replay_tables` (tests, side facts, extensions).
What the result is then used for:

| use | needs the declarations? | where it can come from |
|---|---|---|
| Errors / `E-NAMESPACE-FAILED` | no | a cached namespace has no errors or goals (only a clean elaboration is written), so it is `Checked` and blocks nothing |
| Warnings | no | stored in the entry (`warnings`, read by `read_tables`), but at the end of the body, after the tables, so reading them today means decoding past the tables. Put them in the entry's head and they come cheaply |
| Doc-link warnings (`W-DOC-LINK`) | by design yes, in practice a syntax pass | not stored (SW-1045): recomputed on each hit by `doc_link_warnings`, which resolves against the loaded scope. `stitchwort doc` already resolves links from the syntax and the project's names without checking (docs/syntax.md, SW-1045); a skipped namespace needs that. aoc has no doc links, so the prototype ignores this |
| Export check (`check_exports`, JS exports fit together) | yes, only if the namespace has exports | an `exports` flag in the head: skip (and not skip loading) accordingly. aoc has none |
| The `checked N namespaces` line | no | the order list |
| A later namespace that imports it | yes | this is why the namespaces a miss imports must load. Exactly its closure; the misses' closures, together, are the "needed" set |
| `--index` navigation output | yes | `nav` rows are in the entry but are merged into the session's index (`write_index`); keep the current path |
| `--counterexamples` | yes, for the targeted theorems | keep the current path (or load only the targeted subtree's closure) |
| Test running, `run`, `build`, `doc`, `axioms`, `audit`, `search` | yes | other commands (they call `load_analysis` too); they pass "everything loaded" and are unchanged |

Nothing else reads a replayed namespace in plain `check`: `discard(session)`
follows the report.

## 2. What it costs today

`STITCHWORT_TIMINGS` rows (wall time under load, summed) for a base run after
a Tests edit: 206 replayed namespaces took 2.8-5.4 s, the 1 re-checked
namespace 0.06-0.16 s, core plus the library files 0.3 s. Wall time under
load 30-80 is inflated, so the split by CPU is: whole run 3.3-3.5 s; the same
run with the replays skipped 0.55-0.7 s; so the replays are about 2.7-2.8 s
(80%), and the floor is core elaboration (0.2-0.3 s), parsing the project and
reading 207 entry files (the rest). Medians of three runs (`results-2026-11-04.log`):

| edit | namespaces replayed | namespaces re-checked | CPU | wall | load |
|---|---:|---:|---:|---:|---:|
| (a) `Day05/Tests/Examples.sw` | 206 | 1 | 3.30 s | 5.7 s | 30-32 |
| (b) `Day05/Proofs/Part2.sw` | 206 | 1 | 3.48 s | 7.8 s | 42-49 |
| (c) `Day05/Day05.sw` | 203 | 4 | 3.53 s | 8.6 s | 42-48 |
| (d) `Common/Range.sw` (`Aoc.Common`) | 148 | 59 | 21.95 s | 55 s | 43-57 |

Each run appends a fresh comment line to the file, so its key changes and the
namespaces that import it miss, as with a real edit (keys hash sources, not
interfaces: a comment edit and a signature edit behave the same). (b)'s
re-check is cheap here (0.2 s) where SW-1170 measured 1.7 s for a Proofs
edit: a comment doesn't change the proofs, which are probably cached per
declaration; a real proof edit adds its own checking time to both columns.

## 3. With only the needed namespaces loaded

Prototype (STITCHWORT_SKIP_UNNEEDED, on this branch only): in
`load_analysis`, a pre-pass computes every namespace's key in order
(`Elaborator::peek_namespace_entry`: `namespace_cache_key`, record the key,
read the entry and check its seal with `open`), the misses are the namespaces
without a valid entry, and the namespaces loaded are `closure(misses)`; the
loop skips the rest, counting them `Checked`. The table in the summary is
measured, three runs each, same machine and load as the base runs (they were
interleaved). The edits loaded 4-6 namespaces; (d) re-checks 59 and loads
exactly those (the 148 others were skipped).

What the prototype leaves out, so its figures are a lower bound: reporting
the skipped namespaces' stored warnings (aoc has none), `check_exports`
(aoc has none), the doc-link pass, and `--index`/`--counterexamples`. I did
not check the prototype's output beyond "checked 207 namespaces of aoc" and
the right miss counts; it is not a correct implementation, only a measurement.

## 4. Who else shares this path

All of `check`, `test`, `run`, `build`, `axioms`, `audit`, `search` and `doc`
go through `load_analysis` (`load_project` for the CLI), and so do the web
playground and `rt`. Of them:

- **`check` without `--index`/`--counterexamples`**: gains (above). `check
  NS` loads NS's closure today; with the change it loads only what the misses
  in that closure need, so `check NS` of an unchanged NS loads nothing.
- **`check --index`, `--counterexamples`, `test`, `run`, `build`, `doc`,
  `axioms`, `search`**: need the declarations (tests are hashed from the
  defs, `run` evaluates them, the index merges nav rows). No gain without a
  further change. `test` is the next candidate (SW-1170's 3.8 s is the same
  replay): a skipped namespace's tests could be reported from the test-result
  cache keyed by the namespace key. Not investigated.
- **`audit`** (`task audit`, `audit:touched`): audits theorem by theorem from
  the loaded terms, so it needs them; `audit NS` already loads only NS's
  closure. No gain.
- **LSP warm-up**: `LiveProject::step` calls `check_project_namespace` for
  every namespace; the editor then answers hover, goto and completion from the
  loaded state, so it needs everything. No gain unless loading were lazy.
- **Tests that start the CLI** (`crates/cli/tests/*.rs` run `check` on small
  projects, mostly with a cold cache): no gain; they should keep passing.
  The driver tests in `crates/driver/tests/check_cache.rs` assert on
  `namespace_hits`; they call `load_project_sources`, which keeps the full
  load unless a caller opts in.

## 5. The plan

**What changes.**

1. `Target`/`load_analysis` gets a second parameter, what the caller will do
   with the result: `Load::Everything` (today's behaviour, for every caller
   but one) or `Load::Diagnostics` (plain `check`). `check` passes
   `Diagnostics` when neither `--index` nor `--counterexamples` is given.
2. A planning pass in `load_analysis` (replacing the prototype's): compute
   keys, find the hits, take the needed set, per above. `peek_namespace_entry`
   becomes `Elaborator::plan_namespace(ns, closure) -> Planned::Hit(summary) |
   Miss`; it runs every *early* check `replay_namespace` runs without a loaded
   state: the seal and key (`open`), the included files' hashes (head), and
   that the library files named in `pre.needs` still exist.
3. Entry format (bump `FORMAT`, 22 -> 23): the head gains a summary: the
   warnings (moved from the tail of the body; `read_tables` reads them from
   there), a has-exports flag, and the names of the namespaces the doc links
   resolved into (below). A skipped namespace costs one file read and a head
   parse.
4. Skipped namespaces still get their key recorded (`namespace_keys`) and
   `outcomes`; their summary's warnings are added to the diagnostics in
   canonical order, so the output order is unchanged. The doc-link warnings
   are worked out for them by the syntax-only resolver that `stitchwort doc`
   uses (or, as a first cut, a namespace with a doc link is simply not
   skipped). A namespace with exports is not skipped (or the export check is
   given its definitions' signatures only).
5. A stats counter `namespace_skipped` so tests can see what happened.

Size: about 300 lines of code plus the format change in the entry encoder and
decoder, about 150 lines of tests. One day for Sonnet, with Opus review
(the cache's replay path produces kernel terms, so CLAUDE.md asks for it).
It touches `crates/elab/src/cache/mod.rs`, which other cache work (SW-1187,
8b) also edits: run after it merges, as D2300 says.

**Risks: where a skipped namespace could be reported differently.**

- *Late misses.* A replay can fail after it begins (library files don't load,
  a dependency's hash differs from what the entry recorded) and then the
  namespace is elaborated after all. Skipping never learns this. The key
  covers the compiler build, the library digest, the namespace's sources and
  its closure's keys, so all of those are the same whenever the key is, which
  is why a late miss is a corruption or non-determinism case rather than a
  normal one; but it is a case today's code survives and the new path would
  not. Mitigation: a test mode (`STITCHWORT_CHECK_VERIFY`) that loads
  everything and compares, and a differential test (below). A corrupt entry
  that passes the seal is the unmitigated residual.
- *Doc links* (SW-1045): a warning about a link into another namespace can
  change with no change to the namespace's own key. Never skip a namespace
  with doc links until the syntax-only resolver is used on it.
- *Exports*: handled by the flag, as above.
- *Goals/unfinished:* never cached, so always misses and always loaded; a hit
  that uses an unfinished declaration cannot exist (the key chain makes it a
  miss with the unfinished one).
- *`include`d files* that changed on disk: checked in the plan from the head
  hashes, as the replay does.
- *Blocked namespaces*: a hit never blocks; a miss that fails blocks its
  dependents, which are all misses themselves (their keys include it).
- *Concurrent writers/eviction:* an entry can disappear between the plan and a
  later load of a needed hit; then it is a miss at load time, as today.
  A skipped one has already been counted as a pass from a valid read.

**Tests that would show it is right.**

1. Differential, in `crates/driver/tests/check_cache.rs`'s style: for a
   project fixture and a series of edits (a leaf, a middle namespace, a
   warning-producing one, one introducing an error, one introducing a goal,
   deleting a file), assert that `Diagnostics`-mode output (diagnostics in
   order, `checked`) equals `Everything`-mode output, warm cache both times.
2. Counts: after an edit to a leaf, `namespace_skipped` equals the number
   of hits outside the miss closure, and `namespace_hits` + `namespace_skipped`
   is what it was.
3. Entry with a warning: the warning appears for a skipped namespace.
4. The late-miss test (`fail_namespace_replays_late`) and a corrupted entry:
   the namespace is a miss at plan time.
5. Doc-link and exports fixtures behave as today.
6. CLI: `check --index` and `--counterexamples` still load everything (their
   existing tests in `crates/cli/tests/navigation.rs`, `audit.rs`).
7. The aoc number, here: the same script, CPU after 3 edits under 0.8 s.

## Unsure

- The prototype's wall times: busy machine; only the CPU column should be
  quoted. All four edits ran base and prototype interleaved, so they saw the
  same load.
- (b)'s re-check is cheaper than SW-1170's because the edit was a comment.
- Whether reading all 207 entry files (done by the prototype, included in the
  0.55 s) can be made cheaper by reading heads only: not tried.
- The estimate for the real implementation's overhead (0.05-0.15 s) and the
  size (300 lines) are guesses from reading the code, not measurements.
- Not looked at: `test` reuse of the idea; `check --project` in tests beyond
  reading the call sites.

## Commands

```
nix develop -c cargo build --release -p stitchwort-cli   # base binary, then the prototype
python3 dev/check-skip-unneeded/measure.py BASE PROTO aoc 3
```
Machine: 10-core Mac, load 30-80 (`uptime`: 61-70 at the end).

## As built (D2301, 4 Nov 2026)

Measured the same way (`measure.py`, 3 rounds per edit, medians of CPU =
user+sys), base = `main` at 06bd6c0d, new = `lane/SW-1193`, both release.
The machine was quieter than for the investigation: load 16 falling to 9
(`uptime` at the end: 7.39, 23.26, 40.64). Raw output:
`dev/check-skip-unneeded/results-as-built-2026-11-04.log`.

| edit | loaded (new) | base CPU | new CPU | saved |
|---|---:|---:|---:|---:|
| a `Tests` namespace | 4 | 3.15 s | **0.57 s** | 2.6 s (5.5x) |
| a `Proofs` namespace | 5 | 2.90 s | **0.56 s** | 2.3 s (5.2x) |
| a day's code namespace | 6 | 3.14 s | **0.62 s** | 2.5 s (5.1x) |
| `Aoc.Common` | 59 | 18.83 s | **16.60 s** | 2.2 s (12%) |

The real implementation costs no more than the prototype did (0.56-0.69 s
then): reading the warnings from the entry head and the rewind mark are
lost in the noise.

What differs from the plan in section 5:

- **Errors and goals fall back.** An error's notes can name a namespace
  that isn't imported but was loaded before (`E-UNKNOWN-FIELD`: "`P.Spec`
  adds `Grid.probe`; import it", examples/projects/reject/extension-not-imported).
  So when a namespace checked after one left out reports an error or a goal,
  the session is rewound to before the loop and everything is loaded, as
  today. The differential test found this. Cost, measured on aoc with an
  error in `Day05/Tests/Examples.sw`: 2.89 s against 2.69 s with
  `STITCHWORT_SKIP_UNNEEDED=0` (median of 3, the same binary): 0.2 s, 8%
  slower than today, for a run with an error or open goal.
- **Uses of a miss load too.** A hit that uses a miss, or a namespace with
  syntax errors, is loaded, so a failure blocks it exactly as today. In a
  normal edit those are misses anyway (the keys chain), so this costs
  nothing; it matters only for a corrupt entry or a namespace that is never
  cached.
- **Exports need no flag:** a namespace with an exported definition is
  never cached, so it is always loaded.
- **Doc links:** a namespace with any `[`...`]` link is loaded (and what it
  uses); the syntax-only resolver is not used. aoc has none.
- **Syntax errors:** a namespace with them can have an entry (the part that
  parsed is clean), so it is always loaded, to report them.
- The format bump (23) moves only the warnings into the head.

Output: on aoc, a warm `check` and one with an error print byte for byte the
same with and without skipping (checked by hand). Tests: see the commit.
