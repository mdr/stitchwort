# Test selector: brief for the model that picks the post-merge tests

(SW-1098, D2221.) You are given a merge on `main`. Pick the tests worth
running now, within a time budget, to catch regressions the lane's own tests
could not. You choose; you do not run anything but `cargo nextest list` and
the estimator below, and you change no file.

## Inputs

1. The merge: `git show --stat -m --first-parent <merge>` and the full diff
   (`git diff <merge>^1 <merge>`). Include any follow-up commit the
   orchestrator names (snapshot updates often come in a separate commit).
2. The lane's report: the tests it ran. Don't re-run those unless they are
   cheap (under ~1 s each) or the merge combined them with other changes.
3. The inventory, `target/test-inventory.json` (build it:
   `nix develop -c task test:inventory`; refresh the times from the latest
   run with `-- --junit target/nextest/quick/junit.xml`). Each test has
   `id` (`<binary-id> <name>`), `package`, `binary`, `profiles` (quick,
   broad, all, lane-AREA), `group` (`corpus-sweeps`: runs alone), `time`
   (seconds, from the last run that had it) and `time_known`.

## Budget and estimate

Budget: **120 s** of estimated wall time, the fixed core included. The
estimator does the arithmetic:

    nix develop -c dev/test-inventory --estimate '<filterset>'

It lists what the filterset selects (so it also proves the filter parses and
matches), the tests per binary, the slowest, and
`ESTIMATE = max(sum of times / 8.4, sum of the corpus-sweeps tests, longest test)`:
the machine has 10 cores, about 8.4 of them useful, and sweeps never overlap.
A test with no known time counts as 3 s (flagged); prefer tests with times,
and say how many unknowns you included. Aim for an estimate of 90 to 110 s,
not under 60 (unused budget is wasted) and never over 120. If the estimate
is over, drop whole groups from the bottom of your priority list.
`dev/test-inventory --profile-filter lane-std` prints a lane profile's
filterset, to paste in as `( ... )`.

Sweeps (tests in `corpus-sweeps`, and the examples, hash and AoC corpora) run
on the quick sample (STITCHWORT_TIER=quick) unless the environment variable
`EXAMPLES=<substrings>` is set: then every example or project whose name
contains any of its comma-separated substrings runs, in `cli` `examples` and
`run_js`, and in `hash_stability` `examples`/`projects` (nothing else is
affected). A single name works as before. Use it to cover the examples a
change is about (`EXAMPLES=parse`, or `EXAMPLES=parse,safe-fields` for two),
instead of the 1-in-4 sample.

## The fixed core: always in the filter

Roughly 6 s of wall time. It sits in the filter; `task test:selected` itself
runs `task test:features` and `cargo fmt --check` first.

| Part | Filterset | Time (sum) |
|---|---|---|
| kernel and core | `package(stitchwort-core)` | 37 s |
| parser | `package(stitchwort-syntax)` | 13 s |
| one fast AoC day, end to end | `binary(running) & test(=aoc_answers::year2024_day04)` | 1 s |

Why: the kernel is where an unsound result would come from, and the parser
is under everything else; both are fast. One AoC day exercises the whole
pipeline (parse, elaborate, check, run) on a real program.

## What to add

Read the diff, then spend the rest of the budget in this order. Each group is
a clause in the filterset; give it one line of reasoning.

1. **What changed, and the tests of that area**: the package or binary the
   changed files belong to (`crates/X/` is `package(stitchwort-X)`; tests
   in `crates/X/tests/*.rs` are `binary(name)`), and a lane profile for
   it if `.config/nextest.toml` has one (the `lane-AREA` filters are small
   and fast). Use `grep -rn` in `crates/*/tests` for tests that name the
   changed thing.
2. **What depends on it**, the cross-area risks the lane's targeted tests
   miss:

   | Changed | Add |
   |---|---|
   | `crates/elab/src/std/**.sw` (the library) | `lane-std`; `hash_stability` `prelude` and `examples` and `pinned_hashes` (hash snapshots, 21 to 47 s); `the_standard_library_passes_its_own_tests`; `cli::fmt` `the_repository_sources_are_formatted` (18 s); the examples using the changed file (`EXAMPLES=`); a proof namespace's AoC days if proofs use it |
   | `crates/elab/**` (elaborator, equations, induct) | `package(stitchwort-elab)`; `function_equations`, `function_induct`; `cli::examples` accepted and rejected; `hash_stability` |
   | `crates/elab/src/std_dir.rs`, how library files are named, found or loaded (file naming, spans) | every test that prints paths: `cli` `doc`, `search`, `run`, the `check --index` tests (`goal_index`), and diagnostics snapshots |
   | `crates/elab/src/std/core/**` (the core files), `order.txt` | the snapshots that print `<prelude>` positions, such as driver `navigation` `references_of_a_project` |
   | `crates/core/**` | the fixed core is the start; add `nested_oracle`, `division`, `hash_stability`, `binary(differential)` if evaluation changed |
   | `crates/syntax/**`, `crates/fmt/**` | `package(stitchwort-fmt)` (without `repo`/`fuzz`), `cli::fmt`, `hash_stability`, `binary(lsp)` tests of lane-lsp |
   | `crates/rt/**`, `native`, `js`, `host` | `lane-rt`, `lane-native`, `lane-js`, `lane-effects`, `stitchwort-cli` `run` |
   | `crates/cli/**`, `standalone` | `lane-cli`, `lane-search` for `search`/`doc` |
   | `crates/lsp/**` (the language server) | `lane-lsp` (its tests are `cli`'s `binary(lsp)`); `cargo check --target wasm32-unknown-unknown -p stitchwort-web`, as the playground's editor builds it |
   | `aoc/**` or `games/**` (proofs, programs) | AoC days for the years touched (`aoc_answers`, a few days each ~1 to 5 s), `cli::examples` project tests, `lane-hashes` |
   | `examples/**` | those examples via `EXAMPLES=`, `hash_stability` |
   | snapshots only (`*.snap`) | the test that owns the snapshot, run on the merge result |
   | docs only | the fixed core and nothing else |

3. **Spread**: if the budget is not used, add AoC days from the years the
   change touches (cheapest first), then another lane area next to the
   changed one.

Rules: don't pad with tests unrelated to the change just to use the budget
(stop at the table's list and the spread); do not select `broad`- or
`all`-only tests of the whole-corpus kind (a test whose `time` is over
30 s and not in `quick`) without a clear reason; never select a test the
lane profiles exclude on purpose (the exclusion lists in
`.config/nextest.toml` are for tests that are slow or flaky in the quick
tier).

- **Memory-heavy tests.** Leave `binary(running) & test(/^run_js::/)` (`cli`) out of a selection
  unless `crates/js`, `crates/cli/tests/running/run_js.rs` or the JS runtime changed:
  its node processes take about 1 GB each, and including it pushed a
  selection over the quick tier's 4 GB cap. The same goes for the `cli`
  `extract` tests that run `node test.mjs` (all but
  `generated_code_is_stable`): one node took 2.1 GB. Include them only for
  changes to `crates/js` or `extract.rs`, and then with little else.
- **Filters.** `task test:one -- NAME` matches test names only. For a whole
  test binary use a filterset, `task test:one -- -E 'binary(library) & test(/^hash_stability::/)'`
  (with `EXAMPLES=` for particular examples).

## Output

Exactly this, nothing else:

    FILTER: <one filterset line, usable as nextest -E>
    EXAMPLES: <comma-separated substrings, or none>
    ESTIMATE: <seconds from dev/test-inventory --estimate> (<N> tests, <U> of unknown time)
    - fixed core: ... (one line)
    - <group>: why it is in (one line each)
    - not run: what you left out and why (one line)

The orchestrator's verifier then runs
`SELECTOR_ESTIMATE=<seconds> EXAMPLES=<substrings> nix develop -c task test:selected -- '<FILTER>'`
(`EXAMPLES` only if not none). Check first that the estimator prints the
count you expect, and that the filter is not empty.

## Example: the SW-738 merge (2ab36ac9 and snapshots 91082abe)

Diff: `crates/elab/src/std/Parse/Parse.sw`, `Reads.sw` (library),
`docs/proposals/parser-combinators.md`, then seven hash snapshots (prelude
and six parse/effect examples). The lane ran `lane-std` and its own snapshots.

    FILTER: package(stitchwort-core) | package(stitchwort-syntax) | (binary(aoc_answers) & test(=year2024_day04)) | (binary(std_library) & !test(/^(lazy_loading_changes_nothing_for_.*|the_core_alone_runs_every_example_that_uses_no_library_name|every_builtin_is_bound_once_every_file_has_loaded|no_library_file_declares_a_decision_procedure|small_programs_load_only_the_library_files_they_can_use|the_index_holds_exactly_the_names_an_eager_load_makes|library_tests_run_only_under_the_library_target|the_order_never_depends_on_how_the_program_mentions_things)$/)) | (binary(hash_stability) & test(/^(prelude|examples)$/)) | binary(pinned_hashes) | binary(no_effect) | binary(lambda_shadow) | (package(stitchwort-cli) & binary(examples) & test(/^(accepted|rejected)_examples_/)) | (package(stitchwort-cli) & binary(fmt) & test(=the_repository_sources_are_formatted))
    EXAMPLES: parse
    ESTIMATE: 75.2 (614 tests, 23 of unknown time)
    - fixed core: core, syntax, AoC 2024 day 4.
    - std: the lane-std tests plus the_standard_library_passes_its_own_tests (library edit; unknown time), and the repository formatting check (.sw files changed).
    - hashes: prelude snapshot (13 new names), examples snapshot and pinned_hashes, since the merge changed the library hashes.
    - EXAMPLES=parse: all parse-* examples in the accepted sweep and the hash sweep, instead of the 1-in-4 sample; the estimate counts the sample, so it is an overestimate.
    - parse users: no_effect and lambda_shadow name Parse in their programs.
    - not run: elab package tests (no elaborator change), rt/native/js (no runtime change), AoC beyond one day (no AoC file changed; the projects' hash snapshots did not change).

## Scoring

`task test:selected` appends to `dev/selector-log.tsv` (in the main checkout only). During the trial the
verifier also runs the fixed quick tier; a failure the quick tier caught that
the selection did not is a miss and counts against the selector. See
docs/workflow.md, "Checks after a merge".
