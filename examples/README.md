# Example programs

These `.sw` files are the main test suite: they are checked, run and
snapshot-tested end to end. A test's name is `module::test` (the module is the
file's `mod` name), in the test binary named after its folder (`running`,
`extraction`, `library`), so the nextest filter for one of them is
`-E 'binary(NAME) & test(/MODULE::/)'`.

## Which tests run which folder

| Folder | Test binary (package) | Tests that run it | What they check |
|---|---|---|---|
| `accept/` | `running` (`stitchwort-cli`) | `examples::accepted_examples_check`; `run_js::examples_print_the_same_both_ways` and `run_reference::examples_print_the_same_both_ways` for the files with a `def main` | Must check without errors, their tests must pass, and a declared warning is reported and snapshot-tested. Between them, the `run_*` tests cover each `main` on the fast runtime (`stitchwort run`), JavaScript (`run --js`) and the reference evaluator (`run --reference`), with three inputs, and require the same output and exit status as the fast runtime. |
| `reject/` | `running` (`stitchwort-cli`) | `examples::rejected_examples_fail_for_the_expected_reason` | Must fail with the code on the file's `-- expect-error:` line; the rendered error is snapshot-tested. |
| `soundness/` | `running` (`stitchwort-cli`) | `examples::soundness_examples_fail_for_the_expected_reason` | Must fail like `reject/`, unless the first line is `-- known-gap` (then it must be accepted for now). |
| `goals/` | `running` (`stitchwort-cli`) | `examples::goal_examples_report_their_goals` | Must report open goals (`?`), no errors unless declared with `-- expect-error:`, and its tests must pass unless one is named on `-- expect-test-failure:`. The rendered goals are snapshot-tested. |
| `extract/` | `extraction` (`stitchwort-cli`) | `extract::run_lines_agree_with_the_reference_evaluator`, `extract::random_inputs_agree_with_the_reference_evaluator`, `extract::generated_code_is_stable`, `extract::the_declarations_type_check` (broad tier); also `examples::accepted_examples_check` in `running` | Must check and pass its tests. Every `-- run:` line is compared with the generated JS in Node, 100 random inputs per export are compared with the reference evaluator, and the generated `.js` and `.d.ts` are snapshot-tested (`generated_code_is_stable`); the `.d.ts` must type-check with `tsc`. Many smaller tests in `extract.rs` also use one extraction file by name. |
| `projects/accept/` | `running` (`stitchwort-cli`) | `examples::accepted_projects_check`, `examples::the_trip_journal_checks` | Whole projects must check, have no open goals, and pass their tests. |
| `projects/reject/` | `running` (`stitchwort-cli`) | `examples::rejected_projects_fail_for_the_expected_reason` | A project declares its expected error on a leading `# expect-error: E-CODE` line of its `stitchwort.yaml`, and its rendered message is snapshot-tested. |
| `projects/goals/` | `running` (`stitchwort-cli`) | `examples::goal_projects_report_their_goals` | Whole projects must report their goals and no unexpected errors. |
| `accept/`, `extract/` | `library` (`stitchwort-driver`) | `hash_stability::examples` | Every declaration's content hash is snapshot-tested. |
| `projects/accept/` | `library` (`stitchwort-driver`) | `hash_stability::projects` | The same, for each accepted project's declarations. |

`run_js::examples_print_the_same_both_ways` skips the examples marked
`(run: fails)` and `(run: random)`, which end in an unhandled `Fail` on
purpose. `run_reference::examples_print_the_same_both_ways` runs a daily
sample (every eighth example with a `main`) below the all tier; `EXAMPLES`
overrides the sample.

`task test:example NAME=<part>` runs the seven `examples::` sweeps for
`accept`, `reject`, `soundness` and `goals` (files and projects), and nothing
else: it does not run `extraction`, `run_js`, `run_reference` or
`hash_stability`. `task test:lane AREA=examples NAME=<part>` runs the lane's
share of the `examples::` sweeps.

## `EXAMPLES=name1,name2`

`EXAMPLES` keeps the examples whose **file name** (or, for a project, folder
name) contains any comma-separated part; it is not a path, so use `synonym`,
not `accept/synonym.sw` or `accept`. A part that matches nothing anywhere
fails the test, naming the nearest examples, rather than running nothing.

- It applies to the `examples::` sweeps, `run_js`, `run_reference` and
  `hash_stability`'s `examples` and `projects`.
- When it selects some, it overrides the tier's sample: every matching
  example runs, not every fourth of them.
- `task test:example NAME=…`, `task test:lane AREA=examples NAME=…` and
  `task test:lane AREA=hashes NAME=…` set it; `EXAMPLES` is the same variable
  when calling cargo directly.

The extraction tests (`extract::*` in the `extraction` binary) **do not** read
`EXAMPLES`: they always check every `examples/extract/*.sw`. `EXAMPLES` only
narrows the extraction files that `examples::accepted_examples_check` checks
for warnings and tests. There is no per-example filter for extraction
snapshots.

`goal_index::goal_examples_in_the_index` (in the `server` binary) **does not**
read `EXAMPLES` either: it always checks every `examples/goals/*.sw`. It
snapshots each example's goal diagnostics and asserts that every goal's label
matches its goal data (hypotheses and target) from the language server, so a
new goals example needs its
`server__goal_index__goal_index__<name>.snap` accepted (`cargo insta accept`)
before the test passes.

## Snapshots

`task test:example NAME=…` checks one example's or project's snapshots, and
`task snap:examples NAME=…` rewrites the changed error and goal snapshots
(`INSTA_UPDATE=always`, then `git status --short -- '*.snap'`). For the
extraction snapshots there is no per-example filter, so rerun their test and
insta rewrites only the files that changed:

```sh
task snap:one -- -E 'binary(extraction) & test(=extract::generated_code_is_stable)'
```

`task snap:one -- -E '…'` works for any one test. It writes the `.snap` file in
place, so there is no `.snap.new` to rename and no header line to delete;
`cargo insta review` is also in the dev shell.

Files in `reject/` and `soundness/` start by declaring the error they expect:

```
-- expect-error: E-POSITIVITY
type Bad : Type =
  | MkBad (f : Bad -> Nat)
```

Being rejected for a different reason (a syntax error in the example, an
unknown name, a crash) fails the test. A rejection only counts if it's for the
right reason.

A `soundness/` file whose first line starts with `-- known-gap` documents a
soundness hole we haven't fixed yet (see DESIGN.md §11). It's expected to be
accepted for now, and the test fails once the compiler starts rejecting it, as a
reminder to remove the marker.

An `accept/` file written to cover a fallback path declares the outcome it
must reach, on leading comment lines:

```
-- metrics: guard-as-written: unchecked
```

While the example elaborates, the test collects the lines that
`STITCHWORT_MATCH_METRICS` and `STITCHWORT_REWRITE_METRICS` print
(`crates/elab/src/metrics.rs`), without their ` at=` position, and fails
unless each declared line occurs at least once (`match-as-written: folded`,
`rewrite-retried: without-partial-unfold`, and so on). A later change that
stops the example reaching its path fails it, instead of leaving it passing
through the main path.
