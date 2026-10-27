# Example programs

These `.sw` files are the main test suite. `cargo test` runs every one of them
(see `crates/cli/tests/examples.rs`).

| Directory | Expectation |
|---|---|
| `accept/` | Must type-check without errors. One that declares a warning on a leading `-- expect-warning: W-CODE` line must report it, and its warnings are snapshot-tested. |
| `reject/` | Must fail with the error code the file declares. The error messages are snapshot-tested, so changes to them show up in review. |
| `extract/` | Must type-check, and their exports are extracted to JS. Each `-- run: f args` line is evaluated by both the reference evaluator and the generated JS under Node, and the results must agree (`crates/cli/tests/extract.rs`). |
| `goals/` | Must report open goals (`?`), and no errors unless the file declares one with `-- expect-error:` (a hole beside an error). The rendered goals are snapshot-tested. Their tests (of what's finished) must pass. |
| `soundness/` | The "must reject" suite from DESIGN.md §13: programs that exploit a known paradox (e.g. a non-positive data type), each paired with a nearby program that must be accepted (which goes in `accept/`). Must fail like `reject/`. |

| `projects/accept/NAME/`, `projects/reject/NAME/`, `projects/goals/NAME/` | Whole projects: a folder with a `stitchwort.yaml` and its source files, as for `accept/`, `reject/` and `goals/`. A rejected project declares its error on a leading `# expect-error: E-CODE` comment line of its `stitchwort.yaml`. |

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

After changing an error message, review and accept the new snapshots with:

```sh
cargo insta review
```
