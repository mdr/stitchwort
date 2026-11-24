# SW-4735: notes for review (parallel stage 2, step 2)

Opus lane, 24 Nov 2026. Builds step 2 of docs/proposals/parallel-checking.md
§10.6 (D3732): the cache entry in two parts, a load without part B that
admits stated theorems, and `check --jobs`'s workers loading that way.
Conditions C1, C2, N1 and N3 of docs/reviews/SW-4734-fable-review.md are
addressed below.

## What was built

- **The entry in two parts** (`FORMAT` 46; docs/proposals/check-cache.md,
  "An entry's layout", item 4). `stated_on_load` (cache/mod.rs) picks the
  unit's own theorems whose proofs go to part B: `has_interface`, and no
  instance, `fold`, `opaque`, `tailrec` or parameter-default mark, no
  `unfolding` list, no run body, no validator, and every member of its
  group such a theorem too. Each definition record now has a flag; a
  flagged one has no body and no group in part A. Part B, a blob at the end
  of the body, is the node count and nodes written after everything else
  (so they are exactly the nodes only those proofs reach), then each
  flagged definition's body and group in order. `TermWriter::start_part`
  restarts `Loc` spans' steps at the part boundary, as `read_nodes` does.
  The digest pass is unchanged (no flag, no part B).
- **The decode** takes `proofs`. With it, part B's nodes are appended to
  part A's table and each flagged record gets its body and group: what is
  admitted is what one table gave before. Without it, part B is stepped
  over (the checksum over the whole entry was already verified by `open`),
  and the reference check runs over the nodes read.
- **Admission of a stated theorem**: `Elaborator::admit_stated`, called
  from `submit` at the theorem's place in declaration order. It refuses an
  entry that isn't exact or is being rechecked, a flagged record that
  isn't a theorem or carries any mark or list above, or one without a
  recorded hash; then `kernel::admit_trusted_stated` (a timed wrapper in
  elab/kernel.rs), the id and path check, and **the recorded full hash is
  put in the hash cache in the same step** (C2). A stated theorem is in no
  group, so the group loop skips it; a group listing one fails "members
  disagree". Library files' entries go the same way, binding a built-in to
  a stated theorem as the group path does.
- **Who loads without proofs.** `Elaborator::set_load_without_proofs`
  (default off) and `loads_proofs(hit)`: only `hit.exact && !hit.recheck`.
  So carried-over entries, `--recheck`, and the recheck's digest
  recomputation (which encodes the namespace's own bodies) always load
  whole. The only session that turns it on is a fill worker
  (`parallel.rs`, `Worker::new`). The check after the fill is a separate
  session with the default.
- **A measuring switch**: `STITCHWORT_LOAD_PROOFS=0` on a plain `check`
  (`Load::Diagnostics` only; main.rs), which `measure_load.sh` already
  uses. It is not step 3: there is no restart with proofs after an error,
  so over a namespace with an error a note's text may differ. Step 3
  replaces it.
- **Stats**: `Stats::stated` counts theorems admitted stated (added into a
  fill's stats). The cache's debug "written" line ends with part B's bytes
  and its theorem count; `measure_cache_split.sh` totals it.

## C1: the invariant instead of patching readers

`Session::check_prepared` with `Load::Everything` turns loading without
proofs off before it checks, and afterwards calls
`project::assert_holds_no_stated_theorem`, a panic with "internal error"
(`Elaborator::holds_stated_theorems` scans the kernel's definitions; about
a hundred thousand flag reads on the largest project). Every command that
uses what it loads (`test`, `run`, `build`, `axioms`, `audit`, `doc`,
`--index`, `--counterexamples`, the editor) goes through that with
`Load::Everything`, so declhash, the trial, timings, assume.rs:157,
equation_notes and opaque.rs `local_owner` never meet a stated theorem
there. Not covered by the assertion: `Load::Diagnostics` sessions, which
are the plain `check` (its readers are the summary's reliance line,
covered by W) and the trial command (trial_cmd.rs:568). Neither turns the
option on in this lane; step 3 must keep the trial loading whole.

Test: `a_load_without_proofs_holds_all_but_the_proofs_and_never_reaches_a_command_that_reads_them`
(crates/driver/tests/projects/parallel.rs): the assertion fires on a
session loaded without proofs, and a session asked to load without proofs
but loading with `Load::Everything` holds none and counts none.

## C2: the dump

`canonical_dump_without_proofs` prints `-` for every theorem's (not only
stated ones') group, `stated` flag, `unfolding` list, body, transparency
set, `lift_leaf` and `recursive`, so the text doesn't say how a theorem
was loaded. `canonical_dump` is unchanged byte for byte (the format
specifiers moved from `{:?}` to `{}` over the same `{:?}` text). The test
above compares the two dumps of a whole and a proof-less load of the same
warm cache: equal; the full dumps differ (so the test isn't empty).

## N1, the spec, N3

- N1: erase.rs rule 3 now says a proof definition isn't run at any number
  of arguments.
- docs/core.md "Stated theorems": the caller sentence names
  `admit_stated` and its exactness condition; the arity sentence says
  "depends on" and how `unfolds_head` and the folded-call tests compare
  arity before `body_seen`; the "never stated" paragraph lists the marks.
- **N3: the replay is the only new caller of `admit_trusted_stated`.**
  `grep -rn admit_trusted_stated crates` lists the definition in
  core/check.rs, the timed wrapper in elab/kernel.rs, its one caller
  `Elaborator::admit_stated` in elab/cache/mod.rs, and the tests that
  were there before (core/tests/it/stated.rs, driver/axioms.rs).

## Deviations from the design

- **Bodies only; proof-private helpers stay in part A** (the orchestrator's
  call 10.6 allowed this unless helpers are over a fifth of part B; not
  measured on a real project in this lane). So no position map. The cost:
  a theorem whose group holds its `match` helper (a recursive theorem
  proved by `match`) loads whole, and every helper's body (often the bulk
  of a `match` proof) is still loaded. On the test fixture `Par.Facts`,
  part B is 19% of the entry against 30% "proofs" from the SW-4729
  estimate. Leaving helpers out (with their table rows, which today sit in
  part A's tables in entry order) is the follow-up if the measurement says
  so.
- Instance theorems, and theorems with `unfolding` lists, load whole
  rather than carrying those marks into `admit_trusted_stated` (a kernel
  API change this lane avoided). The fixture has no instance theorem: I
  found no surface form of one quickly; the writer's rule covers it by
  reading `Def::instance`.
- No fixture for "a theorem in a group with a computing definition": I
  could not write one in source quickly (a definition and a theorem that
  refer to each other); the group rule in `stated_on_load` covers it, and
  `bumpId` (recursive through its `match` helper) is a group with a
  non-theorem member that loads whole.
- *Correction (24 Nov 2026, SW-4741):* `bumpId` has no helper. A `match`
  that is a definition's whole body, on a parameter, becomes its own case
  tree, so `bumpId` is a group of one and loads stated (sound: nothing
  outside the cache reads its body or `recursive` flag). Only a lifted
  `match` (one under a call, as in the fixture's `bumpBack`) joins the
  theorem's group and makes it load whole; the test now pins both.

## Tests

See the lane report. New: the two tests above, plus
`workers_loading_without_proofs_write_what_one_job_does` (four namespaces
of theorems, `Par.Facts` given an entry first so a worker must replay it;
two jobs, six schedules: report, session dump and every entry byte equal
to one job's, `stated > 0` in the fill and 0 in the check after it).

## Measured (24 Nov, lane, Speedwell at load about 5)

`tools/fmt`, the closure of `Fmt.PassProofs` (7 namespaces), cold check
then three warm `STITCHWORT_SKIP_UNNEEDED=0 check Fmt.PassProofs` each way
(the switch also applies to the library files' entries):

| | wall | peak memory |
|---|---|---|
| cold check | 12.5 s | 584 MB |
| warm, whole | 1.04-1.06 s | 518 MB |
| warm, without proofs | 0.93-0.94 s | 436 MB |

So 11% less time and 16% less memory on this closure. Part B is 33.5% of
the 10.9 MB of these entries, against 44.3% for the SW-4729 estimate of
"proofs" (which includes the 49 proof-private helpers kept in part A
here). Well short of §10.4's guess (a load falling to between a third
and two thirds): the replay's fixed costs (names, tables, library) stay,
and helpers stay. For the whole project (the orchestrator's run):

    docs/proposals/parallel-checking/measure_load.sh target/release/stitchwort tools/fmt OUT
    docs/proposals/parallel-checking/measure_cache_split.sh target/release/stitchwort REPO OUT   # now prints part B's total
    docs/proposals/parallel-checking/measure_jobs.sh ...   # --jobs 4 and 8 against 1, byte-compare
