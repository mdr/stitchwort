# SW-4735: Fable review of the two-part entry and workers loading without proofs

Parallel checking stage 2, step 2 (docs/proposals/parallel-checking.md §10.6,
D3732). Reviewed: `lane/SW-4735` at `8ed5eb8f9`, the diff against its merge
base with `main` (commit `2f0544c0e` is the code), with
docs/reviews/SW-4735-notes.md and the conditions of
docs/reviews/SW-4734-fable-review.md (C1, C2, N3). A paper review, with one
small probe project run on the worktree's release binary. 24 November 2026.

## Verdict

**Sound; merge.** A stated theorem is made only from an entry this build
wrote exactly and is using without `--recheck`; an entry is never written for
a namespace with an error, a goal or a declaration that relies on one; only
fill workers (and the measuring switch) load that way, and every session that
uses what it loads is asserted to hold none. Nothing that later code can see
of a theorem is in part B. No finding blocks the merge. One finding is a
decision about the measuring switch (F1); the rest are small.

## The six questions

### 1. Which entries load without proofs

- `loads_proofs(hit)` is `!(without_proofs && hit.exact && !hit.recheck)`,
  and both decodes (a namespace's and a library file's) pass it. `admit_stated`
  tests `hit.exact && !hit.recheck` again itself, so a decode called wrongly
  is refused, not trusted.
- `hit.exact` comes only from `usable`: the stamp says exact, the compiler
  build is this one, and the library interface is this session's. A stamp is
  exact only when the writing session had carried nothing over
  (`!carried_anything()`). A carried-over entry that this kernel checks again
  is kept as carried over (`keep_rechecked`), so it never becomes exact.
- `--recheck` sets `hit.recheck` on every entry, and the digest recomputation
  runs only then, so it always has the bodies. The digest pass that a writer
  runs covers the unit's own definitions, which that session elaborated and
  holds whole; dependencies enter by `interface_hash`, the same for a stated
  and a proved theorem.
- A failed proof can't be stated, twice over: its stand-in is an assumption,
  so `proof_hidden` (and `has_interface`) is false and `stated_on_load` leaves
  it out; and the namespace's entry isn't written at all (`ok` in
  `elaborate_namespace_cached`: no error, no goal, `unfinished_count` unchanged).
- The recorded full hash put in the hash cache is trusted without being
  recomputed. That is no new trust: an exact entry's hashes were already
  taken as recorded (`hashes_as_recorded` runs only for carried or rechecked
  entries). A replay refused after `admit_stated` goes through
  `forget_since`, which drops the hash with the definition.
- A session holding stated theorems writes exact entries. That is the
  design's induction (§10.3, step 2), not a leak: every stated theorem it
  held came from an exact entry.

Probe: a namespace with an open goal over a warm dependency, with one job,
with `--jobs 2` and with the switch: no entry written for it or its
dependant, the same output and exit code three ways.

### 2. Who loads without proofs

- `set_load_without_proofs(true)` has two callers outside tests:
  `Worker::new` (parallel.rs) and the measuring switch in `check` (main.rs).
  The option is off by default and isn't part of the options' fingerprint
  (correctly: it changes which entries are read, not what checking gives).
- `check_prepared` with `Load::Everything` turns it off before loading and
  asserts afterwards that the kernel holds no stated theorem. That is C1 as
  asked: one invariant, tested, covering readers nobody has listed.
- The three other `Load::Diagnostics` sessions (`goal`, `goal --summary`,
  the trial command at `trial_cmd.rs:568`) never set the option. Step 3 must
  keep it that way for the trial, as the notes say.
- The check after a fill is a new session with the default, so everything
  reported comes from whole loads, as D3732 asks.

The switch is F1.

### 3. What is in part B

`stated_on_load` takes a definition only if it is a sealed theorem
(`has_interface`: a final theorem with a body and no assumption label), has
no instance, `fold`, `opaque`, `tailrec` or parameter-default mark, no
`unfolding` list, no run body and no validator, and every member of its group
is one of the unit's own and passes the same test. Against what later code
can see of a definition:

| Seen by later code | In part B? |
|---|---|
| Type, name, path, span, theorem flag | no: part A |
| Body of anything that unfolds or runs | no: only sealed theorems, whose bodies the kernel freezes and `computing_body` hides |
| Instance, `fold`, `opaque`, `tailrec`, parameter default | no: excluded |
| `unfolding` list (read by `opaque.rs` `local_owner`) | no: excluded |
| Run bodies, validators, natives | no: excluded, and the kernel refuses them on a stated theorem |
| `match` helpers | no: they are definitions, not theorems, and stay in part A; a theorem recursive through its helper shares its group and loads whole |
| Hashes | users refer to a sealed theorem by `interface_hash`; a group's hash covers every member, hence the whole-group rule; the full hash is recorded in part A |
| Tables (readings, names, navigation) | part A; they refer to a theorem by id |

*Correction (24 Nov 2026, SW-4741):* the `match` helpers row holds only for a
lifted `match`; one that is a theorem's whole body, on a parameter, is the
theorem's own case tree, so a recursive theorem like `bumpId` is a group of
one and loads stated, soundly.

What a stated theorem lacks that a proved one has (group, transparency set,
`lift_leaf`, `recursive`) has no reader outside the cache's own writer, the
dump and `tailrec.rs` (which reads the group of a definition being
elaborated). I grepped `crates/elab`, `driver`, `cli` and `core` for each.

A `theorem` must have a proposition for its type (`E-NOT-A-PROP`, probed), so
the writer's test (`has_interface`) and the kernel's (`def_mark` in
`admit_trusted_stated`) can't disagree and leave an entry that is refused on
every load.

### 4. A worker's entry against one job's

What goes into an entry from outside the unit, and why it is the same:

- **Dependency records**: `interface_hash` of each (cache/mod.rs, `Out::def`),
  equal for stated and proved.
- **The unit's own hashes**: `def_hash` of definitions whose bodies the
  session holds; a reference to a dependency's theorem hashes by interface, to
  anything else by a full hash the session has (recorded or computed).
- **Reliance**: a stated theorem is a leaf. Equal to the whole walk by
  invariant W, and a namespace where it would matter (it relies on a goal)
  writes no entry.
- **Warnings and notes**: the body readers that could feed one
  (`equation_notes.rs`, `assume.rs:157`, `opaque.rs` `declined_holding`) are
  for an error's note or an opaque definition; errors aren't cached and opaque
  theorems load whole.
- **Digest**: as in question 1.

Probe: `Par.Uses` (three theorems over a dependency with a recursive theorem,
plain theorems and a theorem with an `unfolding` list over an opaque
definition) written once by a session that held the dependency without proofs
and once by one that held it whole, same cache folder: `diff -r` equal.

What could still differ, not checked: a warning code I didn't read whose text
depends on a dependency's proof. The orchestrator's whole-project byte
compare is the test for that.

### 5. The encoding

- Part A's bytes don't depend on how the entry will be read; there is one
  writer. The question is whether a whole load installs what FORMAT 45 did,
  and it does: part B's nodes are written after everything else, so no part A
  node refers to one; part B's are appended to the same table, and each
  flagged record gets its body and group in order.
- `Loc` spans are steps from the previous one. `start_part` resets the
  writer's `last_loc`, and `read_nodes` starts each call at 0. They agree.
- Strings, files and dependency records that only proofs use are in the
  head, so a load without proofs still checks those dependencies' hashes:
  conservative, never wrong.
- `open` verifies the BLAKE3 checksum over everything before a decode, so the
  stepped-over blob is covered. The blob's length is bounds-checked
  (`Reader::raw`), "bytes after the tables" and "bytes after the proofs" are
  both refused, and the reference check runs over the nodes actually read.
- `e.out.problem` is now tested after part B is written, so a failure while
  writing a proof is still caught.
- `FORMAT` 46. The pinned digests in `check_cache/digest.rs` moved only
  because `FORMAT` is hashed into the digest; the digest pass writes no flag
  and no part B.

### 6. The docs

`docs/core.md` "Stated theorems" and `check-cache.md` "An entry's layout" match
the code, with three points: F1 (the switch isn't mentioned), F2 (the
parameter default) and F4.

## Findings

**F1 (low; a decision). The measuring switch `STITCHWORT_LOAD_PROOFS=0`.**
On a plain `check` with `Load::Diagnostics` it makes the reporting session
hold stated theorems and write entries from it. I found no way for it to
change a verdict: it is the worker's situation, covered by the same argument,
and the probes (an error, an open goal, a dependant relying on the goal) gave
identical output and exit codes. It can't skip a proof report either: every
command that reads proofs loads with `Load::Everything`, which turns it off.
But it contradicts what the docs say ("only `check --jobs`'s workers"), it is
an undocumented way for a user-facing command to report from a session
without proofs, and the lane's own comment says a note's text may differ.
Recommendation: merge with it, since `measure_load.sh` needs it for the
measurement that decides step 3; add one sentence to `check-cache.md` and
`core.md` naming it; remove it in step 3, which replaces it. If Matt would
rather no user-facing check reports without proofs on `main` even behind an
environment variable, it is eight lines to drop and the measurement runs from
the lane's binary.

**F2 (nit). The reader's refusals are one short of the writer's rule.**
`stated_on_load` excludes a parameter default's mark; `admit_stated` doesn't
test `param_defaults`, and the mark would be dropped in silence. A validator
is refused by the kernel, so that one fails closed. No real entry can have
either (a theorem is never a parameter default), and the entry is sealed and
exact; but `core.md` says "the replay refuses an entry that says otherwise".
Add the test or soften the sentence.

**F3 (low). The fixture's shapes.** `Par.Facts` has a recursive theorem,
plain theorems and a `@[reading]` theorem. It has no theorem with an
`unfolding` list, no instance theorem, no mutual group of theorems, and
`canonical_dump_without_proofs` hides the `unfolding` list and flags of every
theorem, so it wouldn't notice a whole-loaded theorem losing its list. My
probe covered the `unfolding` case by entry bytes. A theorem with an
`unfolding` list in the fixture, and the dump hiding fields only for theorems
that `stated_on_load` would take, would close it. A follow-up ticket, not a
condition.

**F4 (nit). `--timings` is not behind the assertion.** The comment in
`check_prepared` and the notes list "`--timings`' sizes" among the readers
`Load::Everything` covers. `check --timings` is a plain check and loads with
`Load::Diagnostics`. It is harmless: `timings.rs` `made` sizes the
definitions made in a declaration's frame, which the session elaborated and
holds whole. The comment should say that instead.

**F5 (note for step 3). The assertion covers `check_prepared` only.** A
session that loads namespaces another way (the test helper `load_each` calls
`check_project_namespace` directly) isn't asserted. Today nothing outside
tests does that with the option on. Step 3, which turns the option on for
plain checks, should keep the option's setter to the two call sites and
restate the rule there.

## Checked and sound

- The exactness chain: `usable`, the stamp, `carried_anything`,
  `keep_rechecked`, `loads_proofs`, `admit_stated`'s own test (question 1).
- Invariant W's write condition, read in the code and probed.
- N3: `admit_trusted_stated` has one caller outside tests, `admit_stated`.
- C1: the assertion, its placement, and every `Load::Diagnostics` site.
- C2: the hash is inserted in the same step as the admission, and forgotten
  with it on a refused replay; the dump.
- The qualification rule against every reader of a group, flag or list I
  could find (question 3).
- The encoding: node order, `Loc` steps, head tables, checksum, trailing
  bytes, `FORMAT` (question 5).
- Dependency records, own hashes and digests equal for a worker and one job
  (question 4), by reading and by one probe.
- No narrowing (D3688): no proved tool or top theorem is touched; a load
  without proofs accepts the same sources.

## Not checked

- No test was run: the lane's three tests and the pinned digests are the
  lane's report and the verifier's run.
- Whole projects (`tools/fmt`, `aoc/`, std) with `--jobs`: the orchestrator's
  measurement. My probe was two to three small namespaces.
- Library files' entries loaded without proofs (`bind_builtin_def` on a
  stated theorem): read, not probed apart from the probe's use of `Std`.
- Every warning code's text against a stated dependency (question 4).
- `--jobs` with `--index` (navigation tables written by workers holding
  stated theorems): the tables refer to theorems by id and span; not probed.
- A late miss in a worker after stated theorems were admitted: read
  (`forget_since`), not exercised.
- The lane's timing and memory figures.
