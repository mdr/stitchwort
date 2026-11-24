# Stage 3 steps 2 and 3 (SW-4765, SW-4767): Fable review of the trust path

Reviewed: step 2 as merged on `main` (`63197e295`: `crates/elab/src/cache/deferral.rs`, the
interface entry in `cache/mod.rs`, `check::admit_trusted_unproved`, `Store::read_interface`) and
step 3 on `lane/SW-4767` at `3280938af` (`git diff main...lane/SW-4767`: `crates/driver/src/parallel.rs`,
`project.rs`, `live.rs`, `crates/cli/src/main.rs`). 24 Nov 2026, about 20 minutes. This is step 4 of
the build plan in `docs/proposals/parallel-checking-stage-3.md` §9, with SW-4764 (F3 of
`docs/reviews/SW-4763-review.md`) included.

**Verdict: merge.** I found no way for an interface entry or a promise to reach a "checked", a
message, a saved entry that a later run accepts early, or a session other than a worker's. The
findings are two small robustness points and test gaps; none needs fixing before the merge.

Marks: **[run]** shown by a test I ran; **[read]** traced in the code; **[argued]** reasoned, not
traced to the end.

## Tests run (in the lane's worktree; nothing left behind, `git status` clean)

| Filter | Result |
|---|---|
| `package(stitchwort-cli) & binary(running) & test(/examples::soundness/)` | 1 passed |
| `package(stitchwort-driver) & binary(projects) & test(/interface_pass::\|parallel::/)` | 17 passed, 60 s |
| three uncommitted probes, `test(/parallel::probe_/)` (below) | 3 passed, then deleted |

The probes are saved at
`/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw4767r/probes.rs`.
As run they printed their counts; the saved file turns three of those printed figures into
assertions (noted in it), which I did not re-run in that form.

## The one failure that matters: why it can't happen

The argument has two halves, and both are small.

**1. Only a worker's session can hold an unproved theorem [read].** Two functions make one.
`check::leave_stated` has one caller (`Elaborator::group_checked`, `crates/elab/src/lib.rs:3878`),
reached only when `defers_proofs` is true, which needs `options.interface_pass` set;
`set_interface_pass` has one caller, `Worker::interface` in `parallel.rs`.
`check::admit_trusted_unproved` has one caller (`admit_stated`, `cache/mod.rs:5037`), under
`hit.interface`, which is set only by `interface_read`, which needs `without_proofs`, no
`--recheck`, and a store whose `read_interface` returns something. One store overrides
`read_interface`: `WorkerStore`, private to `parallel.rs`, made only in `Worker::new`. The check
after the fill uses its own session (`new_session`, `main.rs:2407`) with
`CheckCache` or `MemoryStore`, both on the default `None`. `fill` has one caller outside tests
(`fill_in_parallel`, for `check`); `test`, `run`, `axioms`, `build`, `doc` and the language server
never start it. The assertion in `check_prepared`, the two goal-search loads and the server's step
is a backstop behind that, and it is placed before anything is returned to be printed.

**2. A worker's entries are believed only through the key chain [read], [run].** A worker writes
`M`'s whole entry under a key made from each dependency's digest as its session has it
(`namespace_cache_key`, `cache/mod.rs:1162`): the claimed digest, for one loaded from an interface.
A session has a digest for `N` from three places only: `N`'s whole entry (replayed or planned),
its own full check of `N` that passed and encoded (no error, no goal, nothing unfinished, not
cancelled, no failed dependency), or an interface pass. The third is the worker's alone (half 1).
A dependency with no digest is keyed by its text under another tag (`"text"` against `"digest"`),
so the keys can't meet. So by induction from the bottom of the graph: any session but a worker
finds `M`'s entry only when every namespace below has a whole entry, or passed its own check there,
with exactly the digest `M` was checked against. That is W′, and it holds for the same run's last
pass, a later run, a later run on other commands, `--carry-over` (same key, `read_others`) and
`--recheck` (same key, then checked again by the kernel with proofs loaded).

On top of the key, each reference from `M`'s entry to a theorem of `N` is recorded by path and
interface hash and compared on replay (`Out::def`, `cache/mod.rs:2030`), and a failed proof's
stand-in and a `?` hash under their own tags (`hash::has_interface`), so a theorem whose proof
failed can't stand in for the promised one even if a digest were wrong.

What the digest must cover for this is unchanged from stage 2: everything of `N` the kernel reads
when checking `M`, which for a deferred theorem is its type alone (rule F seals a proved
theorem's body the same way). The interface pass computes its digest with the same encoder over
the same session state it publishes, and an unproved theorem's record enters the digest as a
proved sealed theorem's does (`sealed`, type, `interface_hash`). Where the interface pass and the
full check could elaborate a statement differently (`decreasing_group`'s own route, `retype_total`
after a body), the result is a different digest, so a mismatch and lost time, not a wrong entry.

**Probed [run]** (`probe_a_false_promise_never_reaches_a_checked`, 8 schedules each):

- `Par.Facts` gets a false theorem with a failing proof (`later: bump n = Succ n`), and `Par.Uses`
  proves `bump 0 = 1` from it. In 6 of 8 schedules a worker wrote `Par.Uses`'s entry above the
  false promise. In all 8: the report is one job's; `Par.Facts` has no entry; a second check of
  the same source over that cache, loading everything, replays nothing above it and reports the
  same.
- Then the statement is changed to a true one (`bump n = n`), so `Par.Uses` must now fail. Over
  the cache the first run left, one job and four jobs both report exactly what a fresh one-job
  check reports. The entry written against the false statement is never found.
- D3737's reuse: a true statement with a wrong proof, then fixed with the same statement. The
  one-job check over the first run's cache replayed 2 namespaces in the 6 schedules that had
  written them, and its report and its session dump equal a fresh check's.

## The brief's questions

**Can a deferred theorem's statement differ from what the proof job checks?** Only into a
mismatch. The rule is read from the parse (`plain_theorem`), before any signature; both passes
elaborate the signature with the same `self.signature`. Checked each item:

- *Attributes.* Only `@[reading]` and the `@[walk…]` family pass rule 2. `after_definition`
  (`lib.rs:4166`) files both from the id after the theorem is settled, in the same place relative
  to later declarations in both passes ("filed once proved") [read].
- *Defaults, `unfolding`, `opaque`, instances, exports, a syntax error:* refused by rule 2, and
  again by `leave_stated` from the kernel's own marks.
- *Mutual groups.* `defers_proofs` takes the source component, which can only be larger than the
  kernel's groups (a member must be declared before another's body can name it), so a theorem in
  a real group with a computing definition is never deferred [argued]. The fixture's `pick`/
  `pickOk` covers it.
- *A failed dependency mid-group.* `leave_stated` is called member by member; if the second is
  refused (`E-FAILED-DEPENDENCY`), the first stays stated, the component fails,
  `abandon_pending` fails the rest, the pass has an error, and `Worker::interface` rewinds and
  leaves the namespace [read].
- *Local definitions.* `group_checked` is only reached for top-level components
  (`lib.rs:3571`), so a `theorem` written inside a `def` is never deferred [read].
- *A theorem with no proof, a non-terminating recursive one, a duplicate name, a goal or a broken
  proof used by a later definition of the same namespace and from above, a mutual pair with one
  proof broken:* each reports as one job on disk, in memory and on a second run over the cache,
  6 schedules each [run, `probe_odd_shapes_report_as_one_job`].

**The reliance walk in a worker.** `assumption::mentions` treats an unproved theorem as a leaf
that relies on nothing, so a worker never marks `M` unfinished because of a goal or error in a
proof below. That is the promise, and it is only ever used to decide whether the worker writes
`M`'s entry (D3737). The case where it matters for a report is covered by the key chain: a
namespace with a goal or an error gets no digest anywhere, so nothing above it is found
[read; run for the goal and error cases].

**`--no-cache --jobs` (D3731).** Interface entries live in `Interfaces`, never in `MemoryStore`;
the last pass is given a `MemoryStore` clone, whose `read_interface` is the default. Whole
entries in memory obey the same key chain. The failing shapes above report as one job in memory
[run].

**A worker panic, or the fill stopping.** `halt` sets every worker's cancel flag; a cancelled
check writes nothing (`ok` needs `!cancelled`, and both encoders check again after encoding), and
an interface pass publishes its entry only after the same checks. Entries already written or
published are whole and valid by W′. Disk writes are the store's own, as in stage 1 (not re-read here). See R1 for what a
panic does to the run.

**Carried over and `--recheck`.** Both are quietly one job in the same command (`main.rs:2417`),
so no worker ever carries over or rechecks; in a later run both find a worker's entry by its
exact key, so W′ applies as written [read].

**What a worker writes besides namespace entries.** Library file entries, through `ClaimStore`.
A library file is never elaborated as an interface pass (`library_stack_is_empty`), and any
reference from its entry to a project theorem would be recorded by path and interface hash and
checked on replay. Nothing else is written [read for the store; argued for the references].

## SW-4764 (F3 of the step 1 review): the rewinds

**Answer: no path in the elaborator or the fill produces the pattern** (a definition declared
before a theorem left stated, defined after it against the theorem, and kept by a rewind past the
theorem). It needs a declaration to stay pending across another top-level declaration, and none
does:

- The `declare_def` call sites in `crates/elab` (about 30 by `grep`: `group_checked`,
  `decreasing`, `derive`, `opaque`, `interfaces`, `lift`, the unifier's helpers, tests,
  `builtin_docs`) each define what they declare inside the processing of one top-level
  component. I read `group_checked`, the interface methods and the test declaration in full and
  the others by their surroundings only [argued for those]. `module.rs:662` calls
  `abandon_pending` when a component fails, so nothing pending survives into the next whatever
  a call site does.
- `leave_stated` is called only from `group_checked`, on a component whose members are all
  theorems and all deferred, so the only pending declarations at that moment are its own
  members; `group_checked` is not re-entered for a project declaration (a library file loaded
  inside it is never deferred).
- An interface entry is admitted only by a namespace's replay, between loads.
- The rewinds that can pass an unproved theorem are the three in `parallel.rs` (`unload_from`, a
  failed interface pass, a proof job that wrote nothing), all to session marks taken between
  namespaces, where `Elaborator::mark` asserts no declaration is in progress. The rewinds inside
  a declaration (`rewind_globals`, a refused replay's `forget_since`) use marks taken after any
  theorem already settled.
- What a session rewind doesn't put back (`state/session.rs`: counters, logs) holds nothing
  checked against a theorem; `namespace_keys` and `failed_namespaces` are journalled.

What an unproved theorem leaves behind after a rewind past it is therefore only what is meant to
stay: entries in the store, keyed (D3737), and interface entries.

Not proved by a test. A cheap guard would turn the argument into a check: have
`Elaborator::mark` assert the kernel holds no pending definition (a count kept by the kernel, so
it costs nothing). Low priority; suggest closing SW-4764 with this answer and filing the guard
as a small follow-up if wanted.

## Findings, ranked

### R1 (low; robustness, not correctness): a panic only a promise-holding session can raise

Stage 3 creates panics that exist only in workers, by design: asking for the full hash of an
unproved theorem is an internal error (SW-4763 F6, (e)). What happens then depends on which
worker it lands on. On worker 0 (`fill`, the `resume_unwind`), the whole run aborts, though one
job would have passed. On any other worker the panic is dropped (`h.join().unwrap_or_default()`,
and `Tally::panic` is read for worker 0 only), the fill halts, and the last pass does everything
on one thread: right answer, at one-job speed, with only the panic hook's text on stderr and
nothing in `Fill`.

Neither is a wrong result. But the same bug gives a crash or a silent slowdown by schedule, and
the slowdown would not be noticed by the tests' comparisons. I found no reachable caller of a
full hash on an unproved theorem in a worker (the encoder writes none for its own, references go
by interface hash, pins read it as "not pinned"), so this is about the next such bug. Suggest:
count worker panics in `Fill` and in the `--timings` note, and have the standing random-schedule
test assert zero. Whether worker 0's panic should also fall back instead of aborting is the
orchestrator's call; the comment's reason (thread-local state on the caller's thread) still
stands.

### T1 (tests to add; each passed as a probe)

1. **The false promise and D3737's reuse** have no test. The existing failure test checks the
   same run only (`namespace_hits == 0` after the fill). The probe above checks the next run:
   statement changed (entry not found), proof fixed (entry reused, same report and session).
   This is the direct test of W′ across runs, and of the half of the mismatch rule the forced
   mismatch test can't reach (that test sets the board's flag while the digests are in fact
   equal, so it never shows an entry keyed to a wrong digest being missed).
2. **Rule 3's rewinds and the admission of an interface entry are exercised but not asserted.**
   On the stage 3 fixture, 9 of 42 runs (2 and 3 jobs, 21 schedules each) rewound and 9 loaded an
   interface entry [run, `probe_rewinds_happen`]. The standing test asserts `interface_made > 0`
   and `against_promises > 0` only; add `rewinds > 0` and `interface_hits > 0` summed over the
   schedules, so a scheduling change can't quietly stop covering the two paths this review
   leans on.
3. **The odd shapes** (`probe_odd_shapes_report_as_one_job`) are cheap to keep.

### R2 (note): `written` is read from two counters

`Worker::prove` decides that the namespace has an entry from `namespace_written` or
`namespace_hits` going up. It is right today because the store stops serving interface entries
for the job's own namespace (otherwise an interface hit would read as "not written" and leave
the namespace). It affects scheduling only, never trust. A return value from the elaborator
saying what happened would be sturdier than a counter difference; not needed now.

### R3 (note): progress notes are the one thing workers print

`print_progress_note` de-duplicates "still checking" notes by text in a set that only grows.
Fine for a run. It is worth one line in the design note's §5 that these notes come from workers
too, since "workers report nothing" is otherwise exact.

## Not done, not verified

- A real digest mismatch (the interface pass and the full check disagreeing on a statement) can't
  be produced without a hook in the elaborator; that entries above it are missed is shown only
  through the statement-change probe and the key's construction.
- The digest's coverage of what the kernel reads from a namespace is stage 2's property; I
  relied on it and on SW-4735's review, and did not re-audit the encoder field by field.
- `retype_total` and `decreasing_group` against a deferred theorem's statement: argued to end in
  a mismatch at worst; the measured zero mismatches on `tools/fmt` and `aoc` cover the shapes
  those projects have.
- The board: I did not touch SW-4764 or any ticket (a paper lane with no ticket of its own).
