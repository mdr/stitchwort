# SW-4550: soundness review of crates/core and the check cache, 20 to 21 November 2026

Fable paper review, 21 November 2026, of `main` at `81b074d4f`. Read from
the diffs and the code around them. Nothing was built or run.

## In plain words

- **Nothing found that lets a false or ill-typed proposition through.**
- **SW-4512 (the read-back that stops early) can't affect soundness at
  all.** It only changes how the elaborator answers "does this type still
  mention an unknown?". Every term the elaborator makes is still checked by
  the kernel, and the kernel's own read-back takes the old path unchanged.
  The lane's argument that the answers are the same holds, with one honest
  exception: where the old code ran out of steps, depth or size while
  finishing a huge normal form, the new code can now answer "yes" and carry
  on. That makes the elaborator accept a little more (within its limits),
  never wrongly.
- **SW-4452 (carried cache entries) closes the gap it set out to close.**
  A carried entry's field sorts and erasure flags, the only things the
  kernel derives, reads and doesn't hash, are now this kernel's on both
  paths. I found no way for a stale or carried entry to be trusted when it
  shouldn't be. One small hole is left, in behaviour only: the run body of
  a carried entry from a build with the same kernel side is installed
  unchecked and unhashed (F2).
- **The kernel spec is out of date in one sentence** (F1): `docs/core.md`
  still says run bodies are "type-checked but not compared", and doesn't
  say the trusted replay of a carried entry works the field sorts out
  again.
- **A latent crash, older than these changes** (F3): the erased
  placeholder reaching either scan panics on an index out of range.
  I found no way to reach it.
- Everything else under `crates/core` and `crates/driver/src` since
  20 November 12:00 is printing, tests' time limits, or already reviewed.

| | Finding | Kind | Severity |
|---|---|---|---|
| F1 | `docs/core.md` not updated for SW-4452 | spec text | low |
| F2 | A carried, same-kernel entry's run body is neither hashed nor checked | behaviour only, not soundness | low |
| F3 | `has_unsolved` and `unsolved_in` panic on the erased placeholder | latent crash, not reachable that I can see | low |
| F4 | `normal_form_meets` skips `note_readback` when it stops early | statistics only | trivial |

## 1. SW-4512: `normal_form_meets` and `has_unsolved`

**What can go wrong here at all.** `has_unsolved` is asked by nine places
in the elaborator, each deciding what to try next (hold a lambda, postpone
an argument, wait on a row, call an instance ready) or which message to
give. A wrong answer gives a different elaboration or a different error;
the term that results goes through the kernel as before. So the worst case
is an elaborator bug, never an unsound acceptance. The kernel's read-back
(`quote`, `quote_at_most`, `quote_folded`) goes through `quote_as`, which
calls `quote_as_until` with `stop = None`: the new block is skipped and
the `Met` result can't arise, so the kernel computes exactly what it did.
`normal_form_meets` has one caller, `has_unsolved`.

**The argument, checked.** Old: read back the whole normal form (cap
100,000 nodes, else the folded read-back), zonk keeping every unknown,
scan for an unsolved one. New: the same read-back, stopping at the first
value that is an unsolved unknown; if none is met, scan the finished term;
past the cap, the folded read-back, zonked and scanned as before.

- *New "yes" implies old "yes".* The value met is one the old read-back
  also visits, and `visit` turns it into `Term::Meta(m)` (or the elision,
  for the erased placeholder). Every assembly task (`Pi`, `Lam`, `Data`,
  `Ctor`, `NatAdd`, `Eq`, `Spine`) keeps all its parts, so that node is in
  the finished term. `force` replaces every solved unknown
  (`needs_forcing`), so the term's unknowns are all unsolved and zonking
  leaves them: `zonk_solved` on an unsolved head evaluates and reads back
  as written, and with `keep = |_| true` never takes its unfolding branch.
- *New "no" implies old "no".* An unknown the early test misses (a call or
  a solved unknown that forces to one; `Succ` of a call, which `visit`
  handles by direct recursion) is still in the finished term, which the
  new code scans with the same predicate.
- *Past the cap.* If the unknown is met within the first 100,000 nodes of
  a larger normal form, new says "yes" at once; old fell back to the
  folded read-back. Those agree because a folded call's normal form is a
  function of its closed definition and its arguments, so any unknown in
  the normal form is in some argument, and the folded term shows the
  arguments. If none is met before the cap, both run the same fallback
  (`has_unsolved` repeats `unsolved_in`'s three lines).
- *Order.* `has_unsolved` drops which unknown it was; the three callers
  that use it kept `unsolved_in`. The doc comment says the order may
  differ, which is right.

**Where the answers do differ.**

1. *Resource errors.* Old: an error from finishing the read-back (the step
   budget, depth, a size limit under 100,000, an error in zonking)
   propagated, or at the two diagnostic callers (`total_lambda_note`,
   `partial_callback`) counted as "no". New: if an unknown is met first,
   the answer is "yes". So a declaration that ran out of steps can now
   check (the commit's step counts show this direction), and two messages
   can lose or gain a note. Neither is a correctness problem: every
   caller's "yes" branch is the cautious one (wait, postpone, hold).
2. *`doneIn Empty v`, in theory.* Zonking rewrites `doneIn {a} Empty v` to
   `v`, dropping `a`. If `a` were the only unsolved unknown, old said "no"
   and new says "yes". In a normal form `doneIn` is unfolded already
   (`Effect.doneIn` is a plain definition), so this needs it opaque or
   stuck; I don't think it happens, and the new answer is the truer one.

**The erased placeholder (F3).** `visit` reads `Head::Var(ERASED)` back as
`Term::Meta(ELIDED)`, and `ELIDED` is `usize::MAX`. The new early test
hands `ELIDED` to `stop`; `has_unsolved`'s `stop` is
`g.meta_solution(m).is_none()`, and the elaborator's store indexes
(`state/metas.rs:135`, `self.metas.borrow()[m]`), so it panics. The old
path panicked too: zonking a bare `Term::Meta(ELIDED)` goes to
`zonk_solved`, which evaluates and forces it through the same lookup. So
behaviour is unchanged (a crash either way), and I found no route for an
erased value to these callers: the elaborator makes them only in
`counterexample/`, for messages. Not soundness. Fix, two lines: in
`has_unsolved` (and `unsolved_in`), `m == ELIDED ||` before the lookup,
which is what `normal_form_meets`'s doc ("or erased placeholder")
already promises its callers. No reproducer: I couldn't construct one.

**The cap fallback.** Identical to `unsolved_in`'s. `zonk_keeping` with
`|_| true` can't report an unsolved unknown or an open goal; it can pass
on a resource error, as before.

**Callers that might rely on the old behaviour.** None relies on the
read-back having finished: each uses only the boolean. `proof_branch_type`
quotes the type itself afterwards. No caller uses the read-back's side
effects, except that a finished read-back leaves calls' unfoldings kept
for later (docs/core.md, "the steps a declaration's check takes can depend
on which earlier check already forced a call"): steps change, results
don't, and the lane measured hashes unchanged.

**F4.** The early return doesn't call `budget.note_readback(size)`. It
feeds `--timings`' largest-read-back figure only.

## 2. SW-4452 (and the stage 2 fixes it follows)

Read: `c96d96ebf`, and the code as it now stands in
`crates/elab/src/cache/mod.rs` (`usable`, `cache_read`, `keep_rechecked`,
`admit_replayed`, `submit`) and `crates/core/src/check.rs`
(`admit_trusted_data_group`, `recompute_field_sorts`, `admit_data_group`,
`set_run_body`). SW-4450's M1 fix (`2a3978ba8`) was made after that review
and not reviewed since, so I read it too.

**When an entry is trusted, as built.**

| Entry | `Hit` | Path | Beyond the terms |
|---|---|---|---|
| This build's, written with nothing carried | exact | trusted | nothing: this build produced every part |
| Another build's, same kernel side; or one this build re-checked and kept | not exact, no re-check | trusted | hashes recomputed and compared; field sorts and erasure recomputed (SW-4452) |
| Another kernel side's, or any with `--recheck` | re-check | the kernel's checking calls | hashes, field sorts and erasure, run body compared (M1, SW-4452) |

- `carried = !hit.exact` is the right test: `keep_rechecked` stamps a kept
  entry not exact, and `usable` gives "exact" only to this build's own
  file with a matching compiler and interface; `cache_read` drops an exact
  verdict on anyone else's file.
- `keep_rechecked` runs only after `replay` returned `Ok` with
  `hit.recheck`, that is after `submit`, the built-in comparison and
  `hashes_as_recorded` all passed. It rewrites the stamp, never the body.
- **M1's fix is right.** After `define_data_group`, each member's
  installed `field_sorts` and `field_erased` are compared with the
  entry's, constructor counts included; a difference is a refusal and the
  undo.
- **`recompute_field_sorts` matches the checked path.** Same context as
  `admit_data_group` (the first member's parameters bound, each field
  bound after it, unbound per constructor), the same `check_type` and
  `is_type_former` calls, inside `in_kernel_modes`, with the group
  pending. It leaves out positivity, universe fit and the
  declared-later test, which is fine: the kernel side that wrote the
  entry is this one and ran them. A failure is a refusal, and the unit is
  elaborated.
- **What the hash covers** (`hash.rs`): the terms, `theorem`, `instance`,
  `opaque` with its `unfolding` list, a data type's sort, record flag,
  `no_eta`, auto parameters, constructors' `implicit` and `braced`.
  Derived by the kernel on install on both paths, never taken from the
  entry: group, `recursive`, transparency sets, eta, nestable, inert
  arguments. Not hashed and taken from the entry: field sorts and erasure
  (now recomputed), the run body (F2), and the marks `fold`, `tailrec`
  and parameter defaults, which the kernel takes from any elaborator
  untrusted.

So for a proof, a carried entry on the trusted path now rests on: the
kernel-side fingerprint covering `crates/core` (unchanged, tested), the
key, and the hash comparison. I found no stale-entry path: SW-4452
doesn't touch keys or dependency comparison.

**F2. A carried entry's run body on the trusted path.** For a
same-kernel-side carried entry, `admit_trusted_run_body` checks shape
only, and no hash covers the term. The decode self-check exists because
another build's encoder may not match this decoder; a run body misread
that way (and still well-shaped) would be installed, and `stitchwort run`
and tests would run it. The kernel never unfolds a run body, so no
proposition is affected: a wrong test result or program output, not
unsoundness. Sketch: build A writes an entry holding a `decreasing`
definition; build B (same `crates/core`, a codec change for some term
form without a `FORMAT` bump) carries it; the body and type are refused
by their hashes if misread, the run body is not. Fix: on the trusted path
with `carried`, send the run body through `set_run_body` (one type check
per measure-recursive definition), as the re-check does; or hash it into
the entry's self-check. Low.

**The run-body comparison** (`format!("{t:?}")` of the installed term
against the entry's) errs only towards refusal. If `check` ever returns a
term that differs from its input, or a library definition's run body is
replaced when it is bound as a built-in (SW-4450 left `length_run_body`
unchased), a re-check would refuse that unit every time and elaborate it:
a cost, visible in `refused_on_recheck`, not a trust problem. Worth one
look at the counter after the next kernel-side change.

**F1. `docs/core.md` line 557** still reads "Run bodies are type-checked
but not compared", and says nothing of the trusted replay recomputing
field sorts for carried entries. SW-4452 updated the proposal's "As
built" only; the spec is the kernel's (D3210). Two sentences.

## 3. Everything else since 20 November 12:00

`git log --since='2026-11-20 12:00' -- crates/core crates/driver/src`,
plus `crates/elab/src/cache` and `crates/elab/src/kernel.rs`.

| Commit | What | Verdict |
|---|---|---|
| `e87365f3f` SW-4512 | `value.rs` | section 1 |
| `c96d96ebf` SW-4452 | `check.rs`, cache | section 2 |
| `2a3978ba8`, `781ecf5d8`, `0fdec7072` SW-4410 | stage 2 re-check | reviewed as SW-4450; the M1 fix read here, right |
| `31eaee168`, `34deb598e` SW-4409 | stage 1, kernel-side fingerprint | reviewed as SW-4409/SW-4422; the fingerprint is the evaluation one, all of `crates/core`, with a test that names the files |
| `f95039a87`, `ce710cb3f` | unit-test compile fixes | tests only |
| `99b5d8b6f`, `97d0f93ea`, `c470dd45c`, `e1eddae24`, `fd0169409` | `pretty.rs` | printing only |
| `346cc9d73` SW-1822 | bundle content id for the language server's kept session | which session is reused, keyed by content instead of an address; nothing the kernel trusts |
| `5fe0f8af4`, `7232384e3`, `99416ddd5` | `float_gate` deadline | a test harness: the all-natives-off mode now stops at 30 s and reports failure, never a pass; the natives-on against float-natives-off comparison is untouched |
| `29533b25f`, `e4ca5b6f5` | `fixes.rs` | quick fixes for editors |
| `bc9d030a2`, `cf65b9f7c`, `97d0f3df5` | docs headers, `Session::start` options, `check --only` hint | not trust |

## What I did not check

- Nothing was run; every claim above is from reading.
- I did not re-read `decode`'s dependency comparison, `replay_tables`, or
  `hash.rs` beyond a grep for which fields it covers.
- F3's "not reachable" is from a grep for where the elaborator makes
  erased values, not a proof.
- The elaborator-side changes of SW-4385 (guards refining goals) and the
  other lanes of these two days outside `crates/core`, the driver and the
  cache were out of scope; the kernel checks their output.
