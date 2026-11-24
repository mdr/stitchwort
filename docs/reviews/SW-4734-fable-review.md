# SW-4734: Fable review of the stated theorem in the kernel

Parallel checking stage 2, step 1 (docs/proposals/parallel-checking.md §10,
D3732). Reviewed: `lane/SW-4734` at `bb0a46964`, the diff against its merge
base with `main` (commit `6036ccf8d` is the code), with
docs/reviews/SW-4734-notes.md and SW-4732's stage 2 list
(docs/reviews/SW-4732-body-read-audit.md §4, on `main`). A paper review, with
one probe run on the worktree's and the main checkout's release binaries.
24 November 2026.

## Verdict

**Sound; merge.** Nothing in this lane can make a stated theorem outside a
test, the kernel treats one as the proved theorem everywhere it checks, the
kernel accepts nothing less, and F1 (proof calls erased at any arity) can't
change what a program computes. No finding blocks the merge. Two findings
are conditions on step 2 (SW-4735), which is the first lane to make a stated
theorem in a real session; three are small.

## The six questions

### 1. Who can make one

- `Def::stated` is `pub(crate)`. It is written in two places in
  `crates/core`: `push_marked_def` (always `false`) and
  `admit_trusted_stated` (`check.rs`, the one `def.stated = true`). `defs_mut`
  is `pub(crate)`. The only other writers of a `Def` are behind the
  `test-bypass` feature (`env.rs`), as before.
- Callers of `admit_trusted_stated` in the tree: `crates/core/tests/it/stated.rs`
  and the unit test in `crates/driver/src/axioms.rs`. No caller in `elab`,
  `driver`, the cache or any command, so no user input and no cache file
  reaches it in this lane. There is no `leave_stated`, and no path from a
  pending or failed theorem to a stated one: the marks and `define_group`,
  `retype_def` act on pending definitions only, and a stated theorem is
  never pending.
- The function itself: the same structural checks as `admit_trusted_def`,
  then `def_mark` on the type's value, with erasure stopped and the empty
  transparency set, before anything is pushed; a refusal adds nothing.
  `def_mark` is `prop_mark`, which derives every mark from sorts and reads
  none off the term, so a wrong entry can't pass a computing type as a
  proposition.

It is a `pub fn`, like the other `admit_trusted_*`. What keeps stage 3's use
out is review, not the type system (finding N3).

### 2. Treated as proved

While checking, erasure is off (`in_kernel_modes`, `in_own_view` and
`determined` stop it; only the driver's run and test paths and the
counterexample search turn it on), and every definition with `Def::proof`
is frozen: `body_seen` is `None` for proved and stated alike. I read every
remaining direct reader of `def.body` and `def.arity` in `crates/core/src`:

| Reader | Stated against proved |
|---|---|
| `value.rs` `case_tree`, `slot_type`, `unfold_for`, `unfolds_head` and the folded-call helpers | reached only for a definition that unfolds, or test `body_seen` too: never a frozen one |
| eta's `next_parameter` | reads only a body that may be seen (SW-4728, in this branch) |
| `hash.rs` `has_interface`, `interface_hash` | the tag `theorem` and the type: equal by construction. A proved theorem's `unfolding` list, group and flags aren't in it either |
| `hash.rs` proofless | a proof member of a group already stands apart and hashes as `proof-def`, theorem, type; the stated branch produces the same bytes. Users leave a call of it out altogether (`is_proof`) |
| `hash.rs` content (`def_hash`) | `None` unless the hash cache holds the recorded one. Users never ask: they refer by interface hash |
| `assumption::mentions` | a leaf: sound by invariant W only, as the doc now says |
| `reference.rs` | the same freeze test, written apart; never erases, so see N2 |
| `pretty.rs`, `termination.rs` | parameter-default helpers and members being checked: never a theorem |

The refusals (`run_body_shape`, `add_validator`, `native::register_shaped`,
`float::register_def`) apply only to a definition with `stated` set, so none
changes anything for a session without one. `registry::bind_def` and the
`Nat.addZero` fit check accept a stated theorem; they test a statement's
shape, and a stated theorem's statement was proved, so that is sound.

The seven elaborator tests are each `body().is_some()` to `defined()`, the
same answer for every definition that isn't stated.

### 3. Fail closed

`axioms` (both walks) and `audit`'s witness scan go through `walked_body`,
which panics on a stated theorem. `audit`'s scan is over every definition,
so one stated theorem anywhere in an audit session stops it: correct, since
that session should hold none.

Against SW-4732's "needs the proofs" list, the lane leaves these reading
`body()` as before: `declhash.rs` (`def_uses`), `live/trial.rs`,
`timings.rs`, `assume.rs:157`, `equation_notes.rs`. With a stated theorem
each would answer from the statement alone, silently. None can meet one in
this lane. See finding C1.

Reliance (`relied_on`, `mentions`, the test runner's goal walk) treats a
stated theorem as a leaf. That is the design (§10.2) and is right only by
invariant W; it is not an under-report as long as step 2 makes a stated
theorem only from an entry.

### 4. F1: proof calls erased at any arity

**Sound, and it can't change a result.**

- `Def::proof` is `prop_mark` of the type, and a function type is a
  proposition exactly when its codomain is (`check.rs`, `prop_mark`). So a
  call of a proof definition is a proof at every number of arguments, fewer
  or more than its arity. Erasing it is rule 3 of `erase.rs` applied to a
  value that rule's own argument already covers.
- An erased value applied stays erased (`apply_step`), and before F1 a
  partial application became erased the moment it got its last argument. So
  the two runs differ only in a value that is a partial application of a
  proof definition: a neutral before, the placeholder now.
- Such a value has a function type, so nothing can `case` or `J` on it
  directly; the only thing a run does with it is apply it or pass it along.
  It sits only in positions whose type is a proposition, which are never
  printed or compared (`erase.rs`, "Why it's safe").
- `def.proof` implies the old test's `of_def(..).result` wherever that was
  computed, so nothing that used to run is now erased except a proof.
- The checker never erases, so no verdict, term, hash or cache entry moves.
  `erase::of_def`, `proof_positions` and the proofless hash aren't touched.

What can move: step counts of a run that passes a partially applied theorem
around (fewer steps, an `eval_step` saved by `quick`), and so a run within
a few steps of `E-RESOURCE`. A side effect worth having: a run's steps no
longer depend on the shape of a proof (its arity), which was a small
rule 6 leak into running.

Probe (`scratchpad/sw4734/review/p1.sw`): a two-parameter theorem applied to
one argument, passed through a function polymorphic over a `Prop`, dropped
in one definition and used as `J`'s proof in another. `run` prints `7`, `5`
and both tests pass, the same on the main checkout's binary (before F1) and
the worktree's.

Not checked: whether any test or snapshot records a step count that F1
moves (the lane ran the erasure and natives tests; the verifier's run is the
check), and the counterexample search, which also runs with erasure and can
now erase a call of a theorem that is still pending, where before the call
stayed stuck. That can only change which counterexample a message offers; I
did not read that path.

### 5. Does the kernel accept less (D3688)

No. Every new refusal is guarded by `def.stated`. `push_def` is split with
the same order of work. `Hasher::declaration` moves an `expect` below the
proofless branch, which a definition with a body never notices. No top
theorem or proved tool is touched.

### 6. docs/core.md "Stated theorems"

Accurate, with two wording points:

- "nothing in conversion reads a frozen definition's body or arity":
  `unfolds_head` and the folded-call tests do compare a spine with the arity
  first, then fail on `body_seen`. True in effect; "nothing in conversion
  depends on" would be exact.
- "Its only caller is the cache's replay" is step 2's state. In this lane it
  has no caller outside tests, which the notes say and the spec could.

Also N1 below (the erasure rule elsewhere in the docs).

## Findings

**C1 (condition on step 2, medium). The readers that aren't fail-closed.**
D3732 says anything reporting on proofs loads them "and refuses rather than
guesses". Five sites from SW-4732's list still guess (question 3), and so
does one that list doesn't have: `opaque.rs` `local_owner` finds a local
helper's owner by scanning every definition's `unfolding` list, and a
theorem may have a list (`theorem nextIsOne: next = 1 unfolding next`),
which a stated theorem lacks; that one changes a note's text only. Treating
each site is the wrong shape of fix. Recommended: step 2 keeps one fact
true and tests it, "a session loaded with `Load::Everything` holds no stated
theorem" (an assertion where the load finishes, or a count on the kernel),
so every such reader is covered at once, including ones nobody has listed.
Repro: none possible in this lane; no session can hold one.

**C2 (condition on step 2, low). What a stated theorem doesn't carry.**
`admit_trusted_stated` has no way to give it the proved theorem's
`unfolding` list, transparency set, group or `recursive` flag, and the marks
do nothing to a final definition. I found no reader in the kernel for which
that changes a check or a hash (question 2). But `cache/dump.rs` prints
`unfolding`, `group` and the state for every definition, so step 2's
byte-compare of a session loaded with stated theorems against one loaded
whole will differ on those fields for any theorem with a list or a group
unless dump prints `-` for a theorem there too, as F2 did for arity. And if
step 2 ever asks for a stated theorem's content hash before the replay has
put the recorded one in the cache, it gets `None`, not an error: the replay
should insert the hash in the same step as the admission.

**N1 (nit). The erasure rule is still written the old way.** `erase.rs`'s
module doc, rule 3, says a definition whose result is erased "isn't run once
it has all its arguments". For a proof definition that is now "at any number
of arguments". The new "Running" paragraph in core.md is right; the module
doc should match.

**N2 (note). Runs without erasure.** `run --reference` and a run with
erasure disabled never erase, so a stated theorem there is a stuck neutral
where the proved one would compute. Harmless while every session that runs
loads proofs; it is one more reader for C1's rule to cover.

**N3 (note). Stage 3 is kept out by review only.** `admit_trusted_stated` is
public and its precondition ("a theorem this build's kernel then proved") is
a doc comment. That is the same standing as the other `admit_trusted_*`.
Step 2's review should confirm its one new caller is the replay of an entry
and nothing else; a later lane adding a second caller is the thing to catch.

## Checked and sound

- The constructor and its guards; no route from user input, a cache file or
  an unchecked proof (question 1).
- Every direct reader of a body or arity in the kernel (question 2).
- Interface and proofless hashes equal for stated and proved, including a
  recursive theorem (its own group of one or more) and a theorem with an
  `unfolding` list, by reading `hash.rs`.
- Erasure is off for all checking, so F1 is a change to running only.
- F1's argument, and one probe on both binaries.
- No narrowing (question 5).
- The spec section against the code.

## Not checked

- No test was run: not the lane's `stated.rs`, nor the soundness set. The
  lane reports them; the verifier runs them.
- `crates/rt` and `crates/js` beyond the three guards the notes cite
  (`E-RUNTIME`, `E-EXPORT`, the erased skip), which I read and which match.
- `add_validator`'s and the native registrations' new refusals: read, and
  untested, as the notes say.
- The counterexample search under F1, and whether any recorded step count
  moves (question 4).
- The elaborator's 40-odd readers of a body's content against a stated
  theorem: SW-4732 audited them for sealed proofs; step 2's byte-compare is
  the test for stated ones.
- Invariant W itself, which reliance now rests on: taken from §10.3 as
  argued there.
