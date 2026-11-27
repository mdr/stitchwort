# SW-4679 (rule K's fresh levels checked on 32-bit): soundness review

Fable, 27 Nov 2026. Reviewed: `git diff main...lane/SW-4679 -- crates docs` (commit
`714854071`): `crates/core/src/value.rs`, `crates/core/src/reference.rs`,
`crates/core/tests/it/rule_k.rs`, `docs/core.md`. Marks: **[read]** from the code,
**[run]** from a test, **[inferred]** argued, not traced line by line.

## Verdict

**Merge.** The change closes the overflow it targets and "not equal" is a safe answer
everywhere it is used. No blocking issue. Four follow-ups, of which N1 (a single test, or
on 32-bit a top-level comparison, running past its range under binders) is a real remaining
way to break condition A and should be a ticket now; it was there before this change.

## 1. Does it close the overflow? Yes [read]

- `test_levels(base, used)` gives the range `[base + used, base + used + 2^24 - 1]` and
  returns `None` unless the top of it fits in `usize`: `used + 2^24` is checked, then
  `base + (taken - 1)`. `taken - 1` can't underflow. `base + used` is then below the checked
  sum, so the unchecked addition in the result is safe.
- 32-bit: base 2^31, 128 ranges of 2^24 fill `[2^31, 2^32 - 1]` exactly; the 129th gets
  `None`. 64-bit: `None` needs about 2^40 tests in progress, which the stack stops long
  before; the path is the same code.
- Every place that makes a level from the reserved range goes through it: K's test and
  both of S's index tests in `value.rs` (all through `meet_in_evaluation`), and
  `ends_equal` and `rule_s` in `reference.rs` (through `ends_level`, which also checks
  `depth * 2^24`). A grep for `RESERVED_LEVELS`, `LEVELS_PER_TEST` and `1 << 40` finds no
  other arithmetic.
- On `None` the function returns before the `Restore` guard, the counter and the memo are
  touched, so nothing is left to undo and the forced "no" is not filed in the memo.

So within the stated model (each test stays inside its own 2^24) no fresh level can equal a
real variable's or another test's. The model's own assumption is N1.

## 2. Is "not equal" sound on overflow? Yes [read, inferred]

"Not equal" means the cast (or the one-shape `case`) stays stuck. A stuck cast is a state
the kernel must already handle for any cast whose ends are equal in fact but not yet seen
to be (open ends that a substitution later makes equal), and two stuck casts are compared by
parts, which is sound in the model whatever fired. So refusing to fire can only lose an
equality.

Uses of the answer:

- `ends_meet` in `eval` (three sites) and `fire_cast`: `false` leaves the cast stuck / returns
  `None`.
- `one_shape` (rule S): `false` leaves the `case` stuck.
- The note-builder near `value.rs:6522` (why a call is stuck on a proof): on overflow it
  would say the indices differ and show the pair. A wrong note, in a message only.
- An outer test whose comparison meets the overflowing one: it compares with a stuck cast
  and may itself answer "no" where it would have answered "yes". Again only a lost
  equality: every "yes" `conv` gives over stuck casts holds in the model.

Negated uses: I found no place where the kernel accepts because a comparison failed. Index
unification calls a branch impossible only on a constructor clash; a stuck cast is neutral,
so it gives "stuck" (`E-INDEX-STUCK`), never "impossible" **[inferred from docs/core.md,
`unify_index.rs` not re-read]**. The elaborator may branch on "different", but what it
concludes is re-checked.

One thing the change makes untrue (N2): the memo's comment says an answer found at one
level holds at any. A "no" that came from an overflow deeper down is filed by the outer
test and reused for the same pair met at a shallower level, where it would have been "yes".
Still only a lost equality, and only on 32-bit past 128 tests.

## 3. Other collisions: one test running past its own range (N1, pre-existing)

`conv` goes under a binder with a plain `level + 1` (`codomains`, lambda against lambda,
eta, `push_eta`) and nothing bounds how far. `conv_with` is a work list, not recursion, so
the stack doesn't stop it; the only limit is the step budget, 10^10 by default, and a binder
costs a handful of steps.

- **A test more than 2^24 binders deep (both targets).** 1.7 x 10^7 levels at even 100
  steps each is under a fifth of the budget, so it is reachable **[inferred, not run]**: a
  type computed by recursion, such as `T (Succ n) = (x: Nat) → T n` against an equal but
  differently written one, descends one binder per unfolding with small closures and no
  growing memory. Past 2^24 the test's fresh variables have the levels of the next test's
  range. A cast evaluated under those binders starts a nested test whose first fresh
  variable can then be the outer variable that is free in its ends: `w => w` against
  `w => x` answers "equal", which is finding A again. The consequence is a cast firing with
  unequal ends (under a hypothesis of that equation): subject reduction lost in evaluation,
  not directly a proof of `False`, but outside the argument core.md gives.
- **A top-level comparison reaching the reserved range (32-bit only).** 2^31 binders is
  2.1 x 10^9 levels, inside the budget if a level costs under about 4.6 steps; a lambda
  against a lambda is one comparison step plus two applications, so this is marginal
  **[inferred]**. On 64-bit 2^40 levels exceeds the default budget (though
  `STITCHWORT_WORK_LIMIT` can raise it).
- **Wrapping `level + 1` itself** needs 2^32 levels on 32-bit: also near the budget's edge.

Should it be guarded now? Not in this lane: it isn't what the ticket targets, the fix
touches `conv`'s hot path and needs a decision (where the limit lives, since the elaborator
calls `conv` at arbitrary levels), and the shape that reaches it is contrived. But file it
now, as Opus work with a Fable review, with the repro above to be built. A sketch: the
machine keeps the top of the range of the comparison in progress (`RESERVED_LEVELS` outside
a test, the test's last level inside one), and the four `level + 1` sites go through one
helper that returns a resource error (`Nesting("comparison")`) at that top. One compare per
binder.

## 4. The reference evaluator calling `test_levels`: acceptable [read]

It still keeps its own counter (`ENDS_DEPTH`, a depth, against the kernel's level count) and
its own multiplication; what it shares is three lines of pure checked arithmetic with a unit
test. The earlier claim ("calls nothing in `value.rs` that evaluates") still holds:
`test_levels` evaluates nothing. What is lost: a slip in `test_levels` is in both. But the
differential check could never have caught one there, since the overflow is unreachable on
64-bit and the reference isn't built for the web. If the stricter rule "the reference
shares only data types" is wanted, two lines of its own (`depth.checked_mul`, then
`checked_add` twice) would do; I wouldn't hold the merge for it.

## 5. Tests and docs

- `rule_k_levels_stop_at_the_top_of_the_range` moves the base so that 64-bit sees a 32-bit
  sized range: 128 tests, then `None`. Good; it is the only cover the 32-bit count gets, as
  no test runs on a 32-bit target.
- `the_ends_test_out_of_levels_says_different` fails without the fix (release: the level
  wraps to 0 and `z => z`, `z => v0` are "equal"; debug: overflow panic), checks that even
  equal ends are stuck, that the counter is left alone, and that tests work again after.
  Good. It doesn't cover rule S's path or the reference evaluator's `ends_level`; both are
  the same call, so fine.
- `docs/core.md`: the new sentences are accurate. Missing, once N1 is filed: that a single
  test is assumed to stay within 2^24 binders (today the text reads as if the scheme were
  complete). `value.rs`'s comment on `meet_in_evaluation` ("an answer found at one level
  holds at any") needs "unless a test below ran out of levels" (N2).
- [run] In the lane worktree, release: `value::tests::rule_k_levels_stop_at_the_top_of_the_range`, `rule_k::the_ends_test_out_of_levels_says_different` and `rule_k::the_ends_test_makes_its_own_fresh_variables` all pass (3 of 3). I did not run the new test against the unfixed code; that it fails there is from reading it.

## Follow-ups (possible tickets)

- **N1. Bound a comparison's binder depth to its level range** (soundness, pre-existing;
  Opus + Fable review). Section 3. Includes building the repro to see how many steps and
  seconds 2^24 binders take.
- **N2. Overflow answers and the memo.** Either don't file a "no" computed while a test
  below ran out of levels (a flag on the machine), or make running out a resource error
  (`E-RESOURCE`, "no answer") instead of "not equal": then no answer depends on depth, the
  memo's comment stays true, and the web says what happened. The ticket asked for "not
  equal", and it is sound; this is a design choice, small.
- **N3. 128 nested tests is few on the web.** Nesting follows recursion depth when a cast's
  ends hold the recursive call (`examples/accept/cast-ends-tested-once.sw` nests 40). With
  this change `tower hyp 129 = 0 := byComputing` would be refused on the web build and
  accepted natively (before it, the web build wrapped: the unsound case). A checked file
  behaving differently by target is user-visible. Options: N2's resource error (at least a
  clear message), or levels handed out compactly (a nested test starting just above the
  level its parent has reached, which also removes the fixed 2^24 and so N1's first case).
- **N4. The stuck-on-a-proof note** (`value.rs` near 6522) reports differing indices when
  the test ran out of levels. Cosmetic; goes away with N2's resource error.

## Not checked

- No 32-bit build or run; the 32-bit claims are from the arithmetic and the moved-base test.
- N1's repro was not written or run; the reachability is from reading `conv_with` and the
  budget.
- `unify_index.rs` was not re-read for negated uses of a comparison.
