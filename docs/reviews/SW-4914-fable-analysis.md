# SW-4914 (a comparison running past its level range): options for D3758

Fable, 27 Nov 2026. Read: `docs/core.md` (rules K and S, comparisons inside evaluation),
`crates/core/src/value.rs` (`test_levels`, `meet_in_evaluation`, `conv_with` and the five
fresh-variable sites, `ShapeMemo`, read-back, `mark_of_type`), `machine.rs`, `reference.rs`,
`check.rs` and `erase.rs` where they make variables, `docs/reviews/SW-4679-fable-review.md`,
and `git diff main...lane/SW-4914`. Marks: **[read]** from the code, **[run]** from a run,
**[inferred]** argued, not traced line by line.

## Recommendation

**(b), compact levels**, built on the lane's branch (its helper is already at the five
sites), with four additions: running out of levels is `E-RESOURCE`, never "not equal"; the
cap sits below the three sentinel levels at the top of `usize`; the reference evaluator
keeps fixed ranges with the lane's bound, so the two implementations differ; and an
invariant check behind a test flag. Details in section 5.

Reason in one line: (a) and (b) are both sound, but (a) leaves two refusals of correct
programs (a test over 2^24 binders deep; on the web, a 129th nested test, which ordinary
recursion depth reaches), and (b) leaves none on either target and makes the web and
native builds agree.

## 1. Is the bug as described? Yes [run, read]

- **Reproduced.** `probe/dtop1.sw` (depth 2^24 + 1) with the main checkout's release
  binary: `checked dtop1.sw`, exit 0 **[run, by me]**. The lane's logs show depth 2^24
  refused with `E-REFL` on both builds, and 2^24 + 1 `E-RESOURCE` with its fix **[lane's
  logs, read]**.
- **Mechanism [read].** The outer test (`castP`'s ends, `T D` against `U hyp D 0`) starts
  at 2^40 and makes one fresh variable per binder, so the last, `y`, is at 2^40 + D - 1.
  Evaluating `U`'s base case under it starts a nested test at 2^40 + 2^24, whose first
  fresh variable (for `w`) is at 2^40 + 2^24. At D = 2^24 + 1 that is `y`, so `w => w`
  against `w => y` answers "equal", the inner cast fires, the two types compare equal and
  the outer cast fires. The probe needs the exact depth only because its inner functions
  have one binder; inner functions with j + 1 binders collide at D = 2^24 + 1 + j.
- **The five sites [read].** `codomains`, lambda against lambda, eta in `conv_step`,
  `push_eta`, and `same_trees_of`'s `level + k`. I found no sixth in anything a test runs:
  read-back is not called from evaluation or comparison, and rule S's `slot_type` makes no
  variables. `conv_with` is a work list, so only the step budget limits depth (about 70
  steps a binder in the probes: 1.2 x 10^9 steps for 2^24).
- **Consequence: a cast firing with unequal ends, not a false theorem.** The probe's
  theorem is true and provable honestly: `castP a b h n = n` follows by `J` on `h`
  **[inferred, not run]**, and `hyp` is absurd anyway. What is wrong is the
  *computation*: `byComputing` accepted an equation that does not hold by computing.
- **Can it reach `False`? I found no route, and argue there is no direct one
  [inferred].** The wrong answer always belongs to the *nested* test, and a nested test
  only runs for a cast (or a rule S `case`) whose proof is in scope: `p: x = y`, or a
  proof of `D idx`. So every wrong firing uses an equation that has a proof where it
  fires: an instance of equality reflection, which holds in the model core.md argues
  from. The outer test's own variables never collide with each other, so its answer is
  wrong only through such firings. What is lost is what core.md actually claims: subject
  reduction (the fired cast's base has type `P x`, used at `P y`, equal only by the
  hypothesis), and with an absurd hypothesis the evaluator then runs ill-typed terms (a
  number applied as a function), which nothing in the kernel is argued safe for: a panic
  or a loop is possible, and I did not trace every reader. Treat it as a soundness bug
  (outside the argument), with no known exploit.
- **A worse relative, 32-bit only [inferred].** `level + 1` itself wrapping (2^32 binders
  in a top-level comparison) makes a comparison's *own* fresh variable name a real one,
  with no proof behind the wrong answer. At 70 steps a binder that is far past the default
  budget; a raised `STITCHWORT_WORK_LIMIT` could reach it. All options below close it with
  a checked addition.

## 2. Is (a) sound and complete for this class? Sound; two gaps beside it

- **Sound [read].** The helper is at all five kernel sites and at the reference
  evaluator's four (`conv_in`'s three, `same_trees`, `eta`), each *before* the fresh
  variable is used. Inside a test the top is `RESERVED_LEVELS + cast_levels`, the next
  test's first level, so every variable a test makes is below every nested test's; outside
  a test the top is `RESERVED_LEVELS`. Rule S goes through `meet_in_evaluation`, so it is
  covered. The error is a `Result` error, propagated by `?`, never filed in the memo; the
  one `.ok()?` (the stuck-on-a-proof note) only loses a message. I found no caller that
  accepts on a comparison's error.
- **Gap F1, pre-existing, 32-bit only [read, not run].** The last (128th) test's range is
  `[2^32 - 2^24, 2^32 - 1]`, which contains the sentinels `usize::MAX - 2` (`DUMMY_LEVEL`),
  `usize::MAX - 1` (`erase::ERASED`) and `usize::MAX` (`unused()`). A test there 2^24 - 3
  binders deep makes a fresh variable that evaluation takes for the erased placeholder
  (`is_erased` at `value.rs` 1769, 2646, 2692, 3181, 3781; 3181 takes a `case` branch on
  it). The lane's `fresh_past` saturates the top to `usize::MAX` there, so (a) does not
  close it. One line: cap fresh levels at `usize::MAX - 3`.
- **Gap F2, pre-existing, 32-bit only [read].** `check::is_type_former` (`check.rs`
  5463) walks a type's `Pi`s with `level += 1`, unchecked and outside `conv`. Past 2^31
  its variables are in the tests' range. It decides erasure flags, not proofs, and the
  budget stops it first at default settings; it should use the same checked helper.
- **Not complete in the other sense: it refuses correct programs.** The lane's
  `probe/etop1.sw` (two genuinely equal types 2^24 + 1 deep) checks on main in 42 s and is
  `E-RESOURCE` with (a) **[lane's logs]**. That is the kernel accepting less (D3688's kind
  of narrowing, though of the kernel, not a proved tool). And SW-4679's limits stay: the
  web build's 129th nested test answers "not equal" (N3: recursion depth 129 through a
  cast, where `examples/accept/cast-ends-tested-once.sw` already nests 40), and that "no"
  is filed in the memo (N2).
- The elaborator's unifier makes its own levels and is not covered by either option; the
  kernel rechecks what it concludes.

## 3. Is (b) sound? Yes, on one invariant, which needs care at three points

**The invariant.** The machine keeps `reached`: one above the highest level any comparison
in progress has made a variable at, or been told is free. A test started by evaluation
makes its fresh variables from `max(RESERVED_LEVELS, reached)`. It is sound if every
variable free in the test's two values is below that.

- **Where the free variables come from [inferred].** A cast is evaluated either outside
  any comparison (its variables are the context's, below `RESERVED_LEVELS` because a
  context that deep cannot exist in memory, as today) or while some comparison's task at
  level `l` runs (its variables are below `l`, by `conv`'s precondition). So it is enough
  that `reached >= l` for every task of every comparison in progress.
- **Point 1: the fresh variable is used before its task exists.** All five sites apply a
  closure to the fresh variable at `level` and only then push the task at `level + 1`;
  that application can already evaluate a cast with the variable in its ends. So `reached`
  must be raised in the helper, before the application, not when a task is popped. The
  lane's `fresh_past` is called in exactly that place at all five sites.
- **Point 2: a maximum, not the current level.** Sibling tasks of one comparison reuse
  levels, and a shared lazy value made under a deeper task may be forced later under a
  shallower one. The maximum over the whole comparison covers both; "the level of the task
  now running" would not.
- **Point 3: entry.** `conv_with` must raise `reached` to its own `level` argument on
  entry (the caller's promise that everything below it may be free) and restore the old
  value on exit. That also covers a top-level comparison that passes `RESERVED_LEVELS`,
  so that limit goes too.
- **Nesting and return.** A nested test starts at `reached`, raises it as it goes, and
  restores it when it returns (as `Restore` does for `cast_levels` today). Restoring is
  safe if the test's variables do not outlive it. They cannot reach the values of the
  comparison around it: a lazy cell forced during the test computes from its own
  environment, and the test returns a `bool`. They can stay in caches (the answer memo,
  call memos), where they are only ever matched structurally, never evaluated; see next
  point. This is the same assumption sibling tasks already make inside every comparison,
  so (b) adds no new one.
- **The answer memo (N2's caveat) [read `ShapeMemo`, inferred].** Entries are found by
  `identical` values, variable levels included. An answer is a function of the two values
  alone provided the test started above their free variables, since `conv` does not
  depend on which unused levels it takes. Under (b) that proviso always holds, so an
  entry filed when level L named one binder and found again when L names another is still
  right (the two pairs are the same up to renaming). And with running out an error rather
  than "not equal", no answer depends on depth any more: the comment "an answer found at
  one level holds at any" becomes true without N2's exception. Errors are not filed
  (already so).
- **Levels a running maximum would not see.**
  - Read-back (`quote`): makes variables at context levels and is never called inside a
    test **[read: no caller in evaluation or comparison]**. A term has a node per binder
    read back, so it cannot reach `RESERVED_LEVELS` on either target. Unchanged.
  - The checker's own binders (`cx.level()`): context depth, bounded by the term. Unchanged.
  - `is_type_former`: F2 above; give it the helper.
  - The elaborator: its unifier's levels, `mark_of_type`'s `level + 1_000_000`, and
    `DUMMY_LEVEL`. All untrusted and as today; the cap (below) keeps test levels off
    `DUMMY_LEVEL`.
- **The failure mode to respect.** Under fixed ranges, a site that forgets the helper is
  wrong only 2^24 binders deep. Under (b) it is wrong one binder deep. That makes a miss
  much easier to catch (every nested-test example exercises it) and much worse to ship.
  Hence the two safeguards in section 5: the reference evaluator on a different scheme,
  and a flagged check of the invariant itself.
- **32-bit.** Levels run from 2^31 to the cap, 2^31 in all along one chain of nested
  tests (not per test, and not 128 tests). Every level costs steps (about 70 in the
  probes), so the default budget ends the check long before; past it the checked addition
  gives `E-RESOURCE`. No wrap, no "not equal".

## 4. Other options

- **(c1) One counter for the whole check, never reused.** Sound and needs no argument
  about return, but it breaks the memo (the same pair met twice would have different
  levels in its nested values and never match, bringing back the doubling SW-4673 fixed)
  and on 32-bit it runs out by total work rather than depth. Worse than (b).
- **(c2) A tag for fresh variables (a bit, or a `Head` variant).** Separates fresh from
  real, which was never the problem here: this collision is fresh against fresh, an outer
  test's variable against a nested test's. Not a fix on its own.
- **(c3) Two-part names: (test depth, binder index) in `Head::Var`.** Collision-free by
  construction, and `RESERVED_LEVELS` disappears. Sound and limit-free. But every match on
  `Head::Var` in the kernel and elaborator changes, `conv`'s level becomes a pair, and the
  value may grow (a speed cost on the hot path). (a) is this idea packed into one word
  with a 24-bit index; (b) gets the same result without touching the value. I would pick
  this only if (b)'s invariant proved hard to keep.
- **(d) (a) with wider ranges: 2^40 levels per test on 64-bit.** One constant; no
  refusal the default budget can reach natively (2^40 binders is 7 x 10^13 steps); the
  argument stays static. It is the best *simple* option and a fair choice if the web
  build's limits are judged acceptable. But 32-bit has only 2^31 levels to split, so the
  web keeps a reachable limit on nesting or on depth, and differs from native. Making
  levels 64-bit on every target would fix that at the cost of conversions at every place
  a level indexes an environment.

By end state: soundness (a) = (b) = (c3) = (d), all with a checked bound; simplicity (d),
(a), then (b), then (c3); refusals (b) = (c3) none, (d) web only, (a) both targets; speed
all one compare (and for (b) one store) per binder, (c3) possibly slower.

## 5. Recommendation in detail: (b)

Kernel (`value.rs`, `machine.rs`), from the lane's branch:

1. `Machine::cast_levels` becomes `reached` (meaning as in section 3). `test_levels` and
   `LEVELS_PER_TEST` go from the kernel.
2. The helper at the five sites: checked `level + k`; error (`E-RESOURCE`) above a cap of
   `usize::MAX - 3` (below the sentinels, F1); raise `reached` to the result. No site in
   comparison code makes a variable any other way.
3. `conv_with` raises `reached` to its `level` on entry and restores on exit.
4. `meet_in_evaluation` starts at `max(RESERVED_LEVELS, reached)`, restores on return,
   clears the memo when the outermost test ends (as now). No "not equal" path: N2 and N4
   close, and so does N3 (no count of nested tests).
5. `is_type_former` uses the checked helper (F2).

Safeguards:

6. The reference evaluator keeps fixed ranges with the lane's `fresh_past` and its own
   arithmetic (not `value::test_levels`). It recurses, so its stack stops it long before
   2^24; it never needs compact levels. Differential runs then compare two different
   schemes at ordinary depths, which is where a missed site in (b) would show.
7. A check behind a test flag (as `STITCHWORT_CHECK_OPERATIONS` is): at the start of a
   test, walk the two values and closure environments without forcing, and assert every
   variable is below the start level (sentinels apart). On for the soundness examples and
   the fuzzers.

Tests (all small, named):

- `rule_k.rs`: the lane's test turned round. With `reached` set as if 2^24 binders deep,
  `w => cast` against `w => 0` (ends `z => z`, `z => w`) is *different*: not equal, and
  not an error. It answers "equal" on main.
- A nested test starts at `reached` and `reached` is back after it returns, after it
  errors, and after the outermost ends.
- At the cap: an error, `reached` and the memo left as they were, tests work again after.
- More than 128 nested tests with a 32-bit-sized space (the moved-base trick of
  `rule_k_levels_stop_at_the_top_of_the_range`): all answered.
- Unchanged and still passing: `examples/soundness/proof-irrelevance-31` and `-35`,
  `examples/accept/cast-ends-tested-once.sw`, `rules-k-and-s-nesting.sw`, the existing
  `rule_k` tests.
- Once, by hand or on Overmind, not in a suite (25 to 75 s and 300 MB each):
  `probe/dtop1.sw` gives `E-REFL`, `probe/etop1.sw` checks.

`docs/core.md`, "The comparisons inside evaluation": replace the fixed-range sentences
with: fresh variables start at the larger of 2^40 (2^31 on 32-bit) and one above the
highest level any comparison in progress has reached; a test gives its levels back when it
returns; running out is `E-RESOURCE`; the invariant and its three points; the memo
sentence, now unconditional. Drop "answers not equal" and the 128. Name the consequence
of SW-4914 accurately (a cast fired on unequal ends; no false theorem found). Update the
comments on `RESERVED_LEVELS` and `meet_in_evaluation` to match.

Who: Opus (kernel), then a Fable review of the diff, since a missed site is silent.
Estimate 40 min for the lane.

## Not checked

- No 32-bit build or run; the 32-bit claims are arithmetic.
- That `castP a b h n = n` is provable by `J` was not run.
- F1's effect (a fresh variable taken for the erased placeholder) is read from the
  `is_erased` sites, not reproduced.
- The "no route to `False`" argument assumes core.md's model validates firing a cast
  along any proof in scope; I did not re-derive that, nor trace what evaluation does with
  every ill-typed redex under an absurd hypothesis.
- That no persistent cache evaluates (rather than matches) a value holding a finished
  test's variable is from reading `ShapeMemo` and the call memo's use, not an exhaustive
  audit of the machine's caches.
- The main checkout's release binary was assumed to be built from current `main`.
