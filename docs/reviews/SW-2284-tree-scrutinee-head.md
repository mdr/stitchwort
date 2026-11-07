# SW-2284: review of SW-2257 (tree comparisons bring a scrutinee to its head)

Reviewed: merge `6c67ab844` (`crates/core/src/value.rs` `walk_tree` and
`tree_scrutinee`, `crates/core/src/reference.rs` `same_trees`'s `settle`,
`proof_equivalence.rs`, `docs/core.md`). Read only. I also checked three
small probes with the release binary built after the merge.

## Summary

**Sound.** Everything newly accepted follows from delta (unfolding a folded
call) and iota on a number's or compact text's head, which is what `branch`
already does when a program runs. The three arms added to `walk_tree` are the
same arms as `branch`'s, with the same guards (`d` is `Nat`; `d` is the text
builtin's list). The reference agrees. The walk ends: every turn of its loop
uses a budget step, and the number of splits is bounded by the depth of the
tree, not by the size of the number or text. The slowdown has a plausible
cause in the code (F1): every walk that used to stop at the first folded
scrutinee now runs that call's unfolding again, on each side. Evaluation had
already run the same unfolding to get the call stuck.

Top recommendations:
1. F1: in `same_trees_of`, don't walk the second tree when the first walk
   ends in `Other`. Then measure how many unfoldings `tree_scrutinee` runs on
   the AoC check before going further.
2. F2: a scrutinee that stays a stuck folded call still makes the comparison
   answer "different". Compare it as a stuck `case` instead, or document the
   gap that remains under G1.
3. F3: add an "alike helpers" context over compact text to the property
   tests. The new `Chars` arm has no test.
4. F4: remove G1 and G3 from `known_gap` and fold their tests into the main
   one.
5. F5: two small `core.md` edits.

| # | Severity | Confidence | Area | Finding |
|---|---|---|---|---|
| F1 | medium | medium | performance | Walks now replay the folded unfoldings that evaluation already did, on both sides, even when the answer stays "different" |
| F2 | low | medium | completeness | A scrutinee that stays a stuck folded call still gives `Other`; G1 is marked fixed without saying so |
| F3 | low | high | test gap | No property-test context reaches `walk_tree`'s `Chars` arm |
| F4 | low | high | maintainability | `known_gap` still excuses the G1 and G3 pairs from the main wrapping test |
| F5 | low | high | docs | `core.md`'s G1 row overstates the fix; the conversion bullet could name the head computation |

No high findings, one medium, four low.

## Findings

### F1 (medium, medium confidence): the extra work is real, and part of it is easy to avoid

`crates/core/src/value.rs` `walk_tree`, `tree_scrutinee` and
`same_trees_of` (`match (walk_tree(g, t1, …)?, walk_tree(g, t2, …)?)`).

`same_stuck_trees` only sees calls that evaluation has already left stuck.
To get there, evaluation walked the same tree and unfolded each folded
scrutinee on its path (`Frame::Scrutinee`). The walk now replays the whole
path. Each folded scrutinee is a full `run` of that definition: a
`decreasing` definition's fuelled helper, `k * x`, a dictionary or a lift
leaf. Folded-by-name calls and dictionaries don't glue, so nothing is shared
with evaluation's earlier unfolding. Before the change, such a walk returned
`Other` at the first folded scrutinee, at almost no cost.

The probe pairs are the usual shape: `pickA (yes 0) x` against
`pickB (yes 0) x`, with the same argument on both sides. There the same
unfolding runs twice, once per side. A walk that now gets past what used to
stop it also evaluates and compares leaves, and those can open further
trees. Most of that work is in the elaborator's unification. There, a
comparison that answers "different" is ordinary (it tries another route),
so for those comparisons the new work only adds time. A step count up by
about 10% and user time up by about 9% (73 s against 67 s) fit work that the
change really adds, more than noise. That is consistent with the walk's
steps and `run`'s steps both being charged to the budget.

Cheap guards, in order of value:
- **Short-circuit the second walk (S).** `same_trees_of` builds the tuple
  eagerly, so when `t1`'s walk ends in `Other`, `t2` is still walked and its
  scrutinees unfolded, and the answer is `false` either way. Walk `t1`, and
  return `false` on `Other` before walking `t2`. One caveat: if walking `t2`
  would run out of budget, the answer becomes `false` instead of
  `E-RESOURCE`. That only happens where `t1` already decided "different" by a
  shared limit. I'd accept it, but the reference should do the same, so the
  modes stay alike.
- **Share one unfolding between the sides (S to M).** When both sides' slots
  hold the same value (`Rc::ptr_eq`, the common case shown above), give the
  second walk the first walk's result. Keep this local to one
  `same_trees_of` call. Don't make a table keyed by addresses that outlives
  the call.
- **Measure first.** Count the calls to `tree_scrutinee` that unfold, and
  their steps, on the uncached AoC check. That shows whether the replays
  explain the 6 s before any heavier fix, such as writing the unfolded value
  back into `env`. I'd avoid that last one, because leaves and eta fields
  would then show unfoldings in solutions.

### F2 (low, medium confidence): a stuck folded scrutinee still means "different"

`walk_tree`, the `_ => return Ok(TreeEnd::Other)` arm, reached when
`tree_scrutinee` returns a value for which `folded_call` still holds; and
`settle` in `reference.rs` (`_ => return Ok(None)`).

When `unfold_folded` returns `None` (the folded definition's own tree is
stuck and gives back the same call), the walk answers "different". Two
alike trees stuck on the same such call are equal by the congruence rule
for `case`. The scrutinees are equal by the limits' rule ("a call folded by
name and stuck is compared by its definition and arguments"). Every mode
agrees, so this is a gap, not a soundness problem.

The gap is narrow. These two probes are accepted after the merge:
`pickA (yes y) x = pickB (yes y) x`, with a `decreasing` `yes` on a variable
(it unfolds to the fuelled helper's stuck call), and
`pickA (observe q) x = pickB (observe q) x`, with a lift-leaf `observe` on a
variable (it unfolds to the stuck `Quot.lift`). What's left is the case
where unfolding gives back the same call, such as a dictionary-valued
function matching on a variable. I didn't construct a probe for it.

The `!folded_call` guard on the `Stuck` arm used to keep a folded call that
*could* unfold from being compared as stuck. Now `tree_scrutinee` has
already tried, so the guard can go: compare a still-folded scrutinee as a
stuck `case`, in both evaluators. Keep the eta arm's guard, which matches
`branch`. Size S to M, plus a probe.

### F3 (low, high confidence): the `Chars` arm has no test

The "text match" context in `proof_equivalence.rs` uses one definition,
`textTag`, so it never reaches `same_stuck_trees`. The alike-helper contexts
are all over `Nat`. The reference expands compact text in `force`, so a
property test with a context like `headA s x` against `headB s x`, for
`s` = `"ab"` or `""`, would compare this arm against the reference. A probe
of this shape (`chars.sw`, with `headA "abc".chars x = headB "abc".chars x`)
is accepted. I didn't confirm that the literal stays compact by the time it
reaches the walk. Size S.

### F4 (low, high confidence): G1 and G3 are still listed as gaps

`known_gap`, the first three arms. Those pairs are still filtered out of
`wrapping_a_subterm_in_an_identity_keeps_it_equal` and checked only by
`wrapping_known_failure_g1` and `_g3`, whose names say "known failure" but
which now pass. Delete the three arms and the two tests. The main test then
covers these pairs, and `the_known_gaps_hold_in_the_plain_evaluator` stops
checking them. Size S.

### F5 (low, high confidence): `core.md`

- The G1 row says "fixed". After F2, it should say what's left (a scrutinee
  that stays a stuck folded call), or F2 should be fixed first.
- The "Conversion `≡`" bullet ("a `case` whose scrutinee's head is a
  constructor takes its branch") is correct, given the "Head" definition
  (folded call unfolded, `k` split, a range split). A link to "Head", or a
  few words in brackets, would make it clear that numbers and text count.
- The rest is accurate. G3's "number or a range" matches the `Nat` and
  `Chars` arms. The comment at `value.rs` above `opens_by_tree` is updated
  to match.

## Checked and sound

- **Definitional.** `tree_scrutinee` is delta (`unfold_folded`, then
  `force`), and the split arms are `branch`'s `Ctor`, `Nat`/`NatAdd`
  (guarded on `Nat`) and `Chars` (guarded on `text.list`) arms. Nothing
  else is newly accepted. A `Nat` of another type, or an empty
  `split_value`, falls through to `Other`.
- **Eta arm.** Unchanged. It still projects from `unforced`, as `branch`
  does from the environment's value. A neutral that comes out of an
  unfolding can now take it, which is correct.
- **Reference agreement.** `settle` adds the same unfolding (`unfold_folded`
  repeats until the value is no longer folded) and the `Nat` split. It needs
  no `Chars` arm, because the reference's `force` expands compact lists. The
  reference's `is_folded` is the machine's `folded_call` (it leaves out
  fields of calls), so a stuck `(f x).i` scrutinee is `Stuck` in both.
- **Glued and unglued.** `tree_scrutinee` loops on `folded_call` after
  `force`, so a glued result that forces to another folded call (SW-2126) is
  unfolded too. In unglued mode `unfold_folded` returns it directly. The
  un-ignored G1 and G3 pairs run in every mode.
- **Termination and budget.** `tree_scrutinee` uses a step per unfolding,
  and `run` uses its own. Each split is a turn of `walk_tree`'s loop, which
  uses a step and goes one node down a finite tree. `chars::split` is O(1)
  (`uncons` shares the buffer). `native::split` costs O(digits) for `n - 1`,
  at most once per node. A huge number or text can't make a walk long.
- **Memo (SW-395, SW-2269).** It is keyed on the two calls, not on their
  scrutinees, so this change doesn't affect it.
- **1 Nov review** (`docs/research/rust-codebase-review.md`,
  `architecture-review.md`): it has no findings on this code.

## Tickets to file

- **Lane A (Opus, 45 min): tree walk costs and stuck folded scrutinees.**
  F1's short-circuit and sharing, in `value.rs` and the reference. Count
  `tree_scrutinee`'s unfoldings on one AoC day before and after. F2's
  removal of the guard, with a probe and a `core.md` edit (F5's first
  point).
- **Lane B (Sonnet, 30 min): proof_equivalence tidy-up.** F3's
  "alike helpers over text" context, F4's removal of G1 and G3 from
  `known_gap` and the two tests, and F5's second point.

No D questions.

Calls I made: I recommend the short-circuit despite the `E-RESOURCE`
caveat, as long as both evaluators get it. I recommend against writing the
unfolded scrutinee back into the environment.
