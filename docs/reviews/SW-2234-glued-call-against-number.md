# SW-2234: review of merge `41789a4a6` (SW-2211, a glued call against a number)

This is a review of SW-2211. That change alters what kernel conversion
accepts, so D2364 calls for an Opus review. I read code only: no builds or
runs.

What I read:

- The merge: `git show 41789a4a6 -m --first-parent`.
- In `crates/core/src/value.rs`: `conv`, `conv_with`, `conv_step` (the
  whole of it), `force`, `force_now`, `needs_forcing`, `force_call`,
  `resume`'s `Unfolded` arm, `unfold_now`, `glues`, `is_folded`,
  `folded_call` and `unfold_folded`.
- In `crates/core/src/native.rs`: `nat_like`, `view_with`, `compare_with`,
  `compare_lazily` and `view_to_call`.
- In `crates/core/src/reference.rs`: the number and folded parts of `conv`.
- In `crates/elab/src/unify.rs`: `unify_step` up to the number rule, and
  `one_step_apart`.
- The elaborator's other callers of `value::conv`.
- The changed test, `crates/driver/tests/proofs/proof_equivalence.rs`.
- `check_work.rs`'s SW-1153 test.
- `docs/reviews/SW-2158-glued-leaf-unfolding.md`, and tickets SW-2157 and
  SW-2211.

## Summary

**The change is sound, and it does what it says.** The new rule does one
thing: when a glued call meets a number, it replaces the call by
`force(call)`, its unfolding. That is a delta step, so every equality the
kernel now accepts is definitional.

The equalities it adds are the ones unglued evaluation and the reference
already accepted. Unglued, `jOuter 0` evaluates straight to the folded
call `outerN 0`. `conv_step`'s folded-call rule unfolds that before
numbers are compared, and the reference does the same (`reference.rs`,
around line 620). Glued, the call used to reach `compare_lazily`. That
function forced it to `outerN 0`, then kept it as a base it never opens.
Now the forced value goes back to the top of `conv_step`, where it meets
the same folded-call rule. So this closes a D3030 gap and opens none.

The lane's claim of "no extra work" is right:

- `compare_lazily` would have forced the same call on its first turn
  anyway (Q3).
- The unifier needed no change: it forces both sides before its
  folded-call rule and its number rule (Q4).
- The `docs/core.md` clause is accurate (Q5).

The work list can't loop without spending budget (Q2). The rule can fire
again, though, which the code comment denies (F1).

What's left is all SW-2157: the number comparison still doesn't open a
folded call under `Succ`. The depth-3 disagreement and the failure of
transitivity that the lane found are that gap, not this rule (F3).

No D questions.

Top recommendations:

1. Fix the comment's claim that the rule "happens once a side". It can fire
   again on a call that `unfold_folded` keeps. It still terminates, for the
   reasons in Q2 (F1, S).
2. Add two matrix terms (F2, S):
   - a definition that isn't `decreasing` and returns a field of a
     `decreasing` call, `def valueOf (x: Nat): Nat := (countDown x).value`;
   - a `decreasing` definition whose leaf is `valueOf`.

   Together they cover a glued call that forces to a field of a call, and
   the rule firing a second time. By my reading, both were wrong glued
   before SW-2211 and are right now.
3. Keep SW-2157 on Opus. When it lands, check whether its fix makes this
   rule redundant: a base that is a folded call would then be opened
   inside the number comparison. Then remove the rule or keep it, and
   update its `core.md` clause to match (F3).
4. Nothing to do on cost.
5. Nothing to do on the unifier.

| # | Finding | Severity | Confidence | Size |
|---|---|---|---|---|
| F3 | The number comparison still doesn't open folded calls under `Succ`. Glued and unglued still disagree at depth 3, and glued isn't transitive there. Already SW-2157. | medium (pre-existing) | high | M (SW-2157) |
| F1 | The comment "this happens once a side" is wrong: the rule can fire again on a call that `unfold_folded` keeps. | low | high | S |
| F2 | No matrix term where a glued call forces to a field of a call, or where the rule fires twice. | low | medium | S |

## Answers to the brief's questions

**Q1. Is every newly accepted equality definitional, and is it what
unglued and reference evaluation give?**

Yes, on both counts.

- **Definitional.** The rule pushes `(force(a), force(b))`
  (`value.rs:3257-3262`). `force` on the side that is a number changes
  nothing, because `needs_forcing` is false for anything but a call or a
  solved unknown. On the call, `force` gives its unfolding, through
  `force_call` and `unfold_now`. A hidden opaque body and a pending group
  member therefore still never unfold (`unfold_now`'s first test). Nothing
  is equated that wasn't equal by a delta step.
- **Agreement with unglued and reference.** Every definition with a body
  glues, `J`-bodied `jOuter` included (`unfold_now`, lines 2256-2271).
  Unglued, the unfolding is what evaluating the call gives directly. That
  value is then compared from the top in both modes, so they take the same
  rules from there. The reference's `conv` also unfolds a folded call at
  the top before numbers. The matrix checks all three for the new terms.
- **Mode.** In shortcut mode the rule is just as safe, since forcing is
  unfolding.
- **Memo.** `CallMemo` is untouched, because the rule never records
  anything.
- **Order.** The rule sits after the folded-call rule. If `b` is folded and
  `a` is a call, `b` is unfolded first, and the pair comes back here if
  `b` unfolds to a number. The new pairs this fixes, such as `jOuter 0`
  against `outerN 0`, go through that path; the matrix covers them, since
  both are depth-1 terms.

**Q2. The budget, and whether it can loop.**

A glued call never forces to another glued call at the top. `force_now`
returns a kept unfolding only if `!needs_forcing`. Otherwise it runs the
machine, and `resume`'s `Unfolded` arm forces again until the value isn't a
call (`value.rs:1914-1921`). So each firing removes the call it meets.

The rule *can* fire again, on a new call. `unfold_folded` keeps a glued
call as the call when forcing it doesn't give a call folded by name
(`value.rs:2517-2524`). The folded-call rule then pushes that call
against the number, and the new rule fires on it. Here is a scenario:

```
def valueOf (x: Nat): Nat := (countDown x).value

def outerV (x: Nat): Nat
  decreasing x
:=
  match x with
    | Zero => valueOf x
    | Succ m => outerV m [decreasing := omega]

def wrap (x: Nat): Nat := outerV x
```

Compare `wrap 0` with `0`:

1. The rule fires on `wrap 0`, which forces to the folded call `outerV 0`.
2. The folded-call rule unfolds that to the call `valueOf 0`, and keeps it
   as the call.
3. The rule fires again. `valueOf 0` forces to `(countDown 0).value`, which
   is opened from the top and gives `0`.

This still terminates:

- every conversion task steps the budget (`conv_with`, `value.rs:3067`);
- every firing spends at least one evaluation step, either in `run` or on
  the step that first computed a kept unfolding;
- each chain of firings follows a chain of unfoldings, so a call nested
  too deeply ends in E-RESOURCE, not a hang.

The comment's last sentence is wrong (F1), but the code is right.

**Q3. "No extra work": `compare_lazily`'s forcing.**

The claim is right. Take one side a call at the top and the other side
something `nat_like`. On its first turn, `view_to_call` stops at the call
with `k1 = 0`. The number side has either `k2 ≥ 1` (a `Succ`, or a `k + x`
with `k > 0`) or no base (a number or `Zero`).

So neither of the first two arms of `unfold_first` applies, and the third
(`native.rs:848`) forces the call: the same call, once, that the new rule
forces. The eager `native::compare`, used with shortcuts disabled, forces
it in `view_with` too.

From there, the new path does the same work wherever the old one gave the
same answer:

- **A sum or a `Succ`.** It goes back to `compare_lazily`, which keeps the
  calls inside it lazy, as before. SW-1153's case is one: `Succ (length
  xs)` against a glued `length (Cons …)` forces once and then compares
  the two `length` calls by their arguments.
- **A stuck value.** It still gets "different".
- **A folded call.** Only here does the new path do more, by unfolding it.
  That is the fix itself, and unglued does it too.

Beyond that, the new path costs one more conversion task (one budget step)
and a check that `b` needs no forcing. `check_work`'s SW-1153 test only
bounds growth, so it can't be upset by the extra step.

**Q4. Is leaving the unifier alone right?**

Yes. `unify_step` forces both sides (`unify.rs:1325`) before its
folded-call rule and its number rule. The forced call is therefore a
folded call by then, and is unfolded before numbers are compared: the
order the new conv rule recreates.

The rules before the forcing can't intercept a call against a number:

- both shortcuts for calls of one definition, and `one_step_apart`, need
  both sides to be calls;
- `meta_against_call` needs an unknown.

The elaborator's own uses of `value::conv` (`check.rs` `conv_now`,
`congruence.rs`, `derive.rs`, `lib.rs`) get the new rule automatically.
`conv` compares unknowns by their numbers, and `conv_now` refreshes and
retries for that, so a solved unknown against a number needs nothing
extra here.

Under `Succ`, the unifier's `native::compare` has the same gap as conv's.
SW-2157 already lists it.

**Q5. Is the `core.md` clause accurate?**

Yes. "A glued call against a number is forced first and compared again
from the top, so one that computes to such a folded call, `id (f n)`, is
too, as it is with gluing off" matches the code.

`id (f n)` is a fair example: `id` has a body, so it glues. The clause
doesn't mention the gap under `Succ`. That belongs with SW-2157, whose fix
will rewrite this sentence (F3).

**Q6. Are the matrix rows enough?**

Mostly. `withProof` covers a call that returns its argument past a proof.
`jOuter` covers `J` on `rfl` with a `decreasing` base. `jRefl` covers `J`
on a theorem's proof, folded by name. All three are compared against `0`,
`Succ 0` and `Succ (Succ 0)`, in every mode and in both orders. The
missing shapes are two (F2):

- a glued call that forces to a field of a call;
- the rule firing twice.

The depth-3 case can't go in until SW-2157 lands: the matrix would fail.

## Findings

### F1 (low, high confidence): the comment says the rule fires once a side

`crates/core/src/value.rs:3255-3256`: "The forced value is never a call, so
this happens once a side."

The first half is true. The conclusion isn't: the `wrap 0` scenario in Q2
fires the rule twice on one side. A reader who trusts the comment might
later move the rule, or add one that turns a value into a call, without
checking termination.

Recommended change (S): replace the sentence with one like "The forced
value is never a call; a call met here again comes from unfolding further,
and each conversion task spends budget."

### F2 (low, medium confidence): matrix gaps

`crates/driver/tests/proofs/proof_equivalence.rs`, `FIELDS_PROGRAM` and
`FIELD_OPS`.

1. **No glued call that forces to a field of a call.** Take `def valueOf
   (x: Nat): Nat := (countDown x).value`. By my trace, `valueOf 0`
   against `0` was false glued before SW-2211. `compare_lazily` forced the
   call to the stuck field `(countDown 0).value` and kept it as a base.
   Unglued, `is_folded`'s first arm unfolds it and gives true. Now glued is
   true as well. That is another instance of the bug this change fixed,
   but no matrix term exercises it.
2. **The rule never fires twice.** Q2's `outerV` (or `wrap`) shape would
   cover it.

Recommended change (S): add `valueOf` and `outerV` to `FIELDS_PROGRAM`,
`FIELD_OPS` and `field_op`. Then run `task test:one -- proof_equivalence`.
The matrix grows by the square of its term count, so check that the run
stays fast.

### F3 (medium, pre-existing, high confidence): folded calls under `Succ`

`native::compare_lazily` and `view_to_call` (`native.rs:828-880`),
`compare_with`, the reference's `compare_with` call, and the unifier's
`native::compare`. A base that is a folded call is never opened, so
`Succ (outerN 0)` against `2` is false in every mode. That is an
incompleteness all modes share.

Glued and unglued also disagree, at depth 3:

- `Succ (withProof (outerN 0))` against `Succ (withProof 1)`:
  - glued: the two `withProof` calls are compared by their arguments, and
    `outerN 0` against `1` is true at the top;
  - unglued: `Succ (outerN 0)` against `2`, false.
- So glued says these two are equal; but it also says `Succ (withProof
  1)` equals `2` and `Succ (withProof (outerN 0))` doesn't, so glued isn't
  transitive.

Every "true" here is still definitional, so nothing unsound is accepted:
the cost is true proofs rejected, and a relation that isn't an equivalence
on such terms.

SW-2211 fixed only the top level, as its ticket says. SW-2157 owns this
and already records the depth-3 case.

Recommended change: SW-2157 as filed (M, Opus). Two notes for that lane:

- Once a folded base is opened inside the number comparison, this rule may
  no longer be needed: the forced value would be opened there. Decide
  whether to keep it (it is cheap, and it keeps the top level the same as
  for other shapes) or to remove it, and rewrite its `core.md` clause to
  match.
- Add the depth-3 pair and `Succ (outerN 0)` to the matrix, as the ticket
  says.

## Checked and sound

- **Only one side can be a call.** The rule's condition can't hold with
  both sides calls, because `nat_like` is false for a call. It can't steal
  a pair from the first rule, which compares two calls of one definition.
- **The number side is unchanged.** `force` on a `nat_like` value changes
  nothing.
- **Shortcuts disabled.** The rule fires in that mode too, which brings it
  into line with glued and unglued (it was wrong in the same way before).
- **The kernel's own glued mode.** It runs the same `conv_step`, and the
  matrix checks it (`How { kernel: true, .. }`).
- **Bases handed on.** The pairs `compare_lazily` hands to `same` are
  never `nat_like`, because `view_to_call` strips the numbers. So a call
  against a base, for example a variable, still goes to the call rule at
  the bottom of `conv_step`, which forces it and compares again from the
  top. That path never needed this fix.
- **Other shapes against a call.** Compact text against a call expands a
  cell and then reaches the call rule, so it was already compared again
  from the top. Numbers were the only rule, placed before the call rule,
  that forced a call without going back to the top. The existing comment
  on the call rule, "the cases above that a call can reach … look inside
  it themselves", is still accurate.
- **`force` can't return a call.** It can't return one at the top
  (`force_now`, and `resume` `Unfolded`).
- **Fields of calls run again.** Repeated unfolding of fields of calls
  (`code-review-core.md`, SW-1829) can now happen on one more path, a call
  that forces to a field of a call against a number. Unglued takes the
  same path, so nothing changes in kind.

## Status of earlier reviews' findings in scope

- **`docs/research/rust-codebase-review.md` (1 Nov).** It has no finding
  on conversion's number path.
- **`docs/reviews/SW-2158-glued-leaf-unfolding.md`.**
  - Recommendation 4, keeping SW-2157 a separate lane, is still right.
    SW-2157 is still open, and this change confirms that the two causes
    are distinct.
  - F1, `unfold_folded` not forcing solved unknowns between levels, is
    outside this change and wasn't touched.
- **`code-review-core.md`'s SW-1829 note** (fields of calls run again) is
  unchanged by this merge. See "Checked and sound".

## Tickets to file

- **Lane A: Sonnet, about 30 min.** F1 and F2 together: reword the
  comment, and add `valueOf` and `outerV` (or `wrap`) to the
  fields-of-calls matrix. Test with `task test:one -- proof_equivalence`.
  It touches no terms or hashes.
- **Lane B: SW-2157, Opus, already filed.** Append F3's notes: decide
  whether to keep the SW-2211 rule once folded bases under `Succ` are
  opened, update its `core.md` clause, and add the depth-3 pair to the
  matrix.

## Calls I made

- F1 and F2 go in one small lane, not two, since both touch only this
  change's area.
- `core.md` says nothing about the gap under `Succ`, and I folded that into
  SW-2157 rather than a separate doc fix: that lane will rewrite the clause
  anyway.
